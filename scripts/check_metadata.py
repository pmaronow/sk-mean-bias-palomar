#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Validate metadata with pinned official Palomar code and upstream v0.4 schema.

Downloaded validators, schemas, their original licenses, and optional JSON
receipts are kept outside the public source tree. No submission is made.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from urllib.request import Request, urlopen

PALOMAR_REVISION = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
SCHEMA_REVISION = "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"
ASSETS = {
    "palomar": {
        "LICENSE": "10321b0cca2b8025d4b5065dd20e22c1f74da2e872c12363e3601974e093bc21",
        "scripts/submission_contract.py": "724f82211ef702e2d1b4e5012183e532bd8f8ba03ba676022e4722a420c5be75",
        "scripts/orcid_validation.py": "2f368bf27a27f150da1a03f502ff0f45845fce1d5ebcf8dcfcf10908b5d360b7",
        "scripts/verification_errors.py": "ce58c4adc2f896a8ce69961d1f49ada7f571d86f9638a196f34197e3293cc776",
        "taxonomies/arxiv-categories.json": "3b339cf140a914c50bab39b1c44df2437ce3984bd09bb2150fcb0edd60eda776",
        "taxonomies/msc2020-codes.json": "b4de69f1f562da01e0f4580cecc0ab36098f5297bb7cdd669c8ec3b0d3606060",
    },
    "upstream": {
        "LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
        "schema/formalization.schema.json": "22bd0b61631535fc68efbdf01e3013362437673ac836d721dfbdf80773244ec3",
        "schema/v0.4.schema.json": "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce",
    },
}


def require_external(path: Path, repository: Path) -> Path:
    resolved = path.resolve()
    if resolved == repository or repository in resolved.parents:
        raise ValueError("validator cache and receipts must be outside the public source tree")
    return resolved


def fetch_assets(cache: Path) -> None:
    repositories = {
        "palomar": ("PalomarRegistry/PalomarSubmission", PALOMAR_REVISION),
        "upstream": ("mathlib-initiative/formalization.yaml", SCHEMA_REVISION),
    }
    for group, files in ASSETS.items():
        repository, revision = repositories[group]
        for filename, expected in files.items():
            target = cache / group / filename
            if not target.resolve().is_relative_to(cache.resolve()):
                raise ValueError(f"cached asset path escapes the external validator cache: {target}")
            if target.is_symlink():
                raise ValueError(f"refusing cached symbolic link: {target}")
            data = target.read_bytes() if target.is_file() else None
            if data is None or hashlib.sha256(data).hexdigest() != expected:
                request = Request(
                    f"https://raw.githubusercontent.com/{repository}/{revision}/{filename}",
                    headers={"User-Agent": "SKMeanBias-local-metadata-verification"},
                )
                with urlopen(request, timeout=30) as response:
                    data = response.read(2 * 1024 * 1024 + 1)
                if len(data) > 2 * 1024 * 1024 or hashlib.sha256(data).hexdigest() != expected:
                    raise ValueError(f"pinned asset failed SHA256 verification: {group}/{filename}")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("metadata", nargs="?", type=Path)
    parser.add_argument("--cache-dir", type=Path, help="external reusable validator cache")
    parser.add_argument("--report", type=Path, help="external JSON receipt path")
    arguments = parser.parse_args()
    repository = Path(__file__).resolve().parent.parent
    metadata = arguments.metadata or repository / "formalization.yaml"
    # Validate every user-selected location before creating any cache directory.
    report_path = require_external(arguments.report, repository) if arguments.report else None
    if arguments.cache_dir:
        cache = require_external(arguments.cache_dir, repository)
    else:
        temporary_parent = require_external(Path(tempfile.gettempdir()), repository)
        cache = Path(tempfile.mkdtemp(prefix="sk-mean-bias-metadata-", dir=temporary_parent))
    fetch_assets(cache)

    import jsonschema
    import yaml

    sys.path.insert(0, str(cache / "palomar"))
    from scripts.submission_contract import (
        declared_orcids,
        load_formalization_metadata,
        normalized_provenance,
    )
    from scripts.orcid_validation import validate_records

    # The official loader rejects duplicate keys and YAML merge keys and checks
    # Palomar's exact taxonomy snapshots and provenance contract.
    document = load_formalization_metadata(metadata)
    if document.get("version") != "v0.4":
        raise ValueError("this repository requires explicit metadata version v0.4")
    schema = json.loads((cache / "upstream/schema/v0.4.schema.json").read_text())
    jsonschema.Draft7Validator.check_schema(schema)
    jsonschema.Draft7Validator(schema).validate(document)
    provenance = normalized_provenance(document)
    orcid_checks = validate_records(declared_orcids(document, provenance))
    license_name = document["project"]["license"]
    root_license = repository / "LICENSE"
    if license_name != "MIT" or not root_license.is_file():
        raise ValueError("expected this project's MIT root LICENSE and matching project.license")
    license_text = root_license.read_text(encoding="utf-8")
    for required in (
        "Permission is hereby granted, free of charge",
        "THE SOFTWARE IS PROVIDED",
    ):
        if required not in license_text:
            raise ValueError("root LICENSE does not contain the expected MIT terms")
    # This identity check does not replace Palomar's SPDX licence detector.
    commit = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "HEAD"],
        text=True, capture_output=True, check=False,
    )
    state = subprocess.run(
        ["git", "-C", str(repository), "status", "--porcelain"],
        text=True, capture_output=True, check=False,
    )
    receipt = {
        "check": "pinned-palomar-metadata-and-upstream-v0.4-schema",
        "passed": True,
        "source_commit": commit.stdout.strip() if commit.returncode == 0 else None,
        "source_dirty": bool(state.stdout.strip()) if state.returncode == 0 else None,
        "metadata_sha256": hashlib.sha256(metadata.read_bytes()).hexdigest(),
        "palomar_verifier_revision": PALOMAR_REVISION,
        "schema_revision": SCHEMA_REVISION,
        "asset_sha256": ASSETS,
        "orcid_checks": orcid_checks,
        "root_license_identity": "MIT expected terms; not the official SPDX detector",
        "limitations": (
            "Checks metadata schema, official Palomar field contract, and any declared ORCID records. "
            "Does not perform Lean builds, proof checks, source-closure validation, or editorial review."
        ),
    }
    if report_path:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("PASS: official pinned Palomar metadata contract and upstream v0.4 schema")
    print(f"Metadata SHA256: {receipt['metadata_sha256']}")
    print(f"External validator cache: {cache}")
    if report_path:
        print(f"Receipt: {report_path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"FAIL: {type(error).__name__}: {error}", file=sys.stderr)
        raise SystemExit(1) from None
