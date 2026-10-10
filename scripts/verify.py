#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Run local verification and bind its outcomes to unchanged public sources.

All generated records and raw logs remain outside the public source tree.
This local pipeline does not execute Palomar's protected canonical intake or
editorial review. Cached build reuse is permitted when Lake judges it current.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from check_repository import source_manifest
from lean_source_scan import check_private_import_capacity, dependencies

ROOT = Path(__file__).resolve().parent.parent
BUILD_TARGETS = ["HexagonUpperBound", "Challenge", "Solution"]
CHECK_NAMES = [
    "metadata", "repository", "statement_preservation", "local_build_closure",
    "lean_build", "source_artifacts", "numbered_claims", "selected_proofs", "comparator",
]


def external(path: Path) -> Path:
    path = path.resolve()
    if path == ROOT or ROOT in path.parents:
        raise ValueError("SK_VERIFY_LOG_DIR and the temporary directory must be outside the public source tree")
    return path


def output_directory() -> Path:
    supplied = os.environ.get("SK_VERIFY_LOG_DIR")
    if supplied:
        output = external(Path(supplied))
        output.mkdir(parents=True, exist_ok=True)
        return output
    parent = external(Path(tempfile.gettempdir()))
    return Path(tempfile.mkdtemp(prefix="sk-mean-bias-checks-", dir=parent))


def public_files() -> list[Path]:
    result = []
    for directory, subdirectories, names in os.walk(ROOT, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake", "__pycache__"}
            and not (Path(directory) / name).is_symlink()
        )
        result.extend(
            path for name in sorted(names)
            if (path := Path(directory) / name).is_file() and not path.is_symlink()
        )
    return sorted(result)


def public_snapshot() -> dict:
    files = {
        path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in public_files()
    }
    digest = hashlib.sha256(json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"algorithm": "sha256", "tree_sha256": digest, "file_sha256": files}


def git_identity() -> dict:
    def query(*arguments):
        process = subprocess.run(
            ["git", "-C", str(ROOT), *arguments], text=True, capture_output=True, check=False,
        )
        return process.stdout.strip() if process.returncode == 0 else None
    state = query("status", "--porcelain")
    return {"commit": query("rev-parse", "HEAD"), "dirty": bool(state) if state is not None else None}


def live_closure() -> dict:
    sources = {path for path in public_files() if path.suffix == ".lean"}
    entrypoints = [ROOT / (name + ".lean") for name in BUILD_TARGETS]
    missing_entrypoints = [str(path.relative_to(ROOT)) for path in entrypoints if not path.is_file()]
    closure = dependencies(entrypoints, [ROOT]) if not missing_entrypoints else set()
    uncovered = sorted(str(path.relative_to(ROOT)) for path in sources - closure)
    extra = sorted(str(path.relative_to(ROOT)) for path in closure - sources)
    return {
        "passed": not missing_entrypoints and not uncovered and not extra,
        "build_targets": BUILD_TARGETS,
        "local_source_files": len(sources),
        "local_import_closure_files": len(closure),
        "outside_build_closure": uncovered,
        "unexpected_closure_files": extra,
        "missing_entrypoints": missing_entrypoints,
        "closure_source_sha256": {
            path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(closure)
        },
        "basis": (
            "Conservative live local-import graph. A successful Lake build of the three entrypoints "
            "must cover every retained local Lean source; artifact presence is supplementary."
        ),
    }


def artifact_check(closure: dict, build_returncode: int) -> dict:
    missing = []
    for name in closure["closure_source_sha256"]:
        artifact = ROOT / ".lake/build/lib/lean" / Path(name).with_suffix(".olean")
        for candidate in [artifact, Path(str(artifact) + ".private"), Path(str(artifact) + ".server"),
                          artifact.with_suffix(".ir")]:
            if not candidate.is_file():
                missing.append(str(candidate.relative_to(ROOT)))
    return {
        "passed": closure["passed"] and build_returncode == 0 and not missing,
        "local_source_files": closure["local_source_files"],
        "complete_local_build_closure": closure,
        "lake_build_exit_code": build_returncode,
        "required_module_artifact_suffixes": [".olean", ".olean.private", ".olean.server", ".ir"],
        "missing_artifacts": missing,
        "cache_policy": "Lake may reuse matching current artifacts; this is not a cold-build claim.",
        "limitation": "Artifact existence alone is not a compiler or independent-kernel certificate.",
    }


def write_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def run_pipeline(output: Path) -> int:
    before = public_snapshot()
    start_identity = git_identity()
    core_before = source_manifest(ROOT)
    input_record = {
        "check": "local-verification-pipeline-input",
        "source_identity": start_identity,
        "public_source_snapshot": before,
        "mathematical_compiler_source_manifest": core_before,
        "pipeline_script_sha256": before["file_sha256"]["scripts/verify.py"],
        "planned_checks": CHECK_NAMES,
        "limitations": "Local checks; not Palomar protected intake or editorial review.",
    }
    write_json(output / "verification-input.json", input_record)
    statuses = {name: {"status": "not_run"} for name in CHECK_NAMES}
    environment = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1", "SK_VERIFY_LOG_DIR": str(output)}
    current = None
    closure = None
    error = None
    runtime = None

    def run(name: str, arguments: list[str], extra_environment: dict | None = None) -> int:
        nonlocal current
        current = name
        log = output / (name + ".log")
        statuses[name] = {"status": "running", "command": arguments, "log": log.name}
        print(f"Checking {name}; log: {log}", flush=True)
        with log.open("w", encoding="utf-8") as stream:
            process = subprocess.run(
                arguments, cwd=ROOT, env={**environment, **(extra_environment or {})},
                stdout=stream, stderr=subprocess.STDOUT, check=False,
            )
        statuses[name].update(
            status="passed" if process.returncode == 0 else "failed",
            exit_code=process.returncode,
            log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
        )
        if process.returncode:
            raise RuntimeError(f"{name} failed with exit {process.returncode}; see {log}")
        return process.returncode

    try:
        runtime = check_private_import_capacity()
        input_record["private_import_runtime"] = runtime
        write_json(output / "verification-input.json", input_record)
        python = sys.executable
        run("metadata", [python, "scripts/check_metadata.py", "--report", str(output / "metadata.json")])
        run("repository", [python, "scripts/check_repository.py", "--output", str(output / "repository.json")])
        run("statement_preservation", [python, "scripts/check_statement_preservation.py", "--output", str(output / "statement-preservation.json")])
        current = "local_build_closure"
        closure = live_closure()
        write_json(output / "local-build-closure.json", closure)
        statuses[current] = {"status": "passed" if closure["passed"] else "failed", "receipt": "local-build-closure.json"}
        if not closure["passed"]:
            raise RuntimeError("Retained sources are outside the requested Lake build closure")
        build_returncode = run("lean_build", ["lake", "build", *BUILD_TARGETS])
        current = "source_artifacts"
        artifacts = artifact_check(closure, build_returncode)
        write_json(output / "source-build.json", artifacts)
        statuses[current] = {"status": "passed" if artifacts["passed"] else "failed", "receipt": "source-build.json"}
        if not artifacts["passed"]:
            raise RuntimeError("Successful full local closure build lacks required module artifacts")
        run("numbered_claims", [python, "scripts/check_numbered_claims.py", "--output", str(output / "numbered-claims")])
        run("selected_proofs", [python, "scripts/audit_selected_proofs.py", "--output", str(output / "selected-proofs")])
        run("comparator", ["bash", "scripts/verify-comparator.sh"], {"SK_VERIFY_LOG_DIR": str(output / "comparator")})
    except (Exception, KeyboardInterrupt) as failure:
        error = f"{type(failure).__name__}: {failure}"
        if current and statuses[current]["status"] == "running":
            statuses[current]["status"] = "failed"
            statuses[current]["error"] = error
    after = public_snapshot()
    core_after = source_manifest(ROOT)
    unchanged = before == after
    core_unchanged = core_before == core_after
    passed = error is None and unchanged and core_unchanged and all(
        item["status"] == "passed" for item in statuses.values()
    )
    write_json(output / "verification-summary.json", {
        "check": "local-complete-verification-pipeline",
        "passed": passed,
        "source_identity_at_start": start_identity,
        "source_identity_at_end": git_identity(),
        "public_sources_unchanged": unchanged,
        "mathematical_compiler_inputs_unchanged": core_unchanged,
        "public_source_snapshot": before,
        "public_source_snapshot_after": after,
        "mathematical_compiler_source_manifest": core_before,
        "pipeline_script_sha256": before["file_sha256"]["scripts/verify.py"],
        "checks": statuses,
        "private_import_runtime": runtime,
        "complete_local_build_closure": closure,
        "failure": error,
        "limitations": "Local pipeline; does not execute Palomar's protected canonical Challenge intake or editorial review.",
    })
    if passed:
        print(f"All requested local checks passed with unchanged sources; records: {output}")
        return 0
    print(f"Verification failed: {error or 'public sources changed during checks'}", file=sys.stderr)
    print(f"Outcome record: {output / 'verification-summary.json'}", file=sys.stderr)
    return 1


def main() -> int:
    try:
        return run_pipeline(output_directory())
    except Exception as error:
        print(f"Verification could not start: {type(error).__name__}: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
