#!/usr/bin/env python3
"""Check quotation/declaration bindings and current transitive axioms.

The generated Lean audit prints the exact elaborated type of every anchor.
This checks binding integrity and proof soundness, not an automated proof of
semantic equivalence between English/TeX and Lean. Coverage notes remain
necessary. Compiler and independent-kernel verification are separate checks.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import tomllib
sys.dont_write_bytecode = True

from lean_source_scan import (scan, dependencies, resolve, collect_artifact_snapshot,
                              verify_artifact_snapshot, check_private_import_capacity)

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = ("numbered_results", "numbered_definitions", "numbered_remarks")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_roots(root):
    roots = [root]
    for cfg in sorted(root.rglob("lakefile.toml")):
        if ".lake" in cfg.relative_to(root).parts:
            continue
        data = tomllib.loads(cfg.read_text())
        roots.append(cfg.parent)
        roots.extend(cfg.parent / lib.get("srcDir", ".")
                     for lib in data.get("lean_lib", []))
    return list(dict.fromkeys(p.resolve() for p in roots))


def module_for(path, roots):
    for base in sorted(roots, key=lambda p: len(p.parts), reverse=True):
        if path.is_relative_to(base):
            module = ".".join(path.relative_to(base).with_suffix("").parts)
            if resolve(module, roots) == path:
                return module
    raise ValueError("no importable module for " + str(path))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--ledger", default="docs/numbered-claims.json")
    ap.add_argument("--output", type=Path, default=Path("../verification-work/numbered-claims"))
    ap.add_argument("--prepare-only", action="store_true",
                    help="Prepare Lean audit; never report kernel verification")
    args = ap.parse_args()
    root = args.root.resolve()
    out = args.output.resolve()
    if out.is_relative_to(root):
        ap.error("--output must be outside the public repository; generated audits and raw logs are verification workspace files")
    out.mkdir(parents=True, exist_ok=True)
    report = {"structural_passed": False, "kernel_axioms_passed": False,
              "proof_bodies_loaded": False,
              "mathematical_fidelity_automated": False,
              "independent_kernel_checked_by_this_script": False}
    try:
        ledger_path = root / args.ledger
        ledger = json.loads(ledger_path.read_text())
        entries = [e for group in GROUPS for e in ledger.get(group, [])]
        counts = {group: len(ledger.get(group, [])) for group in GROUPS}
        if counts != {"numbered_results": 50, "numbered_definitions": 3,
                      "numbered_remarks": 5}:
            raise ValueError("numbered inventory changed: " + repr(counts))
        if len({e["id"] for e in entries}) != len(entries):
            raise ValueError("duplicate numbered entry IDs")
        paper = root / ledger.get("source_root", "paper")
        frozen = {args.ledger: sha(ledger_path)}
        for entry in entries:
            loc = entry["source"]
            path = paper / loc["file"]
            text = path.read_text()
            a, b = loc["source_character_range"]
            quote = text[a:b]
            if quote != loc["quote"] or hashlib.sha256(quote.encode()).hexdigest() != loc["quote_sha256"]:
                raise ValueError("numbered source quotation changed: " + entry["id"])
            frozen[str(path.relative_to(root))] = sha(path)
        roots = source_roots(root)
        anchor_paths = set()
        declared = {}
        auxiliary_targets = {}
        for entry in entries:
            for name in entry.get("lean_declarations", []):
                locs = entry.get("declaration_locations", {}).get(name, [])
                if len(locs) != 1:
                    raise ValueError("ambiguous/missing source location: " + name)
                path = root / locs[0]["file"]
                anchor_paths.add(path)
                declared[name] = locs[0]
            for name, loc in entry.get("target_definitions", {}).items():
                auxiliary_targets[name] = loc
                anchor_paths.add(root / loc["file"])
        declared.update(auxiliary_targets)
        declarations, _ = scan(sorted(anchor_paths), root)
        locations = {}
        for declaration in declarations:
            locations.setdefault(declaration["name"], []).append(declaration)
        catalog = {name: items[0] for name, items in locations.items()}
        for name, recorded in declared.items():
            actual = catalog.get(name)
            if len(locations.get(name, [])) != 1:
                raise ValueError("ambiguous/missing current declaration source: " + name)
            if actual is None or any(actual[key] != recorded[key]
                                     for key in ("file", "kind", "line")):
                raise ValueError("declaration source/kind changed: " + name)
        classifications = []
        for entry in entries:
            names = entry.get("lean_declarations", [])
            kinds = {name: catalog[name]["kind"] for name in names}
            theorem_names = [name for name in names if kinds[name] in {"theorem", "lemma"}]
            if entry["type"] in {"theorem", "lemma", "proposition", "corollary"} and not theorem_names:
                raise ValueError("mathematical result anchored only to nonproof declarations: " + entry["id"])
            classifications.append({"id": entry["id"], "number": entry["number"],
                "type": entry["type"], "anchor_kinds": kinds,
                "proof_anchors": theorem_names,
                "classification": "definition" if entry["type"] == "definition" else
                    "explanatory_uncertified" if not names else
                    "proof_bundle" if len(theorem_names) > 1 else "proved_declaration",
                "semantic_note": entry.get("coverage_note", "")})
        closure = dependencies(sorted(anchor_paths), roots)
        _, violations = scan(sorted(closure), root)
        if violations:
            raise ValueError("source closure has proof-hole/unsafe tokens: " + repr(violations[:10]))
        for path in closure:
            frozen[str(path.relative_to(root))] = sha(path)
        for path in root.rglob("lakefile.toml"):
            if ".lake" not in path.relative_to(root).parts:
                frozen[str(path.relative_to(root))] = sha(path)
        for path in root.rglob("lean-toolchain"):
            if ".lake" not in path.relative_to(root).parts:
                frozen[str(path.relative_to(root))] = sha(path)
        for path in root.rglob("lake-manifest.json"):
            if ".lake" not in path.relative_to(root).parts:
                frozen[str(path.relative_to(root))] = sha(path)
        for path in (root / "scripts/check_numbered_claims.py", root / "scripts/lean_source_scan.py"):
            frozen[str(path.relative_to(root))] = sha(path)
        fingerprint = hashlib.sha256(json.dumps(frozen, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        audit = out / "NumberedClaims.lean"
        # Deliberately NO `module` header: Lean 4.35 imports full transitive
        # private data in this mode. A module's ordinary imports may expose a
        # theorem only as axiomInfo, with precomputed axiom metadata and no body.
        lines = ["import " + m for m in sorted({"Lean", *(module_for(p, roots) for p in anchor_paths)})]
        lines += ["set_option pp.fullNames true", "set_option pp.explicit true",
                  "set_option pp.universes true", "set_option pp.notation false",
                  "set_option pp.proofs false"]
        for name in sorted(declared):
            expected = {"theorem": "thmInfo", "lemma": "thmInfo", "def": "defnInfo",
                        "abbrev": "defnInfo", "opaque": "opaqueInfo", "structure": "inductInfo",
                        "inductive": "inductInfo", "class": "inductInfo"}.get(catalog[name]["kind"])
            if expected:
                lines += ["run_cmd do", "  match (← Lean.getEnv).find? `" + name + " with",
                          "  | some (." + expected + " " + ("proof" if expected == "thmInfo" else "_") + ") =>"]
                if expected == "thmInfo":
                    lines += ["      Lean.Elab.Command.liftTermElabM do",
                              "        unless (← Lean.Meta.isProp proof.type) do",
                              "          Lean.throwError " + json.dumps("theorem target is not a proposition: " + name)]
                else:
                    lines += ["      pure ()"]
                lines += ["  | _ => Lean.throwError " + json.dumps("unexpected compiled declaration kind or unloaded proof body: " + name)]
            lines += ["#eval IO.println " + json.dumps("BEGIN NUMBERED TARGET " + name),
                      "#check " + name,
                      "set_option pp.universes false in #print axioms " + name]
            if catalog[name]["kind"] not in {"theorem", "lemma"}:
                lines += ["#print " + name]
            lines += ["#eval IO.println " + json.dumps("END NUMBERED TARGET " + name)]
        lines += ["example (β : ℝ) (hβ : 1 < β) :",
                  "    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →",
                  "      QuantitativeFollowup.finiteBias n β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) :=",
                  "  HexagonPaper.main_mean_bias_upper β hβ",
                  "example (β : ℝ) (hβ : 1 < β) : QuantitativeFollowup.SmallIntervalTarget β hβ :=",
                  "  QuantitativeFollowup.small_interval_near_zero β hβ"]
        audit.write_text("\n".join(lines) + "\n")
        report.update(structural_passed=True, counts=counts,
            anchors=len(declared) - len(auxiliary_targets), auxiliary_target_definitions=len(auxiliary_targets),
            modules=len(anchor_paths),
            local_dependency_sources=len(closure),
            source_snapshot=frozen, source_revision_sha256=fingerprint,
            ledger_sha256=sha(ledger_path), entries=classifications,
            generated_audit_sha256=sha(audit),
            caution="Exact compiled types and axioms are checked; TeX equivalence and full-source build remain separate obligations.")
        if args.prepare_only:
            report["compiler_validation"] = "not_run"
        else:
            report['private_import_runtime'] = check_private_import_capacity()
            artifacts = collect_artifact_snapshot(root, sorted(closure))
            report['compiled_artifacts'] = artifacts
            report['compiled_artifact_count'] = len(artifacts)
            report['compiled_import_source_count'] = len({record['source_path']
                                                          for record in artifacts.values()})
            report['compiled_import_traversal_complete'] = True
            report['compiled_artifact_sha256'] = hashlib.sha256(json.dumps(
                {label: {k: v for k, v in record.items() if k not in {'path', 'source_path'}}
                 for label, record in artifacts.items()}, sort_keys=True,
                separators=(',', ':')).encode()).hexdigest()
            report['artifact_source_correspondence_prerequisite'] = (
                'Run a fresh lake build first. This audit freezes existing compiled import artifacts; '
                'artifact hashes alone do not establish that they correspond to current source.')
            log = out / "numbered-claims.log"
            with log.open("w") as stream:
                proc = subprocess.run(["lake", "env", "lean", str(audit)], cwd=root,
                                      stdout=stream, stderr=subprocess.STDOUT)
            report["compiler_exit_status"] = proc.returncode
            report["compiler_log_sha256"] = sha(log)
            content = log.read_text()
            if proc.returncode != 0:
                raise ValueError("Lean numbered-target audit failed; see " + str(log))
            axioms = {name: [x.strip() for x in values.split(",") if x.strip()]
                      for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", content)}
            axioms.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", content)})
            exact_targets = {}
            for name in sorted(declared):
                match = re.search(re.escape("BEGIN NUMBERED TARGET " + name) + r"\n(.*?)\n" +
                                  re.escape("END NUMBERED TARGET " + name), content, re.S)
                if not match or name not in axioms:
                    raise ValueError("missing exact target/axiom record: " + name)
                if set(axioms[name]) - STANDARD_AXIOMS:
                    raise ValueError("forbidden transitive axiom: " + name + " " + repr(axioms[name]))
                printed_type = match[1].split("\n'" + name + "'", 1)[0]
                exact_targets[name] = {"printed_type": printed_type,
                    "printed_type_sha256": hashlib.sha256(printed_type.encode()).hexdigest(),
                    "transitive_axioms": axioms[name], "declaration_kind": catalog[name]["kind"],
                    "full_query_output": match[1]}
            if frozen != {name: sha(root / name) for name in frozen}:
                raise ValueError("source/configuration changed during audit")
            changed_artifacts = verify_artifact_snapshot(artifacts)
            report['compiled_artifacts_unchanged_during_audit'] = not changed_artifacts
            if changed_artifacts:
                raise ValueError('compiled import artifacts changed during audit: ' + repr(changed_artifacts[:10]))
            report.update(kernel_axioms_passed=True, compiler_validation="passed",
                          proof_bodies_loaded=True,
                          proof_body_asserted_declarations=sorted(name for name in declared
                            if catalog[name]["kind"] in {"theorem", "lemma"}),
                          proof_body_strategy="No module header loads full transitive private data; every theorem/lemma anchor must be thmInfo with proposition type. Lean's axiom collector remains a separate check.",
                          exact_targets=exact_targets)
    except Exception as error:
        report["failure"] = str(error)
    (out / "numbered-claims.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k in {
        "structural_passed", "kernel_axioms_passed", "anchors", "counts", "failure", "source_revision_sha256"}}))
    return 0 if report["structural_passed"] and (args.prepare_only or report["kernel_axioms_passed"]) else 1


if __name__ == "__main__":
    sys.exit(main())
