#!/usr/bin/env python3
"""Audit selected Solution declarations and their transitive axiom dependencies.

The output directory must be outside the public source tree. MIT licensed.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys
sys.dont_write_bytecode = True
from check_repository import source_manifest
from lean_source_scan import check_private_import_capacity, collect_artifact_snapshot, verify_artifact_snapshot

ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Quot.sound','Classical.choice'}
BRIDGES=['SKMeanBias.pressure_eq_original','SKMeanBias.parisiLimit_eq_variational','SKMeanBias.finiteBias_eq_original']
CORE=['HexagonPaper.main_mean_bias_upper','HexagonPaper.main_mean_bias',
      'QuantitativeFollowup.improved_native_bias',
      'QuantitativeFollowup.followup_actual_four_term_budget','Paper.physicalParisiFormula']

def audit(out):
    runtime=check_private_import_capacity()
    config=json.loads((ROOT/'comparator.json').read_text())
    names=list(dict.fromkeys(config['theorem_names']+BRIDGES+CORE))
    body='import Solution\nimport HexagonPaper.MainUpperOnly\nopen Lean\n'
    # Every anchor is checked as a proposition, not just an arbitrary constant.
    body += 'run_cmd do\n'
    for name in names:
        body+=f'  match (← getConstInfo `{name}) with\n  | .thmInfo proof =>\n      Lean.Elab.Command.liftTermElabM do\n        unless (← Lean.Meta.isProp proof.type) do\n          throwError "Theorem target is not a proposition: {name}"\n  | _ => throwError "Proof body not loaded for theorem: {name}"\n'
    for name in names:body+=f'#check {name}\n#print axioms {name}\n'
    audit=out/'SelectedProofAudit.lean';audit.write_text(body)
    before=source_manifest(ROOT)
    tools={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
           for p in (Path(__file__),ROOT/'scripts/check_repository.py',ROOT/'scripts/lean_source_scan.py')}
    artifacts=collect_artifact_snapshot(ROOT,
        [ROOT/name for name in before['files'] if name.endswith('.lean')])
    artifact_digest=hashlib.sha256(json.dumps(
        {name:{'sha256':item['sha256'],'bytes':item['bytes']} for name,item in artifacts.items()},
        sort_keys=True,separators=(',',':')).encode()).hexdigest()
    proc=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True)
    (out/'selected-proofs.log').write_text(proc.stdout+proc.stderr)
    pattern=re.compile(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]")
    observed={name:[x.strip() for x in axioms.split(',') if x.strip()] for name,axioms in pattern.findall(proc.stdout)}
    for name in re.findall(r"'([^']+)'\s+does not depend on any axioms",proc.stdout):observed[name]=[]
    missing=set(names)-observed.keys()
    forbidden={n:[a for a in ax if a not in ALLOWED] for n,ax in observed.items() if set(ax)-ALLOWED}
    unchanged=before==source_manifest(ROOT)
    tools_unchanged=tools=={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in tools}
    changed_artifacts=verify_artifact_snapshot(artifacts)
    passed=proc.returncode==0 and not missing and not forbidden and unchanged and tools_unchanged and not changed_artifacts
    report={'passed':passed,'proof_bodies_loaded':proc.returncode==0,'lean_exit_code':proc.returncode,'missing_axiom_reports':sorted(missing),
            'private_import_runtime':runtime,
            'forbidden_axioms':forbidden,'axioms':observed,'source_unchanged_during_audit':unchanged,
            'source_manifest':before,'audit_source_sha256':hashlib.sha256(audit.read_bytes()).hexdigest(),
            'checker_sources':tools,'checker_sources_unchanged':tools_unchanged,
            'compiled_artifacts':artifacts,'compiled_artifact_count':len(artifacts),
            'compiled_artifact_digest':artifact_digest,'compiled_artifacts_changed':changed_artifacts,
            'compiled_artifacts_unchanged':not changed_artifacts,
            'build_prerequisite':'Run a successful fresh lake build first; artifact hashes identify the imported compiled data and do not themselves establish source freshness.',
            'limitation':'Axiom inspection is separate from independent kernel replay, run by verify-comparator.sh.'}
    (out/'selected-proofs.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'source_manifest','compiled_artifacts'}},indent=2))
    return 0 if passed else 1

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();out=args.output.resolve()
    if out==ROOT or ROOT in out.parents: parser.error('Output directory must be outside the public source tree')
    out.mkdir(parents=True,exist_ok=True)
    receipt=out/'selected-proofs.json'
    receipt.write_text(json.dumps({'passed':False,'proof_bodies_loaded':False,
                                  'status':'not_completed'},indent=2)+'\n')
    try:
        return audit(out)
    except (Exception,KeyboardInterrupt) as failure:
        error=f'{type(failure).__name__}: {failure}'
        receipt.write_text(json.dumps({'passed':False,'proof_bodies_loaded':False,
                                      'status':'failed','failure':error},indent=2)+'\n')
        print(f'Selected proof audit failed: {error}',file=sys.stderr)
        return 1

if __name__=='__main__':sys.exit(main())
