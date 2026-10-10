#!/usr/bin/env python3
"""Static repository checks; this does not certify Lean proofs.

Original preparation tooling, distributed under the project's MIT licence.
"""
from __future__ import annotations
import argparse, hashlib, json, os, re, subprocess, sys, tomllib
from pathlib import Path
sys.dont_write_bytecode = True

ROOT=Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
TOOLCHAIN='leanprover/lean4:v4.35.0-rc2'
MATHLIB='065356127b1dc0016f66b7283ce0ce2c4055aa55'


def unique_json(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise ValueError('Duplicate JSON key: ' + name)
        result[name] = value
    return result


def dependency_statement_closure(root, packages, require):
    """Check this project's canonical Mathlib manifest and consumed source graph.

    Clean checkout and recorded source bytes are useful local checks. They do
    not reproduce Palomar's isolated canonical Challenge compilation.
    """
    from lean_source_scan import imports
    package_map = {item['name']: item for item in packages}
    require(len(package_map) == len(packages), 'Duplicate dependency package names')
    mathlib_root = root / '.lake/packages/mathlib'
    result = {'canonical_mathlib_manifest_matched': False,
              'materialized_dependency_sources_clean': False,
              'closure_checked': False, 'source_files': {}, 'dependencies': {}}
    if not mathlib_root.is_dir():
        require(False, 'Materialized canonical Mathlib is required for Challenge closure validation')
        return result
    raw = subprocess.check_output(['git', '-C', str(mathlib_root), 'show', MATHLIB + ':lake-manifest.json'])
    upstream = json.loads(raw)['packages']
    result['canonical_mathlib_manifest_sha256'] = hashlib.sha256(raw).hexdigest()
    def remote(url): return url.removesuffix('.git').lower()
    require(remote(package_map['mathlib']['url']) == 'https://github.com/leanprover-community/mathlib4',
            'Mathlib URL differs from the canonical repository')
    expected = {item['name']: item for item in upstream}
    require(set(package_map) == set(expected) | {'mathlib'}, 'Project dependencies differ from canonical Mathlib closure')
    manifest_matches = True
    for name, pinned in expected.items():
        actual = package_map.get(name, {})
        matched = actual.get('rev') == pinned.get('rev') and remote(actual.get('url', '')) == remote(pinned.get('url', ''))
        require(matched, 'Canonical Mathlib manifest mismatch: ' + name)
        manifest_matches = manifest_matches and matched
    result['canonical_mathlib_manifest_matched'] = manifest_matches and set(package_map) == set(expected) | {'mathlib'}
    roots = []
    clean = True
    tracked_sources = {}
    for name, pinned in package_map.items():
        checkout = root / '.lake/packages' / name
        if not checkout.is_dir():
            require(False, 'Dependency is not materialized: ' + name); clean = False; continue
        head = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip()
        require(head == pinned['rev'], 'Materialized dependency pin differs: ' + name)
        changed = subprocess.check_output([
            'git', '-C', str(checkout), 'diff', '--name-only', 'HEAD', '--', '*.lean', '*.toml',
            'lean-toolchain', '**/lean-toolchain', 'lake-manifest.json', '**/lake-manifest.json',
        ], text=True).splitlines()
        tracked = set(subprocess.check_output(['git', '-C', str(checkout), 'ls-tree', '-r', '--name-only', pinned['rev']], text=True).splitlines())
        untracked = []
        for directory, children, names in os.walk(checkout, followlinks=False):
            children[:] = [child for child in children if child not in {'.git', '.lake'}
                           and not (Path(directory) / child).is_symlink()]
            for filename in names:
                source = Path(directory) / filename
                if filename.endswith('.lean') and source.relative_to(checkout).as_posix() not in tracked:
                    untracked.append(source.relative_to(checkout).as_posix())
        okay = head == pinned['rev'] and not changed and not untracked
        require(not changed, 'Tracked dependency source/configuration modified: ' + name + ' ' + repr(changed))
        require(not untracked, 'Untracked dependency Lean sources: ' + name + ' ' + repr(untracked))
        clean = clean and okay
        result['dependencies'][name] = {'revision': head, 'sources_clean': okay,
                                        'modified_source_files': changed, 'untracked_lean_sources': untracked}
        roots.append((checkout.resolve(), name))
        tracked_sources[name] = tracked
    result['materialized_dependency_sources_clean'] = clean
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip()).resolve()
    core = prefix / 'src/lean'
    require(core.is_dir(), 'Selected toolchain source tree is unavailable')
    search = [(core, 'lean-core'), *roots]
    pending = ['Init', *imports(root / 'Challenge.lean')]
    visited = set()
    closure_okay = True
    while pending:
        module = pending.pop()
        if module in visited: continue
        visited.add(module)
        relative = Path(*module.split('.')).with_suffix('.lean')
        local = root / relative
        if local.is_file():
            require(False, 'Root-local source shadows a Challenge import: ' + module)
            closure_okay = False
        selected = next(((base / relative, package) for base, package in search if (base / relative).is_file()), None)
        if selected is None:
            require(False, 'Challenge import source does not resolve canonically: ' + module)
            closure_okay = False; continue
        source, package = selected
        boundary = next(base for base, name in search if name == package)
        if source.is_symlink() or not source.resolve().is_relative_to(boundary):
            require(False, 'Challenge canonical source escapes its package: ' + module)
            closure_okay = False; continue
        if package != 'lean-core' and source.relative_to(boundary).as_posix() not in tracked_sources[package]:
            require(False, 'Challenge uses an untracked dependency source: ' + module)
            closure_okay = False
        result['source_files'][module] = {'package': package, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        pending.extend(name for name in imports(source) if name != 'all')
    result['closure_checked'] = closure_okay and clean and result['canonical_mathlib_manifest_matched']
    result['toolchain_prefix'] = str(prefix)
    result['source_count'] = len(result['source_files'])
    result['limitation'] = 'Local source/checkout validation; not protected canonical compilation or cache authentication.'
    return result

def source_inputs(root: Path):
    """Mathematical/compiler inputs, without receipts, outputs or caches."""
    for p in sorted(root.rglob('*')):
        if any(s in p.parts for s in ('.git','.lake','__pycache__')) or not p.is_file(): continue
        rel=p.relative_to(root)
        if p.suffix in {'.lean','.toml','.yaml','.tex','.bib','.sty','.cls'} or rel.as_posix() in {
            'lean-toolchain','lake-manifest.json','comparator.json','docs/numbered-claims.json'}:
            yield p

def source_manifest(root: Path):
    files={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in source_inputs(root)}
    digest=hashlib.sha256(json.dumps(files,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    return {'algorithm':'sha256','source_digest':digest,'files':files}

def check(root: Path):
    from lean_source_scan import mask, imports
    failures=[]
    def require(ok,msg):
        if not ok: failures.append(msg)
    root=root.resolve(); allfiles=[p for p in root.rglob('*') if '.git' not in p.parts and '.lake' not in p.parts]
    require(not any(p.is_symlink() for p in allfiles),'Source tree contains symlinks')
    files=[p for p in allfiles if p.is_file()]
    require(sum(p.stat().st_size for p in files)<=500*1024*1024,'Checkout exceeds 500 MiB')
    leanfiles=[p for p in files if p.suffix=='.lean']
    for p in leanfiles:
        text=p.read_text(); active=mask(text); rel=str(p.relative_to(root))
        require(len(text.splitlines())<=10000,rel+': exceeds 10000 physical lines')
        if p.name!='lakefile.lean':
            require(bool(re.match(r'\s*module\s*(?:\n|$)',active)),rel+': missing first module command')
            require(len(re.findall(r'(?m)^module[ \t]*$',active))==1,rel+': duplicate module command')
        tokens=re.findall(r'\b(?:sorry|admit|sorryAx|native_decide|Lean\.ofReduceBool)\b',active)
        custom=re.findall(r'(?m)^\s*(?:(?:public|private|protected)\s+)*(?:axiom|constant)\s+',active)
        if p==root/'Challenge.lean':
            require(tokens==['sorry']*6,'Challenge must contain exactly six intentional theorem sorries')
            require(not custom,'Challenge contains a custom axiom')
        else:
            require(not tokens,rel+': proof-hole/forbidden-reduction tokens '+repr(tokens))
            require(not custom,rel+': custom axiom/constant declaration')
    compiled={'.olean','.ilean','.ir','.trace','.a','.bc','.dll','.dylib','.o','.obj','.so'}
    require(not any(p.suffix in compiled or p.name.endswith(('.olean.private','.olean.server')) for p in files),
            'Compiled Lean output outside .lake')
    require(sum((root/x).is_file() for x in ('lakefile.toml','lakefile.lean'))==1,'Need exactly one Lakefile')
    for name in ('lakefile.toml', 'lakefile.lean'):
        if (root/name).is_file(): require((root/name).stat().st_size <= 1024*1024, 'Lakefile exceeds 1 MiB')
    if (root/'lakefile.toml').is_file(): tomllib.loads((root/'lakefile.toml').read_text())
    require(not (root/'.gitmodules').exists(), 'Submitted Git submodules are not permitted')
    require((root/'lean-toolchain').read_text().strip()==TOOLCHAIN,'Toolchain differs from checked canonical pin')
    lock=json.loads((root/'lake-manifest.json').read_text())
    packages=lock['packages']
    for dep in packages:
        require(dep['type']=='git','Unexpected non-Git external dependency: '+dep['name'])
        require(bool(re.fullmatch(r'[0-9a-f]{40}',dep.get('rev',''))),'Nonimmutable revision: '+dep['name'])
        require(bool(re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?',dep.get('url',''))),
                'Nonpublic/noncanonical Git URL: '+dep['name'])
        materialized=root/'.lake/packages'/dep['name']
        if materialized.is_dir():
            sha=subprocess.check_output(['git','-C',str(materialized),'rev-parse','HEAD'],text=True).strip()
            require(sha==dep['rev'],'Materialized dependency pin differs: '+dep['name'])
    mathlib=next((x for x in packages if x['name']=='mathlib'),{})
    require(mathlib.get('rev')==MATHLIB,'Mathlib differs from checked canonical release')
    if (root/'.lake/packages/mathlib/lean-toolchain').is_file():
        require((root/'.lake/packages/mathlib/lean-toolchain').read_text().strip()==TOOLCHAIN,'Mathlib toolchain mismatch')
    config_path = root/'comparator.json'
    require(config_path.stat().st_size <= 1024*1024, 'Comparator config exceeds 1 MiB')
    config=json.loads(config_path.read_text(), object_pairs_hook=unique_json)
    required_keys = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
    require(isinstance(config, dict) and required_keys <= set(config), 'Comparator config lacks required keys')
    require(set(config) <= required_keys | {'definition_names', 'enable_nanoda'}, 'Unknown Comparator configuration keys')
    require(isinstance(config.get('theorem_names'), list) and all(isinstance(name,str) and name for name in config.get('theorem_names',[])),
            'Comparator theorem names must be a nonempty string array')
    require(isinstance(config.get('permitted_axioms'), list), 'Comparator permitted_axioms must be an array')
    require('external_kernels' not in config,'Submitted comparator config contains external_kernels')
    require(config.get('challenge_module')=='Challenge' and config.get('solution_module')=='Solution','Unexpected module selection')
    require(bool(config.get('theorem_names')),'No selected theorem names')
    require(set(config.get('permitted_axioms',[]))<=ALLOWED_AXIOMS,'Forbidden permitted axiom')
    require(config.get('definition_names',[])==[],'Concrete interface must not contain definition holes')
    challenge=root/'Challenge.lean'
    require(len(challenge.read_text().splitlines())<=1000 and challenge.stat().st_size<=100*1024,'Challenge source limits exceeded')
    require(all(name.startswith(('Mathlib.','Lean.','Init.','Std.')) for name in imports(challenge)),
            'Challenge imports noncanonical project definitions')
    require((root/'formalization.yaml').is_file(),'Missing formalization.yaml')
    require((root/'formalization.yaml').stat().st_size <= 256*1024, 'Metadata exceeds 256 KiB')
    require((root/'LICENSE').is_file(),'Missing root LICENSE')
    licenses = [path for path in root.iterdir() if path.is_file() and re.fullmatch(
        r'(?:license|licence|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?',path.name,re.I)]
    require(len(licenses)==1, 'Need exactly one accepted root licence file')
    require(0 < (root/'LICENSE').stat().st_size <= 1024*1024, 'Root licence must be nonempty and at most 1 MiB')
    for p in files:
        with p.open('rb') as stream: beginning = stream.read(128)
        require(not beginning.startswith(b'version https://git-lfs.github.com/spec/v1'),str(p.relative_to(root))+': LFS pointer')
    canonical_closure = dependency_statement_closure(root, packages, require)
    return {'status':'failed' if failures else 'passed','static_checks_only':True,'failures':failures,
            'lean_source_files':len(leanfiles),'source_bytes':sum(p.stat().st_size for p in files),
            'max_lean_lines':max(len(p.read_text().splitlines()) for p in leanfiles),
            'challenge_lines':len(challenge.read_text().splitlines()),'challenge_bytes':challenge.stat().st_size,
            'intentional_challenge_sorries':6,'canonical_challenge_closure':canonical_closure,'manifest':source_manifest(root)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--output',type=Path,help='Write a report outside the source tree')
    args=parser.parse_args()
    if args.output and args.output.resolve().is_relative_to(args.root.resolve()):
        parser.error('Output report must be outside the public source tree')
    report=check(args.root)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(report,indent=2)+'\n')
    summary={k:v for k,v in report.items() if k not in {'manifest','canonical_challenge_closure'}}
    summary['canonical_challenge_closure']={k:v for k,v in report['canonical_challenge_closure'].items()
                                          if k not in {'source_files','dependencies','toolchain_prefix'}}
    print(json.dumps(summary,indent=2))
    return bool(report['failures'])

if __name__=='__main__': sys.exit(main())
