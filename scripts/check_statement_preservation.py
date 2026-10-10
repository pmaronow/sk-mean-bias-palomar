#!/usr/bin/env python3
"""Compare preserved Lean source statements with their supplied originals.

Original preparation tooling, distributed under the project's MIT licence.

This is a conservative source comparison, not a Lean parser or a kernel check.
It removes comments and normalizes whitespace, module/export wrappers, and
visibility. Theorem/lemma proof bodies are excluded from signature comparison;
definition bodies, declaration context, and import changes are checked separately.
Only the explicitly documented name-only compatibility renames below are allowed.
The default comparison uses compact hashes made from the immutable original
extraction. --original-root additionally permits inspection of exact changed
signatures. Regenerating that baseline requires the original archive SHA256.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SIGNATURE_PARSER = 'top-level-bindings-v2'
RENAMES = {
    'HexagonPaper/TreeLikelihood.lean': {
        'treeNativeFullLaw_endpoint_records_direct': 'treeNativeFullLaw_endpoint_records',
    },
    'QuantitativeFollowup/SupportingGeneratedObservedRawNormalizerPairTransport.lean': {
        'observedRawNormalizerComponentLeafCast': 'componentLeafCast',
    },
    'QuantitativeFollowup/SupportingGeneratedNormalizerPairTransport.lean': {
        'normalizerComponentLeafCast': 'componentLeafCast',
    },
}
MODIFIERS = r'(?:(?:public|private|protected|noncomputable|unsafe|partial|meta|nonrec|local)\s+)*'
KINDS = r'theorem|lemma|def|abbrev|opaque|structure|inductive|class|instance|axiom|constant'
DECL = re.compile(r'(?m)^[ \t]*(?:@\[[^\n]*?\][ \t]*)?' + MODIFIERS +
                  r'(?P<kind>' + KINDS + r')\b')
COMMAND = re.compile(
    r'(?m)^[ \t]?(?:@\[[^\n]*?\][ \t]*)?' + MODIFIERS +
    r'(?:' + KINDS + r'|namespace|section|end|open|variable|universe|set_option|'
    r'attribute|include|omit|export|syntax|macro|elab|notation|infix[lr]?|prefix|'
    r'postfix|initialize|register_option|example)\b|^[ \t]?#(?:check|print|eval|exit|reduce)\b')
TOKEN = re.compile(r'«[^»]*»|"(?:\\.|[^"\\])*"|(?:[^\W\d]|_)[\w\'.!?]*|'
                   r'\d+(?:\.\d+)?|:=|=>|->|←|→|≤|≥|≠|==|\S', re.UNICODE)


def uncomment(source: str, mask_strings: bool = False) -> str:
    """Mask nested comments while retaining offsets and physical line numbers."""
    out = list(source)
    i = depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if source[i] == '\\' and i + 1 < len(source):
                if mask_strings: out[i:i+2] = '  '
                i += 2
            else:
                if source[i] == '"': string = False
                if mask_strings and source[i] != '\n': out[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i):
            j = source.find('\n', i)
            if j < 0: j = len(source)
            out[i:j] = ' ' * (j-i); i = j
        elif source[i] == '"':
            if mask_strings: out[i] = ' '
            string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(out)


def normalize(source: str, path: str, current: bool) -> str:
    source = uncomment(source)
    source = re.sub(r'(?m)^[ \t]*module[ \t]*$', '', source)
    source = re.sub(r'(?m)^[ \t]*(?:@\[expose\][ \t]+)?public[ \t]+section[ \t]*$', '', source)
    source = re.sub(r'@\[expose\][ \t]*', '', source)
    source = re.sub(r'\b(?:public|private)[ \t]+', '', source)
    if current:
        for new, old in RENAMES.get(path, {}).items():
            source = re.sub(r'(?<![\w\'])' + re.escape(new) + r'(?![\w\'])', old, source)
    return source


def tokens(source: str) -> str:
    return ' '.join(TOKEN.findall(source))


def body_start(source: str) -> int:
    """Find the declaration body after any type-local binding assignments.

    Top-level `let`, `letI`, `have`, and `haveI` expressions can occur in the declared
    type. Their next unbracketed `:=` introduces a local value, rather than
    the theorem/definition body. Explicit binders and bracketed expressions
    already protect their own internal assignments.
    """
    depth = pending_bindings = 0
    for match in TOKEN.finditer(source):
        token = match.group()
        if token in ('(', '[', '{', '⦃', '⟨'):
            depth += 1
        elif token in (')', ']', '}', '⦄', '⟩'):
            depth -= 1
        elif depth == 0:
            if token in ('let', 'letI', 'have', 'haveI'):
                pending_bindings += 1
            elif token == ':=':
                if pending_bindings:
                    pending_bindings -= 1
                else:
                    return match.start()
            elif token in ('where', '|') and not pending_bindings:
                return match.start()
    return len(source)


def inventory(source: str, path: str, current: bool) -> dict:
    active = normalize(source, path, current)
    boundaries = [match.start() for match in COMMAND.finditer(active)] + [len(active)]
    declarations = []
    erased = list(active)
    for match in DECL.finditer(active):
        start = match.start()
        stop = next(x for x in boundaries if x > start)
        text = active[start:stop]
        split = body_start(text)
        header = tokens(text[:split])
        after_kind = re.sub(r'^' + MODIFIERS + r'(?:' + KINDS + r')\s*', '', header)
        name_match = re.match(r'(«[^»]*»|[^\s(:{\[]+)', after_kind)
        name = name_match.group() if name_match else '<anonymous>'
        declarations.append({
            'kind': match['kind'], 'name': name,
            'line': active.count('\n', 0, start) + 1,
            'signature': header, 'body': tokens(text[split:]),
        })
        # The remaining skeleton retains namespace/section/variable commands.
        for i in range(start, stop):
            if erased[i] != '\n': erased[i] = ' '
    context = ''.join(erased)
    imports = re.findall(r'(?m)^[ \t]*import[ \t]+([^\n]+)', context)
    imports = [item for line in imports for item in line.split()]
    context = re.sub(r'(?m)^[ \t]*import[ \t]+[^\n]+', '', context)
    return {'declarations': declarations, 'context': tokens(context), 'imports': imports}


def source_violations(source: str, path: str) -> list[dict]:
    active = uncomment(source, mask_strings=True)
    violations = []
    for match in re.finditer(r'\b(?:sorry|admit|sorryAx|native_decide|Lean\.ofReduceBool)\b', active):
        violations.append({'file': path, 'line': active.count('\n', 0, match.start()) + 1,
                           'token': match.group()})
    for match in DECL.finditer(active):
        if match['kind'] in ('axiom', 'constant'):
            violations.append({'file': path, 'line': active.count('\n', 0, match.start()) + 1,
                               'token': match['kind']})
    for match in re.finditer(r'(?m)^[ \t]*(?:public[ \t]+|private[ \t]+)*(?:unsafe|partial)[ \t]+', active):
        violations.append({'file': path, 'line': active.count('\n', 0, match.start()) + 1,
                           'token': match.group().strip()})
    return violations


def digest(files: dict) -> str:
    return hashlib.sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def compact_inventory(inventory: dict) -> dict:
    return {
        'declarations': [{
            'kind': declaration['kind'], 'name': declaration['name'], 'line': declaration['line'],
            'signature_sha256': hashlib.sha256(declaration['signature'].encode()).hexdigest(),
            'body_sha256': hashlib.sha256(declaration['body'].encode()).hexdigest(),
        } for declaration in inventory['declarations']],
        'context_sha256': hashlib.sha256(inventory['context'].encode()).hexdigest(),
        'imports': inventory['imports'],
    }


def lean_paths(root: Path) -> dict[str, Path]:
    return {str(path.relative_to(root)): path for path in root.rglob('*.lean')
            if '.lake' not in path.parts and '.git' not in path.parts}


def file_hashes(paths: dict[str, Path]) -> dict[str, str]:
    return {name: hashlib.sha256(path.read_bytes()).hexdigest()
            for name, path in paths.items()}


def check(root: Path, original: Path | None, baseline_path: Path) -> dict:
    # Freeze every preparation input before scanning, and rehash it afterward.
    # A report from a concurrently edited source tree is a failed snapshot.
    configurations = {
        'source_origins': root / 'provenance/source-origins.json',
        'checker': Path(__file__).resolve(),
    }
    absent_configurations = {}
    if baseline_path.is_file():
        configurations['statement_baseline'] = baseline_path.resolve()
    elif original is not None:
        # A first immutable baseline may be created after this comparison.
        absent_configurations['statement_baseline'] = baseline_path.resolve()
    configuration_before = file_hashes(configurations)
    prepared_paths_before = lean_paths(root)
    prepared_before = file_hashes(prepared_paths_before)
    origins = json.loads(configurations['source_origins'].read_text())
    original_paths = {entry['original_path']: original / entry['original_path']
                      for entry in origins} if original else {}
    original_before = file_hashes(original_paths) if original else {}
    baseline = json.loads(baseline_path.read_text()) if original is None else None
    if baseline and baseline.get('schema_version') != 1:
        raise ValueError('Unsupported statement-baseline schema')
    if baseline and baseline.get('signature_parser') != SIGNATURE_PARSER:
        raise ValueError('Statement baseline predates the complete type-local binding signature parser')
    if baseline and baseline.get('allowed_name_only_renames') != RENAMES:
        raise ValueError('Documented rename policy differs from the immutable baseline')
    if baseline and not re.fullmatch(r'[0-9a-f]{64}', baseline.get('original_archive_sha256', '')):
        raise ValueError('Baseline lacks the immutable original archive SHA256')
    original_records = {} if original else baseline['files']
    signature_changes, definition_changes, context_changes, import_changes = [], [], [], []
    proof_changes, violations, errors, renames = [], [], [], []
    original_hashes, current_hashes, visited_prepared_hashes = {}, {}, {}
    count = Counter()
    for origin in origins:
        path = origin['path']
        before_path = original / origin['original_path'] if original else None
        after_path = root / path
        if (before_path and not before_path.is_file()) or not after_path.is_file():
            errors.append({'file': path, 'error': 'Missing original or prepared file'}); continue
        before_bytes = before_path.read_bytes() if before_path else None
        after_bytes = after_path.read_bytes()
        before = before_bytes.decode() if before_bytes is not None else None
        after = after_bytes.decode()
        visited_prepared_hashes[path] = hashlib.sha256(after_bytes).hexdigest()
        record = original_records.get(path)
        if before is None and (not record or record['original_path'] != origin['original_path']):
            errors.append({'file': path, 'error': 'Original mapping absent from or inconsistent with baseline'}); continue
        original_hashes[origin['original_path']] = hashlib.sha256(before.encode()).hexdigest() if before is not None else record['original_sha256']
        current_hashes[path] = hashlib.sha256(after.encode()).hexdigest()
        violations.extend(source_violations(after, path))
        try:
            a = inventory(before, path, False) if before is not None else record['inventory']
            b = inventory(after, path, True)
        except (ValueError, StopIteration) as error:
            errors.append({'file': path, 'error': str(error)}); continue
        if before is not None:
            original_records[path] = {
                'original_path': origin['original_path'],
                'original_sha256': original_hashes[origin['original_path']],
                'inventory': compact_inventory(a),
            }
        for new, old in RENAMES.get(path, {}).items():
            if re.search(r'\b' + re.escape(new) + r'\b', uncomment(after)):
                renames.append({'file': path, 'original': old, 'prepared': new,
                                'reason': 'Documented name-only duplicate/visibility compatibility repair'})
        ca = compact_inventory(a) if before is not None else a
        cb = compact_inventory(b)
        da, db = ca['declarations'], cb['declarations']
        count.update(d['kind'] for d in da)
        if [d['signature_sha256'] for d in da] != [d['signature_sha256'] for d in db]:
            signature_changes.append({'file': path,
                'original': a['declarations'] if before is not None else da,
                'prepared': b['declarations']})
        else:
            for index, (old, new) in enumerate(zip(da, db)):
                if old['body_sha256'] == new['body_sha256']: continue
                change = {'file': path, 'name': old['name'], 'kind': old['kind'],
                          'original_line': old['line'], 'prepared_line': new['line'],
                          'original_body_sha256': old['body_sha256'],
                          'prepared_body_sha256': new['body_sha256']}
                if old['kind'] in ('theorem', 'lemma'):
                    proof_changes.append(change)
                else:
                    definition_changes.append(change | {
                        'original_body': a['declarations'][index]['body'] if before is not None else '<hash-only baseline>',
                        'prepared_body': b['declarations'][index]['body']})
        if ca['context_sha256'] != cb['context_sha256']:
            context_changes.append({'file': path,
                'original': a['context'] if before is not None else '<hash-only baseline>',
                'original_sha256': ca['context_sha256'], 'prepared': b['context']})
        if a['imports'] != b['imports']:
            removed = sorted(set(a['imports']) - set(b['imports']))
            added = sorted(set(b['imports']) - set(a['imports']))
            import_changes.append({'file': path, 'removed': removed, 'added': added})
            if removed:
                errors.append({'file': path, 'error': 'Original imports removed', 'imports': removed})
            if any(not name.startswith(('Mathlib.', 'Lean.', 'Init.', 'Std.')) for name in added):
                errors.append({'file': path, 'error': 'New noncanonical imports require independent review', 'imports': added})
    # Newly supplied interface modules have no original statement to compare.
    mapped = {entry['path'] for entry in origins}
    if baseline and set(original_records) != mapped:
        errors.append({'error': 'Original file map and baseline have different path sets'})
    if baseline and digest(original_hashes) != baseline['original_source_digest']:
        errors.append({'error': 'Original file hashes no longer match the recorded original source digest'})
    unmapped = sorted(str(path.relative_to(root)) for path in root.rglob('*.lean')
                      if '.lake' not in path.parts and '.git' not in path.parts
                      and str(path.relative_to(root)) not in mapped)
    for path in unmapped:
        source_bytes = (root/path).read_bytes()
        visited_prepared_hashes[path] = hashlib.sha256(source_bytes).hexdigest()
        source = source_bytes.decode()
        found = source_violations(source, path)
        if path == 'Challenge.lean':
            intentional = [v for v in found if v['token'] == 'sorry']
            found = [v for v in found if v['token'] != 'sorry']
            declarations = inventory(source, path, True)['declarations']
            holes = [declaration for declaration in declarations
                     if re.search(r'\bsorry\b', declaration['body'])]
            if len(intentional) != 6 or len(holes) != 6 or any(
                    declaration['kind'] not in ('theorem', 'lemma') for declaration in holes):
                errors.append({'file': path, 'error': 'Expected six intentional Challenge theorem placeholders'})
        violations.extend(found)
    snapshot_changes = []
    appeared = sorted(name for name, path in absent_configurations.items() if path.exists())
    if appeared:
        snapshot_changes.append({'input': 'configuration', 'appeared': appeared})
    prepared_paths_after = lean_paths(root)
    if set(prepared_paths_before) != set(prepared_paths_after):
        snapshot_changes.append({
            'input': 'prepared_sources',
            'added': sorted(set(prepared_paths_after) - set(prepared_paths_before)),
            'removed': sorted(set(prepared_paths_before) - set(prepared_paths_after)),
        })
    try:
        prepared_after = file_hashes(prepared_paths_after)
        configuration_after = file_hashes(configurations)
        original_after = file_hashes(original_paths) if original else {}
        for label, before_hashes, after_hashes in (
                ('prepared_sources', prepared_before, prepared_after),
                ('configuration', configuration_before, configuration_after),
                ('original_sources', original_before, original_after)):
            changed = sorted(name for name in before_hashes.keys() & after_hashes.keys()
                             if before_hashes[name] != after_hashes[name])
            if changed:
                snapshot_changes.append({'input': label, 'changed': changed})
        changed_during_read = sorted(name for name, value in visited_prepared_hashes.items()
                                    if prepared_before.get(name) != value)
        if changed_during_read:
            snapshot_changes.append({'input': 'prepared_source_reads', 'changed': changed_during_read})
        if original:
            changed_original_reads = sorted(name for name, value in original_hashes.items()
                                            if original_before.get(name) != value)
            if changed_original_reads:
                snapshot_changes.append({'input': 'original_source_reads', 'changed': changed_original_reads})
    except OSError as error:
        snapshot_changes.append({'input': 'snapshot_rehash', 'error': str(error)})
    if snapshot_changes:
        errors.append({'error': 'Preparation inputs changed during source comparison',
                       'changes': snapshot_changes})
    failed = bool(signature_changes or definition_changes or context_changes or violations or errors)
    return {
        'status': 'failed' if failed else 'passed',
        'source_comparison_only': True,
        'source_snapshot_unchanged': not snapshot_changes,
        'snapshot_input_sha256': configuration_before,
        'snapshot_absent_inputs': sorted(absent_configurations),
        'prepared_complete_source_digest': digest(prepared_before),
        'snapshot_changes': snapshot_changes,
        'limitations': [
            'Conservative lexical comparison; it does not elaborate Lean types or prove mathematical equivalence.',
            'Visibility and exposed-module wrappers are normalized; their compiler behavior requires an actual build.',
            'Added imports are inventoried, not certified; transitive forbidden axioms require kernel axiom reports.',
            'Theorem proof bodies may change while their statements remain identical; proof validity requires kernel checks.',
            'New interface files are excluded from original comparison and require their separate Comparator checks.',
        ],
        'mapped_files': len(origins), 'declaration_counts': dict(count),
        'original_source_digest': digest(original_hashes), 'prepared_source_digest': digest(current_hashes),
        'original_file_sha256': original_hashes, 'prepared_file_sha256': current_hashes,
        'allowed_name_only_renames': renames,
        'signature_changes': signature_changes, 'definition_body_changes': definition_changes,
        'declaration_context_changes': context_changes, 'theorem_proof_body_changes': proof_changes,
        'import_changes': import_changes, 'unmapped_new_sources': unmapped,
        'forbidden_source_tokens': violations, 'errors': errors,
        '_original_baseline': original_records,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--original-root', type=Path,
                        help='Root of the supplied original lean-formalization extraction')
    parser.add_argument('--baseline', type=Path, default=ROOT/'provenance/statement-baseline.json')
    parser.add_argument('--write-baseline', type=Path,
                        help='Create compact signature/body/context hashes from the original extraction')
    parser.add_argument('--original-archive-sha256', help='Required immutable original archive hash for baseline creation')
    parser.add_argument('--original-archive-name', help='Original uploaded archive filename, for provenance')
    parser.add_argument('--output', type=Path, help='Write the full report outside the public source tree')
    args = parser.parse_args()
    root = args.root.resolve()
    original = args.original_root.resolve() if args.original_root else None
    if args.write_baseline and (not original or not args.original_archive_sha256 or
                               not re.fullmatch(r'[0-9a-f]{64}', args.original_archive_sha256)):
        parser.error('--write-baseline requires --original-root and an immutable --original-archive-sha256')
    if args.output and args.output.resolve().is_relative_to(root):
        parser.error('Keep generated comparison reports outside the public source tree')
    report = check(root, original, args.baseline)
    original_records = report.pop('_original_baseline')
    if args.write_baseline and report['status'] != 'passed':
        print('Refusing baseline generation from a failed or changing source comparison', file=sys.stderr)
    elif args.write_baseline:
        baseline = {
            'schema_version': 1, 'signature_parser': SIGNATURE_PARSER,
            'origin': 'Hashes computed from the original supplied extraction, before compatibility normalization',
            'original_archive_sha256': args.original_archive_sha256,
            'original_source_digest': report['original_source_digest'],
            'normalization': 'Nested comments; whitespace tokens; module/export wrappers and public/private visibility. Context is retained.',
            'allowed_name_only_renames': RENAMES, 'files': original_records,
        }
        if args.original_archive_name:
            baseline['original_archive_name'] = args.original_archive_name
        args.write_baseline.parent.mkdir(parents=True, exist_ok=True)
        args.write_baseline.write_text(json.dumps(baseline, ensure_ascii=False, separators=(',', ':'))+'\n')
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({
        'status': report['status'], 'source_comparison_only': True,
        'source_snapshot_unchanged': report['source_snapshot_unchanged'],
        'mapped_files': report['mapped_files'], 'declaration_counts': report['declaration_counts'],
        'allowed_name_only_renames': report['allowed_name_only_renames'],
        **{key: len(report[key]) for key in (
            'signature_changes', 'definition_body_changes', 'declaration_context_changes',
            'theorem_proof_body_changes', 'import_changes', 'forbidden_source_tokens', 'errors')},
        'unmapped_new_sources': report['unmapped_new_sources'],
    }, ensure_ascii=False, indent=2))
    return int(report['status'] != 'passed')


if __name__ == '__main__':
    sys.exit(main())
