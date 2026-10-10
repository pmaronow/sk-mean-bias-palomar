"""Conservative source inventory; kernel axiom reports remain authoritative."""
from pathlib import Path
import hashlib
import re
import subprocess
import sys
import tomllib

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?'
                  r'(?P<mods>(?:(?:public|private|protected|noncomputable|unsafe|partial|meta|nonrec)\s+)*)'
                  r'(?P<kind>theorem|lemma|def|abbrev|opaque|structure|inductive|class|instance|axiom|constant)'
                  r'\s+(?P<name>[^\s(:{\[]+)')

def mask(text):
    """Retain line numbers while masking nested Lean comments and strings."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                out[i:i+2] = '  '; i += 2
            else:
                if text[i] == '"': string = False
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: j = len(text)
            out[i:j] = ' ' * (j-i); i = j
        elif text[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    return ''.join(out)

def scan(paths, root):
    declarations, violations = [], []
    for path in paths:
        source, scopes = mask(path.read_text()), []
        relative = str(path.relative_to(root))
        for match in re.finditer(r'\b(?:sorry|admit|sorryAx|native_decide)\b', source):
            violations.append({'file': relative, 'line': source.count('\n', 0, match.start()) + 1,
                               'token': match.group()})
        for number, line in enumerate(source.splitlines(), 1):
            namespace = re.match(r'\s*(?:public\s+)?namespace\s+([\w.]+)\s*$', line)
            section = re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section(?:\s+([\w.]+))?\s*$', line)
            end = re.match(r'\s*end(?:\s+([\w.]+))?\s*$', line)
            if namespace:
                scopes.append(('namespace', namespace[1])); continue
            if section:
                scopes.append(('section', section[1] or '')); continue
            if end:
                if scopes: scopes.pop()
                continue
            match = DECL.match(line)
            if not match:
                continue
            if match['kind'] in {'axiom', 'constant'} or {'unsafe', 'partial'} & set(match['mods'].split()):
                violations.append({'file': relative, 'line': number, 'token': match['kind']})
            if 'private' in match['mods'].split():
                continue
            name = match['name']
            prefix = '.'.join(s for kind, s in scopes if kind == 'namespace')
            name = name.removeprefix('_root_.') if name.startswith('_root_.') else \
                '.'.join(s for s in [prefix, name] if s)
            declarations.append({'name': name, 'kind': match['kind'], 'file': relative, 'line': number})
    return declarations, violations

def imports(path):
    """Read import lines, including Lean 4's visibility-qualified imports.

    Comments and strings are masked first. Horizontal whitespace keeps a
    match on its own line; a blank import line cannot consume a later command.
    Both ordinary module lists and ``public import`` are used by the release's
    vendored dependencies. ``private`` and ``meta`` qualifiers are recognized
    as well, so they cannot silently cut the transitive source closure.
    """
    return [module for match in re.finditer(
                r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\n]+)',
                mask(path.read_text()), re.M)
            for module in match[1].split()]

def resolve(module, roots):
    relative = Path(*module.split('.')).with_suffix('.lean')
    return next((root / relative for root in roots if (root / relative).is_file()), None)

def dependencies(paths, roots):
    pending, seen = list(paths), set()
    while pending:
        path = pending.pop()
        if path in seen: continue
        seen.add(path)
        pending += [p for module in imports(path) if (p := resolve(module, roots)) is not None]
    return seen

def check_private_import_capacity(*, platform=None, sysctl_path=None):
    """Check Linux's mapping limit before importing the full private closure.

    Full proof-body audits map many compiled module parts. This preflight only
    reads host configuration; it never changes it. Other platforms have no
    Linux sysctl to check and return an explicit not-applicable result. The
    keyword overrides support deterministic tests without altering the host.
    """
    platform = sys.platform if platform is None else platform
    minimum = 262144
    result = {'platform': platform, 'status': 'not_applicable',
              'linux_vm_max_map_count': None,
              'linux_vm_max_map_count_minimum': minimum}
    if not platform.startswith('linux'):
        return result
    path = Path('/proc/sys/vm/max_map_count') if sysctl_path is None else Path(sysctl_path)
    try:
        observed = int(path.read_text().strip())
    except (OSError, ValueError) as error:
        raise ValueError('Cannot check Linux vm.max_map_count for full proof-body imports: '
                         + str(error)) from error
    if observed < minimum:
        raise ValueError('Full proof-body imports require Linux vm.max_map_count >= '
                         + str(minimum) + '; observed ' + str(observed)
                         + '. Ask the host administrator to increase vm.max_map_count '
                         + 'before rerunning the audit.')
    result.update(status='passed', linux_vm_max_map_count=observed)
    return result

def collect_artifact_snapshot(root, sources, include_external=True):
    """Freeze compiled import artifacts; this does not replace a fresh build.

    `sources` contains absolute or repository-relative Lean paths. The return
    value maps stable artifact labels to absolute paths, byte counts and SHA256.
    Module sources require all exported/server/private .olean parts. External
    imports are followed through available package/toolchain source roots. An
    import without source fails closed: freezing just its own artifact would
    leave its unknown transitive imports outside this certificate.
    """
    root = Path(root).resolve()
    source_bases = [(root, root / '.lake/build/lib/lean', '')]
    if include_external:
        for package in sorted((root / '.lake/packages').glob('*')):
            if not package.is_dir():
                continue
            artifact_base = package / '.lake/build/lib/lean'
            source_bases.append((package.resolve(), artifact_base, 'packages/' + package.name + '/'))
            cfg = package / 'lakefile.toml'
            if cfg.is_file():
                data = tomllib.loads(cfg.read_text())
                for lib in data.get('lean_lib', []):
                    src = lib.get('srcDir', '.')
                    if src != '.':
                        source_bases.append(((package / src).resolve(), artifact_base,
                                             'packages/' + package.name + '/'))
        prefix = subprocess.run(['lake', 'env', 'lean', '--print-prefix'], cwd=root,
                                check=True, capture_output=True, text=True).stdout.strip()
        prefix = Path(prefix)
        source_bases.append((prefix / 'src/lean', prefix / 'lib/lean', 'toolchain/'))
        # Lake keeps source under a separate nested root but exports modules
        # such as Lake.Util.Casing into the same toolchain artifact library.
        source_bases.append((prefix / 'src/lean/lake', prefix / 'lib/lean', 'toolchain/'))
    source_bases = list(dict.fromkeys(source_bases))
    roots = [source for source, _, _ in source_bases]
    pending = [Path(p) if Path(p).is_absolute() else root / p for p in sources]
    if include_external:
        pending.extend(p for name in ('Init', 'Lean') if (p := resolve(name, roots)) is not None)
    seen, artifacts = set(), {}
    while pending:
        source = pending.pop().resolve()
        if source in seen:
            continue
        seen.add(source)
        matches = [(base, lib, label) for base, lib, label in source_bases
                   if source.is_relative_to(base)]
        if not matches:
            raise ValueError('cannot locate compiled artifacts for ' + str(source))
        base, library, label = max(matches, key=lambda item: len(item[0].parts))
        module_path = source.relative_to(base).with_suffix('.olean')
        artifact = library / module_path
        source_bytes = source.read_bytes()
        is_module = re.search(r'^[ \t]*module[ \t]*$', mask(source_bytes.decode()), re.M) is not None
        parts = [artifact]
        for suffix in ('.server', '.private'):
            part = Path(str(artifact) + suffix)
            if is_module or part.is_file():
                parts.append(part)
        for part in parts:
            if not part.is_file():
                raise ValueError('missing compiled import artifact: ' + str(part))
            key = label + 'lib/lean/' + str(part.relative_to(library))
            content = part.read_bytes()
            artifacts[key] = {'path': str(part.resolve()), 'bytes': len(content),
                              'sha256': hashlib.sha256(content).hexdigest(),
                              'source_path': str(source),
                              'source_sha256': hashlib.sha256(source_bytes).hexdigest(),
                              'imports_traversed_from_source': True}
        for name in imports(source):
            path = resolve(name, roots)
            if path is not None:
                pending.append(path)
            else:
                raise ValueError('cannot freeze transitive compiled import closure: '
                                 + name + ' has no available source (imported by '
                                 + str(source) + ')')
    return artifacts

def verify_artifact_snapshot(snapshot):
    """Return labels of missing/changed files from collect_artifact_snapshot."""
    changed, checked_sources = [], set()
    for label, record in snapshot.items():
        path = Path(record['path'])
        if not path.is_file():
            changed.append(label)
            continue
        content = path.read_bytes()
        if len(content) != record['bytes'] or hashlib.sha256(content).hexdigest() != record['sha256']:
            changed.append(label)
        source_name = record.get('source_path')
        if source_name is not None and source_name not in checked_sources:
            checked_sources.add(source_name)
            source = Path(source_name)
            if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != record['source_sha256']:
                changed.append(label + ':import-source')
    return changed
