#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Compare the declared statements and replay the proved closure in three kernels.
set -euo pipefail
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"
for command_name in bwrap lake lean python3; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    printf 'error: required command unavailable: %s\n' "$command_name" >&2
    exit 1
  fi
done
lean_prefix=$(lean --print-prefix)
for executable in lake leanexport leanchecker nanoda_bin con-ron; do
  if [[ ! -x "$lean_prefix/bin/$executable" ]]; then
    printf 'error: pinned Lean toolchain does not bundle %s\n' "$executable" >&2
    exit 1
  fi
done
private_import_runtime=$(python3 - "$repository_root" <<'PY'
from pathlib import Path
import json
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(sys.argv[1]) / "scripts"))
from lean_source_scan import check_private_import_capacity
try:
    print(json.dumps(check_private_import_capacity(), sort_keys=True))
except Exception as error:
    print(f"error: private-import runtime preflight failed: {error}", file=sys.stderr)
    raise SystemExit(1)
PY
)
verification_directory=$(python3 - "$repository_root" "${SK_VERIFY_LOG_DIR:-}" <<'PY'
from pathlib import Path
import sys
import tempfile
root = Path(sys.argv[1]).resolve()
def external(path):
    path = path.resolve()
    if path == root or root in path.parents:
        raise SystemExit("SK_VERIFY_LOG_DIR and the temporary directory must be outside the public source tree")
    return path
if sys.argv[2]:
    output = external(Path(sys.argv[2]))
    output.mkdir(parents=True, exist_ok=True)
else:
    parent = external(Path(tempfile.gettempdir()))
    output = Path(tempfile.mkdtemp(prefix="sk-mean-bias-verification-", dir=parent))
print(output)
PY
)
python3 - "$repository_root" "$verification_directory" <<'PY'
from pathlib import Path
import hashlib
import json
import os
import sys
root, output = map(lambda p: Path(p).resolve(), sys.argv[1:])
inputs = {}
for directory, subdirectories, names in os.walk(root, followlinks=False):
    subdirectories[:] = sorted(name for name in subdirectories
                              if name not in {".git", ".lake", "__pycache__"}
                              and not (Path(directory) / name).is_symlink())
    for name in sorted(names):
        path = Path(directory) / name
        if path.is_file() and not path.is_symlink() and (
            name.endswith(".lean") or name in {
                "lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json"
            }
        ):
            inputs[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
(output / "comparator-input-sha256.json").write_text(json.dumps(inputs, indent=2) + "\n")
PY
configuration=$(mktemp "$verification_directory/protected-comparator.XXXXXXXX.json")
trap 'rm -f "$configuration"' EXIT
python3 - comparator.json "$configuration" "$lean_prefix" <<'PY'
import json
from pathlib import Path
import sys
source, target, prefix = sys.argv[1:]
source_path = Path(source)
if source_path.is_symlink() or not source_path.is_file() or source_path.stat().st_size > 1024 * 1024:
    raise SystemExit("error: Comparator configuration must be a regular file at most 1 MiB")
def unique_object(pairs):
    value = {}
    for name, item in pairs:
        if name in value:
            raise ValueError("duplicate Comparator key: " + name)
        value[name] = item
    return value
config = json.loads(source_path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
if not isinstance(config, dict):
    raise SystemExit("error: comparator.json must contain one object")
required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
if not required <= set(config) or set(config) - required - {"definition_names", "enable_nanoda"}:
    raise SystemExit("error: Comparator configuration contains missing or forbidden fields")
if config["challenge_module"] != "Challenge" or config["solution_module"] != "Solution":
    raise SystemExit("error: this repository requires its Challenge/Solution module pair")
for field in ["theorem_names", "definition_names"]:
    names = config.get(field, [])
    if not isinstance(names, list) or not all(isinstance(name, str) and name for name in names):
        raise SystemExit("error: Comparator declaration names must be arrays of nonempty strings")
if not config["theorem_names"]:
    raise SystemExit("error: Comparator requires a nonempty theorem_names array")
axioms = config["permitted_axioms"]
if not isinstance(axioms, list) or not all(name in {"propext", "Quot.sound", "Classical.choice"} for name in axioms):
    raise SystemExit("error: Comparator permits only the three standard axioms")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [str(Path(prefix) / "bin/nanoda_bin")],
    "con-ron": [str(Path(prefix) / "bin/con-ron"), "--jobs=2"],
}
Path(target).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
export TMPDIR="$verification_directory"
printf 'Verification transcript: %s/comparator.log\n' "$verification_directory"
set +e
lake comparator --config "$configuration" 2>&1 | tee "$verification_directory/comparator.log"
pipeline_exit=("${PIPESTATUS[@]}")
comparator_exit=${pipeline_exit[0]}
transcript_exit=${pipeline_exit[1]}
set -e
python3 - "$repository_root" "$verification_directory" "$lean_prefix" "$comparator_exit" "$transcript_exit" "$configuration" "$private_import_runtime" <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess
import sys
root, output, prefix = map(Path, sys.argv[1:4])
exit_code = int(sys.argv[4])
transcript_exit = int(sys.argv[5])
protected_config = Path(sys.argv[6])
private_import_runtime = json.loads(sys.argv[7])
transcript = (output / "comparator.log").read_text(encoding="utf-8", errors="replace")
kernels = ["nanoda", "con-ron", "Lean default"]
acceptance = {name: f"{name} kernel accepts the solution" in transcript.splitlines() for name in kernels}
passed = exit_code == 0 and transcript_exit == 0 and all(acceptance.values()) and "Your solution is okay!" in transcript.splitlines()
def git(*args):
    proc = subprocess.run(["git", "-C", str(root), *args], text=True, capture_output=True)
    return proc.stdout.strip() if proc.returncode == 0 else None
files = {}
for path in sorted(root.rglob("*")):
    relative = path.relative_to(root)
    if any(part in {".git", ".lake", "__pycache__"} for part in relative.parts):
        continue
    if path.is_file() and not path.is_symlink():
        files[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
input_before = json.loads((output / "comparator-input-sha256.json").read_text())
input_after = {name: value for name, value in files.items()
               if name.endswith(".lean") or Path(name).name in {
                   "lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json"
               }}
inputs_unchanged = input_before == input_after
passed = passed and inputs_unchanged
source_digest = hashlib.sha256(json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
git_state = git("status", "--porcelain")
report = {
    "check": "local-comparator-and-independent-kernel-replay",
    "passed": passed,
    "comparator_exit": exit_code,
    "transcript_write_exit": transcript_exit,
    "private_import_runtime": private_import_runtime,
    "executed_protected_configuration": json.loads(protected_config.read_text()),
    "executed_protected_configuration_sha256": hashlib.sha256(protected_config.read_bytes()).hexdigest(),
    "kernels": acceptance,
    "verification_inputs_unchanged": inputs_unchanged,
    "verification_input_sha256": input_before,
    "source_commit": git("rev-parse", "HEAD"),
    "source_dirty": bool(git_state) if git_state is not None else None,
    "source_tree_sha256": source_digest,
    "source_file_sha256": files,
    "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
    "binary_sha256": {
        name: hashlib.sha256((prefix / "bin" / name).read_bytes()).hexdigest()
        for name in ["lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]
    },
    "configuration_sha256": hashlib.sha256((root / "comparator.json").read_bytes()).hexdigest(),
    "limitations": "Local check; does not execute Palomar's protected canonical Challenge build or editorial review.",
}
(output / "comparator-summary.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(f"Structured result: {output / 'comparator-summary.json'}")
if not passed:
    print("error: Comparator, all three kernel acceptances, and unchanged verification inputs are required", file=sys.stderr)
    raise SystemExit(exit_code or 1)
PY
