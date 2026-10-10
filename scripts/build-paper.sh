#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Build the current manuscript without putting TeX intermediates in source.
set -euo pipefail
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
for command_name in pdflatex bibtex python3; do
  command -v "$command_name" >/dev/null || { printf 'Missing %s\n' "$command_name" >&2; exit 1; }
done
paper_build_directory=$(python3 - "$repository_root" "${SK_PAPER_BUILD_DIR:-}" <<'PY'
from pathlib import Path
import sys
import tempfile
root = Path(sys.argv[1]).resolve()
def external(path):
    path = path.resolve()
    if path == root or root in path.parents:
        raise SystemExit("SK_PAPER_BUILD_DIR and the temporary directory must be outside the public source tree")
    return path
if sys.argv[2]:
    output = external(Path(sys.argv[2]))
    output.mkdir(parents=True, exist_ok=True)
else:
    parent = external(Path(tempfile.gettempdir()))
    output = Path(tempfile.mkdtemp(prefix="sk-mean-bias-paper-", dir=parent))
print(output)
PY
)
cd "$repository_root/paper"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$paper_build_directory" main.tex > "$paper_build_directory/first-run.log" 2>&1
(cd "$paper_build_directory"; BIBINPUTS="$repository_root/paper:" bibtex main > bibtex.log 2>&1)
for pass_number in 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$paper_build_directory" main.tex > "$paper_build_directory/pass-$pass_number.log" 2>&1
done
printf 'Built manuscript: %s/main.pdf\n' "$paper_build_directory"
