#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Local verification with external receipts bound to unchanged public sources.
set -euo pipefail
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
export PYTHONDONTWRITEBYTECODE=1
exec python3 "$repository_root/scripts/verify.py"
