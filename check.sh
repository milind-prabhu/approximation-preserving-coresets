#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build
audit_output="$(mktemp)"
trap 'rm -f -- "$audit_output"' EXIT
lake env lean Audit.lean | tee "$audit_output"
python3 scripts/check_audit.py "$audit_output"
echo 'Build and axiom audit passed.'
