"""Verify complete axiom reports and the source hashes in the supplied audit."""
from pathlib import Path
import hashlib
import json
import re
import sys

root = Path(__file__).resolve().parents[1]
report = Path(sys.argv[1]).read_text()
expected = set(re.findall(r"^#print axioms (\S+)", (root / 'Audit.lean').read_text(), re.M))
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", report):
    found[name] = {a.strip() for a in axioms.split(',') if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", report):
    found[name] = set()
assert expected <= found.keys(), f'Missing reports: {sorted(expected - found.keys())}'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in found.items():
    assert axioms <= allowed, f'Unexpected axioms in {name}: {axioms - allowed}'
summary = json.loads((root / 'verification-summary.json').read_text())
for rel, digest in summary['sources'].items():
    assert hashlib.sha256((root / rel).read_bytes()).hexdigest() == digest, f'Source hash mismatch: {rel}'
print(f'Audit passed: {len(expected)} declarations; only standard Lean axioms; '
      f'{len(summary["sources"])} source hashes match.')
