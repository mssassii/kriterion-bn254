#!/usr/bin/env python3
"""Independent complete-bit accounting for P1a and the later width-101 integration."""
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
# Reproduce the inherited query counts and schedule from the independent table model.
subprocess.run(['python3', '-B', 'Scratch/check_combined.py'], cwd=root, check=True)

def layout(label_bits):
    parts = dict(curve=3 * 254, rows=91 * (254 + 3), exception=91 * 2 * 4,
                 conversion=2 * 2885 * label_bits, records=(367 + 275) * 620)
    bits = sum(parts.values())
    return dict(label_bits=label_bits, components_bits=parts, bits=bits,
                padding_bits=(-bits) % 8, ciphertext_bytes=(bits+7)//8,
                garble_queries=1061622, evaluate_queries=1054788)
actual = layout(104)
assert actual['ciphertext_bytes'] == 127875
assert actual['bits'] == 1022997 and actual['padding_bits'] == 3
future = layout(101)
assert future['ciphertext_bytes'] == 125711
report = dict(current104=actual, modeled101=future,
              note='Width101 is a model only until its independent proofs are integrated and checked.')
print(json.dumps(report, indent=2))
(root / 'evidence/packed-public/independent-metrics.json').write_text(json.dumps(report, indent=2)+'\n')
