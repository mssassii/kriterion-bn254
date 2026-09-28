#!/usr/bin/env python3
"""Opus P1b: independent expectations for the 101-bit-label candidate (84 moduli, 26 width-9 rows).

Recomputes, from the formulas (not from Lean constants): the three metrics with 101 lanes, the packed conversion
vector bytes and padding, the serializer piece count, and the exact security inequality at the refined charge.
Run: python3 Scratch/opus_check_w101.py
"""
from fractions import Fraction as F
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import opus_budget_model as m  # noqa: E402
from opus_next_ideas import queries, constant, W9  # noqa: E402

W = 101
P = m.P
moduli = m.moduli_from_source()
assert len(moduli) == 84 and 17 not in moduli
g, e, blocks = queries(label_bits=W)
g104, e104, blocks104 = queries(label_bits=104)
assert (g, e, blocks) == (g104, e104, blocks104) == (1061622, 1054788, 2885), 'queries must not change with w'
packed = (W * blocks + 7) // 8
pad = 8 * packed - W * blocks
M = math.prod(moduli)
record_bytes = math.ceil((2 * M - 1).bit_length() / 8)
total = 96 + 91 * 33 + 91 + 2 * packed + 642 * record_bytes
odd = [x for x in moduli if x != 256]
pins = 32 + 2 * len(odd)
published_joins = sum((8 if x not in W9 else 9) - 1 + ((32 * (x - 1)).bit_length() - (9 if x in W9 else 8) - 1) - 1
                      + (max(9 if x in W9 else 8, (32 * (x - 1)).bit_length() - 5) - (9 if x in W9 else 8))
                      + ((32 * (x - 1)).bit_length() - max(9 if x in W9 else 8, (32 * (x - 1)).bit_length() - 5))
                      for x in odd)
pieces = (3 + 182 + 182 + 642) + 2 * published_joins + 2 * pins * W + 2
C, _ = constant()
c = F(1, 2 ** W) + F(1, P - 1)
Q = 2 ** 100 - 1
worst = max(C + 2 * c * 2 ** 100 * q1 + c * 2 ** 100 * q2 - (q1 + q2 + 2) for q1, q2 in ((0, 0), (Q, 0), (0, Q)))
share_ok = (1 * (P - 1) + 2 ** W) * 2 ** 100 * 2 ** 152 <= (2 ** 151 + 1) * (2 ** W * (P - 1))
lean_closure = F(1408, 1000) + 2 * F(1, 1000) - 2   # constant shares + excess bound 1/1000 (Budget.lean) minus 2
print(f'metrics: {total} B / {g} / {e}  (conversion {2 * packed} B = 2 x {packed}, pad {pad} bits each)')
print(f'blocks {blocks}, pins {pins}, published joins {published_joins}, serializer pieces {pieces}')
print(f'constant C = {float(C):.6f}; stage-1 coef = 1 + {float(F(2 ** (101), P - 1)):.3e}; '
      f'worst vertex margin = {float(-worst):.6f} units; kernel share holds: {share_ok}')
assert (total, packed, pad, pieces, published_joins, pins) == (126114, 36424, 7, 43393, 1193, 198)
assert worst < 0 and share_ok and lean_closure < 0
print('width-101 expectations: OK')
