#!/usr/bin/env python3
"""Opus W1: independent expectations for "window charged at its proved size, modulus 41 -> 17" on 857e88b.

Derives every literal the patch needs from the formulas (not from Lean): metrics, coordinate budgets, join/pin
counts, serializer pieces, record width, product, and the exact constant with the proved window term.
Run: python3 Scratch/opus_check_w1.py
"""
from fractions import Fraction as F
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import opus_budget_model as m  # noqa: E402
from opus_window_model import evaluate, constant, P  # noqa: E402

W = 101
W9 = [59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
      383, 389, 397]
BASE = m.moduli_from_source()
TABLE = sorted([x for x in BASE if x != 41] + [17]) if 41 in BASE else BASE
assert 17 in TABLE and 41 not in TABLE and len(TABLE) == 84
widths = {x: 9 for x in W9}
r = evaluate(TABLE, widths)
M = math.prod(TABLE)
rows = [m.odd_row(x, widths.get(x, 8), W) for x in TABLE if x != 256]
ch = [8] * 31 + [6]
cg = sum(m.extract(w, 14, W)[0] for w in ch)
ce = sum(m.extract(w, 14, W)[1] for w in ch)
coord = {}
for name, s in (('x', 367), ('y', 275)):
    coord['g' + name] = cg + sum(q['garble'] for q in rows) + sum(x * m.pad_q(x, s) for x in TABLE)
    coord['e' + name] = ce + sum(q['evaluate'] for q in rows) + sum((x - 1) * m.pad_q(x, s) for x in TABLE)


def joins(x):
    w0 = widths.get(x, 8)
    ell = (32 * (x - 1)).bit_length()
    w1, keep = ell - w0 - 1, max(w0, ell - 5)
    return (w0 - 1) + (w1 - 1) + (keep - w0) + (ell - keep)


pj = sum(joins(x) for x in TABLE if x != 256)
pins = 32 + 2 * sum(1 for x in TABLE if x != 256)
pieces = (3 + 182 + 182 + 642) + 2 * pj + 2 * pins * W
C = constant(TABLE, True)
smudge = F(1284 * (P - 1) ** 2 + 273 * P, M) * 2 ** 100
window = F(15 * ((P - 1) ** 2 + 1), M) * 2 ** 100
print('table', TABLE)
print(f"metrics {r['bytes']} B / {r['G']} / {r['E']}; bits {r['bits']}; padding {(-r['bits']) % 8}; record bits {r['record_bits']}")
print(f"coord budgets {coord}; blocks {r['blocks']}; joinCount {222 + pj}; published joins {pj}; pins {pins}; pieces {pieces}")
print(f"log2 M {math.log2(M):.4f}; M = {M}")
print(f"constant {float(C):.6f}: smudge {float(smudge):.6f} (share 77/50: {smudge <= F(77, 50)}), "
      f"window {float(window):.6f} (share 1/50: {window <= F(1, 50)}); closure <= 2: {C + F(1, 1000) <= 2}")
assert r['record_bits'] == 618 and 2 * M <= 2 ** 618 and smudge <= F(77, 50) and window <= F(1, 50)
assert (r['bytes'], r['G'], r['E']) == (125450, 1060976, 1054152)
