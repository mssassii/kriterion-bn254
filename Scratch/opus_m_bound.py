#!/usr/bin/env python3
"""Opus: exact lower bound on the CRT product M from the two-unit constant budget (current proof structure)."""
from fractions import Fraction as F
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from opus_next_ideas import constant, MODULI  # noqa: E402

P = 21888242871839275222246405745257275088696311157297823662689037894645226208583


def log2(q):
    return math.log2(q.numerator) - math.log2(q.denominator)


M = math.prod(MODULI)
C, _ = constant()
S = F(1284 * (P - 1) ** 2 + 273 * P) * 2 ** 100          # one smudge copy is S / M units
others = C - 2 * S / M
print(f'current log2 M = {math.log2(M):.6f}; constant C = {float(C):.6f}; two smudge copies = {float(2 * S / M):.6f}; '
      f'all other constant terms = {float(others):.6e}')
for spare, label in ((F(0), 'exact (no per-query excess reserved)'), (F(1, 1000), "reserving the proof's 1/1000 excess")):
    print(f'{label}: log2 M_min = {log2(2 * S / (2 - others - spare)):.6f}')
print(f'if one smudge copy only: log2 M_min = {log2(S / (2 - others)):.6f}')
print(f'strictly under 100,000 B: bits <= {99999 * 8}; current unpadded 1,005,687; reduction >= {1005687 - 99999 * 8}')
