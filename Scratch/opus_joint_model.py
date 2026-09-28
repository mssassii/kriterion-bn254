#!/usr/bin/env python3
"""Opus structural research: joint byte model over the two structural axes, at the W1 accounting.

Axes: digit count D (Astra's larger-radix information counts, codex 7ac0895 evidence/structural/larger-radices.md),
affine records per digit r (7 today), and the conversion word range C (Scratch/opus_carry_model.py). For each point it
prints the exact public bits with W1 components, and the room left under <= 799,992 bits expressed as extra
conversion blocks per coordinate (X) or extra records.

Record width: 618 (W1) and, separately, the floor implied by the privacy constant for E = r D + 5 encodings, taking
smudgeError = (2E (p-1)^2 + 273 p)/M (the 1284 = 2 * 642 numerator scaled with E; the 273 p term kept, an assumption),
window 15((p-1)^2+1)/M and the W1 remainder (pads, collisions, cutoff) as fixed. That floor is a bound on the width,
not a selected modulus table: conversion blocks are held at the W1 table's value (so it is conservative) and queries
are NOT modeled. Everything here is a projection; no row construction, recursion bound or privacy proof exists for
D < 91. Run: python3 Scratch/opus_joint_model.py
"""
from fractions import Fraction as F
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import opus_carry_model as cm  # noqa: E402  (prints its own table on import)
from opus_window_model import constant, P  # noqa: E402

W, TARGET = 101, 8 * 99_999
TABLE = cm.TABLE
M = math.prod(TABLE)
REST = constant(TABLE, True) - (F(1284 * (P - 1) ** 2 + 273 * P, M) + F(15 * ((P - 1) ** 2 + 1), M)) * 2 ** 100
BLOCKS = {C: cm.total(C, 32 * 13)[0] for C in (32, 4, 2, 1)}


def record_floor(E):
    """Least bitlen(2M - 1) compatible with constant + 1/1000 <= 2 for E encodings (M real, then 2M needs bits)."""
    num = (2 * E * (P - 1) ** 2 + 273 * P + 15 * ((P - 1) ** 2 + 1)) * 2 ** 100
    room = F(2) - F(1, 1000) - REST
    m_min = F(num) / room
    return math.floor(math.log2(2 * m_min)) + 1


def bits(D, r, C, R, extra_blocks=0):
    return 762 + 265 * D + (r * D + 5) * R + 2 * (BLOCKS[C] + extra_blocks) * W


print('\n# joint model (W1 accounting; REST constant =', float(REST), ')')
assert bits(91, 7, 32, 618) == 1003595
for name, D in (('norm 7 (W1)', 91), ('norm 13', 69), ('norm 19', 60), ('norm 49', 46)):
    for r in (7, 8):
        E = r * D + 5
        for C in (32, 4, 2):
            for R in sorted({618, record_floor(E)}):
                b = bits(D, r, C, R)
                room = TARGET - b
                print(f'{name:12s} D={D:2d} r={r} E={E:3d} C={C:2d} R={R}: {b:>9,} bits = {(b + 7) // 8:>7,} B; '
                      f'room {room:>8,} bits = {room // (2 * W):>6,} extra blocks/coord or {room // R:>5,} records')
print('\nrecord-width floor by encodings:', {E: record_floor(E) for E in (642, 488, 327, 250)})
