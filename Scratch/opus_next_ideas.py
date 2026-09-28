#!/usr/bin/env python3
"""Opus: exact projections for the next savings on the combined configuration (84 moduli, width 9 on 26 rows).

Projections only (no Lean). Exact rationals for every privacy inequality; exact bit/byte counts.
Run: python3 Scratch/opus_next_ideas.py
"""
from fractions import Fraction as F
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import opus_budget_model as m  # noqa: E402

P, R = m.P, m.R
E_GATE, G_GATE = 1055879, 1759967
W9 = [59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373,
      379, 383, 389, 397]
MODULI = m.moduli_from_source()          # H1 source: 84 moduli, no 17
assert len(MODULI) == 84 and 17 not in MODULI
WIDTHS = {x: 9 for x in W9}
S_X, S_Y = 367, 275


def queries(label_bits=104, slack=120, widths=WIDTHS, moduli=MODULI):
    rows = [m.odd_row(x, widths.get(x, 8), label_bits) for x in moduli if x != 256]
    ch = [8] * 31 + [6]
    cg = sum(m.extract(w, 14, label_bits)[0] for w in ch)
    ce = sum(m.extract(w, 14, label_bits)[1] for w in ch)
    g = e = 0
    for s in (S_X, S_Y):
        g += cg + sum(r['garble'] for r in rows) + sum(x * m.pad_q(x, s, slack) for x in moduli)
        e += ce + sum(r['evaluate'] for r in rows) + sum((x - 1) * m.pad_q(x, s, slack) for x in moduli)
    blocks = 32 * 13 + sum(r['blocks'] for r in rows)
    return g + 2291, e + 1783, blocks


def constant(slack=120, moduli=MODULI):
    """The whole-chain constant in units of 2^-100 (Budget.lean `chainError`), pads recomputed at `slack`."""
    M = math.prod(moduli)
    pads = F(637 * (2 ** 384 % P), 2 ** 384)
    for s in (S_X, S_Y):
        for x in moduli:
            if x != 256:
                pads += F(x * x ** s, 2 ** (256 * m.pad_q(x, s, slack)))
    smudge = F(1284 * (P - 1) ** 2 + 273 * P, M)
    terms = F(G_GATE, P) + 3 * pads + 2 * smudge + F(546 + 455, R - 1) + F(185 + 1, 2 ** 128)
    return terms * 2 ** 100, 3 * pads * 2 ** 100


def fits(C, charge):
    """Exact check of `C + 2c·2^100·q₁ + c·2^100·q₂ ≤ q₁ + q₂ + 2` for all q₁ + q₂ < 2^100 (vertices suffice)."""
    a1, a2 = 2 * charge * 2 ** 100, charge * 2 ** 100
    Q = 2 ** 100 - 1
    return all(C + a1 * q1 + a2 * q2 <= q1 + q2 + 2 for q1, q2 in ((0, 0), (Q, 0), (0, Q))), a1, a2


def bitpacked_bytes(label_bits, record_bits=None, field_bits=256, flag_bits=8, blocks=None):
    M = math.prod(MODULI)
    record_bits = record_bits or 8 * math.ceil((2 * M - 1).bit_length() / 8)
    total = 3 * field_bits + 91 * (field_bits + flag_bits) + 91 * 8 + 2 * blocks * label_bits + 642 * record_bits
    return math.ceil(total / 8), total


def main():
    g0, e0, blocks = queries()
    base_bytes = 96 + 91 * 33 + 91 + 2 * blocks * 13 + 642 * 78
    C, pads3 = constant()
    M = math.prod(MODULI)
    rec_min = (2 * M - 1).bit_length()
    print(f'combined (projection): {base_bytes} B / {g0} / {e0}; blocks {blocks}; constant C = {float(C):.6f} '
          f'units (pads x3 = {float(pads3):.3e}); record bits needed {rec_min}')
    assert (base_bytes, g0, e0) == (128276, 1061622, 1054788)

    print('\n-- label width w: security (exact) and bytes --')
    print(' w | charge   | stage-1 coef | stage-2 coef | fits +2? | queries g / e | packed labels B | saving')
    for w in (104, 103, 102, 101, 100):
        for name, c in (('4/2^w', F(4, 2 ** w) + F(1, P - 1)), ('1/2^w', F(1, 2 ** w) + F(1, P - 1))):
            ok, a1, a2 = fits(C, c)
            g, e, b = queries(label_bits=w)
            packed = math.ceil(2 * b * w / 8)
            print(f'{w:3d} | {name:7s} | {float(a1):12.6f} | {float(a2):12.6f} | {str(ok):8s} | {g} / {e} | '
                  f'{packed} | {2 * b * 13 - packed}')

    # The exact margin at w = 101 with the refined charge.
    c101 = F(1, 2 ** 101) + F(1, P - 1)
    Q = 2 ** 100 - 1
    worst = C + 2 * c101 * 2 ** 100 * Q - (Q + 2)
    print(f'\nw=101, refined charge: worst vertex (q1 = 2^100-1, q2 = 0) slack = {float(-worst):.6f} units '
          f'(C = {float(C):.6f}; excess per stage-1 query = 2^101/(p-1) = {float(F(2 ** 101, P - 1)):.3e})')

    print('\n-- whole-Public bit packing (fields 254 bits, flags 3 bits, records at bitlen(2M-1)) --')
    for w in (104, 103, 102, 101):
        b = queries(label_bits=w)[2]
        by, bits = bitpacked_bytes(w, rec_min, 254, 3, b)
        print(f'w={w}: {by} B ({bits} bits), saving {base_bytes - by} vs {base_bytes}')
    for rb in (624, rec_min):
        by, _ = bitpacked_bytes(104, rb, 256, 8, blocks)
        print(f'records only at {rb} bits (labels 104, fields/flags unpacked): {by} B, saving {base_bytes - by}')
    by, _ = bitpacked_bytes(104, 624, 254, 3, blocks)
    print(f'fields 254 + flags 3 only: {by} B, saving {base_bytes - by}')

    print('\n-- pad slack: leftover constant budget -> fewer body queries -> more width-9 rows --')
    for slack in (120, 116, 112, 110, 108, 106, 104):
        Cs, p3 = constant(slack)
        ok, _, _ = fits(Cs, F(4, 2 ** 104) + F(1, P - 1))
        g, e, _ = queries(slack=slack)
        print(f'slack {slack}: C = {float(Cs):.4f} (pads x3 {float(p3):.3e}) fits={ok}; queries {g} / {e} '
              f'(eval headroom {E_GATE - e})')

    # Cheapest extra width-9 rows (evaluation delta per row) on top of the 26, for headroom planning.
    extra = []
    for x in MODULI:
        if x == 256 or x in WIDTHS:
            continue
        a, b = m.odd_row(x, 8), m.odd_row(x, 9)
        if b['ell'] - 10 < 1 or 511 > max(255, x - 1, 2 ** (a['ell'] - 1) - 128):
            continue
        extra.append((2 * (b['evaluate'] - a['evaluate']), x))
    extra.sort()
    print('next width-9 rows by evaluation cost:', extra[:6], '(each saves 52 B)')


if __name__ == '__main__':
    main()
