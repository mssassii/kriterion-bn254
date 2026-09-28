#!/usr/bin/env python3
"""Opus: exact model for charging the hidden-window term at its proved size and re-choosing one modulus.

Current proof (857e88b): hiddenWindowError := smudgeError = (1284(p-1)^2 + 273p)/M, although CurveWindow.lean proves
the event mass is at most 15((p-1)^2 + 1)/M. Charging the proved term lowers the two-unit M bound. This script:
  * computes the exact constant for a candidate table under both definitions;
  * tries single swaps m -> m' (m' coprime, >= 17, unused) and the width-9 greedy under the evaluation cap;
  * reports whole-stream bits/bytes with the packed codec (fields 254, flags 3, entry 8, labels 101,
    record field = bitlen(2M - 1)).
Projections only; no Lean.
"""
from fractions import Fraction as F
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import opus_budget_model as m  # noqa: E402

P, R = m.P, m.R
E_GATE, G_GATE, W = 1055879, 1759967, 101
BASE_COMMIT = '857e88b66f91ce0c61ab0e86ff6d8b9e9bf91790'  # the search starts from the submitted table, not the tree
BASE = list(map(int, m.re.findall(r'\d+', m.re.search(
    r'def bn254Moduli.*?#\[(.*?)\]', __import__('subprocess').run(
        ['git', 'show', f'{BASE_COMMIT}:Construction/CRT/Interface.lean'], cwd=m.ROOT, capture_output=True, text=True,
        check=True).stdout, m.re.S)[1])))


def pads_error(moduli, slack=120):
    total = F(637 * (2 ** 384 % P), 2 ** 384)
    for s in (367, 275):
        for x in moduli:
            if x != 256:
                total += F(x * x ** s, 2 ** (256 * m.pad_q(x, s, slack)))
    return total


def constant(moduli, window_proved):
    M = math.prod(moduli)
    smudge = F(1284 * (P - 1) ** 2 + 273 * P, M)
    window = F(15 * ((P - 1) ** 2 + 1), M) if window_proved else smudge
    return (F(G_GATE, P) + 3 * pads_error(moduli) + smudge + window + F(546 + 455, R - 1) + F(186, 2 ** 128)) * 2 ** 100


def evaluate(moduli, widths):
    rows = [m.odd_row(x, widths.get(x, 8), W) for x in moduli if x != 256]
    ch = [8] * 31 + [6]
    cg = sum(m.extract(w, 14, W)[0] for w in ch)
    ce = sum(m.extract(w, 14, W)[1] for w in ch)
    g = e = 0
    for s in (367, 275):
        g += cg + sum(r['garble'] for r in rows) + sum(x * m.pad_q(x, s) for x in moduli)
        e += ce + sum(r['evaluate'] for r in rows) + sum((x - 1) * m.pad_q(x, s) for x in moduli)
    blocks = 32 * 13 + sum(r['blocks'] for r in rows)
    M = math.prod(moduli)
    rec = (2 * M - 1).bit_length()
    bits = 762 + 91 * 257 + 91 * 8 + 2 * blocks * W + 642 * rec
    return dict(G=g + 2291, E=e + 1783, blocks=blocks, record_bits=rec, bits=bits, bytes=(bits + 7) // 8)


def greedy(moduli):
    widths = {}
    base = evaluate(moduli, widths)['E']
    cands = []
    for x in moduli:
        if x == 256:
            continue
        a, b = m.odd_row(x, 8, W), m.odd_row(x, 9, W)
        if b['ell'] - 10 < 1 or 511 > max(255, x - 1, 2 ** (a['ell'] - 1) - 128):
            continue
        cands.append((2 * (b['evaluate'] - a['evaluate']), x))
    e = base
    for d, x in sorted(cands):
        if e + d + 500 <= E_GATE:
            widths[x] = 9
            e += d
    return widths


def main():
    cur_w = {x: 9 for x in [59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
                            353, 359, 367, 373, 379, 383, 389, 397]}
    cur = evaluate(BASE, cur_w)
    assert (cur['bytes'], cur['G'], cur['E'], cur['bits']) == (125711, 1061622, 1054788, 1005687), cur
    print('current', cur, 'C(two copies) =', float(constant(BASE, False)))
    results = []
    for out in [x for x in BASE if x != 256]:
        for new in [17, 289]:
            table = sorted([x for x in BASE if x != out] + [new])
            if any(math.gcd(a, b) != 1 for i, a in enumerate(table) for b in table[i + 1:]):
                continue
            if 2 * ((P - 1) ** 2 + 1) > math.prod(table) + 1:
                continue
            C = constant(table, True)
            if C + F(1, 1000) > 2:
                continue
            w = greedy(table)
            r = evaluate(table, w)
            results.append((r['bytes'], out, new, float(C), r, len(w)))
    results.sort(key=lambda t: t[0])
    for b, out, new, C, r, nw in results[:8]:
        print(f'swap {out}->{new}: {b} B (bits {r["bits"]}, records {r["record_bits"]}), G {r["G"]}, E {r["E"]} '
              f'(headroom {E_GATE - r["E"]}), width-9 rows {nw}, constant {C:.4f}')
    table = BASE
    print('no swap, window proved: constant', float(constant(table, True)))


if __name__ == '__main__':
    main()
