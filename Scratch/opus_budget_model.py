#!/usr/bin/env python3
"""Opus: exact-integer cost and constant-error model for modulus-table changes.

Reproduces the pinned entry's three metrics and its constant privacy error (Proof/Privacy/CRT/Glue/Budget.lean,
`chainError`), then evaluates dropping moduli under two closures of the work bound:

* unit 1: the current `chainError_budget`, constant part <= 1 (`first + second + 1`);
* unit 2: `steps + 1 = size + 2 + firstFuel + secondFuel >= first + second + 2`
  (`BoundedMachine.Adversary.steps`), so the constant part may reach 2 units.

Every error term is an exact fraction; the constant is compared against the unit with integer arithmetic.
This is a cost/budget model, not a Lean proof.  Run: python3 Scratch/opus_budget_model.py
"""
from fractions import Fraction
import json
import math
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
P = 21888242871839275222246405745257275088696311157297823662689037894645226208583
R = 21888242871839275222246405745257275088548364400416034343698204186575808495617
G_GATE, E_GATE = 1759967, 1055879
LABEL_BITS = 104


def ceildiv(a, b):
    return (a + b - 1) // b


def cast_answers(width, label_bits=LABEL_BITS):
    return ceildiv(ceildiv(label_bits, 128 // width), 2)


def extract(width, ring_width, label_bits=LABEL_BITS):
    leaves = 1 << width
    answers = cast_answers(ring_width, label_bits)
    return leaves - 2 + leaves * answers, leaves - width - 1 + (leaves - 1) * answers


def odd_row(m, w0=8, label_bits=LABEL_BITS):
    ell = (32 * (m - 1)).bit_length()
    w1 = ell - w0 - 1
    keep = max(w0, ell - 5)
    g0, e0 = extract(w0, ell, label_bits)
    g1, e1 = extract(w1, ell - w0, label_bits)
    growth = 2 ** keep - 2 ** w0
    pins = (ell - 1) + (ell - w0 - 1)
    joins = (w0 - 1) + (w1 - 1) + (keep - w0) + (ell - keep)
    return dict(m=m, ell=ell, blocks=pins + joins,
                garble=g0 + g1 + growth + (ell - keep) * m,
                evaluate=e0 + e1 + growth - (keep - w0) + (ell - keep) * (m - 1))


def pad_q(m, count, slack=120):
    return ceildiv(count * 8, 256) if m == 256 else ceildiv((m ** count).bit_length() + slack, 256)


def metrics(moduli, widths=None, label_bits=LABEL_BITS):
    widths = widths or {}
    rows = [odd_row(m, widths.get(m, 8), label_bits) for m in moduli if m != 256]
    chunks = [8] * 31 + [6]
    chunk_g = sum(extract(w, 14, label_bits)[0] for w in chunks)
    chunk_e = sum(extract(w, 14, label_bits)[1] for w in chunks)
    blocks = 32 * 13 + sum(r['blocks'] for r in rows)
    M = math.prod(moduli)
    record_bytes = ceildiv((2 * M - 1).bit_length(), 8)
    g = e = 0
    for count in (367, 275):
        g += chunk_g + sum(r['garble'] for r in rows) + sum(m * pad_q(m, count) for m in moduli)
        e += chunk_e + sum(r['evaluate'] for r in rows) + sum((m - 1) * pad_q(m, count) for m in moduli)
    label_bytes = ceildiv(label_bits, 8)
    return dict(bytes=96 + 91 * 33 + 91 + 2 * blocks * label_bytes + 642 * record_bytes,
                garble=g + 2291, evaluate=e + 1783, blocks=blocks, record_bytes=record_bytes,
                log2M=round(math.log2(M), 3))


def pad_swap(moduli):
    """One swap: sum over both coordinates and odd moduli of m * m^S / 2^(256 q), plus 637 (2^384 mod p)/2^384."""
    total = Fraction(637 * (2 ** 384 % P), 2 ** 384)
    for count in (367, 275):
        for m in moduli:
            if m == 256:
                continue
            total += Fraction(m * m ** count, 2 ** (256 * pad_q(m, count)))
    return total


def constant_error(moduli, smudge_count=1284, window_count=1284):
    """The constant part of `chainError` (Budget.lean), times 2^100.  `hiddenWindowError := smudgeError` today."""
    M = math.prod(moduli)
    smudge = Fraction(smudge_count * (P - 1) ** 2 + 273 * P, M)
    window = Fraction(window_count * (P - 1) ** 2 + 273 * P, M)
    terms = dict(collision=Fraction(G_GATE, P), padSwap3=3 * pad_swap(moduli), smudge=smudge, window=window,
                 exceptional=Fraction(546, R - 1), kernel=Fraction(455, R - 1),
                 coincidence=Fraction(185, 2 ** 128), cutoff=Fraction(1, 2 ** 128))
    return {k: v * 2 ** 100 for k, v in terms.items()}


def moduli_from_source():
    text = (ROOT / 'Construction/CRT/Interface.lean').read_text()
    return list(map(int, re.findall(r'\d+', re.search(r'def bn254Moduli.*?#\[(.*?)\]', text, re.S)[1])))


def main():
    moduli = moduli_from_source()
    base = metrics(moduli)
    assert (base['bytes'], base['garble'], base['evaluate']) == (130122, 988438, 981506), base
    c0 = constant_error(moduli)
    c0_total = sum(c0.values())
    out = dict(status='exact integer model; not a Lean proof', baseline=base,
               baseline_constant_units=float(c0_total),
               baseline_terms={k: float(v) for k, v in c0.items()})
    drops = []
    for m in moduli:
        if m == 256:
            continue
        rest = [x for x in moduli if x != m]
        M = math.prod(rest)
        if 2 * ((P - 1) ** 2 + 1) > M:
            continue
        met = metrics(rest)
        c = sum(constant_error(rest).values())
        c_win5 = sum(constant_error(rest, window_count=10).values())
        drops.append(dict(dropped=m, **met, saved=base['bytes'] - met['bytes'],
                          garble_delta=met['garble'] - base['garble'],
                          evaluate_delta=met['evaluate'] - base['evaluate'],
                          constant_units=round(float(c), 4), fits_unit1=c <= 1, fits_unit2=c < 2,
                          constant_units_window5=round(float(c_win5), 4), fits_unit2_window5=c_win5 < 2))
    out['single_drops_fitting_unit2'] = [d for d in drops if d['fits_unit2']]
    out['single_drops_fitting_unit2_window5'] = [d for d in drops if d['fits_unit2_window5']]
    out['any_drop_fits_unit1'] = any(d['fits_unit1'] for d in drops)
    # 103-bit labels, bit-packed (bytes only; queries recomputed with 103 lanes).
    m103 = metrics(moduli, label_bits=103)
    packed = 96 + 91 * 33 + 91 + ceildiv(2 * m103['blocks'] * 103, 8) + 642 * m103['record_bytes']
    out['label103_bitpacked'] = dict(bytes=packed, saved=base['bytes'] - packed,
                                     garble=m103['garble'], evaluate=m103['evaluate'])
    # Combination with a greedy width-9 schedule (Astra's admissibility rule, `codex/Scratch/check_width9.py`).
    combos = []
    for drop in [None] + [d['dropped'] for d in out['single_drops_fitting_unit2']]:
        rest = [x for x in moduli if x != drop]
        widths = greedy_width9(rest)
        met = metrics(rest, widths)
        combos.append(dict(dropped=drop, width9=sorted(widths), rows9=len(widths), **met,
                           saved=base['bytes'] - met['bytes'], evaluate_headroom=E_GATE - met['evaluate']))
    out['drop_plus_width9'] = combos
    print(json.dumps(out, indent=2))


def greedy_width9(moduli, margin=500):
    """Cheapest-evaluation-first width-9 substitutions within the evaluation gate minus `margin`."""
    base = metrics(moduli)['evaluate']
    candidates = []
    for m in moduli:
        if m == 256:
            continue
        a, b = odd_row(m, 8), odd_row(m, 9)
        if b['ell'] - 9 - 1 < 1 or 511 > max(255, m - 1, 2 ** (a['ell'] - 1) - 128):
            continue
        candidates.append((2 * (b['evaluate'] - a['evaluate']), m))
    selected, evaluation = {}, base
    for delta, m in sorted(candidates):
        if evaluation + delta + margin <= E_GATE:
            selected[m] = 9
            evaluation += delta
    return selected


if __name__ == '__main__':
    main()
