#!/usr/bin/env python3
"""Exact-integer cost experiment for a selective width-9 conversion schedule.

This reproduces the pinned source's three metrics before modeling a new schedule.
It does not certify Lean elaboration, privacy, program equivalence, or hosted acceptance.
Run from any directory: python3 Scratch/check_width9.py
"""
import json
import math
from pathlib import Path
import re

from check_fallback import check_reach_certificates

ROOT = Path(__file__).resolve().parents[1]


def ceildiv(a, b):
    return (a + b - 1) // b


def cast_answers(width):
    return ceildiv(ceildiv(104, 128 // width), 2)


def extraction(width, ring_width):
    leaves = 2 ** width
    answers = cast_answers(ring_width)
    return (leaves - 2 + leaves * answers,
            leaves - width - 1 + (leaves - 1) * answers)


def row(modulus, width):
    ell = (32 * (modulus - 1)).bit_length()
    width1 = ell - width - 1
    keep = max(width, ell - 5)
    if width1 < 1:
        return None
    g0, e0 = extraction(width, ell)
    g1, e1 = extraction(width1, ell - width)
    growth = 2 ** keep - 2 ** width
    return dict(modulus=modulus, ell=ell, w0=width, w1=width1, keep=keep,
                blocks=(ell - 1) + (ell - width - 1) + (width - 1) +
                       (width1 - 1) + (keep - width) + (ell - keep),
                garble=g0 + g1 + growth + (ell - keep) * modulus,
                evaluate=e0 + e1 + growth - (keep - width) + (ell - keep) * (modulus - 1))


def metrics(moduli, rows):
    chunk_g = sum(extraction(w, 14)[0] for w in [8] * 31 + [6])
    chunk_e = sum(extraction(w, 14)[1] for w in [8] * 31 + [6])
    blocks = 32 * 13 + sum(r['blocks'] for r in rows)
    coordinate_g, coordinate_e = [], []
    for count in [367, 275]:
        pads = [(m, ceildiv(count * 8, 256) if m == 256 else
                 ceildiv((m ** count).bit_length() + 120, 256)) for m in moduli]
        coordinate_g.append(chunk_g + sum(r['garble'] for r in rows) + sum(m*q for m, q in pads))
        coordinate_e.append(chunk_e + sum(r['evaluate'] for r in rows) + sum((m-1)*q for m, q in pads))
    return dict(ciphertext_bytes=96 + 91 * 33 + 91 + 2 * blocks * 13 + 642 * 78,
                garble_queries=sum(coordinate_g) + 2291,
                evaluate_queries=sum(coordinate_e) + 1783,
                conversion_labels_per_coordinate=blocks,
                coordinate_garble=coordinate_g, coordinate_evaluate=coordinate_e)


def main():
    interface = (ROOT / 'Construction/CRT/Interface.lean').read_text()
    match = re.search(r'def bn254Moduli.*?#\[(.*?)\]', interface, re.S)
    moduli = list(map(int, re.findall(r'\d+', match[1])))
    historical = json.loads((ROOT / 'Scratch/fallback_schedule.json').read_text())
    reach_count, reach_slack = check_reach_certificates(moduli, historical)
    baseline = metrics(moduli, [row(m, 8) for m in moduli if m != 256])
    assert (baseline['ciphertext_bytes'], baseline['garble_queries'], baseline['evaluate_queries']) == (
        130122, 988438, 981506)
    candidates = []
    for m in moduli:
        if m == 256:
            continue
        a, b = row(m, 8), row(m, 9)
        if b is None:
            continue
        need = max(255, m - 1, 2 ** (a['ell'] - 1) - 128)
        if 2 ** 9 - 1 > need:
            continue
        candidates.append(dict(modulus=m, garble_delta=2*(b['garble']-a['garble']),
                               evaluate_delta=2*(b['evaluate']-a['evaluate']),
                               bytes_saved=26*(a['blocks']-b['blocks'])))
    candidates.sort(key=lambda r: (r['evaluate_delta'], r['modulus']))
    selected = []
    evaluation = baseline['evaluate_queries']
    for candidate in candidates:
        if evaluation + candidate['evaluate_delta'] + 500 <= 1055879:
            selected.append(candidate['modulus'])
            evaluation += candidate['evaluate_delta']
    selected_rows = [row(m, 9 if m in selected else 8) for m in moduli if m != 256]
    for r in selected_rows:
        m, ell, w0, w1, keep = (r[k] for k in ['modulus', 'ell', 'w0', 'w1', 'keep'])
        assert 1 <= w0 and 1 <= w1 and w0 + w1 + 1 == ell
        assert w0 <= keep <= ell <= 14 and m <= 2 ** keep
        need = max(255, m-1, 2 ** (ell-1)-128)
        assert 2 ** w0 - 1 <= need
        assert 2 ** w0 * (2 ** w1 - 1) <= need
        assert all(2 ** level - 1 <= need for level in range(w0, keep))
        assert all(m <= 2 ** level for level in range(keep, ell))
    actual = metrics(moduli, selected_rows)
    assert actual['evaluate_queries'] == evaluation
    assert actual['garble_queries'] <= 1759967
    params = (ROOT / 'Construction/CRT/Params.lean').read_text()
    selector = re.search(r'def selectiveWidth0.*?\(\[(.*?)\]\s*: List Nat\)', params, re.S)
    assert selector, 'the implementation must declare the selected first-stage widths'
    implemented = list(map(int, re.findall(r'\d+', selector[1])))
    assert sorted(implemented) == sorted(selected)
    assert 'def bn254Table : CrtTable := selectiveTableOf bn254Moduli' in params
    assert 'CrtTable.ofModuli 254 8 14 moduli selectiveKind padSlack' in params
    label = (ROOT / 'Construction/CRT/Label.lean').read_text()
    assert 'abbrev labelBits : Nat := 104' in label
    result = dict(status='exact integer cost model; this script does not run Lean or hosted verification',
                  implementation_schedule_checked=True,
                  baseline=baseline, record_product_bits=math.prod(moduli).bit_length(),
                  unchanged_reach_certificates_checked=reach_count,
                  reach_certificate_min_slack=reach_slack,
                  width9_candidate=dict(selected_moduli=sorted(selected), rows=len(selected),
                                        **actual, evaluate_headroom=1055879-evaluation),
                  ranked_row_deltas=candidates)
    output = ROOT / 'evidence/width9-cost-model.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'ranked_row_deltas'}, indent=2))


if __name__ == '__main__':
    main()
