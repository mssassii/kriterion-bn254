#!/usr/bin/env python3
"""Independent arithmetic checks for H1 plus the selected width-9 schedule.

Reproduces the pinned baseline and both individual candidates before deriving the
combined schedule. This script does not run Lean or hosted verification.
"""
import json
import math
from pathlib import Path
import re
import subprocess
from fractions import Fraction

from check_width9 import ceildiv, metrics, row
import opus_gen_budget as budget

ROOT = Path(__file__).resolve().parents[1]
BASE = 'e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05'


def original(path):
    return subprocess.check_output(['git', '-C', str(ROOT), 'show', f'{BASE}:{path}'], text=True)


def moduli_in(source):
    return list(map(int, re.findall(r'\d+', re.search(r'def bn254Moduli.*?#\[(.*?)\]', source, re.S)[1])))


def certs_in(source):
    return list(map(int, re.findall(r'\d+', re.search(r'def certs : List ℕ :=\s*\[(.*?)\]', source, re.S)[1])))


def main():
    baseline_moduli = moduli_in(original('Construction/CRT/Interface.lean'))
    moduli = moduli_in((ROOT / 'Construction/CRT/Interface.lean').read_text())
    assert moduli == baseline_moduli[1:] and baseline_moduli[0] == 17
    assert len(moduli) == 84
    baseline = metrics(baseline_moduli, [row(m, 8) for m in baseline_moduli if m != 256])
    assert [baseline[k] for k in ['ciphertext_bytes', 'garble_queries', 'evaluate_queries']] == [130122, 988438, 981506]
    a1_data = json.loads((ROOT / 'evidence/width9-cost-model.json').read_text())['width9_candidate']
    a1 = metrics(baseline_moduli, [row(m, 9 if m in a1_data['selected_moduli'] else 8)
                                 for m in baseline_moduli if m != 256])
    assert [a1[k] for k in ['ciphertext_bytes', 'garble_queries', 'evaluate_queries']] == [128822, 1062022, 1055144]
    h1 = metrics(moduli, [row(m, 8) for m in moduli if m != 256])
    assert [h1[k] for k in ['ciphertext_bytes', 'garble_queries', 'evaluate_queries']] == [129628, 985094, 978204]

    ranked = []
    for m in moduli:
        if m == 256:
            continue
        old, new = row(m, 8), row(m, 9)
        if new is None or 511 > max(255, m - 1, 2 ** (new['ell'] - 1) - 128):
            continue
        ranked.append(dict(modulus=m, evaluate_delta=2*(new['evaluate']-old['evaluate']),
                           garble_delta=2*(new['garble']-old['garble']),
                           bytes_saved=26*(old['blocks']-new['blocks'])))
    ranked.sort(key=lambda value: (value['evaluate_delta'], value['modulus']))
    assert all(value['bytes_saved'] == 52 and value['evaluate_delta'] > 0 for value in ranked)
    # Equal byte savings make sorting by evaluation cost optimal in this restricted
    # width-8/9 family. The garbling gate is checked on the resulting schedule.
    selected, evaluation = [], h1['evaluate_queries']
    for value in ranked:
        if evaluation + value['evaluate_delta'] <= 1055879:
            selected.append(value['modulus'])
            evaluation += value['evaluate_delta']
    selected.sort()
    assert selected == a1_data['selected_moduli'] + [397]
    assert len(selected) == 26
    cheapest27 = h1['evaluate_queries'] + sum(value['evaluate_delta'] for value in ranked[:27])
    assert cheapest27 > 1055879
    params = (ROOT / 'Construction/CRT/Params.lean').read_text()
    actual_selector = list(map(int, re.findall(r'\d+', re.search(
        r'def selectiveWidth0.*?\(\[(.*?)\]\s*: List Nat\)', params, re.S)[1])))
    assert actual_selector == selected
    assert 'def bn254Table : CrtTable := selectiveTableOf bn254Moduli' in params
    assert 'CrtTable.ofModuli 254 8 14 moduli selectiveKind padSlack' in params

    rows = [row(m, 9 if m in selected else 8) for m in moduli if m != 256]
    candidate = metrics(moduli, rows)
    assert candidate['evaluate_queries'] == evaluation
    assert candidate['garble_queries'] <= 1759967
    reach = (ROOT / 'Proof/Privacy/CRT/Hidden/Reach.lean').read_text()
    base_reach = original('Proof/Privacy/CRT/Hidden/Reach.lean')
    assert reach[reach.index('def chunkBound'):reach.index('def certs')] == \
        base_reach[base_reach.index('def chunkBound'):base_reach.index('def certs')]
    certs = certs_in(reach)
    assert certs == certs_in(base_reach)[1:]
    assert len(certs) == len(moduli)
    slacks = []
    for m, packed in zip(moduli, certs):
        if m == 256:
            continue
        r = row(m, 9 if m in selected else 8)
        ell, w0, w1, keep = (r[key] for key in ['ell', 'w0', 'w1', 'keep'])
        assert 1 <= w0 and 1 <= w1 and w0 + w1 + 1 == ell
        assert w0 <= keep <= min(ell, 9) and ell <= 14 and m <= 2 ** keep
        need = max(255, m - 1, 2 ** (ell - 1) - 128)
        assert 2 ** w0 - 1 <= need and 2 ** w0 * (2 ** w1 - 1) <= need
        bound = min(m, 256) - 1
        for n in range(1, 32):
            digit = packed // 256 ** (n - 1) % 256
            term = digit * pow(2, 8*n, m) % m
            assert digit < (48 if n == 31 else 256) and term <= bound + 1
            bound += term
        assert need <= bound
        slacks.append(bound - need)

    pins = 32 + 2 * len(rows)
    pin_labels = 32 * 13 + sum((r['ell']-1) + (r['ell']-r['w0']-1) for r in rows)
    mod_joins = sum((r['w0']-1) + (r['w1']-1) + (r['keep']-r['w0']) + (r['ell']-r['keep']) for r in rows)
    assert pin_labels + mod_joins == candidate['conversion_labels_per_coordinate']
    counts = dict(pins_per_coordinate=pins, pin_labels_per_coordinate=pin_labels,
                  modulus_joins_per_coordinate=mod_joins, all_joins_per_coordinate=222+mod_joins,
                  serialized_pieces=1009+2*mod_joins+2*pins*104)

    assert budget.generate(baseline_moduli, False) == original('Proof/Privacy/CRT/Glue/BudgetData.lean')
    assert budget.generate(moduli, True) == (ROOT / 'Proof/Privacy/CRT/Glue/BudgetData.lean').read_text()
    p, scalar, product = budget.P, budget.R, math.prod(moduli)
    pad = sum((Fraction(m*m**count, 2**(256*ceildiv((m**count).bit_length()+120, 256)))
               for m in moduli if m != 256 for count in [367, 275]), Fraction())
    swap = pad + 637*Fraction(2**384 % p, 2**384)
    smudge = Fraction(1284*(p-1)**2+273*p, product)
    constant = 3*swap + 2*smudge + Fraction(1759967, p) + Fraction(546+455, scalar-1) + Fraction(186, 2**128)
    assert constant*2**100 <= 2 and smudge*2**100 <= Fraction(7, 10)
    assert 2*((p-1)**2+1) <= product+1 and 2*product <= 256**78
    result = dict(status='exact integer/rational model; Lean and hosted verification are separate',
                  baseline=baseline, a1=a1, h1=h1, combined=candidate, selected_moduli=selected,
                  evaluate_headroom=1055879-evaluation, cheapest_27_evaluate=cheapest27,
                  counts=counts, reach_certificates_checked=len(slacks), min_reach_slack=min(slacks),
                  constant_units_approx=float(constant*2**100), product_bits=product.bit_length(),
                  ranked_width9_deltas=ranked)
    (ROOT / 'evidence/combined-width9-h1/cost-model.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'ranked_width9_deltas'}, indent=2))


if __name__ == '__main__':
    main()
