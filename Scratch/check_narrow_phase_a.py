#!/usr/bin/env python3
"""Independent Phase-A cost cross-check; source reading and exact integer math.

Keep check_fallback.py and its JSON as the historical 128-bit snapshot.  This
script checks the retained fallback selector, then calculates the current
all-width-8, 104-lane variant.
The arithmetic model is not a proof of Lean execution or of perfect correctness.
"""
from collections import Counter
import json
import math
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LABEL_BITS = 104
RAW_BITS = 128


def read(path):
    return (ROOT / path).read_text()


def ceildiv(a, b):
    return (a + b - 1) // b


def cast_answers(width):
    # Each raw answer has two raw blocks. Lanes do not straddle their boundary.
    lanes_per_block = RAW_BITS // width
    blocks = ceildiv(LABEL_BITS, lanes_per_block)
    return ceildiv(blocks, 2)


def extract(width, ring_width):
    leaves = 1 << width
    answers = cast_answers(ring_width)
    return (leaves - 2 + leaves * answers,
            leaves - width - 1 + (leaves - 1) * answers)


def check_number(path, name, expected):
    source = read(path)
    pattern = (r'(?:def|abbrev|theorem)\s+' + re.escape(name)
               + r'\b[^\n]*?(?:=|:=)\s*(\d+)\b')
    match = re.search(pattern, source)
    assert match, f'missing numeric declaration: {path}:{name}'
    assert int(match[1]) == expected, (path, name, match[1], expected)


def main():
    params = read('Construction/CRT/Params.lean')
    interface = read('Construction/CRT/Interface.lean')
    moduli_match = re.search(r'def bn254Moduli.*?#\[(.*?)\]', interface, re.S)
    assert moduli_match
    moduli = list(map(int, re.findall(r'\d+', moduli_match[1])))
    selector = re.search(r'def fallbackWidth0.*?\(\[(.*?)\]\s*: List Nat\)', params, re.S)
    assert selector
    width7 = set(map(int, re.findall(r'\d+', selector[1])))
    reference = json.loads(read('Scratch/fallback_schedule.json'))
    assert width7 == {row['modulus'] for row in reference if row['w0'] == 7}
    assert [row['modulus'] for row in reference] == [m for m in moduli if m != 256]
    assert re.search(r'def bn254Table\s*: CrtTable := width8TableOf bn254Moduli', params)
    assert 'width1 := ell - width0 - 1, keep := max width0 (ell - 5)' in params
    assert Counter(row['w0'] for row in reference) == {8: 67, 7: 17}
    assert re.search(r'def width8Row.*?\{ ell, width0 := 8, width1 := ell - 8 - 1, keep := max 8 \(ell - 5\) \}', params, re.S)

    row_g = row_e = row_pins = row_joins = 0
    for record in reference:
        m = record['modulus']
        ell = (32 * (m - 1)).bit_length()
        w0 = 8
        w1 = ell - w0 - 1
        keep = max(w0, ell - 5)
        # The real schedule preserves ell while using width 8 for every odd row.
        assert record['ell'] == ell, (m, ell)
        assert 7 <= w0 <= 8 and 1 <= w1 and w0 + w1 + 1 == ell
        assert w0 <= keep <= ell <= 14 and m <= 2**keep
        g0, e0 = extract(w0, ell)
        g1, e1 = extract(w1, ell - w0)
        growth_g = 2**keep - 2**w0
        growth_e = growth_g - (keep - w0)
        row_g += g0 + g1 + growth_g + (ell - keep) * m
        row_e += e0 + e1 + growth_e + (ell - keep) * (m - 1)
        row_pins += ell + ell - w0
        row_joins += w0 - 1 + w1 - 1 + keep - w0 + ell - keep

    chunks = [8] * 31 + [6]
    chunk_g = sum(extract(width, 14)[0] for width in chunks)
    chunk_e = sum(extract(width, 14)[1] for width in chunks)
    pins = 32 * 14 + row_pins
    joins = sum(width - 1 for width in chunks) + row_joins
    blocks = pins + joins
    coord_g, coord_e = [], []
    for count in (367, 275):
        body_g = body_e = 0
        for m in moduli:
            answers = (ceildiv(count * 8, 256) if m == 256 else
                       ceildiv((m**count).bit_length() + 120, 256))
            body_g += m * answers
            body_e += (m - 1) * answers
        coord_g.append(chunk_g + row_g + body_g)
        coord_e.append(chunk_e + row_e + body_e)
    garble = sum(coord_g) + 1 + 1092 + 1198
    evaluate = sum(coord_e) + 1 + 1092 + 690
    record_bytes = ceildiv((2 * math.prod(moduli) - 1).bit_length(), 8)
    ciphertext = 96 + 91 * 96 + 91 * 1 + 2 * blocks * (LABEL_BITS // 8) + 642 * record_bytes
    assert (blocks, joins, pins, record_bytes) == (3378, 1450, 1928, 78)
    assert coord_g == [518727, 467420]
    assert coord_e == [515402, 464321]
    assert (ciphertext, garble, evaluate) == (146827, 988438, 981506)
    assert garble + 500 <= 1759967 and evaluate + 500 <= 1055879

    for name, value in [('convCount', blocks), ('ciphertextBytes', ciphertext)]:
        check_number('Construction/CRT/Public.lean', name, value)
    for name, value in [('coordGarbleBudget_x', coord_g[0]), ('coordGarbleBudget_y', coord_g[1]),
                        ('coordEvalBudget_x', coord_e[0]), ('coordEvalBudget_y', coord_e[1]),
                        ('garbleBudget_eq', garble), ('evaluateBudget_eq', evaluate)]:
        check_number('Construction/CRT/BudgetFacts.lean', name, value)
    check_number('Construction/CRT/Label.lean', 'labelBits', LABEL_BITS)
    public = read('Construction/CRT/Public.lean')
    assert 'crtX : Vector Label convCount' in public
    assert 'crtY : Vector Label convCount' in public
    assert public.count('Narrow.labelEncoding.vector convCount') == 2
    print(json.dumps(dict(status='independent integer model passed', label_bits=LABEL_BITS,
        raw_answer_block_bits=RAW_BITS, width8_rows=84, width7_rows=0,
        conversion_labels=blocks, joins=joins, pins=pins, record_bytes=record_bytes,
        ciphertext_bytes=ciphertext, coordinate_garble=coord_g, coordinate_evaluate=coord_e,
        garble_queries=garble, evaluate_queries=evaluate,
        garble_headroom=1759967-garble, evaluate_headroom=1055879-evaluate,
        conversion_garble_per_coordinate=chunk_g+row_g,
        conversion_evaluate_per_coordinate=chunk_e+row_e), indent=2))


if __name__ == '__main__':
    main()
