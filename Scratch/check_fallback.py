#!/usr/bin/env python3
"""Static fallback audit. Uses integer arithmetic and source reading, never Lean.

Run from any directory: python3 Scratch/check_fallback.py
The JSON is the unchanged Round-2 reference schedule. This checks it against the
Lean selector, recomputes costs from the generic tree/cast/growth/fold formulas,
and compares the resulting totals with all changed numeric declarations.
It does not certify Lean elaboration, kernel checking, or executable equivalence.
"""
from collections import Counter
import json
import math
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return (ROOT / path).read_text()


def ceildiv(a, b):
    return (a + b - 1) // b


def integer_list(text):
    return list(map(int, re.findall(r"\d+", text)))


def cast_answers(width):
    # Raw answer blocks and conversion labels are both 128 bits in this patch.
    return ceildiv(ceildiv(128, 128 // width), 2)


def extraction(width, ring_width):
    # Evaluation omits the hot cast and one tree material per noninitial level.
    leaves = 2**width
    queries = cast_answers(ring_width)
    return (leaves - 2 + leaves * queries,
            leaves - width - 1 + (leaves - 1) * queries)


def check_number(path, name, expected):
    source = read(path)
    pattern = (r"(?:def|abbrev|theorem)\s+" + re.escape(name)
               + r"\b[^\n]*?(?:=|:=)\s*(\d+)\b")
    match = re.search(pattern, source)
    assert match, f"missing numeric declaration {path}:{name}"
    assert int(match[1]) == expected, (path, name, match[1], expected)


def check_reach_certificates(moduli, reference):
    """Replay Reach.rows_ok, including each run branch and the final need test.

    This mirrors the Lean definitions literally: unpack 31 little-endian bytes,
    run at n=1 and B=min(m,256)-1, and skip only the implication's m=256 case.
    It does not search for replacement certificates or approximate reachability.
    """
    source = read('Proof/Privacy/CRT/Hidden/Reach.lean')
    compact = ' '.join(source.split())
    # Fail if a definition changes without updating its Python transcription.
    for definition in (
        'def chunkBound (c : ℕ) : ℕ := if c = 31 then 48 else 256',
        'def unpack (packed : ℕ) : List ℕ := '
        '(List.range 31).map fun j => packed / 256 ^ j % 256',
        '| [], _, B => some B',
        'if a < chunkBound n ∧ a * 2 ^ (8 * n) % m ≤ B + 1 then '
        'run m rest (n + 1) (B + a * 2 ^ (8 * n) % m) else none',
        'def need (m ell : ℕ) : ℕ := max 255 (max (m - 1) (2 ^ (ell - 1) - 128))',
        'match run m (unpack packed) 1 (min m 256 - 1) with '
        '| some B => decide (need m (t9Row 32 m).ell ≤ B) | none => false',
        'rowOK (bn254Table.modulus i) (certs.getD i.val 0) = true',
    ):
        assert definition in compact, f'Reach definition changed: {definition}'
    match = re.search(r'def certs : List ℕ :=\s*\[(.*?)\]', source, re.S)
    assert match, 'Reach.certs missing'
    certs = integer_list(match[1])
    assert len(certs) == len(moduli) == 85
    rows = {row['modulus']: row for row in reference}
    slacks = []
    for index, m in enumerate(moduli):
        if m == 256:
            continue  # rows_ok assumes m != 256; its certificate is unused.
        packed = certs[index]
        bound = min(m, 256) - 1
        for j in range(31):
            a = packed // 256**j % 256
            n = j + 1
            term = a * pow(2, 8*n, m) % m
            assert a < (48 if n == 31 else 256), (m, n, 'chunkBound', a)
            assert term <= bound + 1, (m, n, 'run gap', term, bound)
            bound += term
        # t9Row.ell and fallbackRow.ell coincide. The argument is positive,
        # so Python bit_length equals Lean Nat.log2(value)+1 here.
        assert 32*(m-1) > 0
        ell = (32*(m-1)).bit_length()
        assert ell == rows[m]['ell']
        need = max(255, m-1, 2**(ell-1)-128)
        assert need <= bound, (m, 'rowOK', need, bound)
        slacks.append(bound-need)
    assert len(slacks) == 84 and min(slacks) == 112
    return len(slacks), min(slacks)


def main():
    reference = json.loads(read('Scratch/fallback_schedule.json'))
    interface = read('Construction/CRT/Interface.lean')
    params = read('Construction/CRT/Params.lean')
    moduli = integer_list(re.search(r'def bn254Moduli.*?#\[(.*?)\]', interface, re.S)[1])
    selector = re.search(r'def fallbackWidth0.*?\(\[(.*?)\]\s*: List Nat\)', params, re.S)
    assert selector, 'explicit width-7 selector missing'
    width7 = integer_list(selector[1])
    assert len(width7) == len(set(width7)) == 17
    assert set(width7) == {row['modulus'] for row in reference if row['w0'] == 7}
    assert [row['modulus'] for row in reference] == [m for m in moduli if m != 256]
    assert re.search(r'def bn254Table\s*: CrtTable := fallbackTableOf bn254Moduli', params)
    assert re.search(r'def reducedTable\s*: CrtTable := bn254TableOf', params)
    assert 'width1 := ell - width0 - 1, keep := max width0 (ell - 5)' in params
    assert Counter(row['w0'] for row in reference) == {8: 67, 7: 17}
    reach_rows, reach_min_slack = check_reach_certificates(moduli, reference)

    row_g = row_e = row_pins = row_joins = 0
    for record in reference:
        m = record['modulus']
        ell = (32 * (m - 1)).bit_length()
        w0 = 7 if m in width7 else 8
        w1 = ell - w0 - 1
        keep = max(w0, ell - 5)
        assert keep == max(w0, (m - 1).bit_length())
        assert 7 <= w0 <= 8 and 1 <= w1 and w0 + w1 + 1 == ell
        assert w0 <= keep <= ell <= 14 and m <= 2**keep
        assert 32 * (m - 1) < 2**ell
        g0, e0 = extraction(w0, ell)
        g1, e1 = extraction(w1, ell-w0)
        grow_g = 2**keep - 2**w0
        grow_e = grow_g - (keep-w0)
        g = g0 + g1 + grow_g + (ell-keep)*m
        e = e0 + e1 + grow_e + (ell-keep)*(m-1)
        pins = ell + ell-w0
        joins = (w0-1) + (w1-1) + (keep-w0) + (ell-keep)
        actual = dict(modulus=m, ell=ell, w0=w0, w1=w1, keep=keep,
                      blocks=pins+joins, evaluate=e, garble=g)
        assert actual == record, (record, actual)
        # Extremal targets suffice for each monotone slot bound in reach_mod.
        need = max(255, m-1, 2**(ell-1)-128)
        assert 2**w0-1 <= need
        assert 2**w0*(2**w1-1) <= 2**(ell-1)-128 <= need
        assert keep <= 9
        assert all(2**level-1 <= need for level in range(w0, keep))
        assert all(m <= 2**level for level in range(keep, ell))
        row_g += g
        row_e += e
        row_pins += pins
        row_joins += joins

    chunks = [8]*31 + [6]
    chunk_g = sum(extraction(width, 14)[0] for width in chunks)
    chunk_e = sum(extraction(width, 14)[1] for width in chunks)
    pins = 32*14 + row_pins
    joins = sum(width-1 for width in chunks) + row_joins
    blocks = pins+joins
    coord_g, coord_e = [], []
    for count in (367, 275):
        body_g = body_e = 0
        for m in moduli:
            answers = (ceildiv(count*8, 256) if m == 256 else
                       ceildiv((m**count).bit_length()+120, 256))
            body_g += m*answers
            body_e += (m-1)*answers
        coord_g.append(chunk_g+row_g+body_g)
        coord_e.append(chunk_e+row_e+body_e)
    garble = sum(coord_g)+1+1092+1198
    evaluate = sum(coord_e)+1+1092+690
    record_bytes = ceildiv((2*math.prod(moduli)-1).bit_length(), 8)
    ciphertext = 96+91*96+91*12+2*blocks*16+642*record_bytes
    pieces = 2010+2*joins+400*128
    assert (blocks, joins, pins, pieces) == (3412, 1467, 1945, 56144)
    assert (ciphertext, garble, evaluate) == (169184, 1062038, 1054570)
    assert garble+500 <= 1759967 and evaluate+500 <= 1055879

    for name, expected in [('convCount', blocks), ('ciphertextBytes', ciphertext)]:
        check_number('Construction/CRT/Public.lean', name, expected)
    for name, expected in [('coordGarbleBudget_x',coord_g[0]), ('coordGarbleBudget_y',coord_g[1]),
                           ('coordEvalBudget_x',coord_e[0]), ('coordEvalBudget_y',coord_e[1]),
                           ('garbleBudget_eq',garble), ('evaluateBudget_eq',evaluate)]:
        check_number('Construction/CRT/BudgetFacts.lean', name, expected)
    check_number('Proof/Simulator/CRT/Stage1Stored.lean', 'joinCount_eq', joins)
    check_number('Proof/Simulator/CRT/Stage1Size.lean', 'pieces_length', pieces)
    for name, expected in [('expectedBytes',ciphertext), ('expectedGarble',garble),
                           ('expectedEvaluate',evaluate)]:
        check_number('Scratch/Audit.lean', name, expected)
    for path in ('Proof/Privacy/CRT/Glue/Budget.lean','Proof/Privacy/CRT/Glue/BudgetData.lean'):
        text = read(path)
        assert '945076' not in text
        assert '1759967' in text
    p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
    assert 1759967*2**100*1000 <= p
    print(json.dumps(dict(status='static arithmetic checks passed; Lean not run',
        width8_rows=67, width7_rows=17, conversion_blocks=blocks, joins=joins,pins=pins,
        serialized_pieces=pieces, record_bytes=record_bytes, ciphertext_bytes=ciphertext,
        garble_queries=garble,evaluate_queries=evaluate, evaluate_headroom=1055879-evaluate,
        coordinate_garble=coord_g, coordinate_evaluate=coord_e,
        reach_certificates_checked=reach_rows, reach_certificate_min_slack=reach_min_slack,
        conversion_garble_per_coordinate=chunk_g+row_g,
        conversion_evaluate_per_coordinate=chunk_e+row_e),indent=2))


if __name__ == '__main__':
    main()
