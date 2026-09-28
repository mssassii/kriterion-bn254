#!/usr/bin/env python3
"""Opus H1 static checker: the 84-modulus table (modulus 17 dropped) and the two-unit budget closure.

Independent of Lean. It re-derives, from the source's own moduli array, every literal the H1 patch changed and
compares it with the source text; replays `Reach.rows_ok` on the new table; checks that the certificate list is
the pinned list with exactly modulus 17's entry removed; regenerates `BudgetData.lean` and requires byte equality;
and evaluates the whole-chain constant (smudge and hidden window both counted) against two units.
Passing this is a necessary condition, not a Lean proof.  Run: python3 Scratch/opus_check_h1.py
"""
from fractions import Fraction
import math
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import opus_budget_model as model  # noqa: E402
import opus_gen_budget as gen  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PIN = 'e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05'


def read(path):
    return (ROOT / path).read_text()


def pinned(path):
    return subprocess.run(['git', '-C', str(ROOT), 'show', f'{PIN}:{path}'], capture_output=True, text=True,
                          check=True).stdout


def ints(text):
    return list(map(int, re.findall(r'\d+', text)))


def certs_of(source):
    return ints(re.search(r'def certs : List ℕ :=\s*\[(.*?)\]', source, re.S)[1])


def replay_certs(moduli, certs):
    slacks = []
    for m, packed in zip(moduli, certs):
        if m == 256:
            continue
        bound = min(m, 256) - 1
        for j in range(31):
            a = packed // 256 ** j % 256
            n = j + 1
            term = a * pow(2, 8 * n, m) % m
            assert a < (48 if n == 31 else 256) and term <= bound + 1, (m, n)
            bound += term
        ell = (32 * (m - 1)).bit_length()
        need = max(255, m - 1, 2 ** (ell - 1) - 128)
        assert need <= bound, (m, need, bound)
        slacks.append(bound - need)
    return len(slacks), min(slacks)


def expect(path, pattern, value):
    match = re.search(pattern, read(path))
    assert match, (path, pattern)
    assert int(match[1]) == value, (path, pattern, match[1], value)


def main():
    moduli = ints(re.search(r'def bn254Moduli.*?#\[(.*?)\]', read('Construction/CRT/Interface.lean'), re.S)[1])
    base = ints(re.search(r'def bn254Moduli.*?#\[(.*?)\]', pinned('Construction/CRT/Interface.lean'), re.S)[1])
    assert base[0] == 17 and moduli == base[1:], 'the table must be the pinned table without 17'
    count, M = len(moduli), math.prod(moduli)
    assert count == 84 and all(math.gcd(a, b) == 1 for i, a in enumerate(moduli) for b in moduli[i + 1:])
    assert moduli.index(256) == 52 and min(moduli) >= 17 and max(moduli) <= 439
    B = (model.P - 1) ** 2 + 1
    assert 2 * B <= M + 1 and 2 * M <= 256 ** 78, 'wrap exactness and 78-byte records'

    # Reach certificates: the pinned list minus modulus 17's entry, and rows_ok holds on the new table.
    new_certs, old_certs = certs_of(read('Proof/Privacy/CRT/Hidden/Reach.lean')), certs_of(
        pinned('Proof/Privacy/CRT/Hidden/Reach.lean'))
    assert len(old_certs) == 85 and new_certs == old_certs[1:]
    rows, slack = replay_certs(moduli, new_certs)
    assert rows == 83

    # Metrics and counts.
    met = model.metrics(moduli)
    assert (met['bytes'], met['garble'], met['evaluate'], met['blocks']) == (129628, 985094, 978204, 2937)
    expect('Construction/CRT/Public.lean', r'def ciphertextBytes : Nat := (\d+)', met['bytes'])
    expect('Construction/CRT/Public.lean', r'abbrev convCount : Nat := (\d+)', met['blocks'])
    assert 96 + 91 * 33 + 91 + 2 * met['blocks'] * 13 + 642 * 78 == met['bytes']
    budgets = {}
    for name, s in (('x', 367), ('y', 275)):
        rows_ = [model.odd_row(m) for m in moduli if m != 256]
        chunk_g = sum(model.extract(w, 14)[0] for w in [8] * 31 + [6])
        chunk_e = sum(model.extract(w, 14)[1] for w in [8] * 31 + [6])
        budgets['g' + name] = chunk_g + sum(r['garble'] for r in rows_) + sum(m * model.pad_q(m, s) for m in moduli)
        budgets['e' + name] = chunk_e + sum(r['evaluate'] for r in rows_) + sum(
            (m - 1) * model.pad_q(m, s) for m in moduli)
    for lean, key in (('coordGarbleBudget_x', 'gx'), ('coordGarbleBudget_y', 'gy'), ('coordEvalBudget_x', 'ex'),
                      ('coordEvalBudget_y', 'ey')):
        expect('Construction/CRT/BudgetFacts.lean', lean + r' : [^=]*= (\d+)', budgets[key])
    expect('Construction/CRT/BudgetFacts.lean', r'garbleBudget_eq : garbleBudget = (\d+)', met['garble'])
    expect('Construction/CRT/BudgetFacts.lean', r'evaluateBudget_eq : evaluateBudget = (\d+)', met['evaluate'])
    assert budgets['gx'] + budgets['gy'] + 1 + 1092 + 1198 == met['garble']
    assert budgets['ex'] + budgets['ey'] + 1 + 1092 + 690 == met['evaluate']

    odd = [m for m in moduli if m != 256]
    joins = 222 + sum(7 + ((32 * (m - 1)).bit_length() - 10) + (max(8, (32 * (m - 1)).bit_length() - 5) - 8)
                      + ((32 * (m - 1)).bit_length() - max(8, (32 * (m - 1)).bit_length() - 5)) for m in odd)
    pins = 32 + 2 * len(odd)
    published_joins = joins - 222
    pieces = 3 + 182 + 182 + 642 + 2 * published_joins + 2 * pins * 104
    assert (joins, pins, pieces) == (1441, 198, 44631)
    pin_labels = 32 * 13 + sum(2 * (32 * (m - 1)).bit_length() - 10 for m in odd)  # (ell - 1) + (ell - 9)
    assert (published_joins, pin_labels, published_joins + pin_labels) == (1219, 1718, met['blocks'])
    expect('Proof/Simulator/CRT/Stage1Stored.lean', r'joinCount_eq : joinCount = (\d+)', joins)
    expect('Proof/Simulator/CRT/Stage1Stored.lean', r'pinCount_eq : pinCount = (\d+)', pins)
    expect('Proof/Simulator/CRT/Stage1Conv.lean', r'pinCount_eq : pinCount = (\d+)', pins)
    expect('Proof/Simulator/CRT/Stage1Conv.lean', r'∀ k : Fin (\d+), pinWidthAt k', pins)
    expect('Proof/Simulator/CRT/Stage1Size.lean', r'pieces_length : pieces.length = (\d+)', pieces)
    expect('Construction/Simulator/CRT/Stage1.lean', r'def moduliCount : Nat := (\d+)', count)
    expect('Proof/Correctness/CRT/Record.lean', r'bn254Table.product = (\d+)', M)

    # No stale modulus count remains in the table-dependent sources.
    stale = []
    for path in list((ROOT / 'Proof').rglob('*.lean')) + list((ROOT / 'Construction').rglob('*.lean')):
        text = path.read_text()
        for pattern in (r'Fin 85\b', r'< 85\b', r'= 85\b', r'range 85\b', r'\bcnt85\b', r'= 1450\b', r'= 200 :=',
                        r'Fin 200\b', r'45065'):
            if re.search(pattern, text):
                stale.append((str(path.relative_to(ROOT)), pattern))
    assert not stale, stale

    # Budget data: byte-identical to the generator, and the whole-chain constant under two units.
    assert read('Proof/Privacy/CRT/Glue/BudgetData.lean') == gen.generate(moduli, two_unit=True)
    units = sum(model.constant_error(moduli).values())
    assert units < 2
    budget = read('Proof/Privacy/CRT/Glue/Budget.lean')
    assert '(first : ℝ) + (second : ℝ) + 2 := by' in budget and '* 2 ^ 100 * 10 ≤ 7 * BudgetData.M' in budget
    shapes = read('Proof/Privacy/CRT/Glue/Shapes.lean')
    assert 'adversaryMachine.firstFuel + adversaryMachine.secondFuel + 2 ≤ adversaryMachine.steps + 1' in shapes
    smudge = Fraction(1284 * (model.P - 1) ** 2 + 273 * model.P, M) * 2 ** 100
    assert smudge <= Fraction(7, 10)
    linear_constant = 2 * Fraction(7, 10) + Fraction(8, 1000)
    assert linear_constant <= 2

    print(f'H1 static check passed: {count} moduli, log2 M = {math.log2(M):.3f}, '
          f'{rows} certificates (min slack {slack}), {met["bytes"]} B / {met["garble"]} / {met["evaluate"]}, '
          f'constant {float(units):.4f} units (bound used in Lean: 1.408), smudge share {float(smudge):.4f}')


if __name__ == '__main__':
    main()
