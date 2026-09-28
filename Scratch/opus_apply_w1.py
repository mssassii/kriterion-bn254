#!/usr/bin/env python3
"""Opus W1: apply the table-dependent literals (record width 618, limb 4 of 106 bits, 2,881 blocks, 1,413 joins,
43,387 pieces, the budgets and the product) with exact, count-checked replacements. Idempotence is not attempted:
run once on the 857e88b sources. Run: python3 Scratch/opus_apply_w1.py
"""
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'Scratch'))
import opus_budget_model as m  # noqa: E402

M = math.prod(m.moduli_from_source())
assert 41 not in m.moduli_from_source() and 17 in m.moduli_from_source() and 2 * M <= 2 ** 618


def sub(path, old, new, count):
    p = ROOT / path
    text = p.read_text()
    found = text.count(old)
    assert found == count, (path, old, found, count)
    p.write_text(text.replace(old, new))


def subre(path, pattern, new, count):
    p = ROOT / path
    text = p.read_text()
    out, found = re.subn(pattern, new, text)
    assert found == count, (path, pattern, found, count)
    p.write_text(out)


# Record width 620 -> 618 (limb 4: 108 -> 106).
sub('Construction/CRT/Public.lean', '620', '618', 3)
sub('Construction/CRT/Public.lean', 'abbrev convCount : Nat := 2885', 'abbrev convCount : Nat := 2881', 1)
sub('Construction/CRT/Entry.lean', '620', '618', 2)
sub('Construction/Simulator/CRT/Stage1.lean', '620', '618', 5)
sub('Construction/Simulator/CRT/Stage1.lean', 'limb 4 (108 bits)', 'limb 4 (106 bits)', 1)
sub('Construction/Simulator/CRT/Stage1.lean', 'emitWord (recordLimb 4) 108', 'emitWord (recordLimb 4) 106', 1)
sub('Proof/Correctness/CRT/EntryDelivery.lean', '2 ^ 620', '2 ^ 618', 1)
sub('Proof/Correctness/CRT/Record.lean', '2 ^ 620', '2 ^ 618', 3)
subre('Proof/Correctness/CRT/Record.lean', r'bn254Table\.product = \d+', f'bn254Table.product = {M}', 1)
sub('Proof/Correctness/CRT/Record.lean', 'as a literal (619 bits)', f'as a literal ({M.bit_length()} bits)', 1)
sub('Proof/Correctness/CRT/SourceReads.lean', '2 ^ 620', '2 ^ 618', 2)
sub('Proof/Privacy/CRT/Core/BmrIdealOff.lean', '2 ^ 620', '2 ^ 618', 2)
sub('Proof/Simulator/CRT/Stage1Pieces.lean', '620', '618', 7)
sub('Proof/Simulator/CRT/Stage1Record.lean', '620', '618', 11)
sub('Proof/Simulator/CRT/Stage1Record.lean', '108', '106', 6)
sub('Proof/Simulator/CRT/Stage1Conv.lean', 'lsbs 620', 'lsbs 618', 1)
sub('Proof/Simulator/CRT/Stage1Conv.lean', '`2885`', '`2881`', 1)
sub('Proof/Simulator/CRT/Stage1Size.lean', '(2 + 3 * 108)', '(2 + 3 * 106)', 1)
sub('Proof/Simulator/CRT/Stage1Size.lean', '43391', '43387', 3)
sub('Proof/Simulator/CRT/Stage1Stored.lean', 'joinCount = 1415', 'joinCount = 1413', 1)
sub('Proof/Privacy/CRT/Core/ConvFlat.lean', '2885', '2881', 1)

# Budgets (independent expectations: evidence/w1-model.log).
bf = 'Construction/CRT/BudgetFacts.lean'
for old, new in (('555302', '554955'), ('504029', '503730'), ('552027', '551685'), ('500978', '500684'),
                 ('1061622', '1060976'), ('1,061,622', '1,060,976'), ('1054788', '1054152'),
                 ('1,054,788', '1,054,152'), ('2,885 blocks', '2,881 blocks')):
    sub(bf, old, new, 1)
print('applied; product bits', M.bit_length())
