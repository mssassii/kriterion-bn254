#!/usr/bin/env python3
"""Opus P1b: update documentation phrases that state the old 104-bit label width (comments/docstrings only).
Exact (file, old phrase, new phrase) triples; fails if a phrase is missing. No code token is touched."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EDITS = [
    ('Construction/CRT/Lanes.lean', '`Z_{2^l}` is a vector of 104 lanes', '`Z_{2^l}` is a vector of 101 lanes'),
    ('Construction/CRT/Lanes.lean', 'the identity that stores the 104', 'the identity that stores the 101'),
    ('Construction/CRT/ParityCast.lean', 'encode the `104 * width` stored bits', 'encode the `101 * width` stored bits'),
    ('Construction/CRT/Interface.lean', 'The pin natural: 104 lane representatives', 'The pin natural: 101 lane representatives'),
    ('Construction/CRT/Interface.lean', 'densely packed at 104-bit stride', 'densely packed at 101-bit stride'),
    ('Construction/CRT/LabelLanes.lean', 'The 104-lane arithmetic labels', 'The 101-lane arithmetic labels'),
    ('Construction/CRT/LabelLanes.lean', 'with 104-bit stride. Its arithmetic', 'with 101-bit stride. Its arithmetic'),
    ('Construction/CRT/LabelLanes.lean', 'input also has exactly 104 lanes', 'input also has exactly 101 lanes'),
    ('Construction/CRT/LabelLanes.lean', '`ell` consecutive 104-bit labels', '`ell` consecutive 101-bit labels'),
    ('Construction/CRT/LabelLanes.lean', 'Pack 104 arithmetic lanes', 'Pack 101 arithmetic lanes'),
    ('Construction/CRT/LabelLanes.lean', 'labels into 104 arithmetic lanes', 'labels into 101 arithmetic lanes'),
    ('Construction/CRT/LabelLanes.lean', 'All 104 lane representatives occupy at most `104 * ell`',
     'All 101 lane representatives occupy at most `101 * ell`'),
    ('Construction/CRT/LabelLanes.lean', 'labels occupy at most `104 * ell` bits', 'labels occupy at most `101 * ell` bits'),
    ('Construction/Simulator/CRT/Stage1.lean', '| 104 coins (the chunk-join', '| 101 coins (the chunk-join'),
    ('Construction/Simulator/CRT/Stage1.lean', '`n = (κ · pinCount + k) · 104 + lane`', '`n = (κ · pinCount + k) · 101 + lane`'),
    ('Construction/Simulator/CRT/Stage1.lean', 'its 104 active lanes', 'its 101 active lanes'),
    ('Construction/Simulator/CRT/ReplayConversion.lean', '(`j < 104`)', '(`j < 101`)'),
    ('Construction/Simulator/CRT/ReplayCast.lean', 'reads its 104 lanes block-aligned', 'reads its 101 lanes block-aligned'),
    ('Construction/Simulator/CRT/ReplayCast.lean', 'lane region (104 active cells)', 'lane region (101 active cells)'),
    ('Construction/Simulator/CRT/ReplayCast.lean', '/-- The 104 lanes. -/', '/-- The 101 lanes. -/'),
    ('Construction/Simulator/CRT/ReplayCast.lean', '/-- The 104 lanes of a cast', '/-- The 101 lanes of a cast'),
    ('Construction/Simulator/CRT/ReplayCast.lean', 'the 104 lanes of the hot cast', 'the 101 lanes of the hot cast'),
    ('Construction/Simulator/CRT/ReplayExtract.lean', 'for the 104 active lanes at `base .. base + 103`',
     'for the 101 active lanes at `base .. base + 100`'),
    ('Construction/Simulator/CRT/ReplayWords.lean', 'its 104 lanes. -/', 'its 101 lanes. -/'),
    ('Construction/Simulator/CRT/ReplayWords.lean', 'writes its 104 lane cells', 'writes its 101 lane cells'),
    ('Proof/Privacy/CRT/NoJoins/Algebra.lean', 'a low 104-bit conversion part', 'a low 101-bit conversion part'),
    ('Proof/Privacy/CRT/NoJoins/Algebra.lean', 'Keep the high `128 − 104` bits', 'Keep the high `128 − 101` bits'),
    ('Proof/Privacy/CRT/NoJoins/Law.lean', 'resp. `2^-104`)', 'resp. `2^-101`)'),
    ('Proof/Privacy/CRT/NoJoins/Law.lean', 'The low 104 bits of a uniform raw block', 'The low 101 bits of a uniform raw block'),
    ('Proof/Privacy/CRT/NoJoins/Law.lean', 'with probability exactly `2^-104`', 'with probability exactly `2^-101`'),
    ('Proof/Privacy/CRT/Hidden/CaseConv.lean', 'by `2^-104` given the stage-2 view', 'by `2^-101` given the stage-2 view'),
    ('Proof/Privacy/CRT/Hidden/DeltaView.lean', 'are `2^-104` for the projected', 'are `2^-101` for the projected'),
    ('Proof/Privacy/CRT/Hidden/StageOneCast.lean', 'the same 2^-104 conditional', 'the same 2^-101 conditional'),
    ('Proof/Privacy/CRT/Hidden/CaseKeyOff.lean', '≤ 1/2^104 + 1/(p − 1)`', '≤ 1/2^101 + 1/(p − 1)`'),
    ('Proof/Privacy/CRT/Core/Conversion.lean', 'one hidden 104-bit material', 'one hidden 101-bit material'),
    ('Proof/Privacy/CRT/Core/LabelUniform.lean', 'Uniformity of the low 104 bits', 'Uniformity of the low 101 bits'),
    ('Proof/Privacy/CRT/Core/LabelUniform.lean', 'has probability 2^-104 even', 'has probability 2^-101 even'),
    ('Proof/Privacy/CRT/Core/ExtractStageSpec.lean', 'agree at 104 lanes', 'agree at 101 lanes'),
    ('Proof/Simulator/CRT/Stage1Conv.lean', "A pin's `104` lanes", "A pin's `101` lanes"),
    ('Proof/Simulator/CRT/Stage1Conv.lean', 'consecutive 104-bit windows of a natural are its low `104 w` bits',
     'consecutive 101-bit windows of a natural are its low `101 w` bits'),
    ('Proof/Simulator/CRT/ReplayCast.lean', 'bit `i < 101` of `S` is bit `i`', 'bit `i < 101` of `S` is bit `i`'),
    ('Proof/Simulator/CRT/ReplayCast.lean', 'the 104 parity lanes', 'the 101 parity lanes'),
    ('Proof/Simulator/CRT/ReplayCast.lean', 'the same order, the 104', 'the same order, the 101'),
    ('Proof/Simulator/CRT/ReplayCast.lean', 'all 104 lanes of the hot cast', 'all 101 lanes of the hot cast'),
]
for path, old, new in EDITS:
    file = ROOT / path
    text = file.read_text()
    assert old in text, (path, old)
    file.write_text(text.replace(old, new))
print('doc edits:', len(EDITS))
