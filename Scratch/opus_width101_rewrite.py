#!/usr/bin/env python3
"""Opus P1b: rewrite the label-width literals 104 -> 101 in proof/simulator code, by exact patterns only.

Only patterns that state the conversion-label width or the lane count are touched; unrelated 104s (e.g. the pin
word-cell size bound `* 104` in Stage1Size, numerals inside large literals) are not matched. Prints every change.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATTERNS = [
    (r'laneCount = 104\b', 'laneCount = 101'),
    (r'labelBits = 104\b', 'labelBits = 101'),
    (r'< 2 \^ 104\b', '< 2 ^ 101'),
    (r'\bi < 104\b', 'i < 101'),
    (r'\blane < 104\b', 'lane < 101'),
    (r'\(104 \+ ', '(101 + '),
    (r'\) / per ≤ 104 :=', ') / per ≤ 101 :='),
    (r'laneBase \+ 104 <', 'laneBase + 101 <'),
    (r'\(\(2 : ℝ≥0∞\) \^ 104\)⁻¹', '((2 : ℝ≥0∞) ^ 101)⁻¹'),
]
FILES = [p for p in list((ROOT / 'Proof').rglob('*.lean')) + list((ROOT / 'Construction').rglob('*.lean'))]
total = 0
for path in sorted(FILES):
    text = path.read_text()
    new = text
    for pattern, repl in PATTERNS:
        for m in re.finditer(pattern, new):
            line = new.count('\n', 0, m.start()) + 1
            print(f'{path.relative_to(ROOT)}:{line}: {m.group(0)!r} -> {repl!r}')
            total += 1
        new = re.sub(pattern, repl, new)
    if new != text:
        path.write_text(new)
print('substitutions:', total)
