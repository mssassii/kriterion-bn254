#!/usr/bin/env python3
"""Opus structural research: what the chunk-sum carry range costs, at the W1 table.

For odd m the word sigma_m = sum_c T_{c,m}(alpha_c) <= C (m - 1) with C = 32 chunks, so ell = bitlen(C (m - 1)) and a
row publishes 4 ell - 2 w0 - 5 blocks (Intuition.md 3.6; `opus_budget_model.odd_row`). This script prices (a) the
blocks attributable to the carry, i.e. the hypothetical of a carry-free modular word (C = 1), (b) smaller C obtained
with wider chunks (C = ceil(254 / k)), both against the <= 799,992-bit target, and (c) the query cost of (b).
Not a parameter sweep of the entry: only C in {32, 23, 16, 1} and the entry's own schedule rule are evaluated.
Run: python3 Scratch/opus_carry_model.py
"""
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import opus_budget_model as m  # noqa: E402

W = 101
TARGET_BITS = 8 * 99_999
W9 = {59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
      383, 389, 397}
TABLE = m.moduli_from_source()
assert 41 not in TABLE and 17 in TABLE, 'run on the W1 tree'
REC = (2 * math.prod(TABLE) - 1).bit_length()
FIXED = 762 + 91 * 257 + 91 * 8 + 642 * REC            # rows, curve, exception, records


def row(mod, C, w0):
    ell = (C * (mod - 1)).bit_length()
    w0 = min(w0, ell - 2)                               # stage 1 needs width >= 1
    w1 = ell - w0 - 1
    keep = max(w0, ell - 5)
    blocks = 4 * ell - 2 * w0 - 5
    g0, e0 = m.extract(w0, ell, W)
    g1, e1 = m.extract(w1, ell - w0, W)
    ev = e0 + e1 + (2 ** keep - 2 ** w0) - (keep - w0) + (ell - keep) * (mod - 1)
    return ell, blocks, ev


def chunk_cost(k):
    """Chunk trees/casts of width k (254 bits cut into ceil(254/k) chunks) at the 14-bit cast ring: evaluator queries."""
    sizes = [k] * (254 // k) + ([254 % k] if 254 % k else [])
    return len(sizes), sum(m.extract(s, 14, W)[1] for s in sizes), sum(s - 1 for s in sizes) + 0


def total(C, chunk_blocks):
    rows = [row(x, C, 9 if x in W9 else 8) for x in TABLE if x != 256]
    blocks = chunk_blocks + sum(r[1] for r in rows)
    bits = FIXED + 2 * blocks * W
    return blocks, bits, sum(r[2] for r in rows)


base_blocks, base_bits, base_ev = total(32, 32 * 13)
print(f'W1 check: blocks {base_blocks} (expect 2881), bits {base_bits} (expect 1003595), record bits {REC}')
assert (base_blocks, base_bits) == (2881, 1003595)
need = base_bits - TARGET_BITS
print(f'target <= {TARGET_BITS} bits: reduction needed {need} bits = {need / (2 * W):.0f} blocks per coordinate')
for C, label in ((24, 'k=11 chunks'), (16, 'k=16 chunks'), (8, 'hypothetical'), (4, 'hypothetical'), (2, 'hypothetical'), (1, 'carry-free word (hypothetical gadget)')):
    blocks, bits, ev = total(C, 32 * 13)
    print(f'C={C:2d} ({label}): row+chunk-pin blocks {blocks} (-{base_blocks - blocks}), bits {bits} '
          f'(-{base_bits - bits}; meets target: {bits <= TARGET_BITS}); odd-row evaluator queries {ev} vs {base_ev}')
for k in (8, 11, 16):
    n, ev, _ = chunk_cost(k)
    print(f'chunk width {k}: {n} chunks, chunk evaluator queries per coordinate {ev}')
