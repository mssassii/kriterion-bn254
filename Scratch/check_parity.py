#!/usr/bin/env python3
"""Deterministic arithmetic checks, not a substitute for the Lean proofs."""
import random

LABEL_BITS = 104
rng = random.Random(20260927)
checks = 0
for width in range(1, 15):
    modulus = 1 << width
    for depth in (0, 1, 6, 8):
        for delta in (0, rng.getrandbits(LABEL_BITS)):
            leaves = [delta]
            for _ in range(depth):
                right = [rng.getrandbits(LABEL_BITS) for _ in leaves]
                leaves = [a ^ b for a, b in zip(leaves, right)] + right
            # Keep the old full-width raw lane reading; replace only its low bit.
            pin = []
            for lane in range(LABEL_BITS):
                casts = [((rng.randrange(modulus) // 2) * 2 + ((x >> lane) & 1))
                         for x in leaves]
                value = (sum(casts) + ((delta >> lane) & 1)) % modulus
                assert value % 2 == 0
                assert (2 * (value // 2)) % modulus == value
                pin.append(value // 2)
            stored_width = width - 1
            packed = sum(x << (stored_width * i) for i, x in enumerate(pin))
            labels = [(packed >> (LABEL_BITS * j)) % (1 << LABEL_BITS)
                      for j in range(stored_width)]
            unpacked = sum(x << (LABEL_BITS * j) for j, x in enumerate(labels))
            assert [(unpacked >> (stored_width * i)) % (1 << stored_width)
                    for i in range(LABEL_BITS)] == pin
            # Arbitrary serialized strings must also round-trip, not just even pins.
            arbitrary = rng.getrandbits(LABEL_BITS * stored_width)
            lanes = [(arbitrary >> (stored_width * i)) % (1 << stored_width)
                     for i in range(LABEL_BITS)]
            assert sum(x << (stored_width * i) for i, x in enumerate(lanes)) == arbitrary
            checks += 1

assert 2 * 200 * LABEL_BITS // 8 == 5200
assert 146827 - 5200 == 141627
print(f"Computed: {checks} parity/codec cases passed, including zero delta and stored width zero.")
print("Computed: 400 omitted 104-bit planes save 5200 bytes; target 141627 bytes (one-byte exception entries).")
