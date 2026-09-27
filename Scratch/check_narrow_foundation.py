#!/usr/bin/env python3
"""Deterministic Round-4 sanity checks; never imports or invokes Lean.

The integer and bit-stream pin implementations are independent Python models.
Passing these checks does not establish Lean elaboration, kernel checking, or
equivalence between these models and the Lean definitions. Source checks guard
the frozen Day-1 widths and the absence of existing consumers of the new leaves.
"""

from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import random
import re

ROOT = Path(__file__).resolve().parents[1]
LABEL_BITS = 104
RAW_BITS = 128
LABEL_MASK = (1 << LABEL_BITS) - 1


def compact(path):
    return " ".join((ROOT / path).read_text().split())


def check_sources():
    label = compact("Construction/CRT/Label.lean")
    lanes = compact("Construction/CRT/LabelLanes.lean")
    codec = compact("Construction/CRT/LabelEncoding.lean")
    raw = compact("Construction/CRT/Interface.lean")
    for fragment in (
        "abbrev labelBits : Nat := 104",
        "abbrev RawBlock := BitVec 128",
        "abbrev Label := BitVec labelBits",
        "def clip (x : RawBlock) : Label := x.setWidth labelBits",
        "def embed (x : Label) : RawBlock := x.setWidth 128",
    ):
        assert fragment in label, fragment
    for fragment in (
        "abbrev LLanes (ell : Nat) := Fin labelBits → ZMod (2 ^ ell)",
        "def pinBlocks {ell : Nat} (lanes : LLanes ell) : Fin ell → Label",
        "BitVec.ofNat labelBits (pinNat lanes >>> (labelBits * index.val))",
        "def pinOfBlocks (ell : Nat) (blocks : Fin ell → Label) : LLanes ell",
    ):
        assert fragment in lanes, fragment
    assert "(Kriterion.Encoding.natural 13).map" in codec
    # These are deliberate raw-answer/layout constants, not active label widths.
    for fragment in (
        "abbrev HashN := Nat → Block × Block",
        "abbrev laneCount : Nat := 128",
        "def lanesPerBlock (width : Nat) : Nat := 128 / width",
        "label.toNat + 2 ^ 128 * tag",
        "128 * (lane / lanesPerBlock width)",
    ):
        assert fragment in raw, fragment
    new_modules = {
        "Construction.CRT.Label",
        "Construction.CRT.LabelLanes",
        "Construction.CRT.LabelEncoding",
        "Proof.Privacy.CRT.Core.LabelUniform",
    }
    imports = []
    for path in ROOT.rglob("*.lean"):
        if any(part in {".git", ".lake"} for part in path.relative_to(ROOT).parts):
            continue
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for imported in re.findall(r"^import\s+(\S+)", path.read_text(), re.M):
            if imported in new_modules:
                assert module in new_modules, ("existing consumer", module, imported)
                imports.append([module, imported])
    return sorted(imports)


def check_toy_projection():
    configurations = xor_cases = fibre_values = weighted_cases = 0
    for raw_bits in range(1, 9):
        for bits in range(raw_bits + 1):
            configurations += 1
            raw_card, label_card = 1 << raw_bits, 1 << bits
            mask = label_card - 1
            fibres = Counter(x & mask for x in range(raw_card))
            assert len(fibres) == label_card
            assert set(fibres.values()) == {1 << (raw_bits - bits)}
            fibre_values += raw_card
            for label in range(label_card):
                assert label & mask == label  # clip(embed(label))
            for x in range(raw_card):
                assert ((x & mask) & mask) == (x & mask)
                for y in range(raw_card):
                    assert ((x ^ y) & mask) == ((x & mask) ^ (y & mask))
                    xor_cases += 1
                for label in range(label_card):
                    assert ((x ^ label) & mask) == ((x & mask) ^ label)
            # A view chooses both the guess and a nonnegative rational weight.
            # The hidden raw block is independent and uniform in each view.
            weights = [Fraction(v + 1, 7) for v in range(5)]
            weighted_hits = sum(
                weight * sum((x & mask) == ((3 * v + 1) & mask)
                             for x in range(raw_card)) / raw_card
                for v, weight in enumerate(weights)
            )
            assert weighted_hits == sum(weights) / label_card
            # The raw pair's unused second component multiplies fibre size.
            assert fibres[0] * raw_card == (1 << (2 * raw_bits - bits))
            weighted_cases += len(weights)
    return dict(configurations=configurations, raw_values=fibre_values,
                xor_pairs=xor_cases, weighted_view_cases=weighted_cases)


def pack_radix(lanes, ell):
    number = sum(value << (ell * lane) for lane, value in enumerate(lanes))
    return [(number >> (LABEL_BITS * index)) & LABEL_MASK for index in range(ell)]


def unpack_radix(blocks, ell):
    number = sum(value << (LABEL_BITS * index) for index, value in enumerate(blocks))
    mask = (1 << ell) - 1
    return [(number >> (ell * lane)) & mask for lane in range(LABEL_BITS)]


def from_lsb_bits(bits):
    value = 0
    for bit in reversed(bits):
        value = 2 * value + bit
    return value


def bits_lsb(value, width):
    result = []
    for _ in range(width):
        result.append(value % 2)
        value //= 2
    assert value == 0
    return result


def pack_bitstream(lanes, ell):
    bits = [bit for value in lanes for bit in bits_lsb(value, ell)]
    assert len(bits) == LABEL_BITS * ell
    return [from_lsb_bits(bits[start:start + LABEL_BITS])
            for start in range(0, len(bits), LABEL_BITS)]


def unpack_bitstream(blocks, ell):
    bits = [bit for value in blocks for bit in bits_lsb(value, LABEL_BITS)]
    assert len(bits) == LABEL_BITS * ell
    if ell == 0:
        return [0] * LABEL_BITS
    return [from_lsb_bits(bits[start:start + ell])
            for start in range(0, len(bits), ell)]


def vectors(count, width, rng):
    mask = (1 << width) - 1
    result = [
        [0] * count,
        [mask] * count,
        [index & mask for index in range(count)],
        [mask if index % 2 else 0 for index in range(count)],
    ]
    # Include bits immediately before and after a 104-bit output boundary.
    for bit in sorted({0, 1, 103, 104, 105, count * width - 1}):
        if 0 <= bit < count * width:
            number = 1 << bit
            result.append([(number >> (width * index)) & mask
                           for index in range(count)])
    result.extend([[rng.getrandbits(width) for _ in range(count)] for _ in range(64)])
    return result


def check_pins():
    rng = random.Random(0x1042026)
    widths = [0, 1, 7, 8, 14, 22]
    lane_cases = block_cases = 0
    for ell in widths:
        for lanes in vectors(LABEL_BITS, ell, rng):
            packed = pack_radix(lanes, ell)
            assert len(packed) == ell
            assert packed == pack_bitstream(lanes, ell)
            assert unpack_radix(packed, ell) == lanes
            assert unpack_bitstream(packed, ell) == lanes
            lane_cases += 1
        for blocks in vectors(ell, LABEL_BITS, rng):
            lanes = unpack_radix(blocks, ell)
            assert len(lanes) == LABEL_BITS
            assert lanes == unpack_bitstream(blocks, ell)
            assert pack_radix(lanes, ell) == blocks
            assert pack_bitstream(lanes, ell) == blocks
            block_cases += 1
    return dict(widths=widths, lane_vectors=lane_cases, label_vectors=block_cases)


def decode_label(data):
    if len(data) < 13:
        return None
    return int.from_bytes(data[:13], "little"), data[13:]


def check_bytes():
    rng = random.Random(0x132026)
    values = {0, 1, LABEL_MASK}
    values.update(1 << bit for bit in range(LABEL_BITS))
    values.update(LABEL_MASK ^ (1 << bit) for bit in range(LABEL_BITS))
    values.update(int.from_bytes(bytes([byte]) * 13, "little") for byte in range(256))
    values.update(rng.getrandbits(LABEL_BITS) for _ in range(512))
    tails = [b"", b"\0", bytes([1, 2, 255]), bytes(range(31))]
    cases = 0
    for value in sorted(values):
        encoded = value.to_bytes(13, "little")
        independent = bytes(value // (256 ** index) % 256 for index in range(13))
        assert len(encoded) == 13 and encoded == independent
        for tail in tails:
            assert decode_label(encoded + tail) == (value, tail)
            cases += 1
    for size in range(13):
        assert decode_label(bytes([255]) * size) is None
    return dict(distinct_labels=len(values), roundtrips_with_tail=cases,
                short_inputs=13)


def main():
    assert 256 ** 13 == 2 ** LABEL_BITS
    assert RAW_BITS - LABEL_BITS == 24
    summary = dict(
        status="static source and integer checks passed; Lean not run",
        label_bits=LABEL_BITS,
        raw_bits=RAW_BITS,
        raw_projection_fibre=1 << (RAW_BITS - LABEL_BITS),
        raw_pair_projection_fibre=1 << (2 * RAW_BITS - LABEL_BITS),
        leaf_imports=check_sources(),
        toy_projection=check_toy_projection(),
        dense_pin=check_pins(),
        byte_codec=check_bytes(),
    )
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
