/-
The frozen interface of the CRT delivery layer: the hash of the layer on natural inputs, the tag
layout, the one-block and long hashes, the block-aligned cast reading (D11), the dense pin codec,
the fraction reading of pads (D6), the pad counts (D5), the wrap hint (D7), and the real modulus
table with the closed form of schedule T9 (D4).

Everything here is computable. Kernel rules: the product `M` of the moduli, the powers `m ^ S` and the pad integers are
never unfolded or decided in a proof; they are computed only by kernel-accelerated `Nat`
operations or by `#eval`. No sum over `Fin (2 ^ w)` or over the 85 rows is enumerated.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Batteries.Data.BitVec.Basic
import Cryptography.Primitives

namespace Kriterion.CRT

open Cryptography

/-! ### The hash of the layer -/

/-- The CRT layer's view of the contest hash: a function on the natural hash inputs
`label + 2 ^ 128 * tag`. The scheme instance is `fun n => oracle.2.2 (n : BaseField)`. -/
abbrev HashN := Nat → Block × Block

/-! ### Tags (D10) -/

/-- The tag of one hash position: family `fam < 16`, coordinate `coord < 2` (`x = 0`, `y = 1`),
index `idx < 128`, stage `stage < 4`, level `level < 16`, slot `slot < 2 ^ 16`, part `part < 64`.
In range the code is below `2 ^ 40`. -/
def tagCode (fam coord idx stage level slot part : Nat) : Nat :=
  ((((((fam * 2 + coord) * 128 + idx) * 4 + stage) * 16 + level) * 65536 + slot) * 64 + part)

/-! The tag families. -/
namespace Family
/-- Chunk trees: `idx` the chunk, `level` the hashed level, `slot` the slot. -/
def chunkTree : Nat := 0
/-- Chunk casts: `idx` the chunk, `slot` the leaf, `part` the answer. -/
def chunkCast : Nat := 1
/-- Extraction trees: `idx` the modulus index, `stage` 0 or 1, `level`, `slot`. -/
def extTree : Nat := 2
/-- Extraction casts: `idx` the modulus index, `stage`, `slot` the leaf, `part` the answer. -/
def extCast : Nat := 3
/-- Growth of the kept one-hot: `idx`, `level` the bit position, `slot`. -/
def grow : Nat := 4
/-- Folds: `idx`, `level` the bit position, `slot` the residue. -/
def fold : Nat := 5
/-- Body pads: `idx`, `slot` the residue, `part` the answer. -/
def body : Nat := 6
/-- Embryo masks: `stage` 0 collector sites, 1 paired sites; `slot` the site; `part` the answer. -/
def mask : Nat := 7
/-- Digest labels: `coord`, `slot` the bit position, `part` the bit. -/
def digestLabel : Nat := 8
/-- Digest finals: `slot` the digit. -/
def digestFinal : Nat := 9
/-- The bridge key: `K = (H (hashInput (t mod 2 ^ 128) (tagCode 10 0 0 0 0 0 0))).1`,
a labelled query at the low 128 bits of the curve check's output `t`, so that every hash input of the entry is
labelled. -/
def key : Nat := 10
end Family

/-- The natural hash input of a label at a tag. Below `2 ^ 253 < p` for tags below `2 ^ 125`. -/
def hashInput (label : Block) (tag : Nat) : Nat := label.toNat + 2 ^ 128 * tag

/-- One answer as a 256-bit natural, first block low. -/
def answerNat (answer : Block × Block) : Nat := answer.1.toNat + 2 ^ 128 * answer.2.toNat

/-- Consecutive answers concatenated little-endian, 256 bits each. -/
def packAnswers (count : Nat) (answers : Fin count → Block × Block) : Nat :=
  ∑ j : Fin count, 2 ^ (256 * j.val) * answerNat (answers j)

/-- The one-block hash: the first block of the answer. -/
def h128 (H : HashN) (label : Block) (tag : Nat) : Block := (H (hashInput label tag)).1

/-- The long hash: `count` answers at tags `tagOf 0, ..., tagOf (count - 1)`, concatenated. -/
def hlong (H : HashN) (label : Block) (tagOf : Nat → Nat) (count : Nat) : Nat :=
  packAnswers count fun j => H (hashInput label (tagOf j.val))

/-! ### Arithmetic labels and the cast reading (D11) -/

/-- The lanes of an arithmetic label: one per bit of a block. -/
abbrev laneCount : Nat := 128

/-- An arithmetic label over `Z_{2^width}`: one lane per bit of a block. -/
abbrev Lanes (width : Nat) := Fin laneCount → ZMod (2 ^ width)

/-- Lanes per 128-bit block in a cast of width `width` (no lane straddles a block). -/
def lanesPerBlock (width : Nat) : Nat := 128 / width

/-- Blocks read by a cast of width `width`. -/
def castBlocks (width : Nat) : Nat := (128 + lanesPerBlock width - 1) / lanesPerBlock width

/-- Hash answers read by a cast of width `width` (two blocks per answer). -/
def castAnswers (width : Nat) : Nat := (castBlocks width + 1) / 2

/-- The bit offset of lane `lane` inside the cast natural. -/
def laneOffset (width lane : Nat) : Nat :=
  128 * (lane / lanesPerBlock width) + width * (lane % lanesPerBlock width)

/-- The block-aligned cast reading: lane `i` is `width` bits at `laneOffset width i`. -/
def castLanes (width : Nat) (value : Nat) : Lanes width :=
  fun lane => ((value >>> laneOffset width lane.val : Nat) : ZMod (2 ^ width))

/-! ### The dense pin codec -/

/-- The pin natural: lane `i` at bits `[width * i, width * i + width)`. -/
def pinNat {width : Nat} (lanes : Lanes width) : Nat :=
  ∑ lane : Fin laneCount, (lanes lane).val * 2 ^ (width * lane.val)

/-- The `width` published blocks of a pin, little-endian. -/
def pinBlocks {width : Nat} (lanes : Lanes width) : Fin width → Block :=
  fun index => BitVec.ofNat 128 (pinNat lanes >>> (128 * index.val))

/-- Read a pin back from its blocks. -/
def pinOfBlocks (width : Nat) (blocks : Fin width → Block) : Lanes width :=
  let value := ∑ index : Fin width, (blocks index).toNat * 2 ^ (128 * index.val)
  fun lane => ((value >>> (width * lane.val) : Nat) : ZMod (2 ^ width))

/-! ### Pads: the fraction reading (D6) and the pad counts (D5) -/

/-- The fraction reading of a pad natural `value` of `256 * count` bits for modulus `m` and `S`
digits: `⌊value * m ^ S / 2 ^ (256 * count)⌋`. -/
def fractionValue (m S count value : Nat) : Nat := value * m ^ S / 2 ^ (256 * count)

/-- Digit `e` (little-endian) in base `m`. -/
def digit (m value e : Nat) : Nat := value / m ^ e % m

/-- Bit length. -/
def bitLength (value : Nat) : Nat := Nat.log2 value + 1

/-- Pad answers per slot for an odd modulus: `⌈(bitlen(m ^ S) + slack) / 256⌉`. -/
def padAnswersOdd (slack S m : Nat) : Nat := (bitLength (m ^ S) + slack + 255) / 256

/-- Pad answers per slot for the modulus `2 ^ k`: `⌈S * k / 256⌉`. -/
def padAnswersPow2 (S k : Nat) : Nat := (S * k + 255) / 256

/-- The frozen pad slack. -/
def padSlack : Nat := 120

/-! ### The wrap hint (D7) -/

/-- `B = (p - 1) ^ 2 + 1`: every delivered `a * v` is below it. -/
def wrapBound (p : Nat) : Nat := (p - 1) ^ 2 + 1

/-- The hint of an offset `O < M`: whether `O > M - B`. -/
def wrapHint (M B offset : Nat) : Bool := decide (M - B < offset)

/-- The evaluator's decoding: add `M` when the hint is set and the residue integer is below `B`. -/
def wrapDecode (M B : Nat) (hint : Bool) (value : Nat) : Nat :=
  if hint && decide (value < B) then value + M else value

/-! ### The real table: the 85 moduli and schedule T9 (D4) -/

/-- The 85 moduli in index order: every prime from 17 to 439, the prime powers 49, 81, 121, 125,
169, and 256 (index 53). -/
def bn254Moduli : Array Nat :=
  #[17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59, 61, 67, 71, 73, 79, 81, 83, 89, 97, 101, 103,
    107, 109, 113, 121, 125, 127, 131, 137, 139, 149, 151, 157, 163, 167, 169, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 256, 257, 263, 269, 271, 277, 281, 283,
    293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
    419, 421, 431, 433, 439]

/-- The conversion schedule of one odd modulus: word width `ell`, the widths of extraction
stages 0 and 1 (stage 2 has width 1 and is free), and the kept one-hot width `keep`. The stage
widths satisfy `width0 + width1 + 1 = ell` and `width0 ≤ keep ≤ ell`; growth is `keep - width0`
bits and `ell - keep` bits are folded. -/
structure OddRow where
  ell : Nat
  width0 : Nat
  width1 : Nat
  keep : Nat
deriving Repr, DecidableEq

/-- Schedule T9 in closed form for `chunks` chunks: `ell = bitlen(chunks * (m - 1))`, stages
`(7, ell - 8, 1)`, `keep = max 7 (ell - 5)`. -/
def t9Row (chunks m : Nat) : OddRow :=
  let ell := bitLength (chunks * (m - 1))
  { ell, width0 := 7, width1 := ell - 8, keep := max 7 (ell - 5) }

/-! ### The answer-table reading -/

/-- A tag-indexed answer table read as a hash of the layer: a labelled query `label + 2 ^ 128 * tag`
(with `label < 2 ^ 128`) is answered by its tag alone. Every per-wire statement proved for all
`HashN` holds on tables through this instance. -/
def tableHash (T : Nat → Block × Block) : HashN := fun n => T (n / 2 ^ 128)

end Kriterion.CRT
