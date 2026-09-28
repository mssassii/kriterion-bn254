/-
The complete public value, packed into one little-endian bit stream. Field
constants use 254 bits, row flags use three bits, and records use 620 bits.
Only the final byte is padded. The codec round-trips every public value.
-/

import Construction.CRT.Coord
import Construction.CRT.LabelEncoding
import Construction.CRT.BitPacking
import Construction.ArgoMAC.Public
import Construction.ArgoMAC.ExceptionEncoding
import Construction.ArgoMAC.NormRow

namespace Kriterion.CRT.Entry

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-! ### Sizes and indices -/

/-- The real table (84 moduli, selected width-8/9 odd rows, slack 120). -/
abbrev table : CrtTable := bn254Table

/-- Encodings of `x`: 364 point encodings digit-major with slot `e mod 4` =
(rowX_x7, rowX_x9, rowY_cubic, rowZ_x9), then the curve encodings x3, x5, x7. -/
abbrev xCount : Nat := 367

/-- Encodings of `y`: 273 point encodings digit-major with slot `e mod 3` =
(rowX_y10, rowY_y8, rowY_y10), then the curve encodings y4, y6. -/
abbrev yCount : Nat := 275

/-- Published conversion blocks per coordinate (the half-pins and the modulus joins; the 222 chunk joins are
absorbed into the Lamport labels). -/
abbrev convCount : Nat := 2885

/-- Exact record width. The independently proved honest bound is `2 M < 2^620`. -/
abbrev recordBits : Nat := 620

/-- A published record; every inhabitant fits its packed field. -/
abbrev Record := Fin (2 ^ recordBits)

/-- The row encodings, those with an Embryo mask: `x` 0 .. 363 and `y` 0 .. 272. -/
abbrev RowEncoding := Fin pointElementCountX ⊕ Fin pointElementCountY

/-! ### The public value -/

/-- The complete public value of configuration E. -/
structure Public where
  /-- The curve check's three constants. -/
  curve : BaseField × BaseField × BaseField
  /-- The normalized row data per digit: the `X` constant and the flags `ε_Z`, `ε_S`, `ν`. -/
  rows : Vector NormRow digitCount
  /-- The one-byte exception entry per digit. -/
  exception : Vector Exception.Entry digitCount
  /-- The flat conversion blocks of `x` (`ConvPublic.flatten`). -/
  crtX : Vector Label convCount
  /-- The flat conversion blocks of `y`. -/
  crtY : Vector Label convCount
  /-- The records of `x`. -/
  recX : Vector Record xCount
  /-- The records of `y`. -/
  recY : Vector Record yCount

/-- Exact bit count of the complete public value, before final byte padding. -/
def publicBits : Nat := (254 + (254 + 254)) +
  (digitCount * (254 + 3) + (digitCount * 8 + (convCount * labelBits +
    (convCount * labelBits + (xCount * recordBits + yCount * recordBits)))))

/-- Complete byte count, rounded once after all public components. -/
def ciphertextBytes : Nat := (publicBits + 7) / 8

/-- Canonical final zero padding. -/
def paddingBits : Nat := BitPacking.padding publicBits

/-- The flat blocks of one coordinate read back as the evaluator's conversion material. -/
def convOf (blocks : Vector Label convCount) : ConvPublic := ConvPublic.unflatten table blocks.toArray

/-- The normalized row data of digit `d`. -/
def gammaOf (pub : Public) (digit : Fin digitCount) : NormRow := pub.rows.get digit

/-- The curve constants. -/
def curveOf (pub : Public) : BaseField × BaseField × BaseField := pub.curve

namespace Wire

/-- Every field inhabitant is below the 254-bit bound. -/
def field : BitPacking BaseField 254 :=
  (BitPacking.natural 254).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

/-- All three flags, including values not produced by an honest source. -/
def flags : BitPacking (Bool × Bool × Bool) 3 :=
  (BitPacking.natural 3).map
    (fun value => ⟨(NormRow.flagByte value.1 value.2.1 value.2.2).val, by
      rcases value with ⟨z, s, sign⟩
      cases z <;> cases s <;> cases sign <;> decide⟩)
    (fun value => NormRow.flagsOf ⟨value.val, lt_trans value.isLt (by decide)⟩)
    (fun value => by rcases value with ⟨z, s, sign⟩; cases z <;> cases s <;> cases sign <;> rfl)

/-- Both exception nibbles. -/
def entry : BitPacking Exception.Entry 8 :=
  (BitPacking.natural 8).map
    (fun value => ⟨(Exception.pack value).toNat, (Exception.pack value).isLt⟩)
    (fun value => Exception.unpack (BitVec.ofFin value))
    (fun value => Exception.unpack_pack value)

def normRow : BitPacking NormRow (254 + 3) :=
  (field.pair flags).map
    (fun value => (value.xC0, value.zFlag, value.sFlag, value.sign))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (fun _ => rfl)

def curveTriple : BitPacking (BaseField × BaseField × BaseField) (254 + (254 + 254)) :=
  field.pair (field.pair field)

def label : BitPacking Label labelBits :=
  (BitPacking.natural labelBits).map BitVec.toFin BitVec.ofFin (fun _ => rfl)

def record : BitPacking Record recordBits := BitPacking.natural recordBits

/-- Components are concatenated as bits, in the established public order. -/
def packed : BitPacking Public publicBits :=
  (curveTriple.pair ((normRow.vector digitCount).pair ((entry.vector digitCount).pair
    ((label.vector convCount).pair ((label.vector convCount).pair
      ((record.vector xCount).pair (record.vector yCount))))))).map
    (fun value => (value.curve, value.rows, value.exception, value.crtX, value.crtY, value.recX,
      value.recY))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2.1,
      value.2.2.2.2.2.1, value.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- Complete byte encoding, with an all-public-value, arbitrary-tail inverse. -/
def encoding : Kriterion.Encoding Public := packed.encoding

/-- Every public value occupies the same complete number of bytes. -/
theorem encoding_length (value : Public) : (encoding.encode value).length = ciphertextBytes :=
  BitPacking.encoding_length packed value

end Wire

end Kriterion.CRT.Entry
