/-
The public value of configuration E and its byte codec.

| Field       | Encoding                         | Formula          | Bytes   |
|-------------|----------------------------------|------------------|---------|
| `curve`     | `3 * field`                      | `3 * 32`         | 96      |
| `rows`      | `Vector rowGamma 91`             | `91 * 128`       | 11,648  |
| `exception` | `Vector entry 91`                | `91 * 6`         | 546     |
| `crtX`      | `Vector block 3546`              | `3546 * 16`      | 56,736  |
| `crtY`      | `Vector block 3546`              | `3546 * 16`      | 56,736  |
| `recX`      | `Vector (natural 78) 458`        | `458 * 78`       | 35,724  |
| `recY`      | `Vector (natural 78) 275`        | `275 * 78`       | 21,450  |
| **total**   |                                  |                  | **182,936** |

Every field has a fixed width and there is no tag, so every inhabitant encodes to exactly
`ciphertextBytes` bytes and the size theorem does not mention the garbler (xinshu's `SizedBy`
pattern, `Construction/PGS/Encoding.lean`; the field, block, byte and row encoders are copies of
his private ones).

A record is stored as a 78-byte natural (`2 M < 2 ^ 624 = 256 ^ 78`); that honest records are below
`2 M` is a lemma about the garbler, not part of the type, so `M` never enters a type.
-/

import Construction.CRT.Coord
import Construction.ArgoMAC.Public
import Encoding

namespace Kriterion.CRT.Entry

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-! ### Sizes and indices -/

/-- The real table (85 moduli, T9, slack 120). -/
abbrev table : CrtTable := bn254Table

/-- Encodings of `x`: 455 point encodings digit-major with slot `e mod 5` =
(rowX_x7, rowX_x9, rowY_x7, rowY_x9, rowZ_x9), then the curve encodings x3, x5, x7. -/
abbrev xCount : Nat := 458

/-- Encodings of `y`: 273 point encodings digit-major with slot `e mod 3` =
(rowX_y10, rowY_y8, rowY_y10), then the curve encodings y4, y6. -/
abbrev yCount : Nat := 275

/-- Published conversion blocks per coordinate. -/
abbrev convCount : Nat := 3546

/-- Record width in bytes. -/
abbrev recordBytes : Nat := 78

/-- A published record `h_e * M + Σ_i J_{e,i} * Π_{i' < i} m_{i'}`, a 78-byte natural. -/
abbrev Record := Fin (256 ^ recordBytes)

/-- The row encodings, those with an Embryo mask: `x` 0 .. 454 and `y` 0 .. 272. -/
abbrev RowEncoding := Fin pointElementCountX ⊕ Fin pointElementCountY

/-! ### The public value -/

/-- The complete public value of configuration E. -/
structure Public where
  /-- The curve check's three constants. -/
  curve : BaseField × BaseField × BaseField
  /-- Lane R1's four row constants per digit (X.c0, Y.c0, Y.c4, Z.c0). -/
  rows : Vector RowGamma digitCount
  /-- The 6-byte exception entry per digit. -/
  exception : Vector Exception.Entry digitCount
  /-- The flat conversion blocks of `x` (`ConvPublic.flatten`). -/
  crtX : Vector Block convCount
  /-- The flat conversion blocks of `y`. -/
  crtY : Vector Block convCount
  /-- The records of `x`. -/
  recX : Vector Record xCount
  /-- The records of `y`. -/
  recY : Vector Record yCount

/-- The ciphertext size: `96 + 91 * 128 + 91 * 6 + 2 * 3546 * 16 + 733 * 78`. -/
def ciphertextBytes : Nat := 182936

/-- The flat blocks of one coordinate read back as the evaluator's conversion material. -/
def convOf (blocks : Vector Block convCount) : ConvPublic := ConvPublic.unflatten table blocks.toArray

/-- Lane R1's row constants of digit `d`. -/
def gammaOf (pub : Public) (digit : Fin digitCount) : RowGamma := pub.rows.get digit

/-- The curve constants. -/
def curveOf (pub : Public) : BaseField × BaseField × BaseField := pub.curve

namespace Wire

/-- A field element, `32` bytes, no tag. -/
private def field : Kriterion.Encoding BaseField :=
  (Kriterion.Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

/-- A correlation block, `16` bytes. -/
private def block : Kriterion.Encoding Block :=
  (Kriterion.Encoding.natural 16).map
    (fun value => ⟨value.toNat, by
      have expand : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num
      rw [expand]; exact value.isLt⟩)
    (fun value => BitVec.ofNat 128 value.val)
    (fun value => by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.isLt])

/-- One gadget byte. -/
private def gadgetByte : Kriterion.Encoding (BitVec 8) :=
  Kriterion.Encoding.byte.map
    (fun value : BitVec 8 => ⟨value.toNat, value.isLt⟩)
    (fun value => BitVec.ofNat 8 value.val)
    (fun value => by simp)

/-- One digit's exception entry, `6` bytes. -/
private def entry : Kriterion.Encoding Exception.Entry := gadgetByte.vector 6

/-- One digit's four published row constants, `4 * 32 = 128` bytes. -/
private def rowGamma : Kriterion.Encoding RowGamma :=
  (field.pair (field.pair (field.pair field))).map
    (fun value => (value.xC0, value.yC0, value.yC4, value.zC0))
    (fun ⟨xC0, yC0, yC4, zC0⟩ => ⟨xC0, yC0, yC4, zC0⟩)
    (fun _ => rfl)

/-- The curve constants, `3 * 32 = 96` bytes. -/
private def curveTriple : Kriterion.Encoding (BaseField × BaseField × BaseField) :=
  field.pair (field.pair field)

/-- One record, `78` bytes. -/
private def record : Kriterion.Encoding Record := Kriterion.Encoding.natural recordBytes

/-- The complete public encoding, in the order curve, rows, exception, crtX, crtY, recX, recY. -/
def encoding : Kriterion.Encoding Public :=
  (curveTriple.pair ((rowGamma.vector digitCount).pair ((entry.vector digitCount).pair
    ((block.vector convCount).pair ((block.vector convCount).pair
      ((record.vector xCount).pair (record.vector yCount))))))).map
    (fun value => (value.curve, value.rows, value.exception, value.crtX, value.crtY, value.recX,
      value.recY))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2.1,
      value.2.2.2.2.2.1, value.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-! ### Sizes -/

/-- `encoding` emits exactly `size` bytes for every value. -/
private def SizedBy {alpha : Type} (encoding : Kriterion.Encoding alpha) (size : Nat) : Prop :=
  ∀ value, (encoding.encode value).length = size

private theorem sizedBy_pair {alpha beta : Type} {first : Kriterion.Encoding alpha}
    {second : Kriterion.Encoding beta} {left right : Nat} (hfirst : SizedBy first left)
    (hsecond : SizedBy second right) : SizedBy (first.pair second) (left + right) := by
  intro value
  show ((first.encode value.1) ++ (second.encode value.2)).length = left + right
  rw [List.length_append, hfirst, hsecond]

private theorem sizedBy_map {alpha beta : Type} {base : Kriterion.Encoding alpha} {size : Nat}
    (hbase : SizedBy base size) (encode : beta → alpha) (decode : alpha → beta)
    (inverse : ∀ value, decode (encode value) = value) :
    SizedBy (base.map encode decode inverse) size :=
  fun value => hbase (encode value)

private theorem sizedBy_vector {alpha : Type} {base : Kriterion.Encoding alpha} {size : Nat}
    (hbase : SizedBy base size) (count : Nat) : SizedBy (base.vector count) (count * size) :=
  fun value => Kriterion.Encoding.vector_length base size count value (fun _ => hbase _)

private theorem sizedBy_natural (width : Nat) : SizedBy (Kriterion.Encoding.natural width) width :=
  fun value => Kriterion.Encoding.natural_length width value

private theorem sizedBy_byte : SizedBy Kriterion.Encoding.byte 1 := fun _ => rfl

private theorem field_sized : SizedBy field 32 := sizedBy_map (sizedBy_natural 32) _ _ _

private theorem block_sized : SizedBy block 16 := sizedBy_map (sizedBy_natural 16) _ _ _

private theorem gadgetByte_sized : SizedBy gadgetByte 1 := sizedBy_map sizedBy_byte _ _ _

private theorem entry_sized : SizedBy entry 6 := sizedBy_vector gadgetByte_sized 6

private theorem rowGamma_sized : SizedBy rowGamma 128 :=
  sizedBy_map (sizedBy_pair field_sized (sizedBy_pair field_sized (sizedBy_pair field_sized
    field_sized))) _ _ _

private theorem curveTriple_sized : SizedBy curveTriple 96 :=
  sizedBy_pair field_sized (sizedBy_pair field_sized field_sized)

private theorem record_sized : SizedBy record 78 := sizedBy_natural recordBytes

private theorem encoding_sized :
    SizedBy encoding (96 + (digitCount * 128 + (digitCount * 6 + (convCount * 16 +
      (convCount * 16 + (xCount * 78 + yCount * 78)))))) :=
  sizedBy_map (sizedBy_pair curveTriple_sized
    (sizedBy_pair (sizedBy_vector rowGamma_sized digitCount)
      (sizedBy_pair (sizedBy_vector entry_sized digitCount)
        (sizedBy_pair (sizedBy_vector block_sized convCount)
          (sizedBy_pair (sizedBy_vector block_sized convCount)
            (sizedBy_pair (sizedBy_vector record_sized xCount)
              (sizedBy_vector record_sized yCount))))))) _ _ _

/-- The byte table as an arithmetic identity. -/
theorem byteArithmetic :
    96 + (digitCount * 128 + (digitCount * 6 + (convCount * 16 +
      (convCount * 16 + (xCount * 78 + yCount * 78))))) = ciphertextBytes := by
  simp only [digitCount, convCount, xCount, yCount, ciphertextBytes]

/-- **Every** public value encodes to exactly `ciphertextBytes = 182,936` bytes. -/
theorem encoding_length (value : Public) : (encoding.encode value).length = ciphertextBytes := by
  rw [encoding_sized value, byteArithmetic]

end Wire

end Kriterion.CRT.Entry
