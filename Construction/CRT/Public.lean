/-
The public value of configuration E and its byte codec.

| Field       | Encoding                         | Formula          | Bytes   |
|-------------|----------------------------------|------------------|---------|
| `curve`     | `3 * field`                      | `3 * 32`         | 96      |
| `rows`      | `Vector rowGamma 91`             | `91 * 96`        | 8,736   |
| `exception` | `Vector entry 91`                | `91 * 1`        | 91   |
| `crtX`      | `Vector label 3412`              | `3412 * 13`      | 44,356  |
| `crtY`      | `Vector label 3412`              | `3412 * 13`      | 44,356  |
| `recX`      | `Vector (natural 78) 367`        | `367 * 78`       | 28,626  |
| `recY`      | `Vector (natural 78) 275`        | `275 * 78`       | 21,450  |
| **total**   |                                  |                  | **147,711** |

Every field has a fixed width and there is no tag, so every inhabitant encodes to exactly
`ciphertextBytes` bytes and the size theorem does not mention the garbler (xinshu's `SizedBy`
pattern, `Construction/PGS/Encoding.lean`; the field, block, byte and row encoders are copies of
his private ones).

A record is stored as a 78-byte natural (`2 M < 2 ^ 624 = 256 ^ 78`); that honest records are below
`2 M` is a lemma about the garbler, not part of the type, so `M` never enters a type.
-/

import Construction.CRT.Coord
import Construction.CRT.LabelEncoding
import Construction.ArgoMAC.Public
import Construction.ArgoMAC.ExceptionEncoding

namespace Kriterion.CRT.Entry

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-! ### Sizes and indices -/

/-- The real table (85 moduli, fallback 7/8-bit schedule, slack 120). -/
abbrev table : CrtTable := bn254Table

/-- Encodings of `x`: 364 point encodings digit-major with slot `e mod 4` =
(rowX_x7, rowX_x9, rowY_cubic, rowZ_x9), then the curve encodings x3, x5, x7. -/
abbrev xCount : Nat := 367

/-- Encodings of `y`: 273 point encodings digit-major with slot `e mod 3` =
(rowX_y10, rowY_y8, rowY_y10), then the curve encodings y4, y6. -/
abbrev yCount : Nat := 275

/-- Published conversion blocks per coordinate. -/
abbrev convCount : Nat := 3412

/-- Record width in bytes. -/
abbrev recordBytes : Nat := 78

/-- A published record `h_e * M + Σ_i J_{e,i} * Π_{i' < i} m_{i'}`, a 78-byte natural. -/
abbrev Record := Fin (256 ^ recordBytes)

/-- The row encodings, those with an Embryo mask: `x` 0 .. 363 and `y` 0 .. 272. -/
abbrev RowEncoding := Fin pointElementCountX ⊕ Fin pointElementCountY

/-! ### The public value -/

/-- The complete public value of configuration E. -/
structure Public where
  /-- The curve check's three constants. -/
  curve : BaseField × BaseField × BaseField
  /-- Lane R1's three row constants per digit (X.c0, S.c4, Z.c0). -/
  rows : Vector RowGamma digitCount
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

/-- The ciphertext size: `96 + 91 * 96 + 91 * 1 + 2 * 3412 * 13 + 642 * 78`. -/
def ciphertextBytes : Nat := 147711

/-- The flat blocks of one coordinate read back as the evaluator's conversion material. -/
def convOf (blocks : Vector Label convCount) : ConvPublic := ConvPublic.unflatten table blocks.toArray

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

/-- One digit's exception entry, packed into one byte. -/
private def entry : Kriterion.Encoding Exception.Entry := Exception.entryEncoding

/-- One digit's three published row constants, `3 * 32 = 96` bytes. -/
private def rowGamma : Kriterion.Encoding RowGamma :=
  (field.pair (field.pair field)).map
    (fun value => (value.xC0, value.yC4, value.zC0))
    (fun ⟨xC0, yC4, zC0⟩ => ⟨xC0, yC4, zC0⟩)
    (fun _ => rfl)

/-- The curve constants, `3 * 32 = 96` bytes. -/
private def curveTriple : Kriterion.Encoding (BaseField × BaseField × BaseField) :=
  field.pair (field.pair field)

/-- One record, `78` bytes. -/
private def record : Kriterion.Encoding Record := Kriterion.Encoding.natural recordBytes

/-- The complete public encoding, in the order curve, rows, exception, crtX, crtY, recX, recY. -/
def encoding : Kriterion.Encoding Public :=
  (curveTriple.pair ((rowGamma.vector digitCount).pair ((entry.vector digitCount).pair
    ((Narrow.labelEncoding.vector convCount).pair ((Narrow.labelEncoding.vector convCount).pair
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

private theorem label_sized : SizedBy Narrow.labelEncoding 13 :=
  Narrow.labelEncoding_length

private theorem entry_sized : SizedBy entry 1 := Exception.entryEncoding_length

private theorem rowGamma_sized : SizedBy rowGamma 96 :=
  sizedBy_map (sizedBy_pair field_sized (sizedBy_pair field_sized field_sized)) _ _ _

private theorem curveTriple_sized : SizedBy curveTriple 96 :=
  sizedBy_pair field_sized (sizedBy_pair field_sized field_sized)

private theorem record_sized : SizedBy record 78 := sizedBy_natural recordBytes

private theorem encoding_sized :
    SizedBy encoding (96 + (digitCount * 96 + (digitCount * 1 + (convCount * 13 +
      (convCount * 13 + (xCount * 78 + yCount * 78)))))) :=
  sizedBy_map (sizedBy_pair curveTriple_sized
    (sizedBy_pair (sizedBy_vector rowGamma_sized digitCount)
      (sizedBy_pair (sizedBy_vector entry_sized digitCount)
        (sizedBy_pair (sizedBy_vector label_sized convCount)
          (sizedBy_pair (sizedBy_vector label_sized convCount)
            (sizedBy_pair (sizedBy_vector record_sized xCount)
              (sizedBy_vector record_sized yCount))))))) _ _ _

/-- The byte table as an arithmetic identity. -/
theorem byteArithmetic :
    96 + (digitCount * 96 + (digitCount * 1 + (convCount * 13 +
      (convCount * 13 + (xCount * 78 + yCount * 78))))) = ciphertextBytes := by
  simp only [digitCount, convCount, xCount, yCount, ciphertextBytes]

/-- **Every** public value encodes to exactly `ciphertextBytes = 147,711` bytes. -/
theorem encoding_length (value : Public) : (encoding.encode value).length = ciphertextBytes := by
  rw [encoding_sized value, byteArithmetic]

end Wire

end Kriterion.CRT.Entry
