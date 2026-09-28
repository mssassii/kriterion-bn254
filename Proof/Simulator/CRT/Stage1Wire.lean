/-
**The bits of the CRT wire encoding** (M2).

`Wire.encoding`'s field, block, byte, entry, row, curve and record encoders are private to
`Construction/CRT/Public.lean`; `encoding_eq` restates the encoding with public copies (`rfl`). `wire_bits`: the
byte bits of `Wire.encoding.encode pub` are the curve (`3 × 256` bits), the rows (`91 × 3 × 256`), the exception
nibbles (`91 × 2 × 4`), the two conversion vectors (`3412 × 104` bits each) and the records (`624` bits each), least
significant first.
-/

import Proof.Simulator.Stage1Wire
import Construction.CRT.Layout

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.CRT.Entry (Record recordBytes convCount xCount yCount)
open Kriterion.GarbledCircuit

namespace CrtWire

/-! ### Public copies of the private encoders -/

/-- A field element, `32` bytes. -/
def field : Kriterion.Encoding BaseField :=
  (Kriterion.Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

/-- A conversion label, `13` bytes. -/
def block : Kriterion.Encoding Label := Narrow.labelEncoding

/-- One gadget byte. -/
def gadgetByte : Kriterion.Encoding (BitVec 8) :=
  Kriterion.Encoding.byte.map
    (fun value : BitVec 8 => ⟨value.toNat, value.isLt⟩)
    (fun value => BitVec.ofNat 8 value.val)
    (fun value => by simp)

/-- One exception entry. -/
def entry : Kriterion.Encoding Exception.Entry := Exception.entryEncoding

/-- One digit's row constants. -/
def rowGamma : Kriterion.Encoding RowGamma :=
  (field.pair (field.pair field)).map
    (fun value => (value.xC0, value.yC4, value.zC0))
    (fun ⟨xC0, yC4, zC0⟩ => ⟨xC0, yC4, zC0⟩)
    (fun _ => rfl)

/-- The curve constants. -/
def curveTriple : Kriterion.Encoding (BaseField × BaseField × BaseField) := field.pair (field.pair field)

/-- One record. -/
def record : Kriterion.Encoding Record := Kriterion.Encoding.natural recordBytes

/-- The encoding with the public copies. -/
def encoding : Kriterion.Encoding Entry.Public :=
  (curveTriple.pair ((rowGamma.vector digitCount).pair ((entry.vector digitCount).pair
    ((block.vector convCount).pair ((block.vector convCount).pair
      ((record.vector xCount).pair (record.vector yCount))))))).map
    (fun value => (value.curve, value.rows, value.exception, value.crtX, value.crtY, value.recX,
      value.recY))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2.1,
      value.2.2.2.2.2.1, value.2.2.2.2.2.2⟩)
    (fun _ => rfl)

theorem encoding_eq : Entry.Wire.encoding = encoding := rfl

/-! ### The bits of each encoder -/

theorem field_bits (value : BaseField) : byteBits (encodeOf field value) = lsbs 256 value.val :=
  natural_byteBits 32 _

theorem block_bits (value : Label) : byteBits (encodeOf block value) = lsbs labelBits value.toNat :=
  natural_byteBits 13 _

theorem gadgetByte_bits (value : BitVec 8) :
    byteBits (encodeOf gadgetByte value) = lsbs 8 value.toNat := by
  show SimulatorProtocol.bits 8 value.toNat ++ [] = _
  rw [List.append_nil, bits_eq_lsbs]

theorem record_bits (value : Record) : byteBits (encodeOf record value) = lsbs 624 value.val :=
  natural_byteBits recordBytes _

theorem entry_bits (value : Exception.Entry) :
    byteBits (encodeOf entry value) =
      (List.ofFn fun index : Fin 2 => lsbs 4 value[index.val].toNat).flatten := by
  rw [show entry = gadgetByte.map Exception.pack Exception.unpack Exception.unpack_pack from rfl,
    encodeOf_map, gadgetByte_bits]
  have lo := value[0].isLt
  have hi := value[1].isLt
  have packed : (Exception.pack value).toNat = value[0].toNat + 16 * value[1].toNat := by
    simp only [Exception.pack, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  rw [packed]
  have bits := digitSum_bits 4 2 (fun index => value[index.val].toNat) (fun index => value[index.val].isLt)
  have sum : digitSum 4 2 (fun index => value[index.val].toNat) =
      value[0].toNat + 16 * value[1].toNat := by
    simp [digitSum, Fin.sum_univ_two, Nat.mul_comm]
  rw [sum] at bits
  exact bits

/-- The three row constants of a digit by slot. -/
def rowField (gamma : RowGamma) : Nat → BaseField
  | 0 => gamma.xC0
  | 1 => gamma.yC4
  | _ => gamma.zC0

theorem rowGamma_bits (value : RowGamma) :
    byteBits (encodeOf rowGamma value) =
      (List.ofFn fun index : Fin 3 => lsbs 256 (rowField value index.val).val).flatten := by
  rw [show rowGamma = (field.pair (field.pair field)).map
      (fun value : RowGamma => (value.xC0, value.yC4, value.zC0))
      (fun ⟨xC0, yC4, zC0⟩ => ⟨xC0, yC4, zC0⟩)
      (fun _ => rfl) from rfl, encodeOf_map]
  rw [encodeOf_pair, encodeOf_pair]
  simp only [byteBits_append, field_bits]
  simp [List.ofFn_succ, rowField]

/-- **The bits of the wire encoding.** -/
theorem wire_bits (value : Entry.Public) :
    byteBits (Entry.Wire.encoding.encode value) =
      lsbs 256 value.curve.1.val ++ lsbs 256 value.curve.2.1.val ++ lsbs 256 value.curve.2.2.val ++
      (List.ofFn fun digit : Fin digitCount =>
          (List.ofFn fun index : Fin 3 =>
            lsbs 256 (rowField value.rows[digit.val] index.val).val).flatten).flatten ++
      (List.ofFn fun digit : Fin digitCount =>
          (List.ofFn fun index : Fin 2 =>
            lsbs 4 value.exception[digit.val][index.val].toNat).flatten).flatten ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtX[k.val].toNat).flatten ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtY[k.val].toNat).flatten ++
      (List.ofFn fun e : Fin xCount => lsbs 624 value.recX[e.val].val).flatten ++
      (List.ofFn fun e : Fin yCount => lsbs 624 value.recY[e.val].val).flatten := by
  rw [encoding_eq, encode_eq]
  unfold encoding
  rw [encodeOf_map, encodeOf_pair, encodeOf_pair, encodeOf_pair, encodeOf_pair, encodeOf_pair,
    encodeOf_pair]
  rw [show curveTriple = field.pair (field.pair field) from rfl, encodeOf_pair, encodeOf_pair]
  simp only [byteBits_append]
  rw [field_bits, field_bits, field_bits]
  rw [byteBits_vector, byteBits_vector, byteBits_vector, byteBits_vector, byteBits_vector,
    byteBits_vector]
  simp only [rowGamma_bits, entry_bits, block_bits, record_bits, List.append_assoc]

end CrtWire

end Kriterion.CRT.SimMachine
