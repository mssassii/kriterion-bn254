/-
**The bits of the CRT wire encoding** (M2).

`Wire.encoding`'s field, block, byte, entry, row, curve and record encoders are private to
`Construction/CRT/Public.lean`; `encoding_eq` restates the encoding with public copies (`rfl`). `wire_bits`: the
byte bits of `Wire.encoding.encode pub` are the curve (`3 × 256` bits), the rows (`91 × (256 + 8)`: the `X` constant
and the flags byte), the exception
nibbles (`91 × 2 × 4`), the two packed conversion vectors (`2885 × 101` bits each, then 7 zero bits to whole bytes)
and the records (`624` bits each), least significant first.
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

/-- One digit's normalized row data: the `X` constant, then the flags byte. -/
def normRow : Kriterion.Encoding NormRow :=
  (field.pair NormRow.flagsEncoding).map
    (fun value => (value.xC0, value.zFlag, value.sFlag, value.sign))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (fun _ => rfl)

/-- The curve constants. -/
def curveTriple : Kriterion.Encoding (BaseField × BaseField × BaseField) := field.pair (field.pair field)

/-- One record. -/
def record : Kriterion.Encoding Record := Kriterion.Encoding.natural recordBytes

/-- The encoding with the public copies. -/
def encoding : Kriterion.Encoding Entry.Public :=
  (curveTriple.pair ((normRow.vector digitCount).pair ((entry.vector digitCount).pair
    ((Narrow.packedLabels convCount).pair ((Narrow.packedLabels convCount).pair
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

/-- `n` consecutive `labelBits` windows of a natural are its low `labelBits · n` bits. -/
theorem label_windows (value : Nat) : ∀ n : Nat,
    (List.ofFn fun k : Fin n => lsbs labelBits (value / 2 ^ (labelBits * k.val))).flatten =
      lsbs (labelBits * n) value
  | 0 => rfl
  | n + 1 => by
      rw [List.ofFn_succ_last, List.flatten_append]
      simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [label_windows value n, show labelBits * (n + 1) = labelBits * n + labelBits by ring, lsbs_add]

/-- **The bits of a packed label vector**: the labels' `labelBits`-bit runs, then the zero padding to whole bytes. -/
theorem packed_bits (n : Nat) (labels : Vector Label n) :
    byteBits (encodeOf (Narrow.packedLabels n) labels) =
      (List.ofFn fun k : Fin n => lsbs labelBits labels[k.val].toNat).flatten ++
        lsbs (8 * Narrow.packedBytes n - labelBits * n) 0 := by
  unfold Narrow.packedLabels
  rw [encodeOf_map, ← encode_eq, natural_byteBits]
  have le := Narrow.labelBits_le_packed n
  rw [show 8 * Narrow.packedBytes n = labelBits * n + (8 * Narrow.packedBytes n - labelBits * n) by omega,
    lsbs_add, Nat.div_eq_of_lt (Narrow.packNat_lt labels), Nat.add_sub_cancel_left, ← label_windows]
  congr 1
  refine congrArg List.flatten (congrArg List.ofFn (funext fun k => ?_))
  have same := congrArg BitVec.toNat (Narrow.unpackAt_packNat labels k)
  simp only [Narrow.unpackAt, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at same
  rw [← lsbs_mod labelBits (Narrow.packNat labels / 2 ^ (labelBits * k.val)), same]
  rfl

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

/-- The three row cells of a digit by slot (the stage-1 source's `xC0` and its two hidden cells). -/
def rowField (gamma : RowGamma) : Nat → BaseField
  | 0 => gamma.xC0
  | 1 => gamma.yC4
  | _ => gamma.zC0

/-- The flags byte of a normalized row. -/
def flagsOf (value : NormRow) : Nat := (NormRow.flagByte value.zFlag value.sFlag value.sign).val

theorem flags_bits (flags : Bool × Bool × Bool) :
    byteBits (encodeOf NormRow.flagsEncoding flags) =
      lsbs 8 (NormRow.flagByte flags.1 flags.2.1 flags.2.2).val := by
  show SimulatorProtocol.bits 8 (NormRow.flagByte flags.1 flags.2.1 flags.2.2).val ++ [] = _
  rw [List.append_nil, bits_eq_lsbs]

theorem normRow_bits (value : NormRow) :
    byteBits (encodeOf normRow value) = lsbs 256 value.xC0.val ++ lsbs 8 (flagsOf value) := by
  rw [show normRow = (field.pair NormRow.flagsEncoding).map
      (fun value : NormRow => (value.xC0, value.zFlag, value.sFlag, value.sign))
      (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
      (fun _ => rfl) from rfl, encodeOf_map, encodeOf_pair]
  simp only [byteBits_append, field_bits, flags_bits]
  rfl

/-- **The bits of the wire encoding.** -/
theorem wire_bits (value : Entry.Public) :
    byteBits (Entry.Wire.encoding.encode value) =
      lsbs 256 value.curve.1.val ++ lsbs 256 value.curve.2.1.val ++ lsbs 256 value.curve.2.2.val ++
      (List.ofFn fun digit : Fin digitCount =>
          lsbs 256 value.rows[digit.val].xC0.val ++ lsbs 8 (flagsOf value.rows[digit.val])).flatten ++
      (List.ofFn fun digit : Fin digitCount =>
          (List.ofFn fun index : Fin 2 =>
            lsbs 4 value.exception[digit.val][index.val].toNat).flatten).flatten ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtX[k.val].toNat).flatten ++
      lsbs (8 * Narrow.packedBytes convCount - labelBits * convCount) 0 ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtY[k.val].toNat).flatten ++
      lsbs (8 * Narrow.packedBytes convCount - labelBits * convCount) 0 ++
      (List.ofFn fun e : Fin xCount => lsbs 624 value.recX[e.val].val).flatten ++
      (List.ofFn fun e : Fin yCount => lsbs 624 value.recY[e.val].val).flatten := by
  rw [encoding_eq, encode_eq]
  unfold encoding
  rw [encodeOf_map, encodeOf_pair, encodeOf_pair, encodeOf_pair, encodeOf_pair, encodeOf_pair,
    encodeOf_pair]
  rw [show curveTriple = field.pair (field.pair field) from rfl, encodeOf_pair, encodeOf_pair]
  simp only [byteBits_append]
  rw [field_bits, field_bits, field_bits]
  rw [byteBits_vector, byteBits_vector, byteBits_vector, byteBits_vector, packed_bits, packed_bits]
  simp only [normRow_bits, entry_bits, record_bits, List.append_assoc]

end CrtWire

end Kriterion.CRT.SimMachine
