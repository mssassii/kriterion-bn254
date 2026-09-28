/- The packed public stream and its single final zero-padding run. -/
import Proof.Simulator.CRT.BitPacking
import Construction.CRT.Layout

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.CRT.Entry (Record recordBits convCount xCount yCount)
open Kriterion.CRT.BitPacking

namespace CrtWire

theorem field_bits (value : BaseField) : bitsOf Entry.Wire.field value = lsbs 254 value.val := by
  change bitsOf ((BitPacking.natural 254).map _ _ _) value = _
  rw [bits_map, bits_natural]


theorem block_bits (value : Label) : bitsOf Entry.Wire.label value = lsbs labelBits value.toNat := by
  change bitsOf ((BitPacking.natural labelBits).map _ _ _) value = _
  rw [bits_map, bits_natural]
  rfl

theorem record_bits (value : Record) : bitsOf Entry.Wire.record value = lsbs recordBits value.val := bits_natural recordBits value

theorem entry_bits (value : Exception.Entry) :
    bitsOf Entry.Wire.entry value =
      (List.ofFn fun index : Fin 2 => lsbs 4 value[index.val].toNat).flatten := by
  change bitsOf ((BitPacking.natural 8).map _ _ _) value = _
  rw [bits_map, bits_natural]
  have lo := value[0].isLt
  have hi := value[1].isLt
  have packed : (Exception.pack value).toNat = value[0].toNat + 16 * value[1].toNat := by
    simp only [Exception.pack, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  simp only [Fin.val_mk]
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

/-- The three flags of a normalized row. -/
def flagsOf (value : NormRow) : Nat := (NormRow.flagByte value.zFlag value.sFlag value.sign).val

theorem flags_bits (flags : Bool × Bool × Bool) :
    bitsOf Entry.Wire.flags flags = lsbs 3 (NormRow.flagByte flags.1 flags.2.1 flags.2.2).val := by
  change bitsOf ((BitPacking.natural 3).map _ _ _) flags = _
  rw [bits_map, bits_natural]


theorem normRow_bits (value : NormRow) :
    bitsOf Entry.Wire.normRow value = lsbs 254 value.xC0.val ++ lsbs 3 (flagsOf value) := by
  change bitsOf ((Entry.Wire.field.pair Entry.Wire.flags).map _ _ _) value = _
  rw [bits_map, bits_pair, field_bits, flags_bits]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- **The bits of the wire encoding.** -/
theorem packed_bits (value : Entry.Public) :
    bitsOf Entry.Wire.packed value =
      lsbs 254 value.curve.1.val ++ lsbs 254 value.curve.2.1.val ++ lsbs 254 value.curve.2.2.val ++
      (List.ofFn fun digit : Fin digitCount =>
          lsbs 254 value.rows[digit.val].xC0.val ++ lsbs 3 (flagsOf value.rows[digit.val])).flatten ++
      (List.ofFn fun digit : Fin digitCount =>
          (List.ofFn fun index : Fin 2 =>
            lsbs 4 value.exception[digit.val][index.val].toNat).flatten).flatten ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtX[k.val].toNat).flatten ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtY[k.val].toNat).flatten ++
      (List.ofFn fun e : Fin xCount => lsbs recordBits value.recX[e.val].val).flatten ++
      (List.ofFn fun e : Fin yCount => lsbs recordBits value.recY[e.val].val).flatten := by
  change bitsOf
    (Entry.Wire.curveTriple.pair ((Entry.Wire.normRow.vector digitCount).pair
      ((Entry.Wire.entry.vector digitCount).pair ((Entry.Wire.label.vector convCount).pair
        ((Entry.Wire.label.vector convCount).pair
          ((Entry.Wire.record.vector xCount).pair (Entry.Wire.record.vector yCount)))))))
    (value.curve, value.rows, value.exception, value.crtX, value.crtY, value.recX, value.recY) = _
  rw [bits_pair Entry.Wire.curveTriple]
  rw [bits_pair (Entry.Wire.normRow.vector digitCount)]
  rw [bits_pair (Entry.Wire.entry.vector digitCount)]
  rw [bits_pair (Entry.Wire.label.vector convCount)]
  rw [bits_pair (Entry.Wire.label.vector convCount)]
  rw [bits_pair (Entry.Wire.record.vector xCount)]
  rw [show Entry.Wire.curveTriple = Entry.Wire.field.pair (Entry.Wire.field.pair Entry.Wire.field) from rfl,
    bits_pair Entry.Wire.field, bits_pair Entry.Wire.field]
  rw [field_bits, field_bits, field_bits]
  rw [bits_vector Entry.Wire.normRow, bits_vector Entry.Wire.entry,
    bits_vector Entry.Wire.label, bits_vector Entry.Wire.label,
    bits_vector Entry.Wire.record, bits_vector Entry.Wire.record]
  simp only [normRow_bits, entry_bits, block_bits, record_bits, List.append_assoc]


theorem wire_bits (value : Entry.Public) :
    byteBits (Entry.Wire.encoding.encode value) =
      (lsbs 254 value.curve.1.val ++ lsbs 254 value.curve.2.1.val ++ lsbs 254 value.curve.2.2.val ++
      (List.ofFn fun digit : Fin digitCount =>
          lsbs 254 value.rows[digit.val].xC0.val ++ lsbs 3 (flagsOf value.rows[digit.val])).flatten ++
      (List.ofFn fun digit : Fin digitCount =>
          (List.ofFn fun index : Fin 2 =>
            lsbs 4 value.exception[digit.val][index.val].toNat).flatten).flatten ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtX[k.val].toNat).flatten ++
      (List.ofFn fun k : Fin convCount => lsbs labelBits value.crtY[k.val].toNat).flatten ++
      (List.ofFn fun e : Fin xCount => lsbs recordBits value.recX[e.val].val).flatten ++
      (List.ofFn fun e : Fin yCount => lsbs recordBits value.recY[e.val].val).flatten) ++ List.replicate Entry.paddingBits false := by
  rw [show Entry.Wire.encoding = Entry.Wire.packed.encoding from rfl, encoding_bits, packed_bits]
  rfl

end CrtWire
end Kriterion.CRT.SimMachine
