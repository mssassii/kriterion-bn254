/-
**Memory and word bookkeeping** for the CRT machine's blocks: `writePair`, `storeRam` and `setReg` projections, the
`sampleFp` reading as field arithmetic (`sampleFp_eq`, `word_c256`), and the field instructions on field words
(`fieldMul_words`, `fieldAdd_words`).
-/

import Proof.Simulator.ReplayBase

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Memory bookkeeping -/

omit [FieldCertificate] in
theorem writePair_ram (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem writePair_bits (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem writePair_registers (memory : Memory) (first second : Register) (values : Word × Word)
    (index : Register) :
    (writePair memory first second values).registers index =
      if index = second then values.2 else if index = first then values.1 else
        memory.registers index := by
  simp only [writePair, Function.update_apply]

omit [FieldCertificate] in
theorem storeRam_registers (memory : Memory) (address value : Word) :
    (storeRam memory address value).registers = memory.registers := rfl

omit [FieldCertificate] in
theorem storeRam_bits (memory : Memory) (address value : Word) :
    (storeRam memory address value).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem storeRam_ram (memory : Memory) (address value : Word) :
    (storeRam memory address value).ram = Function.update memory.ram address value := rfl

/-! ### One element -/

omit [FieldCertificate] in
theorem word_two_pow_128 : (word (2 ^ 128)).toNat = 2 ^ 128 := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]

theorem c256_lt : c256 < 2 ^ 256 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by unfold pNat; norm_num)) (by unfold pNat; norm_num)

theorem word_c256 : ((word c256).toNat : BaseField) = 2 ^ 256 := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt c256_lt]
  unfold c256
  rw [pNat_eq, ZMod.natCast_mod]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem sampleFp_eq (first second third : Block) :
    sampleFp first second third =
      (first.toNat : BaseField) + (second.toNat : BaseField) * 2 ^ 128 +
        (third.toNat : BaseField) * 2 ^ 256 := by
  unfold sampleFp blocksToNat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem reg_same (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).registers target = value := by
  rw [setReg_registers, if_pos rfl]

theorem reg_ne (memory : Memory) (target other : Register) (value : Word) (different : other ≠ target) :
    (setReg memory target value).registers other = memory.registers other := by
  rw [setReg_registers, if_neg different]

theorem fieldMul_words (first second : BaseField) :
    Arithmetic.fieldMul.eval (fieldWord first) (fieldWord second) = fieldWord (first * second) := by
  rw [eval_fieldMul, fieldWord_cast, fieldWord_cast]

theorem fieldAdd_words (first second : BaseField) :
    Arithmetic.fieldAdd.eval (fieldWord first) (fieldWord second) = fieldWord (first + second) := by
  rw [eval_fieldAdd, fieldWord_cast, fieldWord_cast]

omit [FieldCertificate] in
theorem word_small {value : Nat} (small : value < 2 ^ 256) : (word value).toNat = value := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
