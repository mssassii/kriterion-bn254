/-
**The replay's toolkit.**

* `blockWord`, `fieldWord`: how the machine's words carry blocks and field elements, and the field
  instructions on them (`eval_fieldAdd`, `eval_fieldSub`, `eval_fieldMul`);
* `bindOpt_assoc`, `bindOpt_pure_right`: reassociations of option binds of trees.
-/

import Proof.Simulator.Tree

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Words -/

/-- A block zero-extended to a word. -/
def blockWord (block : Block) : Word := BitVec.ofNat 256 block.toNat

/-- A field element as its canonical word. -/
def fieldWord (value : BaseField) : Word := BitVec.ofNat 256 value.val

theorem blockWord_toNat (block : Block) : (blockWord block).toNat = block.toNat := by
  unfold blockWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans block.isLt (by norm_num))]

theorem blockWord_block (block : Block) : BitVec.ofNat 128 (blockWord block).toNat = block := by
  rw [blockWord_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem blockWord_xor (first second : Block) :
    blockWord first ^^^ blockWord second = blockWord (first ^^^ second) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, blockWord_toNat, blockWord_toNat, blockWord_toNat, BitVec.toNat_xor]

theorem blockWord_zero : blockWord 0 = 0 := rfl

theorem fieldWord_toNat (value : BaseField) : (fieldWord value).toNat = value.val := by
  unfold fieldWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans value.val_lt (by unfold baseFieldModulus; norm_num))]

theorem fieldWord_cast (value : BaseField) : (((fieldWord value).toNat : Nat) : BaseField) = value := by
  rw [fieldWord_toNat, ZMod.natCast_zmod_val]

theorem fieldWord_injective {first second : BaseField} (same : fieldWord first = fieldWord second) :
    first = second := by
  rw [← fieldWord_cast first, ← fieldWord_cast second, same]

variable [FieldCertificate]

theorem eval_fieldAdd (first second : Word) :
    Arithmetic.fieldAdd.eval first second =
      fieldWord ((first.toNat : BaseField) + (second.toNat : BaseField)) := rfl

theorem eval_fieldSub (first second : Word) :
    Arithmetic.fieldSub.eval first second =
      fieldWord ((first.toNat : BaseField) - (second.toNat : BaseField)) := rfl

theorem eval_fieldMul (first second : Word) :
    Arithmetic.fieldMul.eval first second =
      fieldWord ((first.toNat : BaseField) * (second.toNat : BaseField)) := rfl

/-! ### Option binds of trees -/

omit [FieldCertificate] in
theorem bindOpt_assoc {spec : OracleSpec.{0, 0}} (tree : FreeQuery spec (Option Memory))
    (first second : Memory → FreeQuery spec (Option Memory)) :
    bindOpt (bindOpt tree first) second = bindOpt tree fun memory => bindOpt (first memory) second := by
  unfold bindOpt
  rw [TreeLaws.bind_assoc]
  congr 1
  funext result
  cases result <;> rfl

omit [FieldCertificate] in
theorem bindOpt_pure_right {spec : OracleSpec.{0, 0}} (tree : FreeQuery spec (Option Memory)) :
    bindOpt tree (fun memory => .pure (some memory)) = tree := by
  unfold bindOpt
  conv_rhs => rw [← TreeLaws.bind_pure_right tree]
  congr 1
  funext result
  cases result <;> rfl

end

end Kriterion.ArgoMAC.PlanB.SimMachine
