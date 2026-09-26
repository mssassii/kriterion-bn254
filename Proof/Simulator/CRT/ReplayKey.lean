/-
**The key on the machine** (`agree_keyBlock`): the machine's `keyBlock` against
`liftHash (keyM t)` where `t` is the curve polynomial of the cells, with `K` stored at `key`.
-/

import Proof.Simulator.CRT.ReplayTree
import Proof.Simulator.CRT.Garner
import Proof.Simulator.ReplayElement
import Construction.Simulator.CRT.ReplayKey

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC BN254

section Key

variable [BN254.FieldCertificate]

/-! ### The curve polynomial -/

theorem exec_curvePowers (kc : KeyCells) (memory : Memory) (x y : BaseField)
    (hx : memory.ram (word kc.reqX) = fieldWord x) (hy : memory.ram (word kc.reqY) = fieldWord y) :
    ∃ after, (curvePowers kc).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rA = fieldWord x ∧ after.registers rB = fieldWord y ∧
      after.registers rC = fieldWord (x * x) ∧ after.registers rD = fieldWord (x * x * x) ∧
      after.registers rE = fieldWord (y * y) ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rD → register ≠ rE →
        register ≠ rAddr → after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, fun register n1 n2 n3 n4 n5 n6 => ?_⟩
  all_goals simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, hx, hy]
  · rw [fieldMul_words]
  · rw [fieldMul_words, fieldMul_words]
  · rw [fieldMul_words]
  · simp only [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]

theorem exec_curveStart (kc : KeyCells) (memory : Memory) (c0 c1 d : BaseField)
    (h0 : memory.ram (word kc.constBase) = fieldWord c0)
    (h1 : memory.ram (word (kc.constBase + 1)) = fieldWord c1)
    (hD : memory.registers rD = fieldWord d) :
    ∃ after, (curveStart kc).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rInput = fieldWord (c0 + c1 * d) ∧
      ∀ register, register ≠ rInput → register ≠ rAcc → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, h0, h1, hD]
    rw [fieldMul_words, fieldAdd_words]
  · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3]

theorem exec_curveTerm (cell : Nat) (reg : Register) (memory : Memory) (acc v w : BaseField)
    (n1 : reg ≠ rAcc) (n2 : reg ≠ rAddr)
    (hIn : memory.registers rInput = fieldWord acc) (hCell : memory.ram (word cell) = fieldWord v)
    (hReg : memory.registers reg = fieldWord w) :
    ∃ after, (curveTerm cell reg).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rInput = fieldWord (acc + v * w) ∧
      ∀ register, register ≠ rInput → register ≠ rAcc → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register m1 m2 m3 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, if_neg n1,
      if_neg n2, hIn, hCell, hReg]
    rw [fieldMul_words, fieldAdd_words]
  · simp only [reg_setReg, if_neg m1, if_neg m2, if_neg m3]

theorem exec_curveConst (cell : Nat) (memory : Memory) (acc v : BaseField)
    (hIn : memory.registers rInput = fieldWord acc) (hCell : memory.ram (word cell) = fieldWord v) :
    ∃ after, (curveConst cell).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rInput = fieldWord (acc + v) ∧
      ∀ register, register ≠ rInput → register ≠ rAcc → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register m1 m2 m3 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, hIn, hCell]
    rw [fieldAdd_words]
  · simp only [reg_setReg, if_neg m1, if_neg m2, if_neg m3]

/-- The curve polynomial (the order of `CurveMembership.evaluate`). -/
def curvePoly (x y c0 c1 c2 x3 y4 x5 y6 x7 : BaseField) : BaseField :=
  c0 + c1 * x ^ 3 + c2 * y ^ 2 + x3 * x ^ 2 + y4 * y + x5 * x + y6 + x7

/-- The values the key block reads. -/
structure KeyInputs (kc : KeyCells) (memory : Memory) (x y c0 c1 c2 x3 y4 x5 y6 x7 : BaseField) :
    Prop where
  hx : memory.ram (word kc.reqX) = fieldWord x
  hy : memory.ram (word kc.reqY) = fieldWord y
  h0 : memory.ram (word kc.constBase) = fieldWord c0
  h1 : memory.ram (word (kc.constBase + 1)) = fieldWord c1
  h2 : memory.ram (word (kc.constBase + 2)) = fieldWord c2
  h3 : memory.ram (word kc.x3) = fieldWord x3
  h4 : memory.ram (word kc.y4) = fieldWord y4
  h5 : memory.ram (word kc.x5) = fieldWord x5
  h6 : memory.ram (word kc.y6) = fieldWord y6
  h7 : memory.ram (word kc.x7) = fieldWord x7

/-- **The curve check's output in `rInput`.** -/
theorem exec_curveEval (kc : KeyCells) (memory : Memory) (x y c0 c1 c2 x3 y4 x5 y6 x7 : BaseField)
    (inputs : KeyInputs kc memory x y c0 c1 c2 x3 y4 x5 y6 x7) :
    ∃ after, (curveEval kc).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      after.registers rInput = fieldWord (curvePoly x y c0 c1 c2 x3 y4 x5 y6 x7) ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rD → register ≠ rE →
        register ≠ rAcc → register ≠ rAddr → register ≠ rInput →
        after.registers register = memory.registers register := by
  obtain ⟨m1, run1, ram1, bits1, a1, b1, c1', d1, e1, regs1⟩ :=
    exec_curvePowers kc memory x y inputs.hx inputs.hy
  obtain ⟨m2, run2, ram2, bits2, in2, regs2⟩ := exec_curveStart kc m1 c0 c1 (x * x * x)
    (by rw [ram1]; exact inputs.h0) (by rw [ram1]; exact inputs.h1) d1
  have keep2 : ∀ r, r ≠ rInput → r ≠ rAcc → r ≠ rAddr → m2.registers r = m1.registers r := regs2
  obtain ⟨m3, run3, ram3, bits3, in3, regs3⟩ := exec_curveTerm (kc.constBase + 2) rE m2 _ c2 (y * y)
    (by decide) (by decide) in2 (by rw [ram2, ram1]; exact inputs.h2)
    (by rw [keep2 rE (by decide) (by decide) (by decide)]; exact e1)
  obtain ⟨m4, run4, ram4, bits4, in4, regs4⟩ := exec_curveTerm kc.x3 rC m3 _ x3 (x * x)
    (by decide) (by decide) in3 (by rw [ram3, ram2, ram1]; exact inputs.h3)
    (by rw [regs3 rC (by decide) (by decide) (by decide), keep2 rC (by decide) (by decide) (by decide)]
        exact c1')
  obtain ⟨m5, run5, ram5, bits5, in5, regs5⟩ := exec_curveTerm kc.y4 rB m4 _ y4 y
    (by decide) (by decide) in4 (by rw [ram4, ram3, ram2, ram1]; exact inputs.h4)
    (by rw [regs4 rB (by decide) (by decide) (by decide), regs3 rB (by decide) (by decide) (by decide),
          keep2 rB (by decide) (by decide) (by decide)]
        exact b1)
  obtain ⟨m6, run6, ram6, bits6, in6, regs6⟩ := exec_curveTerm kc.x5 rA m5 _ x5 x
    (by decide) (by decide) in5 (by rw [ram5, ram4, ram3, ram2, ram1]; exact inputs.h5)
    (by rw [regs5 rA (by decide) (by decide) (by decide), regs4 rA (by decide) (by decide) (by decide),
          regs3 rA (by decide) (by decide) (by decide), keep2 rA (by decide) (by decide) (by decide)]
        exact a1)
  obtain ⟨m7, run7, ram7, bits7, in7, regs7⟩ := exec_curveConst kc.y6 m6 _ y6 in6
    (by rw [ram6, ram5, ram4, ram3, ram2, ram1]; exact inputs.h6)
  obtain ⟨m8, run8, ram8, bits8, in8, regs8⟩ := exec_curveConst kc.x7 m7 _ x7 in7
    (by rw [ram7, ram6, ram5, ram4, ram3, ram2, ram1]; exact inputs.h7)
  refine ⟨m8, ?_, by rw [ram8, ram7, ram6, ram5, ram4, ram3, ram2, ram1],
    by rw [bits8, bits7, bits6, bits5, bits4, bits3, bits2, bits1], ?_,
    fun register n1 n2 n3 n4 n5 n6 n7 n8 => ?_⟩
  · unfold curveEval
    rw [Prog.exec_seq_some _ _ _ _ run1, Prog.exec_seq_some _ _ _ _ run2,
      Prog.exec_seq_some _ _ _ _ run3, Prog.exec_seq_some _ _ _ _ run4,
      Prog.exec_seq_some _ _ _ _ run5, Prog.exec_seq_some _ _ _ _ run6,
      Prog.exec_seq_some _ _ _ _ run7, run8]
  · rw [in8]
    unfold curvePoly
    congr 1
    ring
  · rw [regs8 register n8 n6 n7, regs7 register n8 n6 n7, regs6 register n8 n6 n7,
      regs5 register n8 n6 n7, regs4 register n8 n6 n7, regs3 register n8 n6 n7,
      regs2 register n8 n6 n7, regs1 register n1 n2 n3 n4 n5 n7]

omit [BN254.FieldCertificate] in
theorem det_curveEval (kc : KeyCells) : (curveEval kc).OpsSatisfy Op.Det :=
  ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial⟩,
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial⟩,
    ⟨⟨trivial, trivial⟩, trivial, trivial⟩, ⟨⟨trivial, trivial⟩, trivial, trivial⟩,
    ⟨⟨trivial, trivial⟩, trivial, trivial⟩, ⟨⟨trivial, trivial⟩, trivial, trivial⟩,
    ⟨⟨trivial, trivial⟩, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩

/-! ### The key query -/

omit [BN254.FieldCertificate] in
theorem maskKeyTag_eq : maskKeyTag = 687194767360 := by
  unfold maskKeyTag tagCode Family.key
  rfl

theorem maskKeyInput_lt (t : BaseField) : maskKeyInput t < 2 ^ 256 := by
  unfold maskKeyInput hashInput
  have := (BitVec.ofNat 128 t.val).isLt
  rw [maskKeyTag_eq]
  omega

theorem exec_keyInputProg (memory : Memory) (t : BaseField)
    (hIn : memory.registers rInput = fieldWord t) :
    ∃ after, keyInputProg.exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rInput = word (maskKeyInput t) ∧
      ∀ register, register ≠ rB → register ≠ rInput →
        after.registers register = memory.registers register := by
  have tSmall : t.val < 2 ^ 256 :=
    lt_trans t.val_lt (by unfold baseFieldModulus; norm_num)
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, reduceIte, hIn]
    show Arithmetic.add.eval (Arithmetic.and.eval (word t.val) (word (2 ^ 128 - 1)))
      (word (2 ^ 128 * maskKeyTag)) = _
    have bound : t.val % 2 ^ 128 + 2 ^ 128 * maskKeyTag < 2 ^ 256 := by
      rw [maskKeyTag_eq]
      have := Nat.mod_lt t.val (show 0 < 2 ^ 128 by norm_num)
      omega
    rw [eval_and_pow _ 128 tSmall (by norm_num), eval_add_word _ _ bound]
    unfold maskKeyInput hashInput
    rw [BitVec.toNat_ofNat]
  · simp only [reg_setReg, if_neg n1, if_neg n2]

omit [BN254.FieldCertificate] in
theorem det_keyInputProg : keyInputProg.OpsSatisfy Op.Det := ⟨trivial, trivial, trivial, trivial⟩

variable {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The key block** against `liftHash (keyM t')` with `t'` the curve polynomial of the cells. -/
theorem agree_keyBlock (kc : KeyCells) (memory : Memory) (x y c0 c1 c2 x3 y4 x5 y6 x7 : BaseField)
    (inputs : KeyInputs kc memory x y c0 c1 c2 x3 y4 x5 y6 x7) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (K : Block) after => after.ram (word kc.key) = blockWord K ∧
        Frame (Writes.cell kc.key) keyClobbers memory after)
      ((keyBlock kc).tree memory)
      (liftHash (keyM (curvePoly x y c0 c1 c2 x3 y4 x5 y6 x7))) := by
  obtain ⟨m1, run1, ram1, bits1, in1, regs1⟩ := exec_curveEval kc memory x y c0 c1 c2 x3 y4 x5 y6 x7 inputs
  obtain ⟨m2, run2, ram2, bits2, in2, regs2⟩ := exec_keyInputProg m1 _ in1
  unfold keyBlock keyQuery
  rw [tree_seq_exec _ _ (det_curveEval kc) memory m1 run1,
    tree_seq_exec _ _ det_keyInputProg m1 m2 run2,
    tree_query_hash _ m2 _ (maskKeyInput_lt _) in2]
  unfold keyM
  refine .node _ fun (answer : Block × Block) => ?_
  rw [tree_eq_exec _ (show (storeAt kc.key rFirst).OpsSatisfy Op.Det from ⟨trivial, trivial⟩),
    exec_storeAt _ _ _ (by decide)]
  refine .leaf ⟨?_, ⟨fun address off => ?_, ?_, fun register outside => ?_⟩⟩
  · simp only [ram_storeRam, Function.update_self]
    rw [writePair_reg, if_neg (by decide), if_pos rfl]
  · simp only [ram_storeRam, ram_setReg, writePair_ram]
    rw [Function.update_of_ne off, ram2, ram1]
  · simp only [bits_storeRam, bits_setReg, writePair_bits]
    rw [bits2, bits1]
  · have ne : ∀ r, r ∈ [rA, rB, rC, rD, rE, rAcc, rAddr, rInput, rFirst, rSecond] → register ≠ r :=
      fun r mem h => outside (h ▸ mem)
    simp only [reg_storeRam, reg_setReg, if_neg (ne rAddr (by simp)), writePair_reg,
      if_neg (ne rSecond (by simp)), if_neg (ne rFirst (by simp))]
    rw [regs2 register (ne rB (by simp)) (ne rInput (by simp)),
      regs1 register (ne rA (by simp)) (ne rB (by simp)) (ne rC (by simp)) (ne rD (by simp))
        (ne rE (by simp)) (ne rAcc (by simp)) (ne rAddr (by simp)) (ne rInput (by simp))]

end Key

end Kriterion.CRT.SimMachine
