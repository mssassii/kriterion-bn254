/-
**The replay of one fold agrees with the evaluator's `foldEvalM`** (`agree_foldStep`), and the
folds of one modulus with `foldsEvalM` (`agree_foldsLoop`).

The hashing piece is the tree step's (`entryHash` with the fold's cells read as tree cells); the
differences are the hot index, read from RAM instead of `α mod 2 ^ n`, and the update pass, which
reads two materials per residue at compile-time addresses.
-/

import Proof.Simulator.CRT.ReplayTree
import Construction.Simulator.CRT.ReplayFold
import Construction.CRT.Fold

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-- The layout facts one fold needs. -/
structure FoldLayout (cells : FoldCells) (m j : Nat) : Prop where
  mPos : 0 < m
  mSmall : m ≤ 2 ^ 20
  vecBelow : cells.vecBase + m ≤ cells.matBase
  matFits : cells.matBase + m < 2 ^ 256
  hotOff : cells.hot < 2 ^ 256 ∧ (∀ r, r < m → cells.hot ≠ cells.vecBase + r) ∧
    ∀ r, r < m → cells.hot ≠ cells.matBase + r
  joinOff : cells.join j < 2 ^ 256 ∧ (∀ r, r < m → cells.join j ≠ cells.vecBase + r) ∧
    ∀ r, r < m → cells.join j ≠ cells.matBase + r
  bitOff : cells.bit j < 2 ^ 256 ∧ (∀ r, r < m → cells.bit j ≠ cells.vecBase + r) ∧
    ∀ r, r < m → cells.bit j ≠ cells.matBase + r
  joinHot : cells.join j ≠ cells.hot
  bitHot : cells.bit j ≠ cells.hot

/-! ### The pure pieces -/

private theorem exec_foldTest (cells : FoldCells) (ρ : Nat) (memory : Memory) (hot : Nat)
    (hotCell : memory.ram (word cells.hot) = word hot) :
    ∃ after, (foldTest cells ρ).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rA = word hot ^^^ word ρ ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, hotCell]
    rfl
  · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3]

private theorem det_foldTest (cells : FoldCells) (ρ : Nat) : (foldTest cells ρ).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, trivial⟩

private theorem exec_foldRecover (cells : FoldCells) (j : Nat) (memory : Memory) (hot : Nat)
    (X J L : Label) (hotSmall : cells.matBase + hot < 2 ^ 256) (hotLt : hot < 2 ^ 256)
    (xorReg : memory.registers rD = labelWord X)
    (joinCell : memory.ram (word (cells.join j)) = labelWord J)
    (bitCell : memory.ram (word (cells.bit j)) = labelWord L)
    (hotCell : memory.ram (word cells.hot) = word hot) :
    ∃ after, (foldRecover cells j).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.matBase + hot))
        (labelWord (X ^^^ J ^^^ L)) ∧ after.bits = memory.bits ∧
      ∀ register, ¬ treeStepClobbers register →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register outside => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte,
      joinCell, bitCell, hotCell]
    rw [eval_add_word _ _ (by omega), Nat.add_comm, eval_xor, eval_xor, xorReg, labelWord_xor,
      labelWord_xor]
  · simp only [reg_setReg, reg_storeRam, if_neg (ne_of_not_clobbered outside rA (by simp)),
      if_neg (ne_of_not_clobbered outside rB (by simp)), if_neg (ne_of_not_clobbered outside rD (by simp)),
      if_neg (ne_of_not_clobbered outside rE (by simp)), if_neg (ne_of_not_clobbered outside rAddr (by simp))]

private theorem det_foldRecover (cells : FoldCells) (j : Nat) : (foldRecover cells j).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, trivial,
    trivial⟩

/-- The update pass: after `count` residues, residue `ρ < count` holds `h[ρ] ⊕ u_ρ ⊕ u_src(ρ)`. -/
private theorem exec_foldUpdates (cells : FoldCells) (m s : Nat) (memory : Memory)
    (below : cells.vecBase + m ≤ cells.matBase) (fits : cells.matBase + m < 2 ^ 256) (mPos : 0 < m) :
    ∀ count, count ≤ m → ∃ after,
      (Prog.rep count (foldUpdate cells m s)).exec memory = some after ∧
      (∀ ρ, ρ < count → after.ram (word (cells.vecBase + ρ)) =
        memory.ram (word (cells.vecBase + ρ)) ^^^ memory.ram (word (cells.matBase + ρ)) ^^^
          memory.ram (word (cells.matBase + foldSourceNat m s ρ))) ∧
      (∀ address, (∀ ρ, ρ < count → address ≠ word (cells.vecBase + ρ)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rC → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register
  | 0, _ => ⟨memory, Prog.exec_rep_zero _ _, fun ρ bound => absurd bound (by omega), fun _ _ => rfl,
      rfl, fun _ _ _ _ => rfl⟩
  | count + 1, bound => by
      obtain ⟨middle, run, cells', frame, bitsSame, regs⟩ :=
        exec_foldUpdates cells m s memory below fits mPos count (by omega)
      have srcLt : foldSourceNat m s count < m := Nat.mod_lt _ mPos
      have wne : ∀ x y : Nat, x < 2 ^ 256 → y < 2 ^ 256 → x ≠ y → word x ≠ word y :=
        fun x y hx hy hne => word_ne hx hy hne
      have vecNow : middle.ram (word (cells.vecBase + count)) = memory.ram (word (cells.vecBase + count)) :=
        frame _ fun ρ small => wne _ _ (by omega) (by omega) (by omega)
      have matNow : ∀ r, r < m → middle.ram (word (cells.matBase + r)) =
          memory.ram (word (cells.matBase + r)) := fun r rb =>
        frame _ fun ρ small => wne _ _ (by omega) (by omega) (by omega)
      refine ⟨_, by rw [Prog.exec_rep_succ, run, Option.bind_some]; rfl, fun ρ small => ?_,
        fun address off => ?_, ?_, fun register n1 n2 n3 => ?_⟩
      · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg,
          reg_storeRam, reduceIte]
        rw [eval_xor, eval_xor]
        by_cases last : ρ = count
        · subst last
          rw [Function.update_self, vecNow, matNow _ (by omega), matNow _ srcLt]
        · rw [Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)), cells' ρ (by omega)]
      · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg,
          reg_storeRam, reduceIte]
        rw [Function.update_of_ne (off count (by omega)), frame address fun ρ small => off ρ (by omega)]
      · exact bitsSame
      · simp only [reg_setReg, reg_storeRam, if_neg n1, if_neg n2, if_neg n3]
        exact regs register n1 n2 n3

private theorem det_foldUpdates (cells : FoldCells) (m s : Nat) :
    (Prog.rep m (foldUpdate cells m s)).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ =>
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩

/-! ### The hot update -/

/-- One conditional subtraction reduces `y < 2 m` modulo `m`. -/
private theorem cond_sub_mod (y m : Nat) (mPos : 0 < m) (small : y < 2 * m) :
    y - (1 - (if y < m then 1 else 0)) * m = y % m := by
  by_cases lt : y < m
  · rw [if_pos lt, Nat.mod_eq_of_lt lt]; simp
  · rw [if_neg lt, Nat.sub_zero, one_mul, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The evaluator's hot update as the machine computes it. -/
theorem foldHot_step (value j m hot : Nat) :
    (hot + (if value.testBit j then foldShift m j else 0)) =
      value / 2 ^ j % 2 * (2 ^ j % m) + hot := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold foldShift
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ j) with zero | one
  · rw [zero]; simp
  · rw [one]; simp; omega

private theorem exec_hotUpdate (cells : FoldCells) (m j : Nat) (memory : Memory) (value hot : Nat)
    (mPos : 0 < m) (mSmall : m ≤ 2 ^ 20) (hotLt : hot < m) (valueSmall : value < 2 ^ 256)
    (jSmall : j < 256)
    (sigmaCell : memory.ram (word cells.sigma) = word value)
    (hotCell : memory.ram (word cells.hot) = word hot) :
    ∃ after, (hotUpdate cells m (2 ^ j % m) j).exec memory = some after ∧
      after.ram = Function.update memory.ram (word cells.hot)
        (word ((hot + (if value.testBit j then foldShift m j else 0)) % m)) ∧
      after.bits = memory.bits ∧
      ∀ register, ¬ treeStepClobbers register →
        after.registers register = memory.registers register := by
  have shiftLt : 2 ^ j % m < m := Nat.mod_lt _ mPos
  have divSmall : value / 2 ^ j < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) valueSmall
  have bitLe : value / 2 ^ j % 2 ≤ 1 := by have := Nat.mod_lt (value / 2 ^ j) (by norm_num : 0 < 2); omega
  have prodLe : value / 2 ^ j % 2 * (2 ^ j % m) ≤ 2 ^ j % m := by
    calc value / 2 ^ j % 2 * (2 ^ j % m) ≤ 1 * (2 ^ j % m) := Nat.mul_le_mul_right _ bitLe
      _ = _ := one_mul _
  have sumLt : value / 2 ^ j % 2 * (2 ^ j % m) + hot < 2 * m := by omega
  have mBig : m < 2 ^ 256 := by
    have : (2 : Nat) ^ 20 < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    omega
  have lessBit : (if value / 2 ^ j % 2 * (2 ^ j % m) + hot < m then 1 else 0) ≤ 1 := by
    split <;> omega
  have corrSmall : (1 - (if value / 2 ^ j % 2 * (2 ^ j % m) + hot < m then 1 else 0)) * m < 2 ^ 256 := by
    split
    · simp
    · simpa using mBig
  have corrLe : (1 - (if value / 2 ^ j % 2 * (2 ^ j % m) + hot < m then 1 else 0)) * m ≤
      value / 2 ^ j % 2 * (2 ^ j % m) + hot := by
    split
    · simp
    · omega
  set b := value / 2 ^ j % 2 * (2 ^ j % m) with bDef
  obtain ⟨m1, run1, rA1, ram1, bits1, regs1⟩ : ∃ m1, (hotBit cells (2 ^ j % m) j).exec memory = some m1 ∧
      m1.registers rA = word b ∧ m1.ram = memory.ram ∧ m1.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        m1.registers register = memory.registers register := by
    refine ⟨_, rfl, ?_, rfl, rfl, fun register n1 n2 n3 => ?_⟩
    · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, sigmaCell]
      rw [eval_shr_word _ _ valueSmall (by omega),
        show (word 1 : Word) = word (2 ^ 1 - 1) from rfl, eval_and_pow _ _ divSmall (by norm_num),
        pow_one, eval_mul_word _ _ (by omega)]
    · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3]
  have hot1 : m1.ram (word cells.hot) = word hot := by rw [ram1]; exact hotCell
  have runAll : (hotUpdate cells m (2 ^ j % m) j).exec memory = (hotReduce cells m).exec m1 :=
    Prog.exec_seq_some _ _ memory m1 run1
  rw [runAll]
  refine ⟨_, rfl, ?_, by simp only [bits_storeRam, bits_setReg]; exact bits1,
    fun register outside => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte,
      hot1, rA1, ram1]
    rw [eval_add_word _ _ (by omega), eval_less_word _ _ (by omega) mBig,
      eval_sub_word _ _ lessBit (by norm_num), eval_mul_word _ _ corrSmall,
      eval_sub_word _ _ corrLe (by omega), cond_sub_mod _ _ mPos sumLt, foldHot_step]
  · simp only [reg_storeRam, reg_setReg, if_neg (ne_of_not_clobbered outside rA (by simp)),
      if_neg (ne_of_not_clobbered outside rB (by simp)), if_neg (ne_of_not_clobbered outside rC (by simp)),
      if_neg (ne_of_not_clobbered outside rD (by simp)), if_neg (ne_of_not_clobbered outside rE (by simp)),
      if_neg (ne_of_not_clobbered outside rAddr (by simp))]
    exact regs1 register (ne_of_not_clobbered outside rA (by simp))
      (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp))

private theorem det_hotUpdate (cells : FoldCells) (m s j : Nat) :
    (hotUpdate cells m s j).OpsSatisfy Op.Det :=
  ⟨⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial⟩,
    ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      ⟨trivial, trivial⟩⟩⟩

/-! ### The agreement of one fold -/

/-- The invariant of a fold's entry loop after `count` residues. -/
def FoldEntryInv (cells : FoldCells) (m hot : Nat) (start : Memory) (count : Nat)
    (values : Vector Label count) (memory : Memory) : Prop :=
  (∀ r (bound : r < count), r ≠ hot →
      memory.ram (word (cells.matBase + r)) = labelWord (values[r]'bound)) ∧
    memory.registers rD = labelWord (xorSkip hot values) ∧
    (∀ address, (∀ r, r < m → address ≠ word (cells.matBase + r)) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ treeStepClobbers register → memory.registers register = start.registers register

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **One residue of a fold.** -/
theorem agree_foldEntry (cells : FoldCells) (m j : Nat) (layout : FoldLayout cells m j)
    (tagOf : Nat → Nat) (hot : Nat) (hotLt : hot < m) (labels : Fin m → Label) (start : Memory)
    (hotCell : start.ram (word cells.hot) = word hot)
    (vecCells : ∀ ρ : Fin m, start.ram (word (cells.vecBase + ρ.val)) = labelWord (labels ρ))
    (tagSmall : ∀ ρ, ρ < m → tagOf ρ < 2 ^ 127)
    (index : Fin m) (values : Vector Label index.val) (memory : Memory)
    (holds : FoldEntryInv cells m hot start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : Label) after =>
        FoldEntryInv cells m hot start (index.val + 1) (values.push result) after)
      ((foldEntry cells tagOf index.val).tree memory)
      (liftHash (if index.val = hot then pure 0 else hLabelM (labels index) (tagOf index.val))) := by
  obtain ⟨mats, xorReg, frame, bitsSame, regs⟩ := holds
  have below := layout.vecBelow
  have fits := layout.matFits
  have mSmall := layout.mSmall
  have hotSmall : hot < 2 ^ 256 := by omega
  have indexSmall : index.val < 2 ^ 256 := by have := index.isLt; omega
  have hotNow : memory.ram (word cells.hot) = word hot := by
    rw [frame _ fun r rb => word_ne layout.hotOff.1 (by omega) (layout.hotOff.2.2 r rb)]
    exact hotCell
  have labelNow : memory.ram (word (cells.vecBase + index.val)) = labelWord (labels index) := by
    rw [frame _ fun r rb => word_ne (by have := index.isLt; omega) (by omega) (by
      have := index.isLt; omega)]
    exact vecCells index
  obtain ⟨m1, run1, ram1, bits1, rA1, regs1⟩ := exec_foldTest cells index.val memory hot hotNow
  unfold foldEntry
  rw [tree_seq_exec _ _ (det_foldTest cells index.val) memory m1 run1, tree_ite, rA1, liftHash_ite]
  by_cases same : index.val = hot
  · rw [if_pos ((word_xor_eq_zero hotSmall indexSmall).mpr same.symm), if_pos same]
    refine .leaf ⟨fun r bound notSkip => ?_, ?_, fun address off => ?_, ?_,
      fun register outside => ?_⟩
    · have rSmall : r < index.val := by omega
      rw [ram1, Vector.getElem_push_lt rSmall]
      exact mats r rSmall notSkip
    · rw [regs1 rD (by decide) (by decide) (by decide), xorReg, xorSkip_push, if_pos same]
    · rw [ram1]
      exact frame address off
    · rw [bits1]
      exact bitsSame
    · rw [regs1 register (ne_of_not_clobbered outside rA (by simp))
        (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp))]
      exact regs register outside
  · rw [if_neg (fun zero => same ((word_xor_eq_zero hotSmall indexSmall).mp zero).symm),
      if_neg same]
    obtain ⟨m2, run2, ram2, bits2, input2, regs2⟩ :=
      exec_entryInput cells.asTree (tagOf index.val) index.val m1 (labels index)
        (by show m1.ram (word (cells.vecBase + index.val)) = _; rw [ram1]; exact labelNow)
        (tagSmall _ index.isLt)
    have hashSmall : hashInput (embed (labels index)) (tagOf index.val) < 2 ^ 256 := by
      unfold hashInput
      simp only [show ∀ l : Label, (embed l).toNat = l.toNat from Narrow.embed_toNat]
      have : (labels index).toNat < 2 ^ 101 := (labels index).isLt
      have := tagSmall _ index.isLt
      omega
    unfold entryHash
    rw [tree_seq_exec _ _ (det_entryInput cells.asTree (tagOf index.val) index.val) m1 m2 run2,
      tree_query_hash _ m2 _ hashSmall input2, liftHash_hLabelM]
    refine .node _ fun answer => ?_
    have rawFirst : (writePair m2 rFirst rSecond (blockWord answer.1, blockWord answer.2)).registers
        rFirst = blockWord answer.1 := by
      rw [writePair_reg, if_neg (by decide), if_pos rfl]
    obtain ⟨mClip, runClip, ramClip, bitsClip, firstReg, regsClip⟩ :=
      exec_clipReg rFirst (by decide)
        (writePair m2 rFirst rSecond (blockWord answer.1, blockWord answer.2)) answer.1 rawFirst
    rw [tree_seq_exec _ _ (det_clipReg rFirst) _ mClip runClip,
      tree_eq_exec _ (det_entryStore cells.asTree index.val)]
    obtain ⟨m3, run3, ram3, bits3, rD3, regs3⟩ := exec_entryStore cells.asTree index.val mClip
    rw [run3]
    have matSmall : cells.matBase + index.val < 2 ^ 256 := by have := index.isLt; omega
    refine .leaf ⟨fun r bound notSkip => ?_, ?_, fun address off => ?_, ?_,
      fun register outside => ?_⟩
    · show m3.ram (word (cells.matBase + r)) = _
      rw [ram3, firstReg, ramClip, writePair_ram, ram2, ram1]
      by_cases last : r = index.val
      · subst last
        rw [show (cells.asTree).matBase + index.val = cells.matBase + index.val from rfl,
          Function.update_self, Vector.getElem_push_eq]
      · have rSmall : r < index.val := by omega
        rw [show (cells.asTree).matBase + index.val = cells.matBase + index.val from rfl,
          Function.update_of_ne (word_ne (by omega) matSmall (by omega)), Vector.getElem_push_lt rSmall]
        exact mats r rSmall notSkip
    · rw [rD3, firstReg, regsClip rD (by decide) (by decide), writePair_reg, if_neg (by decide), if_neg (by decide),
        regs2 rD (by decide) (by decide) (by decide), regs1 rD (by decide) (by decide) (by decide),
        xorReg, labelWord_xor, xorSkip_push, if_neg same]
    · rw [ram3, show (cells.asTree).matBase + index.val = cells.matBase + index.val from rfl,
        Function.update_of_ne (off index.val index.isLt), ramClip, writePair_ram, ram2, ram1]
      exact frame address off
    · rw [bits3, bitsClip, writePair_bits, bits2, bits1]
      exact bitsSame
    · rw [regs3 register (ne_of_not_clobbered outside rD (by simp))
          (ne_of_not_clobbered outside rAddr (by simp)),
        regsClip register (ne_of_not_clobbered outside rFirst (by simp))
          (ne_of_not_clobbered outside rB (by simp)), writePair_reg,
        if_neg (ne_of_not_clobbered outside rSecond (by simp)),
        if_neg (ne_of_not_clobbered outside rFirst (by simp)),
        regs2 register (ne_of_not_clobbered outside rInput (by simp))
          (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp)),
        regs1 register (ne_of_not_clobbered outside rA (by simp))
          (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp))]
      exact regs register outside

/-- **One fold** against the evaluator's `foldEvalM`: the cold residues asked in ascending order,
the hot material recovered, the vector updated in place, under the frame of the schema. -/
theorem agree_foldStep (cells : FoldCells) (m s j : Nat) (layout : FoldLayout cells m j)
    (tagOf : Nat → Nat) (hot : Nat) (hotLt : hot < m) (bitLabel join : Label)
    (labels : Fin m → Label) (memory : Memory)
    (hotCell : memory.ram (word cells.hot) = word hot)
    (vecCells : ∀ ρ : Fin m, memory.ram (word (cells.vecBase + ρ.val)) = labelWord (labels ρ))
    (joinCell : memory.ram (word (cells.join j)) = labelWord join)
    (bitCell : memory.ram (word (cells.bit j)) = labelWord bitLabel)
    (tagSmall : ∀ ρ, ρ < m → tagOf ρ < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (vec : Fin m → Label) after =>
        (∀ ρ : Fin m, after.ram (word (cells.vecBase + ρ.val)) = labelWord (vec ρ)) ∧
          Frame (foldWrites cells m) treeStepClobbers memory after)
      ((foldStep cells m s j tagOf).tree memory)
      (liftHash (foldEvalM m tagOf s hot bitLabel join labels)) := by
  have below := layout.vecBelow
  have fits := layout.matFits
  have mPos := layout.mPos
  have mSmall := layout.mSmall
  set m0 := setReg memory rD (word 0) with m0Def
  unfold foldStep foldEvalM tableM
  rw [tree_seq_exec (cst rD 0) _ trivial memory m0 rfl, tree_seq, TreeLaws.monad_bind,
    TreeLaws.monad_bind, liftHash_bind, liftHash_bind, liftHash_vector, TreeLaws.bind_assoc]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_rep_vector_plain (foldEntry cells tagOf) (FoldEntryInv cells m hot m0) m _
      (fun index values current holds =>
        agree_foldEntry cells m j layout tagOf hot hotLt labels m0 hotCell vecCells tagSmall index
          values current holds)
      m0 ⟨fun r bound => absurd bound (Nat.not_lt_zero _), by
        rw [m0Def, reg_setReg, if_pos rfl]
        unfold xorSkip
        rw [Fin.foldl_zero]
        rfl,
        fun _ _ => rfl, rfl, fun _ _ => rfl⟩)
  obtain ⟨mats, xorReg, frame, bitsSame, regs⟩ := inv
  have offMat : ∀ x, x < 2 ^ 256 → (∀ r, r < m → x ≠ cells.matBase + r) →
      after.ram (word x) = memory.ram (word x) := fun x small off =>
    frame _ fun r rb => word_ne small (by omega) (off r rb)
  have hotNow : after.ram (word cells.hot) = word hot := by
    rw [offMat _ layout.hotOff.1 layout.hotOff.2.2]; exact hotCell
  have joinNow : after.ram (word (cells.join j)) = labelWord join := by
    rw [offMat _ layout.joinOff.1 layout.joinOff.2.2]; exact joinCell
  have bitNow : after.ram (word (cells.bit j)) = labelWord bitLabel := by
    rw [offMat _ layout.bitOff.1 layout.bitOff.2.2]; exact bitCell
  obtain ⟨m3, run3, ram3, bits3, regs3⟩ := exec_foldRecover cells j after hot (xorSkip hot values) join
    bitLabel (by omega) (by omega) xorReg joinNow bitNow hotNow
  rw [tree_seq_exec _ _ (det_foldRecover cells j) after m3 run3,
    tree_eq_exec _ (det_foldUpdates cells m s)]
  obtain ⟨m4, run4, cells4, frame4, bits4, regs4⟩ := exec_foldUpdates cells m s m3 below fits mPos m le_rfl
  rw [run4]
  have matCell : ∀ r (rb : r < m), m3.ram (word (cells.matBase + r)) =
      labelWord (if r = hot then bitLabel ^^^ join ^^^
        Fin.foldl m (fun acc other => if other.val = hot then acc else acc ^^^ values.get other) 0
        else values.get ⟨r, rb⟩) := by
    intro r rb
    rw [ram3]
    by_cases isHot : r = hot
    · subst isHot
      rw [if_pos rfl, Function.update_self]
      congr 1
      show xorSkip r values ^^^ join ^^^ bitLabel = _
      unfold xorSkip
      simp only [Vector.get_eq_getElem, Fin.getElem_fin]
      rw [BitVec.xor_comm _ bitLabel, BitVec.xor_assoc, BitVec.xor_comm _ join, ← BitVec.xor_assoc]
    · rw [if_neg isHot, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
        mats r rb isHot, Vector.get_eq_getElem]
  have vecCell3 : ∀ r (rb : r < m), m3.ram (word (cells.vecBase + r)) = labelWord (labels ⟨r, rb⟩) := by
    intro r rb
    rw [ram3, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
      offMat _ (by omega) (fun r' rb' => by omega)]
    exact vecCells ⟨r, rb⟩
  refine .leaf ⟨fun ρ => ?_, ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩
  · have ρb := ρ.isLt
    rw [cells4 ρ.val ρb, vecCell3 ρ.val ρb, matCell ρ.val ρb,
      matCell (foldSourceNat m s ρ.val) (Nat.mod_lt _ mPos), labelWord_xor, labelWord_xor]
    rfl
  · have notVec : ∀ r, r < m → address ≠ word (cells.vecBase + r) :=
      fun r rb same => outside (Or.inl ⟨r, rb, same⟩)
    have notMat : ∀ r, r < m → address ≠ word (cells.matBase + r) :=
      fun r rb same => outside (Or.inr ⟨r, rb, same⟩)
    rw [frame4 address notVec, ram3, Function.update_of_ne (notMat hot hotLt), frame address notMat]
    rfl
  · rw [bits4, bits3, bitsSame]
    rfl
  · rw [regs4 register (ne_of_not_clobbered outside rC (by simp))
        (ne_of_not_clobbered outside rE (by simp)) (ne_of_not_clobbered outside rAddr (by simp)),
      regs3 register outside, regs register outside, m0Def, reg_setReg,
      if_neg (ne_of_not_clobbered outside rD (by simp))]

/-! ### The folds of one modulus -/

theorem tree_rep_cons (count : Nat) (body : Nat → Prog) (memory : Memory) :
    (Prog.rep (count + 1) body).tree (FixedIndex := FixedIndex) (EncIndex := EncIndex) memory =
      bindOpt ((body 0).tree memory) (Prog.rep count fun index => body (index + 1)).tree := by
  induction count generalizing memory with
  | zero =>
      rw [Prog.rep, Prog.rep, Prog.rep, tree_seq]
      show bindOpt (.pure (some memory)) _ = _
      exact (bindOpt_pure_right _).symm
  | succ count ih =>
      rw [Prog.rep, tree_seq, ih, Prog.rep, bindOpt_assoc]
      rfl

/-- **The folds of one modulus** at bit positions `start, …, start + count - 1` against the
evaluator's `foldsEvalM`: the final vector and the final hot index in RAM, under the frame of the
vector, the materials and the hot cell. -/
theorem agree_foldsLoop (cells : FoldCells) (m : Nat) (tagOf : Nat → Nat → Nat) (value : Nat)
    (valueSmall : value < 2 ^ 256) (bitLabel join : Nat → Label)
    (sigmaOff : cells.sigma < 2 ^ 256 ∧ cells.sigma ≠ cells.hot ∧
      (∀ r, r < m → cells.sigma ≠ cells.vecBase + r) ∧ ∀ r, r < m → cells.sigma ≠ cells.matBase + r) :
    ∀ (count start hot : Nat) (labels : Fin m → Label) (memory : Memory),
      start + count ≤ 256 →
      (∀ k, k < count → FoldLayout cells m (start + k)) →
      hot < m →
      memory.ram (word cells.sigma) = word value →
      memory.ram (word cells.hot) = word hot →
      (∀ ρ : Fin m, memory.ram (word (cells.vecBase + ρ.val)) = labelWord (labels ρ)) →
      (∀ k, k < count → memory.ram (word (cells.join (start + k))) = labelWord (join (start + k))) →
      (∀ k, k < count → memory.ram (word (cells.bit (start + k))) = labelWord (bitLabel (start + k))) →
      (∀ k ρ, k < count → ρ < m → tagOf (start + k) ρ < 2 ^ 127) →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
        (fun (result : (Fin m → Label) × Nat) after =>
          (∀ ρ : Fin m, after.ram (word (cells.vecBase + ρ.val)) = labelWord (result.1 ρ)) ∧
            after.ram (word cells.hot) = word result.2 ∧
            Frame (foldsWrites cells m) treeStepClobbers memory after)
        ((foldsLoop cells m start count tagOf).tree memory)
        (liftHash (foldsEvalM m tagOf value bitLabel join count start hot labels))
  | 0, start, hot, labels, memory, _, _, hotLt, _, hotCell, vecCells, _, _, _ => by
      unfold foldsLoop
      rw [Prog.rep]
      exact .leaf ⟨vecCells, hotCell, Frame.refl _ _ memory⟩
  | count + 1, start, hot, labels, memory, bound, layouts, hotLt, sigmaCell, hotCell, vecCells,
      joinCells, bitCells, tagSmall => by
      have layout := layouts 0 (by omega)
      rw [Nat.add_zero] at layout
      have mPos := layout.mPos
      have mSmall := layout.mSmall
      have below := layout.vecBelow
      have fits := layout.matFits
      unfold foldsLoop
      rw [tree_rep_cons, tree_seq, bindOpt_assoc]
      simp only [Nat.add_zero]
      rw [show foldsEvalM m tagOf value bitLabel join (count + 1) start hot labels =
          (foldEvalM m (tagOf start) (foldShift m start) hot (bitLabel start) (join start) labels >>=
            fun next => foldsEvalM m tagOf value bitLabel join count (start + 1)
              ((hot + (if value.testBit start then foldShift m start else 0)) % m) next) from rfl,
        TreeLaws.monad_bind, liftHash_bind]
      refine Agree.bindOpt (fun vec after post => ?_)
        (agree_foldStep cells m (2 ^ start % m) start layout (tagOf start) hot hotLt (bitLabel start)
          (join start) labels memory hotCell vecCells
          (by simpa using joinCells 0 (by omega)) (by simpa using bitCells 0 (by omega))
          (fun ρ ρb => by simpa using tagSmall 0 ρ (by omega) ρb))
      obtain ⟨vecAfter, frameF⟩ := post
      have offFold : ∀ x, x < 2 ^ 256 → (∀ r, r < m → x ≠ cells.vecBase + r) →
          (∀ r, r < m → x ≠ cells.matBase + r) → after.ram (word x) = memory.ram (word x) :=
        fun x small offV offM => frameF.ram _ (by
          rintro (⟨r, rb, same⟩ | ⟨r, rb, same⟩) <;> dsimp only at rb same
          · exact offV r rb (word_inj small (by omega) same)
          · exact offM r rb (word_inj small (by omega) same))
      have sigmaNow : after.ram (word cells.sigma) = word value := by
        rw [offFold _ sigmaOff.1 sigmaOff.2.2.1 sigmaOff.2.2.2]; exact sigmaCell
      have hotNow : after.ram (word cells.hot) = word hot := by
        rw [offFold _ layout.hotOff.1 layout.hotOff.2.1 layout.hotOff.2.2]; exact hotCell
      obtain ⟨m2, run2, ram2, bits2, regs2⟩ := exec_hotUpdate cells m start after value hot mPos mSmall
        hotLt valueSmall (by omega) sigmaNow hotNow
      rw [tree_eq_exec _ (det_hotUpdate cells m (2 ^ start % m) start), run2]
      show Agree _ ((Prog.rep count fun index =>
          Prog.seq (foldStep cells m (2 ^ (start + (index + 1)) % m) (start + (index + 1))
            (tagOf (start + (index + 1))))
            (hotUpdate cells m (2 ^ (start + (index + 1)) % m) (start + (index + 1)))).tree m2) _
      have sameLoop : (fun index => Prog.seq (foldStep cells m (2 ^ (start + (index + 1)) % m)
            (start + (index + 1)) (tagOf (start + (index + 1))))
            (hotUpdate cells m (2 ^ (start + (index + 1)) % m) (start + (index + 1)))) =
          fun index => Prog.seq (foldStep cells m (2 ^ (start + 1 + index) % m) (start + 1 + index)
            (tagOf (start + 1 + index)))
            (hotUpdate cells m (2 ^ (start + 1 + index) % m) (start + 1 + index)) := by
        funext index
        rw [show start + (index + 1) = start + 1 + index by omega]
      rw [sameLoop]
      have hot'Lt : (hot + (if value.testBit start then foldShift m start else 0)) % m < m :=
        Nat.mod_lt _ mPos
      have hotAfter : m2.ram (word cells.hot) =
          word ((hot + (if value.testBit start then foldShift m start else 0)) % m) := by
        rw [ram2, Function.update_self]
      have keep2 : ∀ x, x ≠ cells.hot → x < 2 ^ 256 → cells.hot < 2 ^ 256 →
          m2.ram (word x) = after.ram (word x) := fun x ne small hotSmall => by
        rw [ram2, Function.update_of_ne (word_ne small hotSmall ne)]
      have rest := agree_foldsLoop cells m tagOf value valueSmall bitLabel join sigmaOff count (start + 1)
        ((hot + (if value.testBit start then foldShift m start else 0)) % m) vec m2 (by omega)
        (fun k kb => by rw [show start + 1 + k = start + (k + 1) by omega]; exact layouts (k + 1) (by omega))
        hot'Lt
        (by rw [keep2 _ sigmaOff.2.1 sigmaOff.1 layout.hotOff.1]; exact sigmaNow) hotAfter
        (fun ρ => by
          rw [keep2 _ (fun same => layout.hotOff.2.1 ρ.val ρ.isLt same.symm) (by omega) layout.hotOff.1]
          exact vecAfter ρ)
        (fun k kb => by
          have lay := layouts (k + 1) (by omega)
          rw [show start + 1 + k = start + (k + 1) by omega] at *
          rw [keep2 _ lay.joinHot lay.joinOff.1 lay.hotOff.1,
            offFold _ lay.joinOff.1 lay.joinOff.2.1 lay.joinOff.2.2]
          exact joinCells (k + 1) (by omega))
        (fun k kb => by
          have lay := layouts (k + 1) (by omega)
          rw [show start + 1 + k = start + (k + 1) by omega] at *
          rw [keep2 _ lay.bitHot lay.bitOff.1 lay.hotOff.1,
            offFold _ lay.bitOff.1 lay.bitOff.2.1 lay.bitOff.2.2]
          exact bitCells (k + 1) (by omega))
        (fun k ρ kb ρb => by
          rw [show start + 1 + k = start + (k + 1) by omega]; exact tagSmall (k + 1) ρ (by omega) ρb)
      refine rest.mono fun result final post => ?_
      obtain ⟨vecFinal, hotFinal, frameR⟩ := post
      refine ⟨vecFinal, hotFinal, (frameF.trans (Frame.trans ⟨fun address outside => by
          rw [ram2, Function.update_of_ne (fun same => outside same)], bits2, regs2⟩ frameR)).mono
        ?_ fun register inside => ?_⟩
      · rintro address (inside | (inside | inside))
        · exact Or.inl inside
        · exact Or.inr inside
        · exact inside
      · rcases inside with inside | inside | inside <;> exact inside

end Agreement

end Kriterion.CRT.SimMachine

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### The reindex and the first hot index -/

/-- The reindex fold over the first `k` leaves. -/
def reindexPartial (labels : Nat → Label) (m ρ k : Nat) : Label :=
  Fin.foldl k (fun acc (leaf : Fin k) => if leaf.val % m = ρ then acc ^^^ labels leaf.val else acc) 0

theorem reindexPartial_succ (labels : Nat → Label) (m ρ k : Nat) :
    reindexPartial labels m ρ (k + 1) =
      if k % m = ρ then reindexPartial labels m ρ k ^^^ labels k else reindexPartial labels m ρ k := by
  unfold reindexPartial
  rw [Fin.foldl_succ_last]
  simp only [Fin.val_last, Fin.val_castSucc]

/-- The construction's `reindex` is the full partial fold. -/
theorem reindex_eq_partial (n : Nat) (labels : Fin (2 ^ n) → Label) (m : Nat) (ρ : Fin m) :
    reindex n labels m ρ =
      reindexPartial (fun j => if h : j < 2 ^ n then labels ⟨j, h⟩ else 0) m ρ.val (2 ^ n) := by
  unfold reindex reindexPartial stored
  beta_reduce
  congr 1
  funext acc leaf
  rw [dif_pos leaf.isLt]

private theorem exec_reindexResidue (levelBase vecBase n m ρ : Nat) (memory : Memory)
    (labels : Nat → Label) (nSmall : n ≤ 20) (fits : levelBase + 2 ^ n < 2 ^ 256)
    (vecSmall : vecBase + ρ < 2 ^ 256)
    (levelCells : ∀ j, j < 2 ^ n → memory.ram (word (levelBase + j)) = labelWord (labels j)) :
    ∃ after, (reindexResidue levelBase vecBase n m ρ).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (vecBase + ρ))
        (labelWord (reindexPartial labels m ρ (2 ^ n))) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rC → register ≠ rD → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set m0 := setReg memory rD (word 0) with m0Def
  obtain ⟨m1, run1, acc1, ram1, bits1, regs1⟩ := Prog.exec_rep (reindexStep levelBase m ρ)
    (fun k current => current.registers rD = labelWord (reindexPartial labels m ρ k) ∧
      current.ram = memory.ram ∧ current.bits = memory.bits ∧
      ∀ register, register ≠ rC → register ≠ rD → register ≠ rAddr →
        current.registers register = memory.registers register)
    (2 ^ n) (fun k kb current holds => by
      obtain ⟨acc, ram, bits, regs⟩ := holds
      by_cases member : k % m = ρ
      · refine ⟨_, by rw [reindexStep, if_pos member]; rfl, ?_, by simp only [ram_setReg]; exact ram,
          by simp only [bits_setReg]; exact bits, fun register n1 n2 n3 => ?_⟩
        · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte]
          rw [eval_xor, acc, ram, levelCells k kb, labelWord_xor, reindexPartial_succ, if_pos member]
        · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3]
          exact regs register n1 n2 n3
      · refine ⟨current, by rw [reindexStep, if_neg member]; rfl, ?_, ram, bits, regs⟩
        rw [acc, reindexPartial_succ, if_neg member])
    m0 ⟨by rw [m0Def, reg_setReg, if_pos rfl]; unfold reindexPartial; rw [Fin.foldl_zero]; rfl,
      rfl, rfl, fun register n1 n2 n3 => by rw [m0Def, reg_setReg, if_neg n2]⟩
  have runAll : (reindexResidue levelBase vecBase n m ρ).exec memory = some (storeRam (setReg m1 rAddr
      (word (vecBase + ρ))) (word (vecBase + ρ)) (m1.registers rD)) := by
    rw [show reindexResidue levelBase vecBase n m ρ = .seq (cst rD 0)
        (.seq (Prog.rep (2 ^ n) (reindexStep levelBase m ρ)) (storeAt (vecBase + ρ) rD)) from rfl,
      exec_cst_seq, ← m0Def, Prog.exec_seq_some _ _ m0 m1 run1]
    show (Prog.seq (cst rAddr (vecBase + ρ)) (.op (.store rAddr rD))).exec m1 = _
    rfl
  refine ⟨_, runAll, ?_, ?_, fun register n1 n2 n3 => ?_⟩
  · rw [ram_storeRam, ram_setReg, ram1, acc1]
  · rw [bits_storeRam, bits_setReg, bits1]
  · rw [reg_storeRam, reg_setReg, if_neg n3, regs1 register n1 n2 n3]

/-- **The reindex**: residue `ρ < m` holds `reindex n labels m ρ`. -/
theorem exec_reindexBlock (levelBase vecBase n m : Nat) (memory : Memory) (labels : Fin (2 ^ n) → Label)
    (nSmall : n ≤ 20) (levelFits : levelBase + 2 ^ n < 2 ^ 256) (vecFits : vecBase + m < 2 ^ 256)
    (apart : ∀ j, j < 2 ^ n → ∀ ρ, ρ < m → levelBase + j ≠ vecBase + ρ)
    (levelCells : ∀ j : Fin (2 ^ n), memory.ram (word (levelBase + j.val)) = labelWord (labels j)) :
    ∃ after, (reindexBlock levelBase vecBase n m).exec memory = some after ∧
      (∀ ρ : Fin m, after.ram (word (vecBase + ρ.val)) = labelWord (reindex n labels m ρ)) ∧
      (∀ address, (∀ ρ, ρ < m → address ≠ word (vecBase + ρ)) → after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rC → register ≠ rD → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set labels' : Nat → Label := fun j => if h : j < 2 ^ n then labels ⟨j, h⟩ else 0 with labelsDef
  have cells' : ∀ j, j < 2 ^ n → memory.ram (word (levelBase + j)) = labelWord (labels' j) :=
    fun j jb => by rw [labelsDef]; simp only [dif_pos jb]; exact levelCells ⟨j, jb⟩
  obtain ⟨after, run, done, frame, bits, regs⟩ := Prog.exec_rep (reindexResidue levelBase vecBase n m)
    (fun k current =>
      (∀ ρ, ρ < k → current.ram (word (vecBase + ρ)) = labelWord (reindexPartial labels' m ρ (2 ^ n))) ∧
      (∀ address, (∀ ρ, ρ < m → address ≠ word (vecBase + ρ)) → current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧
      ∀ register, register ≠ rC → register ≠ rD → register ≠ rAddr →
        current.registers register = memory.registers register)
    m (fun k kb current holds => by
      obtain ⟨done, frame, bits, regs⟩ := holds
      obtain ⟨next, step, ram, bitsN, regsN⟩ := exec_reindexResidue levelBase vecBase n m k current
        labels' nSmall levelFits (by omega)
        (fun j jb => by
          rw [frame _ fun ρ ρb => word_ne (by omega) (by omega) (apart j jb ρ ρb)]
          exact cells' j jb)
      refine ⟨next, step, fun ρ ρb => ?_, fun address off => ?_, by rw [bitsN, bits],
        fun register n1 n2 n3 => by rw [regsN register n1 n2 n3, regs register n1 n2 n3]⟩
      · rw [ram]
        by_cases last : ρ = k
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done ρ (by omega)
      · rw [ram, Function.update_of_ne (off k kb)]
        exact frame address off)
    memory ⟨fun ρ ρb => absurd ρb (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ _ _ => rfl⟩
  refine ⟨after, run, fun ρ => ?_, frame, bits, regs⟩
  rw [done ρ.val ρ.isLt, reindex_eq_partial]

/-- **The first hot index**: `hot := (σ mod 2 ^ keep) mod m`. -/
theorem exec_hotInit (cells : FoldCells) (keep m : Nat) (memory : Memory) (value : Nat)
    (valueSmall : value < 2 ^ 256) (keepSmall : keep ≤ 16) (mPos : 0 < m) (mSmall : m < 2 ^ 256)
    (sigmaCell : memory.ram (word cells.sigma) = word value) :
    ∃ after, (hotInit cells keep m).exec memory = some after ∧
      after.ram = Function.update memory.ram (word cells.hot) (word (value % 2 ^ keep % m)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rOut → register ≠ rB → register ≠ rD →
        register ≠ rE → register ≠ rF → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have lowSmall : value % 2 ^ keep < 2 ^ 16 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) keepSmall)
  set m1 := setReg (setReg (setReg (setReg memory rAddr (word cells.sigma)) rAcc
    (memory.ram (word cells.sigma))) rB (word (2 ^ keep - 1))) rAcc
    (Arithmetic.and.eval (memory.ram (word cells.sigma)) (word (2 ^ keep - 1))) with m1Def
  have run1 : (Prog.seq (loadAt rAcc cells.sigma) (.seq (cst rB (2 ^ keep - 1))
      (ar .and rAcc rAcc rB))).exec memory = some m1 := rfl
  have acc1 : m1.registers rAcc = word (value % 2 ^ keep) := by
    rw [m1Def, reg_setReg, if_pos rfl, sigmaCell, eval_and_pow _ _ valueSmall (by omega)]
  obtain ⟨m2, run2, out2, ram2, bits2, regs2⟩ := exec_barrett rAcc rOut m 16 (value % 2 ^ keep) m1
    (by decide) (by decide) (by decide) (by decide) (by decide) acc1
    lowSmall mPos mSmall (by norm_num)
  have runAll : (hotInit cells keep m).exec memory = some (storeRam (setReg m2 rAddr (word cells.hot))
      (word cells.hot) (m2.registers rOut)) := by
    rw [show hotInit cells keep m = .seq (.seq (loadAt rAcc cells.sigma) (.seq (cst rB (2 ^ keep - 1))
        (ar .and rAcc rAcc rB))) (.seq (barrett rAcc rOut m 16) (storeAt cells.hot rOut)) from rfl,
      Prog.exec_seq_some _ _ memory m1 run1, Prog.exec_seq_some _ _ m1 m2 run2]
    rfl
  refine ⟨_, runAll, ?_, ?_, fun register n1 n2 n3 n4 n5 n6 n7 => ?_⟩
  · rw [ram_storeRam, ram_setReg, out2, ram2, m1Def]
    rfl
  · rw [bits_storeRam, bits_setReg, bits2, m1Def]
    rfl
  · rw [reg_storeRam, reg_setReg, if_neg n7, regs2 register n2 n4 n5 n6, m1Def, reg_setReg, if_neg n1,
      reg_setReg, if_neg n3, reg_setReg, if_neg n1, reg_setReg, if_neg n7]

end Kriterion.CRT.SimMachine
