/-
**The replay of the body of one modulus agrees with the evaluator's `bodyEvalM`**
(`agree_bodyBlock`), with the pad reading of `padVectorM` done by `fracDigits`.
-/

import Proof.Simulator.CRT.ReplayCast
import Proof.Simulator.CRT.Garner
import Construction.Simulator.CRT.ReplayBody
import Construction.CRT.Body

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### The layout and the sums -/

/-- The layout of one modulus's body: one chain (inputs, then scratch, then outputs). -/
structure BodyChain (bc : BodyCells) (m S q : Nat) : Prop where
  mPos : 0 < m
  mSmall : m ≤ 2 ^ 10
  joinBelow : bc.joinBase + S ≤ bc.vecBase
  vecBelow : bc.vecBase + m ≤ bc.hot
  hotBelow : bc.hot < bc.ansBase
  ansBelow : bc.ansBase + 2 * q ≤ bc.digBase
  digBelow : bc.digBase + S ≤ bc.accA
  accABelow : bc.accA + S ≤ bc.accB
  accBBelow : bc.accB + S ≤ bc.outBase
  outFits : bc.outBase + S < 2 ^ 256

/-- `B_e` after the slots of `values`: the sum of their digits, the hot slot skipped. -/
def accSumB {S n : Nat} (values : Vector (Fin S → Nat) n) (hot : Nat) (e : Fin S) : Nat :=
  ∑ k : Fin n, if k.val = hot then 0 else values.get k e

/-- `A_e` after the slots of `values`: the digits weighted by their slot. -/
def accSumA {S n : Nat} (values : Vector (Fin S → Nat) n) (hot : Nat) (e : Fin S) : Nat :=
  ∑ k : Fin n, if k.val = hot then 0 else k.val * values.get k e

theorem accSumB_push {S n : Nat} (values : Vector (Fin S → Nat) n) (hot : Nat) (x : Fin S → Nat)
    (e : Fin S) : accSumB (values.push x) hot e = accSumB values hot e + (if n = hot then 0 else x e) := by
  unfold accSumB
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Vector.get_eq_getElem, Fin.coe_castSucc,
    Vector.getElem_push_eq]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [Vector.getElem_push_lt k.isLt]

theorem accSumA_push {S n : Nat} (values : Vector (Fin S → Nat) n) (hot : Nat) (x : Fin S → Nat)
    (e : Fin S) : accSumA (values.push x) hot e = accSumA values hot e + (if n = hot then 0 else n * x e) := by
  unfold accSumA
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Vector.get_eq_getElem, Fin.coe_castSucc,
    Vector.getElem_push_eq]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [Vector.getElem_push_lt k.isLt]

theorem accSumB_le {S n : Nat} (values : Vector (Fin S → Nat) n) (hot m : Nat) (e : Fin S)
    (small : ∀ k : Fin n, values.get k e < m) : accSumB values hot e ≤ n * m := by
  unfold accSumB
  calc ∑ k : Fin n, (if k.val = hot then 0 else values.get k e)
      ≤ ∑ _k : Fin n, m := sum_le_sum fun k _ => by split <;> [omega; exact (small k).le]
    _ = n * m := by simp

theorem accSumA_le {S n : Nat} (values : Vector (Fin S → Nat) n) (hot m : Nat) (e : Fin S)
    (small : ∀ k : Fin n, values.get k e < m) : accSumA values hot e ≤ n * (n * m) := by
  unfold accSumA
  calc ∑ k : Fin n, (if k.val = hot then 0 else k.val * values.get k e)
      ≤ ∑ _k : Fin n, n * m := sum_le_sum fun k _ => by
        split
        · omega
        · exact Nat.mul_le_mul k.isLt.le (small k).le
    _ = n * (n * m) := by simp

/-! ### The accumulation -/

private theorem exec_bodyAccum (bc : BodyCells) (S ρ e : Nat) (memory : Memory) (d a b : Nat)
    (digCell : memory.ram (word (bc.digBase + (S - 1 - e))) = word d)
    (aCell : memory.ram (word (bc.accA + e)) = word a)
    (bCell : memory.ram (word (bc.accB + e)) = word b)
    (dSmall : d < 2 ^ 64) (aSmall : a < 2 ^ 128) (bSmall : b < 2 ^ 128) (ρSmall : ρ < 2 ^ 64)
    (apart : bc.accA + e ≠ bc.accB + e) (aFits : bc.accA + e < 2 ^ 256)
    (bFits : bc.accB + e < 2 ^ 256) :
    ∃ after, (bodyAccum bc S ρ e).exec memory = some after ∧
      after.ram = Function.update (Function.update memory.ram (word (bc.accB + e)) (word (b + d)))
        (word (bc.accA + e)) (word (a + d * ρ)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have bdSmall : b + d < 2 ^ 256 := by
    have : (2 : Nat) ^ 128 + 2 ^ 64 < 2 ^ 256 := by norm_num
    omega
  have dρSmall : d * ρ < 2 ^ 256 := by
    calc d * ρ < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' dSmall ρSmall
      _ < 2 ^ 256 := by norm_num
  have adSmall : a + d * ρ < 2 ^ 256 := by
    have : d * ρ < 2 ^ 128 := by
      calc d * ρ < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' dSmall ρSmall
        _ = 2 ^ 128 := by norm_num
    have : (2 : Nat) ^ 128 + 2 ^ 128 < 2 ^ 256 := by norm_num
    omega
  obtain ⟨m1, run1, ram1, bits1, rA1, regs1⟩ : ∃ m1, (bodyAccumB bc S e).exec memory = some m1 ∧
      m1.ram = Function.update memory.ram (word (bc.accB + e)) (word (b + d)) ∧
      m1.bits = memory.bits ∧ m1.registers rA = word d ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        m1.registers register = memory.registers register := by
    refine ⟨_, rfl, ?_, rfl, ?_, fun register n1 n2 n3 => ?_⟩
    · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte,
        digCell, bCell]
      rw [eval_add_word _ _ bdSmall]
    · simp (config := { decide := true }) only [reg_storeRam, reg_setReg, ram_setReg, reduceIte,
        digCell]
    · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2, if_neg n3]
  have aNow : m1.ram (word (bc.accA + e)) = word a := by
    rw [ram1, Function.update_of_ne (word_ne aFits bFits apart)]
    exact aCell
  refine ⟨_, by rw [show bodyAccum bc S ρ e = .seq (bodyAccumB bc S e) (bodyAccumA bc ρ e) from rfl,
    Prog.exec_seq_some _ _ memory m1 run1]; rfl, ?_, ?_, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte,
      aNow, rA1]
    rw [eval_mul_word _ _ dρSmall, eval_add_word _ _ adSmall, ram1]
  · simp only [bits_storeRam, bits_setReg]
    exact bits1
  · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4]
    exact regs1 register n1 n2 n4

/-- The pad digit of encoding `e` for the answers `values` (the output of `padVectorM`). -/
def padDigit (m S q : Nat) {count : Nat} (values : Vector (Block × Block) count) (e : Nat) : Nat :=
  digit m (fractionValue m S q (packAnswers count values.get)) e

theorem padDigit_lt (m S q : Nat) (mPos : 0 < m) {count : Nat} (values : Vector (Block × Block) count)
    (e : Nat) : padDigit m S q values e < m := Nat.mod_lt _ mPos

/-- **The rest of a pad** (after its answers): the digits by `fracDigits`, then the accumulation. -/
private theorem exec_padRest [BN254.FieldCertificate] (bc : BodyCells) (m S q ρ : Nat) (chain : BodyChain bc m S q)
    (ρLt : ρ < m) (start memory : Memory) (values : Vector (Block × Block) q)
    (inv : CastInv (bc.slot ρ) q start q values memory) (a b : Nat → Nat)
    (aCells : ∀ e, e < S → memory.ram (word (bc.accA + e)) = word (a e))
    (bCells : ∀ e, e < S → memory.ram (word (bc.accB + e)) = word (b e))
    (aSmall : ∀ e, e < S → a e < 2 ^ 128) (bSmall : ∀ e, e < S → b e < 2 ^ 128) :
    ∃ after, (Prog.seq (setupConsts m) (.seq (fracDigits bc.ansBase (2 * q) S fun j => bc.digBase + j)
        (Prog.rep S (bodyAccum bc S ρ)))).exec memory = some after ∧
      (∀ e, e < S → after.ram (word (bc.accB + e)) = word (b e + padDigit m S q values e) ∧
        after.ram (word (bc.accA + e)) = word (a e + padDigit m S q values e * ρ)) ∧
      (∀ address, ¬ (Writes.region ⟨bc.ansBase, 2 * q⟩ address ∨ Writes.region ⟨bc.digBase, S⟩ address ∨
          Writes.region ⟨bc.accA, S⟩ address ∨ Writes.region ⟨bc.accB, S⟩ address) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        register ≠ rM → register ≠ rMask → register ≠ rK128 →
        after.registers register = memory.registers register := by
  have := chain.mPos; have := chain.mSmall; have := chain.joinBelow; have := chain.vecBelow
  have := chain.hotBelow; have := chain.ansBelow; have := chain.digBelow; have := chain.accABelow
  have := chain.accBBelow; have := chain.outFits
  have mBig : m < 2 ^ 128 := by
    have : (2 : Nat) ^ 10 < 2 ^ 128 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    omega
  set u := limbValue (halvesOf values) (2 * q) with uDef
  set m1 := setReg (setReg (setReg memory rM (word m)) rMask (word limbMask)) rK128 (word 128) with m1Def
  have consts : LimbConsts m1 m := ⟨by rw [m1Def, reg_setReg, if_neg (by decide), reg_setReg,
      if_neg (by decide), reg_setReg, if_pos rfl], by rw [m1Def, reg_setReg, if_neg (by decide),
      reg_setReg, if_pos rfl], by rw [m1Def, reg_setReg, if_pos rfl]⟩
  obtain ⟨m2, run2, digits2, limbs2, frame2, bits2, regs2⟩ := exec_fracDigits bc.ansBase (2 * q) S
    (fun j => bc.digBase + j) u m m1 (by omega) (fun j jb => by omega) (fun j jb k kb => by omega)
    (fun i j ib jb ne => by omega)
    (fun k kb => by
      show memory.ram _ = _
      have cell := ansCell_halves (bc.slot ρ) q start memory values inv k kb
      simp only [BodyCells.slot] at cell
      rw [cell, limbOf_limbValue _ (halvesOf_lt values) _ k kb])
    (limbValue_lt _ (halvesOf_lt values) _) consts mBig
  have digitNow : ∀ e, e < S → m2.ram (word (bc.digBase + (S - 1 - e))) =
      word (padDigit m S q values e) := fun e eb => by
    rw [digits2 (S - 1 - e) (by omega), padDigit, ← frac_digit_interface m S q _ (S - 1 - e) (by omega),
      show S - 1 - (S - 1 - e) = e by omega, packAnswers_eq_limbValue]
  have accNow : ∀ e, e < S → m2.ram (word (bc.accA + e)) = word (a e) ∧
      m2.ram (word (bc.accB + e)) = word (b e) := fun e eb => by
    constructor
    · rw [frame2 _ (fun k kb => word_ne (by omega) (by omega) (by omega))
        (fun j jb => word_ne (by omega) (by omega) (by omega))]
      exact aCells e eb
    · rw [frame2 _ (fun k kb => word_ne (by omega) (by omega) (by omega))
        (fun j jb => word_ne (by omega) (by omega) (by omega))]
      exact bCells e eb
  obtain ⟨m3, run3, inv3⟩ := Prog.exec_rep (bodyAccum bc S ρ)
    (fun k current =>
      (∀ e, e < S → (e < k → current.ram (word (bc.accB + e)) = word (b e + padDigit m S q values e) ∧
          current.ram (word (bc.accA + e)) = word (a e + padDigit m S q values e * ρ)) ∧
        (k ≤ e → current.ram (word (bc.accB + e)) = word (b e) ∧
          current.ram (word (bc.accA + e)) = word (a e))) ∧
      (∀ address, (∀ e, e < S → address ≠ word (bc.accA + e) ∧ address ≠ word (bc.accB + e)) →
        current.ram address = m2.ram address) ∧
      current.bits = m2.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        current.registers register = m2.registers register)
    S (fun k kb current holds => by
      obtain ⟨accs, frame, bits, regs⟩ := holds
      obtain ⟨bNow, aNow⟩ := (accs k kb).2 le_rfl
      have digHere : current.ram (word (bc.digBase + (S - 1 - k))) = word (padDigit m S q values k) := by
        rw [frame _ fun e eb => ⟨word_ne (by omega) (by omega) (by omega),
          word_ne (by omega) (by omega) (by omega)⟩]
        exact digitNow k kb
      obtain ⟨next, step, ram, bitsN, regsN⟩ := exec_bodyAccum bc S ρ k current
        (padDigit m S q values k) (a k) (b k) digHere aNow bNow
        (lt_of_lt_of_le (padDigit_lt m S q (by omega) values k) (by
          have : (2 : Nat) ^ 10 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
          omega))
        (aSmall k kb) (bSmall k kb) (by
          have : (2 : Nat) ^ 10 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
          omega) (by omega) (by omega) (by omega)
      refine ⟨next, step, fun e eb => ⟨fun lt => ?_, fun le => ?_⟩, fun address off => ?_,
        by rw [bitsN, bits], fun register n1 n2 n3 n4 => by
          rw [regsN register n1 n2 n3 n4, regs register n1 n2 n3 n4]⟩
      · rw [ram]
        by_cases last : e = k
        · subst last
          refine ⟨?_, Function.update_self ..⟩
          rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
            Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
            Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
            Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact (accs e eb).1 (by omega)
      · rw [ram, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
          Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
          Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
          Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
        exact (accs e eb).2 (by omega)
      · rw [ram, Function.update_of_ne (off k kb).1, Function.update_of_ne (off k kb).2]
        exact frame address off)
    m2 ⟨fun e eb => ⟨fun lt => absurd lt (Nat.not_lt_zero _), fun _ => (accNow e eb).symm.symm |>
        fun h => ⟨h.2, h.1⟩⟩, fun _ _ => rfl, rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨accs3, frame3, bits3, regs3⟩ := inv3
  refine ⟨m3, ?_, fun e eb => (accs3 e eb).1 eb, fun address off => ?_, ?_,
    fun register n1 n2 n3 n4 n5 n6 n7 => ?_⟩
  · rw [Prog.exec_seq_some _ _ memory m1 rfl, Prog.exec_seq_some _ _ m1 m2 run2]
    exact run3
  · rw [frame3 address fun e eb => ⟨fun same => off (Or.inr (Or.inr (Or.inl ⟨e, eb, same⟩))),
        fun same => off (Or.inr (Or.inr (Or.inr ⟨e, eb, same⟩)))⟩,
      frame2 address (fun k kb same => off (Or.inl ⟨k, kb, same⟩))
        (fun j jb same => off (Or.inr (Or.inl ⟨j, jb, same⟩)))]
    rfl
  · rw [bits3, bits2]
    rfl
  · rw [regs3 register n1 n2 n3 n4, regs2 register n1 n2 n3 n4, m1Def, reg_setReg, if_neg n7,
      reg_setReg, if_neg n6, reg_setReg, if_neg n5]

section Queries

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- One answer of a long hash with any number of answers (the cast's `agree_castQuery` for a
general count). -/
theorem agree_ansQuery (cells : CastCells) (total : Nat) (ansFits : cells.ansBase + 2 * total < 2 ^ 256)
    (labelSmall : cells.label < 2 ^ 256)
    (labelOff : ∀ b, b < 2 * total → cells.label ≠ cells.ansBase + b) (tagOf : Nat → Nat) (label : Block) (start : Memory)
    (labelCell : start.ram (word cells.label) = blockWord label)
    (tagSmall : ∀ j, j < total → tagOf j < 2 ^ 127)
    (index : Fin (total)) (values : Vector (Block × Block) index.val) (memory : Memory)
    (holds : CastInv cells (total) start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : Block × Block) after =>
        CastInv cells (total) start (index.val + 1) (values.push result) after)
      ((castQuery cells (tagOf index.val) index.val).tree memory)
      (liftHash (askN (hashInput label (tagOf index.val)))) := by
  obtain ⟨done, frame, bitsSame, regs⟩ := holds
  have indexBound := index.isLt
  have labelNow : memory.ram (word cells.label) = blockWord label := by
    rw [frame _ fun b bound => word_ne labelSmall (by omega) (labelOff b bound)]
    exact labelCell
  have hashSmall : hashInput label (tagOf index.val) < 2 ^ 256 := by
    unfold hashInput
    have := label.isLt
    have := tagSmall _ index.isLt
    omega
  set m1 := setReg (setReg memory rAddr (word cells.label)) rInput (blockWord label) with m1Def
  set m2 := setReg m1 rB (word (2 ^ 128 * tagOf index.val)) with m2Def
  set m3 := setReg m2 rInput (word (hashInput label (tagOf index.val))) with m3Def
  have run1 : (loadAt rInput cells.label).exec memory = some m1 := by
    rw [exec_loadAt, labelNow]
  have run3 : (ar .add rInput rInput rB).exec m2 = some m3 := by
    rw [exec_ar_last _ _ _ _ m2 (word label.toNat) (word (2 ^ 128 * tagOf index.val))
      (by rw [m2Def, reg_setReg, if_neg (by decide), m1Def, reg_setReg, if_pos rfl]; rfl)
      (by rw [m2Def, reg_setReg, if_pos rfl]), eval_add_word _ _ hashSmall]
    rfl
  unfold castQuery
  rw [tree_seq_exec _ _ (show (loadAt rInput cells.label).OpsSatisfy Op.Det from ⟨trivial, trivial⟩)
      memory m1 run1,
    tree_seq_exec _ _ (show (cst rB (2 ^ 128 * tagOf index.val)).OpsSatisfy Op.Det from trivial) m1 m2 rfl,
    tree_seq_exec _ _ (show (ar .add rInput rInput rB).OpsSatisfy Op.Det from trivial) m2 m3 run3,
    tree_query_hash _ m3 _ hashSmall (by rw [m3Def, reg_setReg, if_pos rfl])]
  refine .node _ fun (answer : Block × Block) => ?_
  rw [tree_eq_exec _ (show (Prog.seq (storeAt (cells.ansBase + 2 * index.val) rFirst)
      (storeAt (cells.ansBase + (2 * index.val + 1)) rSecond)).OpsSatisfy Op.Det from
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩)]
  set m4 := writePair m3 rFirst rSecond (blockWord answer.1, blockWord answer.2) with m4Def
  have first4 : m4.registers rFirst = blockWord answer.1 := by
    rw [m4Def, writePair_reg, if_neg (by decide), if_pos rfl]
  have second4 : m4.registers rSecond = blockWord answer.2 := by
    rw [m4Def, writePair_reg, if_pos rfl]
  rw [exec_storeAt_seq _ _ _ m4 (by decide), exec_storeAt _ _ _ (by decide)]
  have cellNe : ∀ b c, b < 2 * total → c < 2 * total → b ≠ c →
      word (cells.ansBase + b) ≠ word (cells.ansBase + c) :=
    fun b c bb cb ne => word_ne (by omega) (by omega) (by omega)
  refine .leaf ⟨fun j bound => ?_, fun address off => ?_, ?_, fun register outside => ?_⟩
  · simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg]
    simp (config := { decide := true }) only [reduceIte]
    rw [second4, first4]
    by_cases last : j = index.val
    · subst last
      simp only [Vector.getElem_push_eq]
      refine ⟨?_, Function.update_self ..⟩
      rw [Function.update_of_ne (cellNe (2 * index.val) (2 * index.val + 1) (by omega) (by omega)
        (by omega)), Function.update_self]
    · have jSmall : j < index.val := by omega
      simp only [Vector.getElem_push_lt jSmall]
      rw [Function.update_of_ne (cellNe (2 * j) (2 * index.val + 1) (by omega) (by omega) (by omega)),
        Function.update_of_ne (cellNe (2 * j) (2 * index.val) (by omega) (by omega) (by omega)),
        Function.update_of_ne (cellNe (2 * j + 1) (2 * index.val + 1) (by omega) (by omega) (by omega)),
        Function.update_of_ne (cellNe (2 * j + 1) (2 * index.val) (by omega) (by omega) (by omega))]
      exact done j jSmall
  · simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg]
    simp (config := { decide := true }) only [reduceIte]
    rw [Function.update_of_ne (off (2 * index.val + 1) (by omega)),
      Function.update_of_ne (off (2 * index.val) (by omega))]
    exact frame address off
  · simp only [bits_storeRam, bits_setReg]
    exact bitsSame
  · simp only [reg_storeRam, reg_setReg, if_neg (ne_of_not_cast outside rAddr (by simp))]
    rw [m4Def, writePair_reg, if_neg (ne_of_not_cast outside rSecond (by simp)),
      if_neg (ne_of_not_cast outside rFirst (by simp)), m3Def, reg_setReg,
      if_neg (ne_of_not_cast outside rInput (by simp)), m2Def, reg_setReg,
      if_neg (ne_of_not_cast outside rB (by simp)), m1Def, reg_setReg,
      if_neg (ne_of_not_cast outside rInput (by simp)), reg_setReg,
      if_neg (ne_of_not_cast outside rAddr (by simp))]
    exact regs register outside


/-- **The answers of a long hash**: `castQueries` asks the `total` answers of `hlongM` in order and
stores their halves. -/
theorem agree_ansQueries (cells : CastCells) (total : Nat) (ansFits : cells.ansBase + 2 * total < 2 ^ 256)
    (labelSmall : cells.label < 2 ^ 256)
    (labelOff : ∀ b, b < 2 * total → cells.label ≠ cells.ansBase + b) (tagOf : Nat → Nat)
    (label : Block) (memory : Memory)
    (labelCell : memory.ram (word cells.label) = blockWord label)
    (tagSmall : ∀ j, j < total → tagOf j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex) (CastInv cells total memory total)
      ((castQueries cells tagOf total).tree memory)
      (FreeQuery.vector total fun j => liftHash (askN (hashInput label (tagOf j.val)))) :=
  agree_rep_vector_plain (fun j => castQuery cells (tagOf j) j) (CastInv cells total memory) total _
    (fun index values current holds =>
      agree_ansQuery cells total ansFits labelSmall labelOff tagOf label memory labelCell tagSmall index
        values current holds)
    memory ⟨fun j bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ => rfl⟩

end Queries

/-! ### One slot -/

private theorem exec_bodyTest (bc : BodyCells) (ρ : Nat) (memory : Memory) (hot : Nat)
    (hotCell : memory.ram (word bc.hot) = word hot) :
    ∃ after, (bodyTest bc ρ).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rA = word hot ^^^ word ρ ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, hotCell]
    rfl
  · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3]

private theorem det_padRest (bc : BodyCells) (m S q ρ : Nat) :
    (Prog.seq (setupConsts m) (.seq (fracDigits bc.ansBase (2 * q) S fun j => bc.digBase + j)
      (Prog.rep S (bodyAccum bc S ρ)))).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial, trivial⟩, det_fracDigits _ _ _ _, det_rep _ _ fun _ _ =>
    ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩,
      ⟨trivial, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩⟩⟩

private theorem clobbers_body (register : Register)
    (inside : register ∈ [rA, rB, rC, rAddr, rM, rMask, rK128, rInput, rFirst, rSecond]) :
    bodyClobbers register := by
  revert register inside
  simp only [bodyClobbers, Clobbers.ofList]
  decide

/-- A cell below the scratch is never written by the body. -/
theorem not_bodyWrites_below (bc : BodyCells) (m S q : Nat) (chain : BodyChain bc m S q) (x : Nat)
    (xb : x < bc.ansBase) : ¬ bodyWrites bc S q (word x) := by
  have := chain.ansBelow; have := chain.digBelow; have := chain.accABelow
  have := chain.accBBelow; have := chain.outFits
  rintro (((⟨k, kb, same⟩ | ⟨k, kb, same⟩) | (⟨k, kb, same⟩ | ⟨k, kb, same⟩)) | ⟨k, kb, same⟩) <;> dsimp only at kb same <;> exact absurd (word_inj (by omega) (by omega) same) (by omega)

/-- The invariant of the slot loop after `n` slots. -/
def BodyInv (bc : BodyCells) (m S q hot : Nat) (start : Memory) (n : Nat)
    (values : Vector (Fin S → Nat) n) (memory : Memory) : Prop :=
  (∀ e (eb : e < S), memory.ram (word (bc.accA + e)) = word (accSumA values hot ⟨e, eb⟩) ∧
      memory.ram (word (bc.accB + e)) = word (accSumB values hot ⟨e, eb⟩)) ∧
    (∀ k : Fin n, ∀ e : Fin S, values.get k e < m) ∧
    (∀ address, ¬ bodyWrites bc S q address → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ bodyClobbers register → memory.registers register = start.registers register

section Slot

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **One slot of the body**: its pad, unless it is the hot slot. -/
theorem agree_bodyEntry (bc : BodyCells) (m S q : Nat) (chain : BodyChain bc m S q)
    (tagOf : Nat → Nat → Nat) (final : Fin m → Label) (hot : Nat) (hotLt : hot < m) (start : Memory)
    (hotCell : start.ram (word bc.hot) = word hot)
    (vecCells : ∀ ρ : Fin m, start.ram (word (bc.vecBase + ρ.val)) = labelWord (final ρ))
    (tagSmall : ∀ ρ j, ρ < m → j < q → tagOf ρ j < 2 ^ 127)
    (index : Fin m) (values : Vector (Fin S → Nat) index.val) (memory : Memory)
    (holds : BodyInv bc m S q hot start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (pad : Fin S → Nat) after =>
        BodyInv bc m S q hot start (index.val + 1) (values.push pad) after)
      ((bodyEntry bc m S q tagOf index.val).tree memory)
      (liftHash (if index.val = hot then pure fun _ => 0
        else padVectorM m S q (final index) (tagOf index.val))) := by
  obtain ⟨accs, digitsLt, frame, bitsSame, regs⟩ := holds
  have := chain.mPos; have := chain.mSmall; have := chain.joinBelow; have := chain.vecBelow
  have := chain.hotBelow; have := chain.ansBelow; have := chain.digBelow; have := chain.accABelow
  have := chain.accBBelow; have := chain.outFits
  have ib := index.isLt
  have below : ∀ x, x < bc.ansBase → memory.ram (word x) = start.ram (word x) := fun x xb =>
    frame _ (not_bodyWrites_below bc m S q chain x xb)
  have hotSmall : hot < 2 ^ 256 := by omega
  have indexSmall : index.val < 2 ^ 256 := by omega
  obtain ⟨m1, run1, ram1, bits1, rA1, regs1⟩ :=
    exec_bodyTest bc index.val memory hot (by rw [below _ (by omega)]; exact hotCell)
  unfold bodyEntry
  rw [tree_seq_exec _ _ (show (bodyTest bc index.val).OpsSatisfy Op.Det from
      ⟨⟨trivial, trivial⟩, trivial, trivial⟩) memory m1 run1, tree_ite, rA1,
    liftHash_ite]
  have regsBack : ∀ register, ¬ bodyClobbers register →
      m1.registers register = start.registers register := fun register outside => by
    rw [regs1 register (fun h => outside (clobbers_body _ (by simp [h])))
      (fun h => outside (clobbers_body _ (by simp [h]))) (fun h => outside (clobbers_body _ (by simp [h])))]
    exact regs register outside
  by_cases same : index.val = hot
  · rw [if_pos ((word_xor_eq_zero hotSmall indexSmall).mpr same.symm), if_pos same]
    refine .leaf ⟨fun e eb => ?_, fun k e => ?_, fun address off => ?_, ?_, regsBack⟩
    · rw [ram1, accSumA_push, accSumB_push, if_pos same, if_pos same, Nat.add_zero, Nat.add_zero]
      exact accs e eb
    · rcases Nat.lt_or_ge k.val index.val with lt | ge
      · have := digitsLt ⟨k.val, lt⟩ e
        rw [Vector.get_eq_getElem] at this ⊢
        rw [Vector.getElem_push_lt lt]
        exact this
      · have eq : k = Fin.last index.val := Fin.ext (by have := k.isLt; simp; omega)
        subst eq
        simp only [Vector.get_eq_getElem, Fin.val_last, Vector.getElem_push_eq]
        omega
    · rw [ram1]
      exact frame address off
    · rw [bits1]
      exact bitsSame
  · rw [if_neg (fun zero => same ((word_xor_eq_zero hotSmall indexSmall).mp zero).symm), if_neg same]
    unfold bodyPad padVectorM hlongM
    rw [tree_seq, TreeLaws.monad_bind, TreeLaws.monad_bind, liftHash_bind, liftHash_bind,
      liftHash_vector, TreeLaws.bind_assoc]
    have labelNow : m1.ram (word (bc.slot index.val).label) = labelWord (final index) := by
      show m1.ram (word (bc.vecBase + index.val)) = _
      rw [ram1, below _ (by omega)]
      exact vecCells index
    refine Agree.bindOpt (fun answers after inv => ?_)
      (agree_ansQueries (bc.slot index.val) q (by show bc.ansBase + 2 * q < 2 ^ 256; omega)
        (by show bc.vecBase + index.val < 2 ^ 256; omega)
        (fun b bb => by show bc.vecBase + index.val ≠ bc.ansBase + b; omega) (tagOf index.val)
        (embed (final index)) m1 (by simpa only [blockWord_embed] using labelNow) (fun j jb => tagSmall _ _ ib jb))
    have invCopy := inv
    obtain ⟨_, frameQ, bitsQ, regsQ⟩ := inv
    have offAns : ∀ x, x < 2 ^ 256 → (x < bc.ansBase ∨ bc.ansBase + 2 * q ≤ x) →
        after.ram (word x) = m1.ram (word x) := fun x small apart =>
      frameQ _ fun b bb same => by
        have := word_inj small (by show bc.ansBase + b < 2 ^ 256; omega) same
        simp only [BodyCells.slot] at this
        omega
    rw [tree_eq_exec _ (det_padRest bc m S q index.val)]
    obtain ⟨final', run, accs', frameP, bitsP, regsP⟩ := exec_padRest bc m S q index.val chain ib m1
      after answers invCopy (fun e => if h : e < S then accSumA values hot ⟨e, h⟩ else 0)
      (fun e => if h : e < S then accSumB values hot ⟨e, h⟩ else 0)
      (fun e eb => by rw [dif_pos eb, offAns _ (by omega) (Or.inr (by omega)), ram1]; exact (accs e eb).1)
      (fun e eb => by rw [dif_pos eb, offAns _ (by omega) (Or.inr (by omega)), ram1]; exact (accs e eb).2)
      (fun e eb => by
        rw [dif_pos eb]
        have := accSumA_le values hot m ⟨e, eb⟩ fun k => digitsLt k ⟨e, eb⟩
        have : index.val * (index.val * m) < 2 ^ 128 := by
          have : index.val * (index.val * m) ≤ 2 ^ 10 * (2 ^ 10 * 2 ^ 10) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
          have : (2 : Nat) ^ 10 * (2 ^ 10 * 2 ^ 10) < 2 ^ 128 := by norm_num
          omega
        omega)
      (fun e eb => by
        rw [dif_pos eb]
        have := accSumB_le values hot m ⟨e, eb⟩ fun k => digitsLt k ⟨e, eb⟩
        have : index.val * m < 2 ^ 128 := by
          have : index.val * m ≤ 2 ^ 10 * 2 ^ 10 := Nat.mul_le_mul (by omega) (by omega)
          have : (2 : Nat) ^ 10 * 2 ^ 10 < 2 ^ 128 := by norm_num
          omega
        omega)
    rw [run]
    refine .leaf ⟨fun e eb => ?_, fun k e => ?_, fun address off => ?_, ?_, fun register outside => ?_⟩
    · obtain ⟨bNew, aNew⟩ := accs' e eb
      rw [dif_pos eb] at bNew aNew
      rw [accSumA_push, accSumB_push, if_neg same, if_neg same]
      exact ⟨by rw [aNew, Nat.mul_comm]; rfl, bNew⟩
    · rcases Nat.lt_or_ge k.val index.val with lt | ge
      · have := digitsLt ⟨k.val, lt⟩ e
        rw [Vector.get_eq_getElem] at this ⊢
        rw [Vector.getElem_push_lt lt]
        exact this
      · have eq : k = Fin.last index.val := Fin.ext (by have := k.isLt; simp; omega)
        subst eq
        simp only [Vector.get_eq_getElem, Fin.val_last, Vector.getElem_push_eq]
        exact padDigit_lt m S q (by omega) answers e.val
    · have offRegions : ¬ (Writes.region ⟨bc.ansBase, 2 * q⟩ address ∨ Writes.region ⟨bc.digBase, S⟩ address ∨
          Writes.region ⟨bc.accA, S⟩ address ∨ Writes.region ⟨bc.accB, S⟩ address) := by
        rintro (inside | inside | inside | inside)
        · exact off (Or.inl (Or.inl (Or.inl inside)))
        · exact off (Or.inl (Or.inl (Or.inr inside)))
        · exact off (Or.inl (Or.inr (Or.inl inside)))
        · exact off (Or.inl (Or.inr (Or.inr inside)))
      rw [frameP address offRegions, frameQ address fun b bb same =>
        off (Or.inl (Or.inl (Or.inl ⟨b, bb, by simpa [BodyCells.slot] using same⟩))), ram1]
      exact frame address off
    · rw [bitsP, bitsQ, bits1]
      exact bitsSame
    · rw [regsP register (fun h => outside (clobbers_body _ (by simp [h])))
        (fun h => outside (clobbers_body _ (by simp [h]))) (fun h => outside (clobbers_body _ (by simp [h])))
        (fun h => outside (clobbers_body _ (by simp [h]))) (fun h => outside (clobbers_body _ (by simp [h])))
        (fun h => outside (clobbers_body _ (by simp [h]))) (fun h => outside (clobbers_body _ (by simp [h]))),
        regsQ register (fun inside => outside (by
          revert register inside
          simp only [castClobbers, bodyClobbers, Clobbers.ofList]
          decide))]
      exact regsBack register outside

end Slot

/-! ### The zeroing and the final residues -/

private theorem exec_bodyZero (bc : BodyCells) (m S q : Nat) (chain : BodyChain bc m S q)
    (memory : Memory) :
    ∃ after, (bodyZero bc S).exec memory = some after ∧
      (∀ e, e < S → after.ram (word (bc.accA + e)) = word 0 ∧ after.ram (word (bc.accB + e)) = word 0) ∧
      (∀ address, (∀ e, e < S → address ≠ word (bc.accA + e) ∧ address ≠ word (bc.accB + e)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have := chain.accABelow; have := chain.accBBelow; have := chain.outFits
  set m0 := setReg memory rA (word 0) with m0Def
  obtain ⟨after, run, inv⟩ := Prog.exec_rep
    (fun e => Prog.seq (storeAt (bc.accA + e) rA) (storeAt (bc.accB + e) rA))
    (fun k current =>
      (∀ e, e < k → current.ram (word (bc.accA + e)) = word 0 ∧ current.ram (word (bc.accB + e)) = word 0) ∧
      current.registers rA = word 0 ∧
      (∀ address, (∀ e, e < S → address ≠ word (bc.accA + e) ∧ address ≠ word (bc.accB + e)) →
        current.ram address = m0.ram address) ∧
      current.bits = m0.bits ∧
      ∀ register, register ≠ rAddr → current.registers register = m0.registers register)
    S (fun k kb current holds => by
      obtain ⟨done, zero, frame, bits, regs⟩ := holds
      refine ⟨_, by rw [exec_storeAt_seq _ _ _ current (by decide), exec_storeAt _ _ _ (by decide)],
        fun e eb => ?_, ?_, fun address off => ?_, by simp only [bits_storeRam, bits_setReg]; exact bits,
        fun register notAddr => ?_⟩
      · simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg]
        simp (config := { decide := true }) only [reduceIte, zero]
        by_cases last : e = k
        · subst last
          refine ⟨?_, Function.update_self ..⟩
          rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
            Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
            Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
            Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done e (by omega)
      · simp (config := { decide := true }) only [reg_storeRam, reg_setReg, reduceIte, zero]
      · simp only [ram_storeRam, ram_setReg, reg_storeRam, reg_setReg]
        simp (config := { decide := true }) only [reduceIte]
        rw [Function.update_of_ne (off k kb).2, Function.update_of_ne (off k kb).1]
        exact frame address off
      · simp only [reg_storeRam, reg_setReg, if_neg notAddr]
        exact regs register notAddr)
    m0 ⟨fun e eb => absurd eb (Nat.not_lt_zero _), by rw [m0Def, reg_setReg, if_pos rfl],
      fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨done, _, frame, bits, regs⟩ := inv
  refine ⟨after, by rw [show bodyZero bc S = .seq (cst rA 0) (Prog.rep S fun e =>
      .seq (storeAt (bc.accA + e) rA) (storeAt (bc.accB + e) rA)) from rfl, exec_cst_seq]; exact run,
    done, fun address off => by rw [frame address off]; rfl, bits,
    fun register notA notAddr => by rw [regs register notAddr, m0Def, reg_setReg, if_neg notA]⟩

/-- The final residue as the machine computes it is `bodyEvalM`'s value in `ZMod m`. -/
theorem bodyResidue_value (m A B J hot : Nat) (below : B ≤ J + m * m) :
    (A + (J + m * m - B) * hot) % m =
      ((A : ZMod m) + (hot : ZMod m) * ((J : ZMod m) - (B : ZMod m))).val := by
  rw [← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub below, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self]
  ring

private theorem exec_bodyFinal (bc : BodyCells) (m S q e : Nat) (chain : BodyChain bc m S q)
    (eb : e < S) (memory : Memory) (A B J hot : Nat)
    (aCell : memory.ram (word (bc.accA + e)) = word A)
    (bCell : memory.ram (word (bc.accB + e)) = word B)
    (jCell : memory.ram (word (bc.joinBase + e)) = word J)
    (hotCell : memory.ram (word bc.hot) = word hot)
    (aLe : A ≤ m * (m * m)) (bLe : B ≤ m * m) (jLt : J < m) (hotLt : hot < m) :
    ∃ after, (bodyFinal bc m e).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (bc.outBase + e))
        (word ((A + (J + m * m - B) * hot) % m)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rOut → register ≠ rB → register ≠ rC →
        register ≠ rD → register ≠ rE → register ≠ rF → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have mPos := chain.mPos
  have mSmall := chain.mSmall
  have := chain.accBBelow; have := chain.outFits
  have m3 : m * (m * m) ≤ 2 ^ 30 := by
    calc m * (m * m) ≤ 2 ^ 10 * (2 ^ 10 * 2 ^ 10) := Nat.mul_le_mul mSmall (Nat.mul_le_mul mSmall mSmall)
      _ = 2 ^ 30 := by norm_num
  have mm : m * m ≤ 2 ^ 20 := by
    calc m * m ≤ 2 ^ 10 * 2 ^ 10 := Nat.mul_le_mul mSmall mSmall
      _ = 2 ^ 20 := by norm_num
  have diffLe : J + m * m - B ≤ m + m * m := by omega
  have prodLe : (J + m * m - B) * hot ≤ (m + m * m) * m := Nat.mul_le_mul diffLe hotLt.le
  have prodBound : (m + m * m) * m ≤ 2 ^ 31 := by
    have : (m + m * m) * m = m * m + m * (m * m) := by ring
    omega
  have sumSmall : A + (J + m * m - B) * hot < 2 ^ 32 := by omega
  obtain ⟨m1, run1, rB1, ram1, bits1, regs1⟩ : ∃ m1, (bodySumJ bc m e).exec memory = some m1 ∧
      m1.registers rB = word (J + m * m - B) ∧ m1.ram = memory.ram ∧ m1.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rAddr →
        m1.registers register = memory.registers register := by
    refine ⟨_, rfl, ?_, rfl, rfl, fun register n1 n2 n3 => ?_⟩
    · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, jCell, bCell]
      rw [eval_add_word _ _ (by omega), eval_sub_word _ _ (by omega) (by omega)]
    · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3]
  obtain ⟨m2, run2, rAcc2, ram2, bits2, regs2⟩ : ∃ m2, (bodySumH bc e).exec m1 = some m2 ∧
      m2.registers rAcc = word (A + (J + m * m - B) * hot) ∧ m2.ram = memory.ram ∧
      m2.bits = memory.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rB → register ≠ rC → register ≠ rAddr →
        m2.registers register = memory.registers register := by
    refine ⟨_, rfl, ?_, by simp only [ram_setReg]; exact ram1, by simp only [bits_setReg]; exact bits1,
      fun register n1 n2 n3 n4 => ?_⟩
    · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, ram1, aCell, hotCell,
        rB1]
      rw [eval_mul_word _ _ (by omega), eval_add_word _ _ (by omega)]
    · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4]
      exact regs1 register n2 n3 n4
  obtain ⟨m3', run3, out3, ram3, bits3, regs3⟩ := exec_barrett rAcc rOut m 32 _ m2 (by decide) (by decide)
    (by decide) (by decide) (by decide) rAcc2 sumSmall mPos (by
      have : (2 : Nat) ^ 10 < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      omega) (by norm_num)
  have runAll : (bodyFinal bc m e).exec memory = some (storeRam (setReg m3' rAddr
      (word (bc.outBase + e))) (word (bc.outBase + e)) (m3'.registers rOut)) := by
    rw [show bodyFinal bc m e = .seq (.seq (bodySumJ bc m e) (bodySumH bc e))
        (.seq (barrett rAcc rOut m 32) (storeAt (bc.outBase + e) rOut)) from rfl,
      Prog.exec_seq_some _ _ memory m2 (by rw [Prog.exec_seq_some _ _ memory m1 run1]; exact run2),
      Prog.exec_seq_some _ _ m2 m3' run3, exec_storeAt _ _ _ (by decide)]
  refine ⟨_, runAll, ?_, ?_, fun register n1 n2 n3 n4 n5 n6 n7 n8 => ?_⟩
  · rw [ram_storeRam, ram_setReg, ram3, ram2, out3]
  · rw [bits_storeRam, bits_setReg, bits3, bits2]
  · rw [reg_storeRam, reg_setReg, if_neg n8, regs3 register n2 n5 n6 n7, regs2 register n1 n3 n4 n8]

private theorem det_bodyZero (bc : BodyCells) (S : Nat) : (bodyZero bc S).OpsSatisfy Op.Det :=
  ⟨trivial, det_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩⟩

private theorem det_bodyFinals (bc : BodyCells) (m S : Nat) :
    (Prog.rep S (bodyFinal bc m)).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ =>
    ⟨⟨⟨⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial⟩,
      ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial⟩⟩,
      det_barrett _ _ _ _, ⟨trivial, trivial⟩⟩

theorem accSumA_cast {S n : Nat} (m : Nat) (values : Vector (Fin S → Nat) n) (hot : Nat) (e : Fin S) :
    ((accSumA values hot e : Nat) : ZMod m) =
      ∑ k : Fin n, if k.val = hot then 0 else (k.val : ZMod m) * (values.get k e : ZMod m) := by
  unfold accSumA
  push_cast
  refine sum_congr rfl fun k _ => ?_
  split <;> simp

theorem accSumB_cast {S n : Nat} (m : Nat) (values : Vector (Fin S → Nat) n) (hot : Nat) (e : Fin S) :
    ((accSumB values hot e : Nat) : ZMod m) =
      ∑ k : Fin n, if k.val = hot then 0 else (values.get k e : ZMod m) := by
  unfold accSumB
  push_cast
  refine sum_congr rfl fun k _ => ?_
  split <;> simp

section Block

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The body of one modulus** against the evaluator's `bodyEvalM`: the cold pads asked in
ascending slot order (parts ascending), read by the fraction reading, accumulated, and the residues
`L_e` in the output cells, under the frame of the schema. -/
theorem agree_bodyBlock (bc : BodyCells) (m S q coord i : Nat) (chain : BodyChain bc m S q)
    (final : Fin m → Label) (hot : Nat) (hotLt : hot < m) (joins : Fin S → Nat)
    (joinsLt : ∀ e, joins e < m) (memory : Memory)
    (hotCell : memory.ram (word bc.hot) = word hot)
    (vecCells : ∀ ρ : Fin m, memory.ram (word (bc.vecBase + ρ.val)) = labelWord (final ρ))
    (joinCells : ∀ e : Fin S, memory.ram (word (bc.joinBase + e.val)) = word (joins e))
    (tagSmall : ∀ ρ j, ρ < m → j < q → bodyTag coord i ρ j < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (residues : Fin S → Nat) after =>
        (∀ e : Fin S, after.ram (word (bc.outBase + e.val)) = word (residues e)) ∧
          (∀ e : Fin S, residues e < m) ∧
          Frame (bodyWrites bc S q) bodyClobbers memory after)
      ((bodyBlock bc m S q (bodyTag coord i)).tree memory)
      (liftHash (bodyEvalM m S q coord i final hot joins)) := by
  have := chain.mPos; have := chain.mSmall; have := chain.joinBelow; have := chain.vecBelow
  have := chain.hotBelow; have := chain.ansBelow; have := chain.digBelow; have := chain.accABelow
  have := chain.accBBelow; have := chain.outFits
  obtain ⟨m0, run0, zero0, frame0, bits0, regs0⟩ := exec_bodyZero bc m S q chain memory
  unfold bodyBlock bodyEvalM tableM
  rw [tree_seq_exec _ _ (det_bodyZero bc S) memory m0 run0, tree_seq, TreeLaws.monad_bind,
    TreeLaws.monad_bind, liftHash_bind, liftHash_bind, liftHash_vector, TreeLaws.bind_assoc]
  refine Agree.bindOpt (fun values after inv => ?_)
    (agree_rep_vector_plain (bodyEntry bc m S q (bodyTag coord i)) (BodyInv bc m S q hot memory) m _
      (fun index values current holds =>
        agree_bodyEntry bc m S q chain (bodyTag coord i) final hot hotLt memory hotCell vecCells
          tagSmall index values current holds)
      m0 ⟨fun e eb => by
          obtain ⟨a0, b0⟩ := zero0 e eb
          exact ⟨by rw [a0]; simp [accSumA], by rw [b0]; simp [accSumB]⟩,
        fun k => k.elim0,
        fun address off => frame0 address fun e eb =>
          ⟨fun same => off (Or.inl (Or.inr (Or.inl ⟨e, eb, same⟩))),
            fun same => off (Or.inl (Or.inr (Or.inr ⟨e, eb, same⟩)))⟩,
        bits0,
        fun register outside => regs0 register
          (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
          (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))⟩)
  obtain ⟨accs, digitsLt, frame, bits, regs⟩ := inv
  have below : ∀ x, x < bc.ansBase → after.ram (word x) = memory.ram (word x) := fun x xb =>
    frame _ (not_bodyWrites_below bc m S q chain x xb)
  rw [tree_eq_exec _ (det_bodyFinals bc m S)]
  obtain ⟨final', run, outs, frameF, bitsF, regsF⟩ := Prog.exec_rep (bodyFinal bc m)
    (fun k current =>
      (∀ e (eb : e < S), e < k → current.ram (word (bc.outBase + e)) =
        word ((accSumA values hot ⟨e, eb⟩ + (joins ⟨e, eb⟩ + m * m - accSumB values hot ⟨e, eb⟩) * hot) % m)) ∧
      (∀ address, (∀ e, e < S → address ≠ word (bc.outBase + e)) → current.ram address = after.ram address) ∧
      current.bits = after.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rOut → register ≠ rB → register ≠ rC →
        register ≠ rD → register ≠ rE → register ≠ rF → register ≠ rAddr →
        current.registers register = after.registers register)
    S (fun k kb current holds => by
      obtain ⟨done, frameK, bitsK, regsK⟩ := holds
      have keep : ∀ x, x < bc.outBase → current.ram (word x) = after.ram (word x) := fun x xb =>
        frameK _ fun e eb => word_ne (by omega) (by omega) (by omega)
      obtain ⟨next, step, ram, bitsN, regsN⟩ := exec_bodyFinal bc m S q k chain kb current
        (accSumA values hot ⟨k, kb⟩) (accSumB values hot ⟨k, kb⟩) (joins ⟨k, kb⟩) hot
        (by rw [keep _ (by omega)]; exact (accs k kb).1)
        (by rw [keep _ (by omega)]; exact (accs k kb).2)
        (by rw [keep _ (by omega), below _ (by omega)]; exact joinCells ⟨k, kb⟩)
        (by rw [keep _ (by omega), below _ (by omega)]; exact hotCell)
        (accSumA_le values hot m ⟨k, kb⟩ fun j => digitsLt j ⟨k, kb⟩)
        (accSumB_le values hot m ⟨k, kb⟩ fun j => digitsLt j ⟨k, kb⟩) (joinsLt _) hotLt
      refine ⟨next, step, fun e eb lt => ?_, fun address off => ?_, by rw [bitsN, bitsK],
        fun register n1 n2 n3 n4 n5 n6 n7 n8 => by
          rw [regsN register n1 n2 n3 n4 n5 n6 n7 n8, regsK register n1 n2 n3 n4 n5 n6 n7 n8]⟩
      · rw [ram]
        by_cases last : e = k
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done e eb (by omega)
      · rw [ram, Function.update_of_ne (off k kb)]
        exact frameK address off)
    after ⟨fun e eb lt => absurd lt (Nat.not_lt_zero _), fun _ _ => rfl, rfl,
      fun _ _ _ _ _ _ _ _ _ => rfl⟩
  rw [run]
  haveI : NeZero m := ⟨by omega⟩
  refine .leaf ⟨fun e => ?_, fun e => ZMod.val_lt _,
    ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩
  · rw [outs e.val e.isLt e.isLt, bodyResidue_value _ _ _ _ _
      (by have := accSumB_le values hot m ⟨e.val, e.isLt⟩ fun j => digitsLt j ⟨e.val, e.isLt⟩; omega),
      accSumA_cast, accSumB_cast]
    rfl
  · rw [frameF address fun e eb same => outside (Or.inr ⟨e, eb, same⟩)]
    exact frame address outside
  · rw [bitsF, bits]
  · rw [regsF register (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))
      (fun h => outside (by simp [bodyClobbers, Clobbers.ofList, h]))]
    exact regs register outside

end Block

end Kriterion.CRT.SimMachine
