/-
**The truth-table words on the machine** (`exec_truthWordBlock`) and their equality with the
construction's `truthWord` (`truthWord_val`).
-/

import Proof.Simulator.CRT.ReplayChunks
import Construction.Simulator.CRT.ReplayWords

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### Word arithmetic with wrap-around -/

theorem eval_add_wrap (a b : Nat) : Arithmetic.add.eval (word a) (word b) = word (a + b) := by
  apply BitVec.eq_of_toNat_eq
  show (word a + word b).toNat = _
  rw [BitVec.toNat_add, word, word, word, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    ← Nat.add_mod]

theorem eval_mul_wrap (a b : Nat) : Arithmetic.mul.eval (word a) (word b) = word (a * b) := by
  apply BitVec.eq_of_toNat_eq
  show (word a * word b).toNat = _
  rw [BitVec.toNat_mul, word, word, word, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    ← Nat.mul_mod]

theorem eval_and_wrap (a n : Nat) (nSmall : n ≤ 256) :
    Arithmetic.and.eval (word a) (word (2 ^ n - 1)) = word (a % 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  show (word a &&& word (2 ^ n - 1)).toNat = _
  have maskSmall : 2 ^ n - 1 < 2 ^ 256 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) nSmall
    omega
  have divides : 2 ^ n ∣ 2 ^ 256 := Nat.pow_dvd_pow 2 nSmall
  rw [BitVec.toNat_and, word_toNat maskSmall, Nat.and_two_pow_sub_one_eq_mod,
    word_toNat (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) nSmall))]
  simp only [word, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd a divides

/-! ### One lane -/

private theorem exec_wordTerm (castBase t c leaf i : Nat) (memory : Memory) (acc x : Nat)
    (accReg : memory.registers rA = word acc)
    (cell : memory.ram (word (castBase + 32768 * c + 128 * leaf + i)) = word x) :
    ∃ after, (wordTerm castBase t c leaf i).exec memory = some after ∧
      after.registers rA = word (acc + x * t) ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, rfl, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, cell, accReg]
    rw [eval_mul_wrap, eval_add_wrap]
  · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-- The value of lane `i` of chunk `c`'s contribution after `j` leaves. -/
def wordPartial (X : Nat → Nat → Nat) (truthOf : Nat → Nat → Nat) (c j : Nat) : Nat :=
  ∑ leaf ∈ range j, X c leaf * truthOf c leaf

private theorem exec_wordChunk (castBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (i c : Nat) (memory : Memory) (acc : Nat) (X : Nat → Nat → Nat)
    (accReg : memory.registers rA = word acc)
    (cells : ∀ leaf, leaf < 2 ^ width c →
      memory.ram (word (castBase + 32768 * c + 128 * leaf + i)) = word (X c leaf)) :
    ∃ after, (wordChunk castBase truthOf width i c).exec memory = some after ∧
      after.registers rA = word (acc + wordPartial X truthOf c (2 ^ width c)) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨after, run, acc', ram, bits, regs⟩ := Prog.exec_rep
    (fun leaf => wordTerm castBase (truthOf c leaf) c leaf i)
    (fun j current => current.registers rA = word (acc + wordPartial X truthOf c j) ∧
      current.ram = memory.ram ∧ current.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        current.registers register = memory.registers register)
    (2 ^ width c) (fun j jb current holds => by
      obtain ⟨accNow, ram, bits, regs⟩ := holds
      obtain ⟨next, step, accNext, ramN, bitsN, regsN⟩ := exec_wordTerm castBase (truthOf c j) c j i
        current _ (X c j) accNow (by rw [ram]; exact cells j jb)
      refine ⟨next, step, ?_, by rw [ramN, ram], by rw [bitsN, bits],
        fun register n1 n2 n3 n4 => by rw [regsN register n1 n2 n3 n4, regs register n1 n2 n3 n4]⟩
      rw [accNext, wordPartial, wordPartial, sum_range_succ, Nat.add_assoc])
    memory ⟨by rw [wordPartial, sum_range_zero, Nat.add_zero]; exact accReg, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  exact ⟨after, run, acc', ram, bits, regs⟩

/-- The value of lane `i` over the first `k` chunks. -/
def wordSum (X : Nat → Nat → Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat) (k : Nat) : Nat :=
  ∑ c ∈ range k, wordPartial X truthOf c (2 ^ width c)

private theorem exec_wordLane (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat)
    (width : Nat → Nat) (count ell i : Nat) (memory : Memory) (X : Nat → Nat → Nat)
    (ellSmall : ell ≤ 256) (wordSmall : wordBase + i < 2 ^ 256)
    (cells : ∀ c, c < count → ∀ leaf, leaf < 2 ^ width c →
      memory.ram (word (castBase + 32768 * c + 128 * leaf + i)) = word (X c leaf)) :
    ∃ after, (wordLane castBase wordBase truthOf width count ell i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (wordBase + i))
        (word (wordSum X truthOf width count % 2 ^ ell)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set m0 := setReg memory rA (word 0) with m0Def
  obtain ⟨m1, run1, acc1, ram1, bits1, regs1⟩ := Prog.exec_rep (wordChunk castBase truthOf width i)
    (fun k current => current.registers rA = word (wordSum X truthOf width k) ∧
      current.ram = memory.ram ∧ current.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        current.registers register = memory.registers register)
    count (fun k kb current holds => by
      obtain ⟨accNow, ram, bits, regs⟩ := holds
      obtain ⟨next, step, accNext, ramN, bitsN, regsN⟩ := exec_wordChunk castBase truthOf width i k
        current _ X accNow (fun leaf lb => by rw [ram]; exact cells k kb leaf lb)
      refine ⟨next, step, ?_, by rw [ramN, ram], by rw [bitsN, bits],
        fun register n1 n2 n3 n4 => by rw [regsN register n1 n2 n3 n4, regs register n1 n2 n3 n4]⟩
      rw [accNext, wordSum, wordSum, sum_range_succ])
    m0 ⟨by rw [m0Def, reg_setReg, if_pos rfl, wordSum, sum_range_zero], rfl, rfl,
      fun register n1 _ _ _ => by rw [m0Def, reg_setReg, if_neg n1]⟩
  have runAll : (wordLane castBase wordBase truthOf width count ell i).exec memory =
      (Prog.seq (cst rB (2 ^ ell - 1)) (.seq (ar .and rA rA rB) (storeAt (wordBase + i) rA))).exec m1 := by
    rw [show wordLane castBase wordBase truthOf width count ell i = .seq (cst rA 0)
        (.seq (Prog.rep count (wordChunk castBase truthOf width i))
        (.seq (cst rB (2 ^ ell - 1)) (.seq (ar .and rA rA rB) (storeAt (wordBase + i) rA)))) from rfl,
      exec_cst_seq, ← m0Def, Prog.exec_seq_some _ _ m0 m1 run1]
  rw [runAll]
  refine ⟨_, rfl, ?_, ?_, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte, acc1]
    rw [eval_and_wrap _ _ ellSmall, ram1]
  · simp only [bits_storeRam, bits_setReg]
    exact bits1
  · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2, if_neg n4]
    exact regs1 register n1 n2 n3 n4

/-- **The word block**: lane `i < 128` holds `(Σ_c Σ_α X_{c,α,i} · T_{c,α}) mod 2 ^ ell`. -/
theorem exec_truthWordBlock (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (count ell : Nat) (memory : Memory) (X : Nat → Nat → Nat → Nat) (ellSmall : ell ≤ 256)
    (wordFits : wordBase + 128 < 2 ^ 256)
    (apart : ∀ c, c < count → ∀ leaf, leaf < 2 ^ width c → ∀ i, i < 128 → ∀ i', i' < 128 →
      castBase + 32768 * c + 128 * leaf + i ≠ wordBase + i')
    (castFits : ∀ c, c < count → ∀ leaf, leaf < 2 ^ width c → ∀ i, i < 128 →
      castBase + 32768 * c + 128 * leaf + i < 2 ^ 256)
    (cells : ∀ c, c < count → ∀ leaf, leaf < 2 ^ width c → ∀ i, i < 128 →
      memory.ram (word (castBase + 32768 * c + 128 * leaf + i)) = word (X i c leaf)) :
    ∃ after, (truthWordBlock castBase wordBase truthOf width count ell).exec memory = some after ∧
      (∀ i, i < 128 → after.ram (word (wordBase + i)) =
        word (wordSum (X i) truthOf width count % 2 ^ ell)) ∧
      (∀ address, (∀ i, i < 128 → address ≠ word (wordBase + i)) → after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨after, run, done, frame, bits, regs⟩ := Prog.exec_rep
    (wordLane castBase wordBase truthOf width count ell)
    (fun k current =>
      (∀ i, i < k → current.ram (word (wordBase + i)) = word (wordSum (X i) truthOf width count % 2 ^ ell)) ∧
      (∀ address, (∀ i, i < 128 → address ≠ word (wordBase + i)) → current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        current.registers register = memory.registers register)
    128 (fun k kb current holds => by
      obtain ⟨done, frame, bits, regs⟩ := holds
      obtain ⟨next, step, ram, bitsN, regsN⟩ := exec_wordLane castBase wordBase truthOf width count ell k
        current (X k) ellSmall (by omega)
        (fun c cb leaf lb => by
          rw [frame _ fun i' ib' => word_ne (castFits c cb leaf lb k kb) (by omega)
            (apart c cb leaf lb k kb i' ib')]
          exact cells c cb leaf lb k kb)
      refine ⟨next, step, fun i ib => ?_, fun address off => ?_, by rw [bitsN, bits],
        fun register n1 n2 n3 n4 => by rw [regsN register n1 n2 n3 n4, regs register n1 n2 n3 n4]⟩
      · rw [ram]
        by_cases last : i = k
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done i (by omega)
      · rw [ram, Function.update_of_ne (off k kb)]
        exact frame address off)
    memory ⟨fun i ib => absurd ib (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ _ _ _ => rfl⟩
  exact ⟨after, run, done, frame, bits, regs⟩

/-! ### Cost -/

theorem cost_wordTerm (castBase t c leaf i : Nat) : (wordTerm castBase t c leaf i).cost = 5 := rfl

theorem cost_wordLane (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (count ell i : Nat) :
    (wordLane castBase wordBase truthOf width count ell i).cost =
      5 + ∑ c ∈ range count, 5 * 2 ^ width c := by
  simp only [wordLane, wordChunk, Prog.cost_seq, cost_rep_sum, cost_wordTerm, sum_const, card_range,
    smul_eq_mul]
  show 1 + (_ + (1 + (1 + 2))) = _
  rw [show ∑ c ∈ range count, 2 ^ width c * 5 = ∑ c ∈ range count, 5 * 2 ^ width c from
    sum_congr rfl fun c _ => mul_comm _ _]
  omega

/-- **The cost of the word block**, a closed form in the chunk widths. -/
theorem cost_truthWordBlock (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (count ell : Nat) :
    (truthWordBlock castBase wordBase truthOf width count ell).cost =
      128 * (5 + ∑ c ∈ range count, 5 * 2 ^ width c) := by
  rw [truthWordBlock, Prog.cost_rep _ _ _ (fun i _ => cost_wordLane castBase wordBase truthOf width count ell i)]

/-! ### The link with `truthWord` -/

/-- Lane `i` of the construction's word is the machine's masked sum. -/
theorem truthWord_val (T : CrtTable) (m ell : Nat) (ellLe : ell ≤ T.castWidth)
    (casts : Nat → Nat → Lanes T.castWidth) (i : Fin laneCount) :
    ((truthWord T m ell casts) i).val =
      wordSum (fun c leaf => (casts c leaf i).val) (T.truth m) T.chunkWidth T.chunkCount % 2 ^ ell := by
  haveI : NeZero (2 ^ T.castWidth) := ⟨by positivity⟩
  have key : (∑ c : Fin T.chunkCount, ∑ leaf : Fin (2 ^ T.chunkWidth c.val),
      ((T.truth m c.val leaf.val : Nat) : ZMod (2 ^ T.castWidth)) * casts c.val leaf.val i) =
      ((wordSum (fun c leaf => (casts c leaf i).val) (T.truth m) T.chunkWidth T.chunkCount : Nat) :
        ZMod (2 ^ T.castWidth)) := by
    unfold wordSum wordPartial
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun c => ∑ leaf : Fin (2 ^ T.chunkWidth c),
      ((T.truth m c leaf.val : Nat) : ZMod (2 ^ T.castWidth)) * casts c leaf.val i)]
    refine sum_congr rfl fun c _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun leaf =>
      ((T.truth m c leaf : Nat) : ZMod (2 ^ T.castWidth)) * casts c leaf i)]
    refine sum_congr rfl fun leaf _ => ?_
    rw [ZMod.natCast_zmod_val, mul_comm]
  have divides : 2 ^ ell ∣ 2 ^ T.castWidth := Nat.pow_dvd_pow 2 ellLe
  unfold truthWord reduceTo
  rw [materialize_eq, ZMod.val_natCast]
  beta_reduce
  rw [key, ZMod.val_natCast, Nat.mod_mod_of_dvd _ divides]

/-! ### Stored families are pure -/

theorem freeQuery_vector_pure {spec : OracleSpec.{0, 0}} {α : Type} :
    ∀ (count : Nat) (f : Fin count → α),
      FreeQuery.vector (spec := spec) count (fun index => .pure (f index)) = .pure (Vector.ofFn f)
  | 0, f => by
      show FreeQuery.pure #v[] = _
      congr 1
  | count + 1, f => by
      simp only [FreeQuery.vector, TreeLaws.monad_bind, TreeLaws.monad_pure]
      rw [freeQuery_vector_pure count (fun index => f index.castSucc)]
      show FreeQuery.pure ((Vector.ofFn fun index => f index.castSucc).push (f (Fin.last count))) = _
      congr 1
      ext i h
      simp only [Vector.getElem_ofFn]
      rcases Nat.lt_or_ge i count with lt | ge
      · rw [Vector.getElem_push_lt lt, Vector.getElem_ofFn]
        rfl
      · have : i = count := by omega
        subst this
        rw [Vector.getElem_push_eq]
        rfl

/-- `storeM` and `materializeM` are pure steps: the machine needs no code for them. -/
theorem liftHash_storeM {FixedIndex EncIndex : Type} {α : Type} {count : Nat} (family : Fin count → α) :
    liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (storeM family) = .pure family := by
  unfold storeM tableM
  rw [TreeLaws.monad_bind, liftHash_bind, liftHash_vector]
  simp only [TreeLaws.monad_pure, liftHash_pure]
  rw [freeQuery_vector_pure]
  show FreeQuery.pure (Vector.ofFn family).get = _
  congr 1
  funext i
  simp

theorem liftHash_materializeM {FixedIndex EncIndex : Type} {width : Nat} (lanes : Lanes width) :
    liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (materializeM lanes) = .pure lanes :=
  liftHash_storeM lanes

end Kriterion.CRT.SimMachine
