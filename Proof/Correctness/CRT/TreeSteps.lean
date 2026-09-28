/-
CRT slice, conversion chain part A: the one-hot tree step of `Construction/CRT/Tree.lean` on
`.eval H` (L1 and L2), for every `H : HashN`.

* XOR folds: `xorFoldExcept_eq`, `xorFold_eq_xsum`.
* `extendLevel_eq`: the new level in the node-recursion form of `ExtractSpec.gNode`.
* L1 `extendLevel_invariant`, `evalStepM_correct`: one evaluator step with known bit keeps the
  free-XOR invariant `E = G ⊕ [· = hot]·Δ` and moves the hot index from `a` to `a + b·2^n`.
* L2 `growEvalM_correct`: the growth of a one-hot by `count` known bits, against the garbler's
  `growGarbleM` and its joins.
-/

import Proof.Correctness.CRT.ExtractStage
import Construction.CRT.Coord

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

/-! ### XOR folds (the proofs of xinshu's `Proof/Correctness/PGS/OneHot.lean`, same text) -/

theorem xorFoldExcept_eq_update {count : Nat} (skip : Fin count) (family : Fin count → Label) :
    xorFoldExcept skip family = xorFold (Function.update family skip 0) := by
  unfold xorFoldExcept xorFold
  have body : (fun (acc : Label) (entry : Fin count) =>
        if entry = skip then acc else acc ^^^ family entry)
      = fun (acc : Label) (entry : Fin count) => acc ^^^ Function.update family skip 0 entry := by
    funext acc entry
    by_cases hit : entry = skip
    · subst hit; simp
    · simp [hit]
  rw [body]

theorem xorFoldExcept_congr {count : Nat} (skip : Fin count) (first second : Fin count → Label)
    (agree : ∀ entry, entry ≠ skip → first entry = second entry) :
    xorFoldExcept skip first = xorFoldExcept skip second := by
  rw [xorFoldExcept_eq_update, xorFoldExcept_eq_update]
  congr 1
  funext entry
  by_cases hit : entry = skip
  · subst hit; simp
  · simp [Function.update_of_ne hit, agree entry hit]

theorem xorFoldExcept_xor {count : Nat} :
    ∀ (skip : Fin count) (family : Fin count → Label),
      xorFoldExcept skip family ^^^ family skip = xorFold family := by
  induction count with
  | zero => intro skip; exact skip.elim0
  | succ n ih =>
    intro skip family
    induction skip using Fin.lastCases with
    | last =>
      rw [xorFoldExcept, xorFold, Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [if_neg (Fin.castSucc_ne_last _)]
      rfl
    | cast j =>
      rw [xorFoldExcept, xorFold, Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [Fin.castSucc_inj, if_neg (Ne.symm (Fin.castSucc_ne_last j))]
      have restore := ih j (fun entry : Fin n => family entry.castSucc)
      rw [xorFoldExcept, xorFold] at restore
      rw [BitVec.xor_assoc, BitVec.xor_comm (family (Fin.last n)) (family j.castSucc),
        ← BitVec.xor_assoc, restore]

theorem xorFoldExcept_eq {count : Nat} (skip : Fin count) (family : Fin count → Label) :
    xorFoldExcept skip family = xorFold family ^^^ family skip := by
  conv_rhs => rw [← xorFoldExcept_xor skip family]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xsum_insert_nat {s : Finset Nat} {a : Nat} (h : a ∉ s) (f : Nat → Label) :
    xsum (insert a s) f = f a ^^^ xsum s f :=
  Finset.fold_insert h

/-- `xorFold` over `Fin c` is `xsum` over `range c`. -/
theorem xorFold_eq_xsum {c : Nat} (f : Fin c → Label) :
    xorFold f = xsum (Finset.range c) (fun i => if h : i < c then f ⟨i, h⟩ else 0) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have hstep := ih (fun i => f i.castSucc)
    rw [xorFold] at hstep
    rw [xorFold, Fin.foldl_succ_last, hstep, Finset.range_add_one,
      xsum_insert_nat Finset.notMem_range_self, dif_pos (Nat.lt_succ_self c), BitVec.xor_comm]
    congr 1
    apply xsum_congr
    intro i hi
    have hic : i < c := Finset.mem_range.mp hi
    rw [dif_pos hic, dif_pos (Nat.lt_succ_of_lt hic)]
    rfl

/-! ### Small XOR identities -/

theorem zero_xor_block {width : Nat} (a : BitVec width) : (0 : BitVec width) ^^^ a = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp

theorem xor_self_block {width : Nat} (a : BitVec width) : a ^^^ a = (0 : BitVec width) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp

theorem xor_cancel_left_block {width : Nat} (a b : BitVec width) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, xor_self_block, zero_xor_block]

theorem xor_left_comm_block {width : Nat} (a b c : BitVec width) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

/-- AC-normalize XOR expressions of blocks, cancelling equal atoms and zeros. -/
macro "xor_norm" : tactic =>
  `(tactic| simp only [BitVec.xor_assoc, xor_zero_block, zero_xor_block, xor_self_block,
    xor_cancel_left_block, BitVec.xor_comm, xor_left_comm_block])

theorem xor_step_solve {width : Nat} (Y b d y : BitVec width) : (Y ^^^ b) ^^^ (b ^^^ d) ^^^ (Y ^^^ y) = y ^^^ d := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases Y.getLsbD i <;> cases b.getLsbD i <;> cases d.getLsbD i <;> cases y.getLsbD i <;> rfl

theorem xor_four_cancel {width : Nat} (a b c d : BitVec width) : (a ^^^ c) ^^^ (b ^^^ d) = (a ^^^ b) ^^^ (c ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

/-! ### The level step -/

/-- Split of a slot of level `n + 1` into its parent slot and its new bit. -/
theorem val_split {n : Nat} (e : Fin (2 ^ (n + 1))) :
    e.val = e.val % 2 ^ n + (if e.val.testBit n then 2 ^ n else 0) := by
  have h2 : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have he := e.isLt
  have hpos := Nat.two_pow_pos n
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hlt : e.val < 2 ^ n
  · rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt]; simp
  · have hdiv : e.val / 2 ^ n = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hdiv, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp
    omega

/-- `extendLevel` in the node-recursion form of `ExtractSpec.gNode`. -/
theorem extendLevel_eq {n : Nat} (parent right : Fin (2 ^ n) → Label) (e : Fin (2 ^ (n + 1))) :
    extendLevel n parent right e =
      if e.val.testBit n then right ⟨e.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩
      else parent ⟨e.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ ^^^
        right ⟨e.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ := by
  have hsplit := val_split e
  unfold extendLevel
  by_cases hlt : e.val < 2 ^ n
  · have hb : e.val.testBit n = false := Nat.testBit_lt_two_pow hlt
    have hm : e.val % 2 ^ n = e.val := Nat.mod_eq_of_lt hlt
    rw [dif_pos hlt, hb]
    simp only [Bool.false_eq_true, if_false]
    congr 2 <;> exact Fin.ext hm.symm
  · rw [dif_neg hlt]
    have hb : e.val.testBit n = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      rw [hc] at hsplit
      simp at hsplit
      have := Nat.mod_lt e.val (Nat.two_pow_pos n)
      omega
    rw [hb] at hsplit ⊢
    simp only [if_true]
    congr 1
    apply Fin.ext
    simp only [if_true] at hsplit
    show e.val - 2 ^ n = e.val % 2 ^ n
    omega

/-- **L1**, the level step on labels: if the evaluator's parent level is the garbler's XOR `Δ` at
slot `a`, and its materials are the garbler's XOR `β·Δ` at slot `a`, the new level is the
garbler's XOR `Δ` at `a + β·2^n`. -/
theorem extendLevel_invariant {n : Nat} (G E rG rE : Fin (2 ^ n) → Label) (Δ : Label) (a : Nat)
    (ha : a < 2 ^ n) (β : Bool)
    (hE : ∀ x, E x = G x ^^^ (if x.val = a then Δ else 0))
    (hr : ∀ x, rE x = rG x ^^^ (if x.val = a ∧ β = true then Δ else 0)) (e : Fin (2 ^ (n + 1))) :
    extendLevel n E rE e =
      extendLevel n G rG e ^^^ (if e.val = a + (if β then 2 ^ n else 0) then Δ else 0) := by
  rw [extendLevel_eq, extendLevel_eq, hE, hr]
  dsimp only
  have hsplit := val_split e
  have hr' := Nat.mod_lt e.val (Nat.two_pow_pos n)
  cases hb : e.val.testBit n <;> cases β <;>
    simp only [hb, Bool.false_eq_true, if_false, if_true, and_false, and_true, Nat.add_zero]
      at hsplit ⊢ <;>
    split_ifs <;> first | omega | xor_norm

/-! ### The programs of one step, evaluated -/

theorem eval_garbleStepM (H : HashN) (n : Nat) (tagOf : Nat → Nat) (parent : Fin (2 ^ n) → Label) :
    (garbleStepM n tagOf parent).eval H =
      (extendLevel n parent (fun slot => hLabel H (parent slot) (tagOf slot.val)),
        xorFold (fun slot => hLabel H (parent slot) (tagOf slot.val))) := by
  simp [garbleStepM]

theorem eval_evalStepM (H : HashN) (n : Nat) (tagOf : Nat → Nat) (active : Fin (2 ^ n))
    (bitLabel join : Label) (parent : Fin (2 ^ n) → Label) :
    (evalStepM n tagOf active bitLabel join parent).eval H =
      extendLevel n parent (fun slot =>
        if slot = active then
          join ^^^ bitLabel ^^^ xorFoldExcept active
            (fun s => if s = active then 0 else hLabel H (parent s) (tagOf s.val))
        else hLabel H (parent slot) (tagOf slot.val)) := by
  simp only [evalStepM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq]
  congr 1
  funext slot
  by_cases hs : slot = active
  · simp only [hs, if_true]
    congr 2
    funext s
    by_cases hs' : s = active
    · simp [hs']
    · simp [hs']
  · simp [hs]

/-- **L1**, one evaluator step with a known bit (`evalStepM`), against the garbler's step. -/
theorem evalStepM_correct (H : HashN) (n : Nat) (tagOf : Nat → Nat) (G E : Fin (2 ^ n) → Label)
    (Δ : Label) (a : Nat) (ha : a < 2 ^ n) (β : Bool) (bitMask : Label)
    (hE : ∀ x, E x = G x ^^^ (if x.val = a then Δ else 0)) (e : Fin (2 ^ (n + 1))) :
    (evalStepM n tagOf ⟨a, ha⟩ (bitMask ^^^ (if β then Δ else 0))
        (xorFold (fun slot => hLabel H (G slot) (tagOf slot.val)) ^^^ bitMask) E).eval H e =
      extendLevel n G (fun slot => hLabel H (G slot) (tagOf slot.val)) e ^^^
        (if e.val = a + (if β then 2 ^ n else 0) then Δ else 0) := by
  rw [eval_evalStepM]
  apply extendLevel_invariant G E _ _ Δ a ha β hE
  intro x
  have hcold : ∀ s : Fin (2 ^ n), s ≠ ⟨a, ha⟩ → E s = G s := by
    intro s hs
    rw [hE, if_neg (fun h => hs (Fin.ext h)), xor_zero_block]
  by_cases hx : x = ⟨a, ha⟩
  · subst hx
    simp only [if_true, true_and]
    rw [xorFoldExcept_congr _ _ (fun slot => hLabel H (G slot) (tagOf slot.val)) (by
      intro s hs
      rw [if_neg hs, hcold s hs]), xorFoldExcept_eq]
    cases β
    · simp only [Bool.false_eq_true, if_false]
      exact xor_step_solve _ _ _ _
    · simp only [if_true]
      exact xor_step_solve _ _ _ _
  · have hxa : ¬ x.val = a := fun h => hx (Fin.ext h)
    simp only [hx, if_false, hxa, false_and, xor_zero_block]
    rw [hcold x hx]

/-! ### Growth (L2) -/

theorem mod_two_pow_succ_split (v n : Nat) :
    v % 2 ^ (n + 1) = v % 2 ^ n + (if v.testBit n then 2 ^ n else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h <;> simp [h]

theorem eval_growGarbleM_succ (H : HashN) (tagOf : Nat → Nat → Nat) (start : Nat)
    (labels : Fin (2 ^ start) → Label) (k : Nat) :
    (growGarbleM tagOf start labels (k + 1)).eval H =
      let prev := (growGarbleM tagOf start labels k).eval H
      (extendLevel (start + k) prev.1 (fun slot => hLabel H (prev.1 slot) (tagOf (start + k) slot.val)),
        fun level => if level = start + k then
          xorFold (fun slot => hLabel H (prev.1 slot) (tagOf (start + k) slot.val)) else prev.2 level) := by
  simp only [growGarbleM, FreeQuery.eval_bind, eval_garbleStepM, FreeQuery.eval_pure]

/-- The garbler's level XOR of growth step `j < count`, read from the whole growth. -/
theorem growGarbleM_levelSum (H : HashN) (tagOf : Nat → Nat → Nat) (start : Nat)
    (labels : Fin (2 ^ start) → Label) :
    ∀ count j, j < count →
      ((growGarbleM tagOf start labels count).eval H).2 (start + j) =
        xorFold (fun slot => hLabel H (((growGarbleM tagOf start labels j).eval H).1 slot)
          (tagOf (start + j) slot.val)) := by
  intro count
  induction count with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro j hj
    rw [eval_growGarbleM_succ]
    simp only
    by_cases hjk : j = k
    · subst hjk; rw [if_pos rfl]
    · rw [if_neg (by omega)]
      exact ih j (by omega)

/-- **L2** `growEvalM_correct`: growing the evaluator's one-hot (hot at `value mod 2^start`) by
`count` known bits, with the evaluator's bit labels the masks XOR `value_j·Δ` and the garbler's
joins, gives the garbler's grown one-hot XOR `Δ` at `value mod 2^(start + count)`. -/
theorem growEvalM_correct (H : HashN) (tagOf : Nat → Nat → Nat) (start : Nat)
    (G E : Fin (2 ^ start) → Label) (Δ : Label) (value : Nat) (bitMask bitLabel join : Nat → Label)
    (total : Nat)
    (hE : ∀ x, E x = G x ^^^ (if x.val = value % 2 ^ start then Δ else 0))
    (hbit : ∀ j, j < start + total → bitLabel j = bitMask j ^^^ (if value.testBit j then Δ else 0))
    (hjoin : ∀ j, join j = ((growGarbleM tagOf start G total).eval H).2 j ^^^ bitMask j) :
    ∀ count ≤ total, ∀ x,
      (growEvalM tagOf value bitLabel join start E count).eval H x =
        ((growGarbleM tagOf start G count).eval H).1 x ^^^
          (if x.val = value % 2 ^ (start + count) then Δ else 0) := by
  intro count
  induction count with
  | zero => intro _ x; exact hE x
  | succ k ih =>
    intro hk x
    have ihk := ih (by omega)
    simp only [growEvalM, FreeQuery.eval_bind]
    rw [eval_growGarbleM_succ]
    simp only
    have ha : value % 2 ^ (start + k) < 2 ^ (start + k) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hact : activeAt value (start + k) = ⟨value % 2 ^ (start + k), ha⟩ := rfl
    rw [hact, hbit (start + k) (by omega), hjoin (start + k),
      growGarbleM_levelSum H tagOf start G total k (by omega)]
    rw [evalStepM_correct H (start + k) (tagOf (start + k)) _ _ Δ _ ha (value.testBit (start + k))
      (bitMask (start + k)) ihk x]
    congr 3
    rw [← mod_two_pow_succ_split]
    rfl

end Kriterion.CRT.SliceC
