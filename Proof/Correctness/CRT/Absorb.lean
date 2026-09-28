/-
No chunk joins, correctness (ROUND2 §5): the evaluator's chunk trees with **zero joins** on labels
that **absorb** the chunk joins are its chunk trees with the joins on the honest labels.

The evaluator's step reads its join and its bit label only through `join ⊕ bitLabel`
(`Tree.evalStepM`: the active material is `join ⊕ bitLabel ⊕ cold`), so
`0 ⊕ (B ⊕ J) = J ⊕ B` gives the same step (`evalStepM_xor_congr`); the first level reads its bit
label directly, and the absorbed labels leave each chunk's first bit unchanged
(`CrtTable.chunkShift`). Hence (`coordEvalM_absorb`), for every hash, value and published material
`pub`: the evaluator on `pub.dropChunkJoins` with labels `B j ⊕ chunkShift pub.chunkJoin j` is the
evaluator on `pub` with labels `B j`, as programs (the same queries in the same order). No
condition on `Δ`, the labels or the oracle.
-/

import Proof.Correctness.CRT.FlatLayout

namespace Kriterion.CRT.Absorb

open Cryptography Kriterion.CRT Kriterion.ArgoMAC Kriterion.CRT.FlatLayout

/-! ### One step and one tree -/

/-- `x ⊕ 0 = x` at the literal `0` of `Label` (the `BitVec` lemma is stated at `0#w`). -/
theorem label_xor_zero (x : Label) : x ^^^ (0 : Label) = x := BitVec.xor_zero

/-- `0 ⊕ x = x` at the literal `0` of `Label`. -/
theorem label_zero_xor (x : Label) : (0 : Label) ^^^ x = x := BitVec.zero_xor

/-- The evaluator's step reads its join and its bit label only through their XOR. -/
theorem evalStepM_xor_congr (n : Nat) (tagOf : Nat → Nat) (active : Fin (2 ^ n))
    (b₁ j₁ b₂ j₂ : Label) (parent : Fin (2 ^ n) → Label) (same : j₁ ^^^ b₁ = j₂ ^^^ b₂) :
    evalStepM n tagOf active b₁ j₁ parent = evalStepM n tagOf active b₂ j₂ parent := by
  unfold evalStepM
  simp only [same]

/-- **Absorbing the joins into the bit labels.** The evaluator's tree with bit labels `B'` and
joins `J'` is its tree with `B` and `J` when the first bit label agrees and `J' n ⊕ B' n = J n ⊕ B n`
on every hashed level `1 ≤ n < levels`. -/
theorem treeEvalM_absorb (tagOf : Nat → Nat → Nat) (value : Nat) (B J B' J' : Nat → Label)
    (levels : Nat) (first : 0 < levels → B' 0 = B 0)
    (joined : ∀ n, 1 ≤ n → n < levels → J' n ^^^ B' n = J n ^^^ B n) :
    treeEvalM tagOf value B' J' levels = treeEvalM tagOf value B J levels := by
  induction levels with
  | zero => rfl
  | succ n ih =>
      rw [treeEvalM, treeEvalM,
        ih (fun _ => first (by omega)) fun k lower upper => joined k lower (by omega)]
      congr 1
      funext previous
      by_cases zero : n = 0
      · subst zero
        simp only [if_true, first (by omega)]
      · rw [if_neg zero, if_neg zero]
        exact evalStepM_xor_congr _ _ _ _ _ _ _ _ (joined n (by omega) (by omega))

/-! ### The chunk shift at a chunk's bits -/

theorem chunkOffset_add_lt (T : CrtTable) (c n : Nat) (inRange : n < T.chunkWidth c) :
    T.chunkOffset c + n < T.inputBits := by
  unfold CrtTable.chunkWidth at inRange
  unfold CrtTable.chunkOffset
  have := Nat.lt_min.mp inRange
  omega

theorem chunkWidth_le (T : CrtTable) (c : Nat) : T.chunkWidth c ≤ T.chunkBits := by
  unfold CrtTable.chunkWidth
  exact Nat.min_le_left _ _

/-- Bit `n ≥ 1` of chunk `c` carries the chunk's join of level `n`. -/
theorem chunkShift_at (T : CrtTable) (hk : 0 < T.chunkBits) (J : Nat → Nat → Label) (c n : Nat)
    (lower : 1 ≤ n) (upper : n < T.chunkWidth c) :
    T.chunkShift J (T.chunkOffset c + n) = J c n := by
  have small : n < T.chunkBits := lt_of_lt_of_le upper (chunkWidth_le T c)
  have hmod : (T.chunkOffset c + n) % T.chunkBits = n := by
    unfold CrtTable.chunkOffset
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt small]
  have hdiv : (T.chunkOffset c + n) / T.chunkBits = c := by
    unfold CrtTable.chunkOffset
    rw [Nat.mul_add_div hk, Nat.div_eq_of_lt small, Nat.add_zero]
  unfold CrtTable.chunkShift
  rw [hmod, hdiv, if_neg (by omega)]

/-- The first bit of every chunk carries nothing. -/
theorem chunkShift_first (T : CrtTable) (J : Nat → Nat → Label) (c : Nat) :
    T.chunkShift J (T.chunkOffset c) = 0 := by
  unfold CrtTable.chunkShift CrtTable.chunkOffset
  rw [if_pos (Nat.mul_mod_right _ _)]

/-! ### One chunk and one coordinate -/

/-- **The evaluator's chunk with zero joins on absorbed labels is its chunk with the joins.** -/
theorem chunkEvalM_absorb (T : CrtTable) (coord : Nat) (labels labels' : Nat → Label) (v : Nat)
    (J J' : Nat → Label) (pin : Lanes T.castWidth) (c : Nat)
    (first : 0 < T.chunkWidth c → labels' (T.chunkOffset c) = labels (T.chunkOffset c))
    (joined : ∀ n, 1 ≤ n → n < T.chunkWidth c →
      J' n ^^^ labels' (T.chunkOffset c + n) = J n ^^^ labels (T.chunkOffset c + n)) :
    chunkEvalM T coord labels' v J' pin c = chunkEvalM T coord labels v J pin c := by
  have tree := treeEvalM_absorb (chunkTreeTag coord c) (T.chunkValue v c)
    (fun n => labels (T.chunkOffset c + n)) J (fun n => labels' (T.chunkOffset c + n)) J'
    (T.chunkWidth c) (fun positive => by simpa only [Nat.add_zero] using first positive) joined
  unfold chunkEvalM
  simp only [tree]

/-- **No chunk joins, one coordinate.** The evaluator on the material with its chunk joins zeroed
and labels absorbing the joins (`labels' j = labels j ⊕ chunkShift pub.chunkJoin j` on the
coordinate's bits) is the evaluator on the material with its joins and labels `labels`. -/
theorem coordEvalM_absorb (T : CrtTable) (hk : 0 < T.chunkBits) (S coord : Nat) (pub : ConvPublic)
    (records : Fin S → Nat) (v : Nat) (labels labels' : Nat → Label)
    (absorbed : ∀ j < T.inputBits, labels' j = labels j ^^^ T.chunkShift pub.chunkJoin j) :
    coordEvalM T S coord pub.dropChunkJoins records v labels' =
      coordEvalM T S coord pub records v labels := by
  have chunks : ∀ c : Fin T.chunkCount,
      chunkEvalM T coord labels' v (pub.dropChunkJoins.chunkJoin c.val)
          (Parity.pinExpand T.castWidth
            (pinOfBlocks (T.castWidth - 1) fun k => pub.dropChunkJoins.chunkPin c.val k.val)) c.val =
        chunkEvalM T coord labels v (pub.chunkJoin c.val)
          (Parity.pinExpand T.castWidth (pinOfBlocks (T.castWidth - 1) fun k => pub.chunkPin c.val k.val)) c.val := by
    intro c
    refine chunkEvalM_absorb T coord labels labels' v _ _ _ c.val (fun positive => ?_)
      (fun n lower upper => ?_)
    · have inRange := chunkOffset_add_lt T c.val 0 positive
      rw [Nat.add_zero] at inRange
      rw [absorbed _ inRange, chunkShift_first, label_xor_zero]
    · rw [absorbed _ (chunkOffset_add_lt T c.val n upper), chunkShift_at T hk _ c.val n lower upper]
      show (0 : Label) ^^^ (labels (T.chunkOffset c.val + n) ^^^ pub.chunkJoin c.val n) =
        pub.chunkJoin c.val n ^^^ labels (T.chunkOffset c.val + n)
      rw [label_zero_xor]
      exact BitVec.xor_comm _ _
  have mods : ∀ joins chunks, modEvalM T S coord pub.dropChunkJoins joins v chunks =
      modEvalM T S coord pub joins v chunks :=
    fun joins chunks => funext fun i => modEvalM_congr T S coord _ _ joins v chunks i
      fun row _ => modAgree_dropChunkJoins row i.val pub
  unfold coordEvalM
  simp only [chunks, mods]

end Kriterion.CRT.Absorb
