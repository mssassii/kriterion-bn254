/-
CRT slice, delivery part 2: the chunk step (L2 from the constant wire and
L3) on the programs `treeGarbleM`/`treeEvalM` and `chunkGarbleM`/`chunkEvalM` at `.eval H`.

* `treeEvalM_correct` (L2): the evaluator's tree with known bits is the garbler's XOR `Δ` at
  `value mod 2^n` on every level.
* `chunk_correct` (L3): the evaluator's chunk leaves are the garbler's XOR `Δ` at the chunk value,
  and its casts are the garbler's plus `Δ⃗` exactly there (the hot cast recovered from the pin).
-/

import Proof.Correctness.CRT.Word

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

/-! ### Trees from the constant wire -/

theorem eval_treeGarbleM_one (H : HashN) (tagOf : Nat → Nat → Nat) (Δ b0 : Block) :
    (treeGarbleM tagOf Δ b0 1).eval H =
      (extendLevel 0 (fun _ => Δ) (fun _ => b0), fun _ => 0) := by
  simp [treeGarbleM]

theorem eval_treeGarbleM_succ (H : HashN) (tagOf : Nat → Nat → Nat) (Δ b0 : Block) (n : Nat)
    (hn : n ≠ 0) :
    (treeGarbleM tagOf Δ b0 (n + 1)).eval H =
      let prev := (treeGarbleM tagOf Δ b0 n).eval H
      (extendLevel n prev.1 (fun slot => h128 H (prev.1 slot) (tagOf n slot.val)),
        fun level => if level = n then
          xorFold (fun slot => h128 H (prev.1 slot) (tagOf n slot.val)) else prev.2 level) := by
  simp only [treeGarbleM, FreeQuery.eval_bind, if_neg hn, eval_garbleStepM, FreeQuery.eval_pure]

/-- The garbler's level XOR of level `n` (`1 ≤ n < total`), read from the whole tree. -/
theorem treeGarbleM_levelSum (H : HashN) (tagOf : Nat → Nat → Nat) (Δ b0 : Block) :
    ∀ total n, 1 ≤ n → n < total →
      ((treeGarbleM tagOf Δ b0 total).eval H).2 n =
        xorFold (fun slot => h128 H (((treeGarbleM tagOf Δ b0 n).eval H).1 slot) (tagOf n slot.val)) := by
  intro total
  induction total with
  | zero => intro n _ h; exact absurd h (Nat.not_lt_zero n)
  | succ k ih =>
    intro n h1 h2
    by_cases hk : k = 0
    · subst hk; omega
    · rw [eval_treeGarbleM_succ H tagOf Δ b0 k hk]
      simp only
      by_cases hnk : n = k
      · subst hnk; rw [if_pos rfl]
      · rw [if_neg hnk]; exact ih n h1 (by omega)

theorem eval_treeEvalM_one (H : HashN) (tagOf : Nat → Nat → Nat) (value : Nat)
    (bitLabel join : Nat → Block) :
    (treeEvalM tagOf value bitLabel join 1).eval H = extendLevel 0 (fun _ => 0) (fun _ => bitLabel 0) := by
  simp [treeEvalM]

/-- **L2** `treeEvalM_correct`: the evaluator's tree with known bits (bit labels the masks XOR
`value_j·Δ`, the garbler's joins) is the garbler's tree XOR `Δ` at `value mod 2^n`. -/
theorem treeEvalM_correct (H : HashN) (tagOf : Nat → Nat → Nat) (Δ : Block) (value : Nat)
    (bitMask bitLabel join : Nat → Block) (total : Nat)
    (hbit : ∀ j < total, bitLabel j = bitMask j ^^^ (if value.testBit j then Δ else 0))
    (hjoin : ∀ j, 1 ≤ j → j < total →
      join j = ((treeGarbleM tagOf Δ (bitMask 0) total).eval H).2 j ^^^ bitMask j) :
    ∀ n ≤ total, ∀ x : Fin (2 ^ n), (treeEvalM tagOf value bitLabel join n).eval H x =
      ((treeGarbleM tagOf Δ (bitMask 0) n).eval H).1 x ^^^
        (if x.val = value % 2 ^ n then Δ else 0) := by
  intro n
  induction n with
  | zero =>
    intro _ x
    have hx : x.val = 0 := by have := x.isLt; simp at this; omega
    show (0 : Block) = Δ ^^^ _
    rw [if_pos (by rw [hx, pow_zero, Nat.mod_one]), xor_self_block]
  | succ n ih =>
    intro hn x
    by_cases hn0 : n = 0
    · subst hn0
      rw [eval_treeEvalM_one, eval_treeGarbleM_one]
      have hE : ∀ y : Fin (2 ^ 0), (fun _ => (0 : Block)) y =
          (fun _ => Δ) y ^^^ (if y.val = 0 then Δ else 0) := by
        intro y
        have hy : y.val = 0 := by have := y.isLt; simp at this; omega
        simp only [hy, if_true, xor_self_block]
      have hr : ∀ y : Fin (2 ^ 0), (fun _ => bitLabel 0) y =
          (fun _ => bitMask 0) y ^^^ (if y.val = 0 ∧ value.testBit 0 = true then Δ else 0) := by
        intro y
        have hy : y.val = 0 := by have := y.isLt; simp at this; omega
        simp only [hy, true_and]
        exact hbit 0 (by omega)
      rw [extendLevel_invariant _ _ _ _ Δ 0 (by simp) (value.testBit 0) hE hr x]
      congr 2
      rw [mod_two_pow_succ_split, pow_zero, Nat.mod_one]
    · have ihn := ih (by omega)
      simp only [treeEvalM, FreeQuery.eval_bind, if_neg hn0]
      rw [eval_treeGarbleM_succ H tagOf Δ (bitMask 0) n hn0]
      simp only
      have ha : value % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hact : activeAt value n = ⟨value % 2 ^ n, ha⟩ := rfl
      rw [hact, hbit n (by omega), hjoin n (Nat.one_le_iff_ne_zero.mpr hn0) (by omega),
        treeGarbleM_levelSum H tagOf Δ (bitMask 0) total n (Nat.one_le_iff_ne_zero.mpr hn0) (by omega)]
      rw [evalStepM_correct H n (tagOf n) _ _ Δ _ ha (value.testBit n) (bitMask n) ihn x]
      congr 3
      rw [← mod_two_pow_succ_split]

/-! ### The chunk step (L3) -/

theorem atNat_eq_dite {α : Type} {count : Nat} (family : Fin count → α) (default : α) (i : Nat) :
    atNat family default i = if h : i < count then family ⟨i, h⟩ else default := rfl

theorem eval_ite_pure' (H : HashN) {α : Type} (c : Prop) [Decidable c] (a : α) (p : CM α) :
    (if c then (pure a : CM α) else p).eval H = if c then a else p.eval H := by
  split <;> rfl

/-- **L3** `chunk_correct`: the evaluator's chunk `c` (labels `Z_j ⊕ v_j·Δ`, the garbler's joins and
pin) has the garbler's leaves XOR `Δ` at the chunk value and the garbler's casts plus `Δ⃗` exactly
there. -/
theorem chunk_correct (H : HashN) (T : CrtTable) (coord : Nat) (Δ : Block) (Z : Nat → Block)
    (v c : Nat) :
    let g := (chunkGarbleM T coord Δ Z c).eval H
    let e := (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v g.joins g.pin c).eval H
    (∀ α < 2 ^ T.chunkWidth c, e.leaves α = g.leaves α ^^^ (if α = T.chunkValue v c then Δ else 0)) ∧
      (∀ α < 2 ^ T.chunkWidth c, e.casts α =
        g.casts α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ else 0)) := by
  intro g e
  have hslt : T.chunkValue v c < 2 ^ T.chunkWidth c := chunkValue_lt T v c
  have htree := treeEvalM_correct H (chunkTreeTag coord c) Δ (T.chunkValue v c)
    (fun n => Z (T.chunkOffset c + n))
    (fun n => Z (T.chunkOffset c + n) ^^^ (if v.testBit (T.chunkOffset c + n) then Δ else 0))
    (fun n => ((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0))
      (T.chunkWidth c)).eval H).2 n ^^^ Z (T.chunkOffset c + n)) (T.chunkWidth c)
    (by intro j hj; rw [chunkValue_testBit T v c j hj])
    (fun j _ _ => rfl) (T.chunkWidth c) le_rfl
  rw [Nat.mod_eq_of_lt hslt] at htree
  simp only [g, e, chunkGarbleM, chunkEvalM, FreeQuery.eval_bind, eval_tableM, eval_castM,
    FreeQuery.eval_pure, materialize_eq, sumLanes_eq, eval_ite_pure']
  simp only [htree]
  set s := T.chunkValue v c with hs
  set G1 := ((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)).eval H).1
    with hG1
  set A : Fin (2 ^ T.chunkWidth c) → Lanes T.castWidth := fun x =>
    castLanes T.castWidth (hlong H (G1 x) (chunkCastTag coord c x.val) (castAnswers T.castWidth)) with hA
  have key : ∀ x : Fin (2 ^ T.chunkWidth c),
      (if x.val = s then (0 : Lanes T.castWidth) else if x.val = s then 0 else
        castLanes T.castWidth (hlong H (G1 x ^^^ if x.val = s then Δ else 0) (chunkCastTag coord c x.val)
          (castAnswers T.castWidth))) = if x.val = s then 0 else A x := by
    intro x
    by_cases hx : x.val = s
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx, if_neg hx, if_neg hx, xor_zero_block]
  simp only [key]
  refine ⟨fun α hα => ?_, fun α hα => ?_⟩
  · rw [atNat_of_lt _ _ hα, atNat_of_lt _ _ hα]
    exact htree ⟨α, hα⟩
  · by_cases has : α = s
    · rw [if_pos has, if_pos has, atNat_of_lt _ _ hα]
      have hsplit : ∑ x : Fin (2 ^ T.chunkWidth c), A x =
          ∑ x : Fin (2 ^ T.chunkWidth c), (if x.val = s then (0 : Lanes T.castWidth) else A x) + A ⟨α, hα⟩ := by
        have h1 : ∀ x : Fin (2 ^ T.chunkWidth c),
            A x = (if x.val = s then 0 else A x) + (if x = ⟨α, hα⟩ then A x else 0) := by
          intro x
          by_cases hx : x.val = s
          · have hxa : x = ⟨α, hα⟩ := Fin.ext (hx.trans has.symm)
            rw [if_pos hx, if_pos hxa, zero_add]
          · have hxa : x ≠ ⟨α, hα⟩ := fun h => hx (by rw [h]; exact has)
            rw [if_neg hx, if_neg hxa, add_zero]
        conv_lhs => rw [Finset.sum_congr rfl (fun x _ => h1 x)]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [hsplit]
      ring
    · rw [if_neg has, if_neg has, atNat_of_lt _ _ hα, atNat_of_lt _ _ hα, add_zero]
      simp only
      rw [if_neg has, if_neg has, xor_zero_block]

end Kriterion.CRT.SliceC
