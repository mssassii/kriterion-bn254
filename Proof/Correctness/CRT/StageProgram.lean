/-
CRT slice, conversion chain part B: the fused extraction stage as the query programs
(`Construction/CRT/Extract.lean`: `extStageGarbleM`, `extStageEvalM`) on `.eval H`, for every
`H : HashN` (L8 to L10 on the programs).

* The garbler program computes the pure stage of `ExtractSpec` at `hashStage H w hw treeTag castTag`
  (`extStageGarbleM_eval`).
* The evaluator program's state after round `n` holds the garbler's labels on every node and leaf
  that branches off the active path before level `n`, and its level XORs, class sums and cast sums
  are the garbler's over exactly those nodes and leaves (`Sums`, `expandM_sums`); its active label
  is the garbler's active node XOR `Δ` and its bit labels are the masks XOR `s_k·Δ`
  (`stageRoundM_inv`, `stageRoundsM_inv`).
* `extStage_correct`: leaves `G_α ⊕ [α = s]·Δ`, bits `b_n ⊕ s_n·Δ`, next remainder
  `R' + ⌊σ / 2^w⌋•Δ⃗`.
-/

import Proof.Correctness.CRT.TreeSteps

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

/-! ### Finite sums over slots -/

theorem xsum_filter_ind {s : Finset Nat} (p : Nat → Prop) [DecidablePred p] (f : Nat → Block) :
    xsum (s.filter p) f = xsum s (fun x => if p x then f x else 0) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.filter_insert]
    by_cases hp : p a
    · rw [if_pos hp, xsum_insert_nat (fun h => ha (Finset.mem_filter.mp h).1), xsum_insert_nat ha, ih,
        if_pos hp]
    · rw [if_neg hp, xsum_insert_nat ha, ih, if_neg hp, zero_xor_block]

theorem xsum_xor {s : Finset Nat} (f g : Nat → Block) :
    xsum s (fun x => f x ^^^ g x) = xsum s f ^^^ xsum s g := by
  induction s using Finset.induction_on with
  | empty => show (0 : Block) = 0 ^^^ 0; rw [xor_zero_block]
  | insert a s ha ih =>
    rw [xsum_insert_nat ha, xsum_insert_nat ha, xsum_insert_nat ha, ih]
    xor_norm

theorem image_slot (start d slot : Nat) (hslot : slot < 2 ^ start) :
    (Finset.range (2 ^ d)).image (fun t => slot + 2 ^ start * t) =
      (Finset.range (2 ^ (start + d))).filter (fun x => x % 2 ^ start = slot) := by
  have hpos := Nat.two_pow_pos start
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [pow_add]
      calc slot + 2 ^ start * t < 2 ^ start * (t + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ 2 ^ start * 2 ^ d := Nat.mul_le_mul_left _ ht
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hslot]
  · rintro ⟨hx, hmod⟩
    refine ⟨x / 2 ^ start, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, Nat.add_comm]; exact hx
    · rw [← hmod]; exact Nat.mod_add_div x (2 ^ start)

theorem injOn_slot (start slot : Nat) (s : Set Nat) :
    Set.InjOn (fun t => slot + 2 ^ start * t) s := by
  intro a _ b _ h
  have h' : 2 ^ start * a = 2 ^ start * b := by simpa using h
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos start) h'

/-- XOR over the relative slots of a subtree is the XOR over its absolute slots. -/
theorem xsum_slot (start d slot : Nat) (hslot : slot < 2 ^ start) (F : Nat → Block) :
    xsum (Finset.range (2 ^ d)) (fun t => F (slot + 2 ^ start * t)) =
      xsum (Finset.range (2 ^ (start + d))) (fun x => if x % 2 ^ start = slot then F x else 0) := by
  rw [← xsum_filter_ind, ← image_slot start d slot hslot]
  unfold xsum
  rw [Finset.fold_image (injOn_slot start slot _)]
  rfl

/-- Sum over the relative leaves of a subtree is the sum over its absolute leaves. -/
theorem sum_slot {M : Type} [AddCommMonoid M] (start d slot : Nat) (hslot : slot < 2 ^ start)
    (F : Nat → M) :
    ∑ t ∈ Finset.range (2 ^ d), F (slot + 2 ^ start * t) =
      ∑ x ∈ Finset.range (2 ^ (start + d)), (if x % 2 ^ start = slot then F x else 0) := by
  rw [← Finset.sum_filter, ← image_slot start d slot hslot,
    Finset.sum_image (injOn_slot start slot _)]

theorem sum_slot' {M : Type} [AddCommMonoid M] (start d slot total : Nat) (htot : start + d = total)
    (hslot : slot < 2 ^ start) (F : Nat → M) :
    ∑ t ∈ Finset.range (2 ^ d), F (slot + 2 ^ start * t) =
      ∑ x ∈ Finset.range (2 ^ total), (if x % 2 ^ start = slot then F x else 0) := by
  subst htot; exact sum_slot start d slot hslot F

/-! ### Arithmetic of slots -/

theorem slot_mod (start d slot t : Nat) (hslot : slot < 2 ^ start) :
    (slot + 2 ^ start * t) % 2 ^ (start + d) = slot + 2 ^ start * (t % 2 ^ d) := by
  rw [pow_add, Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hslot,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos start), Nat.div_eq_of_lt hslot, Nat.zero_add]

theorem slot_testBit (start d slot t : Nat) (hslot : slot < 2 ^ start) :
    (slot + 2 ^ start * t).testBit (start + d) = t.testBit d := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add t hslot, if_neg (by omega), Nat.add_sub_cancel_left]

/-- Branching off the active path before level `n + 1`: before level `n`, or at the closed node `c`
of round `n`. -/
theorem branch_succ_iff {x s c n : Nat} (hc : c < 2 ^ (n + 1)) (hcs : c % 2 ^ n = s % 2 ^ n)
    (hcb : c.testBit n ≠ s.testBit n) :
    (x % 2 ^ (n + 1) ≠ s % 2 ^ (n + 1)) ↔ (x % 2 ^ n ≠ s % 2 ^ n ∨ x % 2 ^ (n + 1) = c) := by
  have hcm : c % 2 ^ (n + 1) = c := Nat.mod_eq_of_lt hc
  constructor
  · intro h
    by_cases hA : x % 2 ^ n = s % 2 ^ n
    · right
      have hxb : x.testBit n ≠ s.testBit n := fun hb => h (mod_succ_eq_of hA hb)
      have hxc : x.testBit n = c.testBit n := by
        cases h1 : x.testBit n <;> cases h2 : c.testBit n <;> cases h3 : s.testBit n <;> simp_all
      rw [← hcm]
      exact mod_succ_eq_of (hA.trans hcs.symm) hxc
    · left; exact hA
  · rintro (h | h) heq
    · exact h (by rw [← mod_two_pow_mod_of_le (x := x) (Nat.le_succ n),
        ← mod_two_pow_mod_of_le (x := s) (Nat.le_succ n), heq])
    · rw [h] at heq
      have := congrArg (fun y => y.testBit n) heq
      simp only [Nat.testBit_mod_two_pow, Nat.lt_succ_self n, decide_true, Bool.true_and] at this
      exact hcb this

theorem branch_disjoint {x s c n : Nat} (hcs : c % 2 ^ n = s % 2 ^ n) :
    ¬ (x % 2 ^ n ≠ s % 2 ^ n ∧ x % 2 ^ (n + 1) = c) := by
  rintro ⟨h1, h2⟩
  apply h1
  rw [← mod_two_pow_mod_of_le (x := x) (Nat.le_succ n), h2, hcs]

theorem ite_xor_union {A B C : Prop} [Decidable A] [Decidable B] [Decidable C] (hC : C ↔ (A ∨ B))
    (hd : ¬ (A ∧ B)) (v : Block) :
    (if A then v else 0) ^^^ (if B then v else 0) = if C then v else 0 := by
  by_cases hA : A <;> by_cases hB : B
  · exact absurd ⟨hA, hB⟩ hd
  · rw [if_pos hA, if_neg hB, if_pos (hC.mpr (Or.inl hA)), xor_zero_block]
  · rw [if_neg hA, if_pos hB, if_pos (hC.mpr (Or.inr hB)), zero_xor_block]
  · rw [if_neg hA, if_neg hB, if_neg (fun h => (hC.mp h).elim hA hB), xor_zero_block]

theorem ite_add_union {M : Type} [AddCommMonoid M] {A B C : Prop} [Decidable A] [Decidable B]
    [Decidable C] (hC : C ↔ (A ∨ B)) (hd : ¬ (A ∧ B)) (v : M) :
    (if A then v else 0) + (if B then v else 0) = if C then v else 0 := by
  by_cases hA : A <;> by_cases hB : B
  · exact absurd ⟨hA, hB⟩ hd
  · rw [if_pos hA, if_neg hB, if_pos (hC.mpr (Or.inl hA)), add_zero]
  · rw [if_neg hA, if_pos hB, if_pos (hC.mpr (Or.inr hB)), zero_add]
  · rw [if_neg hA, if_neg hB, if_neg (fun h => (hC.mp h).elim hA hB), add_zero]

/-! ### Helpers on the programs -/

theorem stepMat_pos {rb : Nat} (sp : StageParams rb) (b0 : Block) {n : Nat} (hn : 1 ≤ n) (x : Nat)
    (lab : Block) : stepMat sp b0 n x lab = sp.mat n x lab := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem eval_castM (H : HashN) (l : Nat) (label : Block) (tagOf : Nat → Nat) :
    (castM l label tagOf).eval H = castLanes l (hlong H label tagOf (castAnswers l)) := by
  simp [castM, materialize_eq]

theorem scaleLanes_eq {l : Nat} (k : Nat) (A : Lanes l) : scaleLanes k A = (k : ZMod (2 ^ l)) • A := by
  funext lane; rfl

theorem sumLanes_eq {l count : Nat} (family : Fin count → Lanes l) :
    sumLanes family = ∑ index, family index := materialize_eq _

theorem atNat_of_lt {α : Type} {count : Nat} (family : Fin count → α) (default : α) {i : Nat}
    (h : i < count) : atNat family default i = family ⟨i, h⟩ := by
  simp [atNat, h]

/-! ### The garbler program -/

section Garbler

variable (H : HashN) {rb : Nat}

theorem eval_treeGarbleM (tagOf : Nat → Nat → Nat) (Δ b0 : Block) (sp : StageParams rb)
    (hmat : ∀ n x lab, sp.mat n x lab = h128 H lab (tagOf n x)) :
    ∀ levels,
      (∀ x : Fin (2 ^ levels), ((treeGarbleM tagOf Δ b0 levels).eval H).1 x =
        gNode sp b0 Δ levels x.val) ∧
      (∀ level, ((treeGarbleM tagOf Δ b0 levels).eval H).2 level =
        if 1 ≤ level ∧ level < levels then
          xsum (Finset.range (2 ^ level)) (fun x => sp.mat level x (gNode sp b0 Δ level x))
        else 0) := by
  intro levels
  induction levels with
  | zero =>
    refine ⟨fun x => rfl, fun level => ?_⟩
    rw [if_neg (by omega)]
    rfl
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hn : n = 0
    · subst hn
      simp only [treeGarbleM, FreeQuery.eval_bind, if_true, FreeQuery.eval_pure, stored_eq]
      refine ⟨fun x => ?_, fun level => ?_⟩
      · rw [extendLevel_eq, gNode_succ]
        rfl
      · rw [if_neg (by omega)]
    · simp only [treeGarbleM, FreeQuery.eval_bind, if_neg hn, eval_garbleStepM, FreeQuery.eval_pure]
      refine ⟨fun x => ?_, fun level => ?_⟩
      · rw [extendLevel_eq, gNode_succ, stepMat_pos sp b0 (Nat.one_le_iff_ne_zero.mpr hn), ih1, hmat]
      · by_cases hl : level = n
        · subst hl
          rw [if_pos rfl, if_pos ⟨Nat.one_le_iff_ne_zero.mpr hn, Nat.lt_succ_self _⟩, xorFold_eq_xsum]
          apply xsum_congr
          intro x hx
          rw [dif_pos (Finset.mem_range.mp hx), ih1, hmat]
        · rw [if_neg hl, ih2]
          by_cases hc : 1 ≤ level ∧ level < n
          · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
          · rw [if_neg hc, if_neg (by omega)]

variable (w : Nat) (hw : w ≤ rb) (treeTag castTag : Nat → Nat → Nat)

/-- The garbler program computes the pure stage of `ExtractSpec` over the layer's hash. -/
theorem extStageGarbleM_eval (Δ : Block) (R : Lanes rb) :
    let sp := hashStage H w hw treeTag castTag
    let g := (extStageGarbleM w treeTag castTag Δ R).eval H
    (∀ α < 2 ^ w, g.leaves α = gLeaf sp R Δ α) ∧
      (∀ n < w, g.bits n = gBit sp R Δ n) ∧
      (∀ n, 1 ≤ n → n < w → g.joins n = gJoin sp R Δ n) ∧
      g.pin = gPin sp R Δ ∧ g.next = gNext sp R Δ := by
  intro sp g
  have htree := eval_treeGarbleM H treeTag Δ (laneBit (reduceTo w R) 0) sp (fun _ _ _ => rfl) w
  obtain ⟨ht1, ht2⟩ := htree
  have hcast : ∀ α (hα : α < 2 ^ w), sp.castF α (((treeGarbleM treeTag Δ (laneBit (reduceTo w R) 0) w).eval H).1
      ⟨α, hα⟩) = gCast sp R Δ α := by
    intro α hα
    rw [ht1]; rfl
  have hres : ∀ n, (∑ leaf : Fin (2 ^ w), scaleLanes (leaf.val % 2 ^ n)
      (castLanes rb (hlong H (((treeGarbleM treeTag Δ (laneBit (reduceTo w R) 0) w).eval H).1 leaf)
        (castTag leaf.val) (castAnswers rb)))) = gRes sp R Δ n := by
    intro n
    unfold gRes
    rw [← Fin.sum_univ_eq_sum_range (fun α => ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • gCast sp R Δ α)]
    apply Finset.sum_congr rfl
    intro leaf _
    rw [scaleLanes_eq, ← hcast leaf.val leaf.isLt]
    rfl
  have hpinsum : (∑ leaf : Fin (2 ^ w),
      castLanes rb (hlong H (((treeGarbleM treeTag Δ (laneBit (reduceTo w R) 0) w).eval H).1 leaf)
        (castTag leaf.val) (castAnswers rb))) = ∑ α ∈ Finset.range (2 ^ w), gCast sp R Δ α := by
    rw [← Fin.sum_univ_eq_sum_range (fun α => gCast sp R Δ α)]
    apply Finset.sum_congr rfl
    intro leaf _
    rw [← hcast leaf.val leaf.isLt]
    rfl
  have hbit : ∀ n < w, (if n = 0 then laneBit (reduceTo w R) 0
      else laneBit (reduceTo w R - reduceTo w (gRes sp R Δ n)) n) = gBit sp R Δ n := by
    intro n _; rfl
  simp only [g, extStageGarbleM, FreeQuery.eval_bind, eval_tableM, eval_castM, FreeQuery.eval_pure,
    materialize_eq, stored_eq, sumLanes_eq]
  refine ⟨fun α hα => ?_, fun n hn => ?_, fun n hn1 hnw => ?_, ?_, ?_⟩
  · rw [atNat_of_lt _ _ hα, ht1]; rfl
  · rw [atNat_of_lt _ _ hn, atNat_of_lt _ _ (by omega : n < w + 1)]
    simp only
    rw [hres]
    exact hbit n hn
  · rw [ht2, if_pos ⟨hn1, hnw⟩, atNat_of_lt _ _ hnw, atNat_of_lt _ _ (by omega : n < w + 1)]
    simp only
    rw [hres, hbit n hnw]
    rfl
  · rw [hpinsum]; rfl
  · rw [atNat_of_lt _ _ (by omega : w < w + 1)]
    simp only
    rw [hres]
    rfl

end Garbler

/-! ### Algebra of one round -/

theorem xsum_zero_fun {s : Finset Nat} : xsum s (fun _ => (0 : Block)) = 0 := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [xsum_insert_nat ha, ih, xor_zero_block]

/-- The XOR over a level is the active slot's material XOR the XOR over the other slots. -/
theorem xsum_single_out (n q : Nat) (hq : q < 2 ^ n) (F : Nat → Block) :
    xsum (Finset.range (2 ^ n)) F =
      F q ^^^ xsum (Finset.range (2 ^ n)) (fun x => if x % 2 ^ n ≠ q then F x else 0) := by
  rw [xsum_erase (Finset.mem_range.mpr hq), ← Finset.filter_ne', xsum_filter_ind]
  congr 1
  apply xsum_congr
  intro x hx
  rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hx)]

/-- **L8**, generic: with the closed leaves' class and cast sums and the pin,
`R_n + q • (P - T_n) = res_n + q • Δ⃗`. -/
theorem classSum_identity {rb : Nat} (N : Nat) (A : Nat → Lanes rb) (Δ : Block) (n q : Nat) :
    (∑ α ∈ Finset.range N,
        if α % 2 ^ n ≠ q then ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • A α else 0) +
      ((q : Nat) : ZMod (2 ^ rb)) • ((∑ α ∈ Finset.range N, A α + deltaLanes rb Δ) -
        ∑ α ∈ Finset.range N, if α % 2 ^ n ≠ q then A α else 0) =
    ∑ α ∈ Finset.range N, ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) • A α +
      ((q : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ite_apply,
    Pi.zero_apply]
  have hsplitA : ∑ α ∈ Finset.range N, A α i =
      ∑ α ∈ Finset.range N, (if α % 2 ^ n ≠ q then A α i else 0) +
        ∑ α ∈ Finset.range N, (if α % 2 ^ n ≠ q then 0 else A α i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs <;> simp
  have hsplitC : ∑ α ∈ Finset.range N, ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) * A α i =
      ∑ α ∈ Finset.range N, (if α % 2 ^ n ≠ q then ((α % 2 ^ n : Nat) : ZMod (2 ^ rb)) * A α i else 0) +
        ((q : Nat) : ZMod (2 ^ rb)) *
          ∑ α ∈ Finset.range N, (if α % 2 ^ n ≠ q then 0 else A α i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    by_cases h : α % 2 ^ n ≠ q
    · rw [if_pos h, if_pos h, mul_zero, add_zero]
    · rw [if_neg h, if_neg h, zero_add, not_not.mp h]
  rw [hsplitA, hsplitC]
  ring

/-- The bit of round `n ≥ 1` (L7 through L8). -/
theorem bit_of_classSum {rb : Nat} (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (σ n : Nat)
    (hn : n < sp.w) (hn0 : n ≠ 0) :
    laneBit (reduceTo sp.w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) -
      reduceTo sp.w (gRes sp R Δ n + ((σ % 2 ^ n : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ)) n =
    gBit sp R Δ n ^^^ (if σ.testBit n then Δ else 0) := by
  have hrb : n < rb := Nat.lt_of_lt_of_le hn sp.hw
  rw [← reduceTo_sub sp.hw, laneBit_reduceTo hn, gBit_succ sp R Δ n hn hn0]
  have hsplit : R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ -
      (gRes sp R Δ n + ((σ % 2 ^ n : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ) =
      (R - gRes sp R Δ n) + ((2 ^ n * (σ / 2 ^ n) : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ := by
    have hσ : (σ : ZMod (2 ^ rb)) = ((σ % 2 ^ n : Nat) : ZMod (2 ^ rb)) +
        ((2 ^ n * (σ / 2 ^ n) : Nat) : ZMod (2 ^ rb)) := by
      rw [← Nat.cast_add, Nat.mod_add_div]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hσ]
    ring
  rw [hsplit, laneBit_add_shift hrb, Nat.testBit_div_two_pow, Nat.zero_add]

/-- The bit-0 label (L7 at `n = 0`). -/
theorem bit0_label {rb : Nat} (sp : StageParams rb) (hw1 : 1 ≤ sp.w) (R : Lanes rb) (Δ : Block)
    (σ : Nat) :
    laneBit (reduceTo sp.w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) 0 =
      gBit0 sp R ^^^ (if σ.testBit 0 then Δ else 0) := by
  have hrb : 0 < rb := Nat.lt_of_lt_of_le hw1 sp.hw
  unfold gBit0
  rw [laneBit_reduceTo hw1, laneBit_reduceTo hw1, laneBit_add_smul_delta_zero hrb, Nat.testBit_zero]
  by_cases hσ : σ % 2 = 1 <;> simp [hσ]

/-! ### The evaluator program -/

section Evaluator

variable (H : HashN) {rb : Nat} (w : Nat) (hw : w ≤ rb) (treeTag castTag : Nat → Nat → Nat)

@[simp] theorem hashStage_w (H : HashN) {rb : Nat} (w : Nat) (hw : w ≤ rb)
    (treeTag castTag : Nat → Nat → Nat) : (hashStage H w hw treeTag castTag).w = w := rfl

theorem eval_subtreeM (sp : StageParams rb) (hmat : ∀ n x lab, sp.mat n x lab = h128 H lab (treeTag n x))
    (b0 Δ : Block) (start slot : Nat) (hstart : 1 ≤ start) (hslot : slot < 2 ^ start) :
    ∀ d, (∀ t : Fin (2 ^ d),
        ((subtreeM treeTag start slot (gNode sp b0 Δ start slot) d).eval H).1 t =
          gNode sp b0 Δ (start + d) (slot + 2 ^ start * t.val)) ∧
      (∀ level, ((subtreeM treeTag start slot (gNode sp b0 Δ start slot) d).eval H).2 level =
        if start ≤ level ∧ level < start + d then
          xsum (Finset.range (2 ^ level))
            (fun x => if x % 2 ^ start = slot then sp.mat level x (gNode sp b0 Δ level x) else 0)
        else 0) := by
  intro d
  induction d with
  | zero =>
    refine ⟨fun t => ?_, fun level => ?_⟩
    · have ht : t.val = 0 := by have := t.isLt; simp at this; omega
      simp only [subtreeM, FreeQuery.eval_pure, ht, Nat.mul_zero, Nat.add_zero]
    · rw [if_neg (by omega)]
      rfl
  | succ d ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [subtreeM, FreeQuery.eval_bind, eval_garbleStepM, FreeQuery.eval_pure]
    refine ⟨fun t => ?_, fun level => ?_⟩
    · rw [extendLevel_eq, ih1]
      show _ = gNode sp b0 Δ ((start + d) + 1) (slot + 2 ^ start * t.val)
      rw [gNode_succ, slot_mod start d slot t.val hslot, slot_testBit start d slot t.val hslot,
        stepMat_pos sp b0 (by omega), hmat]
    · by_cases hl : level = start + d
      · subst hl
        rw [if_pos rfl, if_pos ⟨by omega, by omega⟩, xorFold_eq_xsum,
          ← xsum_slot start d slot hslot (fun x => sp.mat (start + d) x (gNode sp b0 Δ (start + d) x))]
        apply xsum_congr
        intro t ht
        rw [dif_pos (Finset.mem_range.mp ht), ih1, hmat]
      · rw [if_neg hl, ih2]
        by_cases hc : start ≤ level ∧ level < start + d
        · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
        · rw [if_neg hc, if_neg (by omega)]

/-- The evaluator's sums after the closed nodes of rounds `0 .. n - 1` are expanded: the garbler's
materials, class sums and casts over exactly the nodes and leaves that branch off the active path of
`s` before level `n`, and the garbler's labels on those leaves. -/
def Sums (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (s n : Nat) (st : StageState rb) : Prop :=
  (∀ j, 1 ≤ j → j < sp.w → st.levelSum j = xsum (Finset.range (2 ^ j)) (fun x =>
      if x % 2 ^ (min j n) ≠ s % 2 ^ (min j n) then sp.mat j x (gNode sp (gBit0 sp R) Δ j x) else 0)) ∧
  (∀ j ≤ sp.w, st.classSum j = ∑ α ∈ Finset.range (2 ^ sp.w),
      (if α % 2 ^ (min j n) ≠ s % 2 ^ (min j n) then
        ((α % 2 ^ j : Nat) : ZMod (2 ^ rb)) • gCast sp R Δ α else 0)) ∧
  (∀ j ≤ sp.w, st.castSum j = ∑ α ∈ Finset.range (2 ^ sp.w),
      (if α % 2 ^ (min j n) ≠ s % 2 ^ (min j n) then gCast sp R Δ α else 0)) ∧
  (∀ α < 2 ^ sp.w, α % 2 ^ n ≠ s % 2 ^ n → st.leaves α = gLeaf sp R Δ α)

/-- Expanding the closed node `c` of round `n` (label: the garbler's) moves the sums from `n` to
`n + 1` and leaves the active label and the bits alone. -/
theorem expandM_sums (R : Lanes rb) (Δ : Block) (s n : Nat) (hn : n < w) (c : Nat)
    (hc : c < 2 ^ (n + 1)) (hcs : c % 2 ^ n = s % 2 ^ n) (hcb : c.testBit n ≠ s.testBit n)
    (st : StageState rb) (hst : Sums (hashStage H w hw treeTag castTag) R Δ s n st) :
    let st' := (expandM w treeTag castTag (n + 1) c (gNode (hashStage H w hw treeTag castTag)
      (gBit0 (hashStage H w hw treeTag castTag) R) Δ (n + 1) c) st).eval H
    Sums (hashStage H w hw treeTag castTag) R Δ s (n + 1) st' ∧ st'.active = st.active ∧
      st'.bits = st.bits := by
  intro st'
  set sp := hashStage H w hw treeTag castTag with hsp
  have hspw : sp.w = w := rfl
  obtain ⟨hL, hC, hT, hE⟩ := hst
  simp only [hspw] at hL hC hT hE
  have hsub := eval_subtreeM H treeTag sp (fun _ _ _ => rfl) (gBit0 sp R) Δ (n + 1) c (by omega) hc
    (w - (n + 1))
  obtain ⟨hs1, hs2⟩ := hsub
  have hwn : n + 1 + (w - (n + 1)) = w := by omega
  have hleaf : ∀ t : Fin (2 ^ (w - (n + 1))),
      ((subtreeM treeTag (n + 1) c (gNode sp (gBit0 sp R) Δ (n + 1) c) (w - (n + 1))).eval H).1 t =
        gLeaf sp R Δ (c + 2 ^ (n + 1) * t.val) := by
    intro t
    rw [hs1]
    unfold gLeaf
    rw [hwn]
    rfl
  have hcastsum : ∀ (V : Nat → ZMod (2 ^ rb)),
      (∑ t : Fin (2 ^ (w - (n + 1))), V (c + 2 ^ (n + 1) * t.val) •
        castLanes rb (hlong H (((subtreeM treeTag (n + 1) c (gNode sp (gBit0 sp R) Δ (n + 1) c)
          (w - (n + 1))).eval H).1 t) (castTag (c + 2 ^ (n + 1) * t.val)) (castAnswers rb))) =
      ∑ α ∈ Finset.range (2 ^ w), (if α % 2 ^ (n + 1) = c then V α • gCast sp R Δ α else 0) := by
    intro V
    rw [← sum_slot' (n + 1) (w - (n + 1)) c w hwn hc (fun α => V α • gCast sp R Δ α),
      ← Fin.sum_univ_eq_sum_range (fun t => V (c + 2 ^ (n + 1) * t) • gCast sp R Δ (c + 2 ^ (n + 1) * t))]
    apply Finset.sum_congr rfl
    intro t _
    rw [hleaf]
    rfl
  have hbr := fun x => branch_succ_iff (x := x) hc hcs hcb
  have hdj := fun x => branch_disjoint (x := x) (c := c) hcs
  simp only [st', expandM, FreeQuery.eval_bind, eval_tableM, eval_castM, FreeQuery.eval_pure]
  refine ⟨⟨fun j hj1 hjw => ?_, fun j hjw => ?_, fun j hjw => ?_, fun α hα hne => ?_⟩,
    by first | rfl | trivial, by first | rfl | trivial⟩
  all_goals simp only [hspw] at *
  · -- level XORs
    show st.levelSum j ^^^ _ = _
    rw [hs2, hL j hj1 hjw]
    by_cases hj : n + 1 ≤ j
    · rw [if_pos ⟨hj, by omega⟩, Nat.min_eq_right (by omega : n ≤ j),
        Nat.min_eq_right hj, ← xsum_xor]
      apply xsum_congr
      intro x _
      exact ite_xor_union (hbr x) (hdj x) _
    · rw [if_neg (by omega), xor_zero_block, Nat.min_eq_left (by omega : j ≤ n),
        Nat.min_eq_left (by omega : j ≤ n + 1)]
  · -- class sums
    show atNat _ 0 j = _
    rw [atNat_of_lt _ _ (by omega : j < w + 1)]
    simp only [stored_eq, materialize_eq, sumLanes_eq, scaleLanes_eq]
    by_cases hj : n + 1 ≤ j
    · rw [if_pos hj, hC j hjw, hcastsum (fun α => ((α % 2 ^ j : Nat) : ZMod (2 ^ rb))),
        Nat.min_eq_right (by omega : n ≤ j), Nat.min_eq_right hj, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro α _
      exact ite_add_union (hbr α) (hdj α) _
    · rw [if_neg hj, hC j hjw, Nat.min_eq_left (by omega : j ≤ n),
        Nat.min_eq_left (by omega : j ≤ n + 1)]
  · -- cast sums
    show atNat _ 0 j = _
    rw [atNat_of_lt _ _ (by omega : j < w + 1)]
    simp only [stored_eq, materialize_eq, sumLanes_eq]
    by_cases hj : n + 1 ≤ j
    · have h1 := hcastsum (fun _ => 1)
      simp only [one_smul] at h1
      rw [if_pos hj, hT j hjw, h1, Nat.min_eq_right (by omega : n ≤ j), Nat.min_eq_right hj,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro α _
      exact ite_add_union (hbr α) (hdj α) _
    · rw [if_neg hj, hT j hjw, Nat.min_eq_left (by omega : j ≤ n),
        Nat.min_eq_left (by omega : j ≤ n + 1)]
  · -- leaves
    show (if α < 2 ^ w ∧ α % 2 ^ (n + 1) = c then _ else st.leaves α) = _
    by_cases hαc : α % 2 ^ (n + 1) = c
    · rw [if_pos ⟨hα, hαc⟩]
      have hlt : α / 2 ^ (n + 1) < 2 ^ (w - (n + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm, hwn]; exact hα
      rw [atNat_of_lt _ _ hlt, hleaf]
      congr 1
      simp only
      rw [← hαc]
      exact Nat.mod_add_div α (2 ^ (n + 1))
    · rw [if_neg (fun h => hαc h.2)]
      have := (hbr α).mp hne
      exact hE α hα (this.resolve_right hαc)

/-- The round invariant of the evaluator program. -/
def Inv (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (s n : Nat) (st : StageState rb) : Prop :=
  st.active = gNode sp (gBit0 sp R) Δ n (s % 2 ^ n) ^^^ Δ ∧ Sums sp R Δ s n st ∧
    ∀ k < n, st.bits k = gBit sp R Δ k ^^^ (if s.testBit k then Δ else 0)

theorem gNode_succ_active {rb : Nat} (sp : StageParams rb) (b0 Δ : Block) (s n : Nat) :
    gNode sp b0 Δ (n + 1) (s % 2 ^ (n + 1)) =
      if s.testBit n then stepMat sp b0 n (s % 2 ^ n) (gNode sp b0 Δ n (s % 2 ^ n))
      else gNode sp b0 Δ n (s % 2 ^ n) ^^^ stepMat sp b0 n (s % 2 ^ n) (gNode sp b0 Δ n (s % 2 ^ n)) := by
  have hsq : (s % 2 ^ (n + 1)) % 2 ^ n = s % 2 ^ n := mod_two_pow_mod_of_le (Nat.le_succ n)
  have hsb : (s % 2 ^ (n + 1)).testBit n = s.testBit n := by
    rw [Nat.testBit_mod_two_pow]; simp
  rw [gNode_succ, hsq, hsb]

/-- After expanding the closed node of round `n` from a state with the sums of round `n`, the round
invariant of `n + 1` holds as soon as the active label and the bits are right. -/
theorem inv_after_expand (R : Lanes rb) (Δ : Block) (s n : Nat) (hn : n < w) (c : Nat)
    (hc : c < 2 ^ (n + 1)) (hcs : c % 2 ^ n = s % 2 ^ n) (hcb : c.testBit n ≠ s.testBit n)
    (label : Block) (st : StageState rb)
    (hst : Sums (hashStage H w hw treeTag castTag) R Δ s n st)
    (hlabel : label = gNode (hashStage H w hw treeTag castTag)
      (gBit0 (hashStage H w hw treeTag castTag) R) Δ (n + 1) c)
    (hact : st.active = gNode (hashStage H w hw treeTag castTag)
      (gBit0 (hashStage H w hw treeTag castTag) R) Δ (n + 1) (s % 2 ^ (n + 1)) ^^^ Δ)
    (hbits : ∀ k < n + 1, st.bits k =
      gBit (hashStage H w hw treeTag castTag) R Δ k ^^^ (if s.testBit k then Δ else 0)) :
    Inv (hashStage H w hw treeTag castTag) R Δ s (n + 1)
      ((expandM w treeTag castTag (n + 1) c label st).eval H) := by
  subst hlabel
  obtain ⟨hs', ha', hb'⟩ := expandM_sums H w hw treeTag castTag R Δ s n hn c hc hcs hcb st hst
  exact ⟨ha'.trans hact, hs', fun k hk => (congrFun hb' k).trans (hbits k hk)⟩

/-- **L10 on the program**, one round `1 ≤ n < w`. -/
theorem stageRoundM_inv (R : Lanes rb) (Δ : Block) (σ : Nat) (joins : Nat → Block) (pin : Lanes rb)
    (hJ : ∀ n, 1 ≤ n → n < w → joins n = gJoin (hashStage H w hw treeTag castTag) R Δ n)
    (hP : pin = gPin (hashStage H w hw treeTag castTag) R Δ)
    (n : Nat) (hn1 : 1 ≤ n) (hn : n < w) (st : StageState rb)
    (hinv : Inv (hashStage H w hw treeTag castTag) R Δ (σ % 2 ^ w) n st) :
    Inv (hashStage H w hw treeTag castTag) R Δ (σ % 2 ^ w) (n + 1)
      ((stageRoundM w treeTag castTag (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)))
        (σ % 2 ^ w) joins pin n st).eval H) := by
  set sp := hashStage H w hw treeTag castTag with hsp
  set s := σ % 2 ^ w with hs
  obtain ⟨hact, hsums, hbits⟩ := hinv
  obtain ⟨hL, hC, hT, hE⟩ := hsums
  have hspw : sp.w = w := rfl
  simp only [hspw] at hL hC hT hE
  have hq : s % 2 ^ n = σ % 2 ^ n := mod_two_pow_mod_of_le (Nat.le_of_lt hn)
  have hsn : s.testBit n = σ.testBit n := by rw [hs, Nat.testBit_mod_two_pow]; simp [hn]
  have hqlt : s % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  -- the class sum of the round
  have hclass : materialize (st.classSum n + scaleLanes (s % 2 ^ n) (pin - st.castSum n)) =
      gRes sp R Δ n + ((σ % 2 ^ n : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ := by
    rw [materialize_eq, scaleLanes_eq, hC n (Nat.le_of_lt hn), hT n (Nat.le_of_lt hn), Nat.min_self, hP]
    unfold gPin gRes
    simp only [hspw]
    rw [classSum_identity, hq]
  -- the bit of the round
  have hbit : laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) -
      reduceTo w (materialize (st.classSum n + scaleLanes (s % 2 ^ n) (pin - st.castSum n)))) n =
      gBit sp R Δ n ^^^ (if s.testBit n then Δ else 0) := by
    rw [hclass, materialize_eq, hsn]
    exact bit_of_classSum sp R Δ σ n hn (by omega)
  -- the hot material
  have hlev : gLevelSum sp R Δ n =
      sp.mat n (s % 2 ^ n) (gNode sp (gBit0 sp R) Δ n (s % 2 ^ n)) ^^^ st.levelSum n := by
    rw [hL n hn1 hn, Nat.min_self]
    exact xsum_single_out n _ hqlt _
  have hhot : laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) -
      reduceTo w (materialize (st.classSum n + scaleLanes (s % 2 ^ n) (pin - st.castSum n)))) n ^^^
        joins n ^^^ st.levelSum n =
      stepMat sp (gBit0 sp R) n (s % 2 ^ n) (gNode sp (gBit0 sp R) Δ n (s % 2 ^ n)) ^^^
        (if s.testBit n then Δ else 0) := by
    rw [hbit, hJ n hn1 hn, stepMat_pos sp _ hn1]
    unfold gJoin
    rw [hlev]
    exact xor_hot_solve _ _ _ _
  have hGs := gNode_succ_active sp (gBit0 sp R) Δ s n
  unfold stageRoundM
  simp only
  rw [hhot, hbit, hact]
  cases hsb : s.testBit n
  · -- bit `n` is 0: the right child `q + 2^n` is closed
    simp only [Bool.false_eq_true, if_false, xor_zero_block]
    have hc : s % 2 ^ n + 2 ^ n < 2 ^ (n + 1) := by rw [pow_succ]; omega
    have hcs : (s % 2 ^ n + 2 ^ n) % 2 ^ n = s % 2 ^ n := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hqlt]
    have hcb' : (s % 2 ^ n + 2 ^ n).testBit n = true := by
      rw [show s % 2 ^ n + 2 ^ n = 2 ^ n * 1 + s % 2 ^ n by ring, Nat.testBit_two_pow_mul_add 1 hqlt,
        if_neg (by omega)]
      simp
    have hcb : (s % 2 ^ n + 2 ^ n).testBit n ≠ s.testBit n := by rw [hcb', hsb]; simp
    refine inv_after_expand H w hw treeTag castTag R Δ s n hn _ hc hcs hcb _ _ ?_ ?_ ?_ ?_
    · exact ⟨hL, hC, hT, hE⟩
    · rw [gNode_succ, hcs, hcb']; rfl
    · show gNode sp (gBit0 sp R) Δ n (s % 2 ^ n) ^^^ Δ ^^^ _ = _
      rw [hGs, hsb]
      simp only [Bool.false_eq_true, if_false]
      exact xor_swap_right _ _ _
    · intro k hk
      show (if k = n then _ else st.bits k) = _
      by_cases hkn : k = n
      · subst hkn; rw [if_pos rfl, hsb]; simp only [Bool.false_eq_true, if_false, xor_zero_block]
        try rfl
      · rw [if_neg hkn]; exact hbits k (by omega)
  · -- bit `n` is 1: the left child `q` is closed
    simp only [if_true]
    have hc : s % 2 ^ n < 2 ^ (n + 1) := by rw [pow_succ]; omega
    have hcs : (s % 2 ^ n) % 2 ^ n = s % 2 ^ n := Nat.mod_mod _ _
    have hcb' : (s % 2 ^ n).testBit n = false := Nat.testBit_lt_two_pow hqlt
    have hcb : (s % 2 ^ n).testBit n ≠ s.testBit n := by rw [hcb', hsb]; simp
    refine inv_after_expand H w hw treeTag castTag R Δ s n hn _ hc hcs hcb _ _ ?_ ?_ ?_ ?_
    · exact ⟨hL, hC, hT, hE⟩
    · rw [xor_cancel_mid, gNode_succ, hcs, hcb']; rfl
    · show _ ^^^ Δ = _
      rw [hGs, hsb]
      rfl
    · intro k hk
      show (if k = n then _ else st.bits k) = _
      by_cases hkn : k = n
      · subst hkn; rw [if_pos rfl, hsb]; rfl
      · rw [if_neg hkn]; exact hbits k (by omega)

/-- The rounds `n, ..., n + r - 1` keep the invariant. -/
theorem stageRoundsM_inv (R : Lanes rb) (Δ : Block) (σ : Nat) (joins : Nat → Block) (pin : Lanes rb)
    (hJ : ∀ n, 1 ≤ n → n < w → joins n = gJoin (hashStage H w hw treeTag castTag) R Δ n)
    (hP : pin = gPin (hashStage H w hw treeTag castTag) R Δ) :
    ∀ r n, 1 ≤ n → n + r ≤ w → ∀ st : StageState rb,
      Inv (hashStage H w hw treeTag castTag) R Δ (σ % 2 ^ w) n st →
      Inv (hashStage H w hw treeTag castTag) R Δ (σ % 2 ^ w) (n + r)
        ((stageRoundsM w treeTag castTag (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)))
          (σ % 2 ^ w) joins pin r n st).eval H) := by
  intro r
  induction r with
  | zero => intro n _ _ st h; exact h
  | succ r ih =>
    intro n hn1 hnr st h
    simp only [stageRoundsM, FreeQuery.eval_bind]
    have h1 := stageRoundM_inv H w hw treeTag castTag R Δ σ joins pin hJ hP n hn1 (by omega) st h
    have h2 := ih (n + 1) (by omega) (by omega) _ h1
    rw [show n + (r + 1) = n + 1 + r by omega]
    exact h2

/-- Round 0: expanding the closed level-1 slot from the empty state gives the invariant at 1. -/
theorem initial_inv (hw1 : 1 ≤ w) (R : Lanes rb) (Δ : Block) (σ : Nat) :
    Inv (hashStage H w hw treeTag castTag) R Δ (σ % 2 ^ w) 1
      ((expandM w treeTag castTag 1 ((σ % 2 ^ w % 2) ^^^ 1)
        (laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ))) 0)
        { levelSum := fun _ => 0
          classSum := fun _ => 0
          castSum := fun _ => 0
          leaves := fun _ => 0
          active := laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ))) 0
          bits := fun k => if k = 0 then
            laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ))) 0 else 0 }).eval H) := by
  set sp := hashStage H w hw treeTag castTag with hsp
  set s := σ % 2 ^ w with hs
  have hspw : sp.w = w := rfl
  have hs0 : s.testBit 0 = σ.testBit 0 := by
    rw [hs, Nat.testBit_mod_two_pow]; simp [show 0 < w by omega]
  have hb0 : laneBit (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) 0 =
      gBit0 sp R ^^^ (if σ.testBit 0 then Δ else 0) := bit0_label sp hw1 R Δ σ
  rw [materialize_eq]
  rw [← hs0] at hb0
  have hmod2 : s % 2 = 0 ∨ s % 2 = 1 := Nat.mod_two_eq_zero_or_one s
  have hsb0 : s.testBit 0 = decide (s % 2 = 1) := Nat.testBit_zero s
  have hG1 : ∀ x, gNode sp (gBit0 sp R) Δ 1 x =
      if x.testBit 0 then gBit0 sp R else Δ ^^^ gBit0 sp R := fun x => rfl
  have hc : (s % 2) ^^^ 1 < 2 ^ (0 + 1) := by rcases hmod2 with h | h <;> rw [h] <;> decide
  have hcs : ((s % 2) ^^^ 1) % 2 ^ 0 = s % 2 ^ 0 := by rw [pow_zero, Nat.mod_one, Nat.mod_one]
  have hcb : ((s % 2) ^^^ 1).testBit 0 ≠ s.testBit 0 := by
    rw [hsb0]; rcases hmod2 with h | h <;> rw [h] <;> decide
  refine inv_after_expand H w hw treeTag castTag R Δ s 0 (by omega) _ hc hcs hcb _ _ ?_ ?_ ?_ ?_
  · refine ⟨fun j hj1 _ => ?_, fun j _ => ?_, fun j _ => ?_, fun α _ hne => ?_⟩
    · show (0 : Block) = _
      simp only [Nat.min_zero, pow_zero, Nat.mod_one, ne_eq, not_true_eq_false, if_false]
      exact xsum_zero_fun.symm
    · show (0 : Lanes rb) = _
      symm; apply Finset.sum_eq_zero; intro α _
      rw [Nat.min_zero, pow_zero, Nat.mod_one, Nat.mod_one, if_neg (fun h => h rfl)]
    · show (0 : Lanes rb) = _
      symm; apply Finset.sum_eq_zero; intro α _
      rw [Nat.min_zero, pow_zero, Nat.mod_one, Nat.mod_one, if_neg (fun h => h rfl)]
    · exact absurd (by rw [pow_zero, Nat.mod_one, Nat.mod_one]) hne
  · show laneBit (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) 0 =
      gNode sp (gBit0 sp R) Δ 1 ((s % 2) ^^^ 1)
    rw [hb0, hG1]
    rcases hmod2 with h | h
    · have hsb : s.testBit 0 = false := by rw [hsb0, h]; decide
      rw [h, hsb]
      simp only [Bool.false_eq_true, if_false, xor_zero_block]
      have : (0 ^^^ 1 : Nat).testBit 0 = true := by decide
      rw [this]; rfl
    · have hsb : s.testBit 0 = true := by rw [hsb0, h]; decide
      rw [h, hsb]
      simp only [if_true]
      have : (1 ^^^ 1 : Nat).testBit 0 = false := by decide
      rw [this]
      simp only [Bool.false_eq_true, if_false]
      exact BitVec.xor_comm _ _
  · show laneBit (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) 0 =
      gNode sp (gBit0 sp R) Δ (0 + 1) (s % 2 ^ (0 + 1)) ^^^ Δ
    rw [hb0, gNode_succ_active]
    simp only [pow_zero, Nat.mod_one]
    rcases hmod2 with h | h
    · have hsb : s.testBit 0 = false := by rw [hsb0, h]; decide
      rw [hsb]
      simp only [Bool.false_eq_true, if_false, xor_zero_block]
      show gBit0 sp R = (Δ ^^^ gBit0 sp R) ^^^ Δ
      xor_norm
    · have hsb : s.testBit 0 = true := by rw [hsb0, h]; decide
      rw [hsb]
      rfl
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    show (if (0 : Nat) = 0 then laneBit (reduceTo w (R + (σ : ZMod (2 ^ rb)) •
      deltaLanes rb Δ)) 0 else (0 : Block)) = _
    rw [if_pos rfl, hb0]
    unfold gBit
    rw [if_pos rfl]

include hw in
/-- **L10 on the programs** `extStage_correct`: for every hash `H`, width `1 ≤ w ≤ rb`, tag
functions, offset `Δ`, remainder mask `R` and value `σ`, the evaluator program run on
`R + σ•Δ⃗`, the stage value `s = σ mod 2^w` and the garbler program's joins and pin returns the
garbler's leaves XOR `[α = s]·Δ`, the garbler's bit masks XOR `σ_n·Δ`, and the garbler's next
remainder plus `⌊σ / 2^w⌋•Δ⃗`. -/
theorem extStage_correct (hw1 : 1 ≤ w) (Δ : Block) (R : Lanes rb) (σ : Nat) :
    let g := (extStageGarbleM w treeTag castTag Δ R).eval H
    let e := (extStageEvalM w treeTag castTag (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)
      (σ % 2 ^ w) g.joins g.pin).eval H
    (∀ α < 2 ^ w, e.leaves α = g.leaves α ^^^ (if α = σ % 2 ^ w then Δ else 0)) ∧
      (∀ n < w, e.bits n = g.bits n ^^^ (if σ.testBit n then Δ else 0)) ∧
      e.next = g.next + ((σ / 2 ^ w : Nat) : ZMod (2 ^ (rb - w))) • deltaLanes (rb - w) Δ := by
  intro g e
  obtain ⟨hgl, hgb, hgj, hgp, hgn⟩ := extStageGarbleM_eval H w hw treeTag castTag Δ R
  set sp := hashStage H w hw treeTag castTag with hsp
  have hspw : sp.w = w := rfl
  set s := σ % 2 ^ w with hs
  have hslt : s < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hsmod : s % 2 ^ w = s := Nat.mod_eq_of_lt hslt
  have hinv0 := initial_inv H w hw treeTag castTag hw1 R Δ σ
  have hinv := stageRoundsM_inv H w hw treeTag castTag R Δ σ g.joins g.pin hgj hgp (w - 1) 1 le_rfl
    (by omega) _ hinv0
  rw [show 1 + (w - 1) = w by omega] at hinv
  obtain ⟨hact, hsums, hbits⟩ := hinv
  obtain ⟨_, hC, hT, hE⟩ := hsums
  simp only [hspw, hashStage_w] at hC hT hE hact hbits
  simp only [e, extStageEvalM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  refine ⟨fun α hα => ?_, fun n hn => ?_, ?_⟩
  · rw [atNat_of_lt _ _ hα, stored_eq, hgl α hα]
    simp only
    by_cases has : α = s
    · rw [if_pos has, if_pos has, hact, hsmod, has]; rfl
    · rw [if_neg has, if_neg has, xor_zero_block]
      exact hE α hα (by rw [Nat.mod_eq_of_lt hα, hsmod]; exact has)
  · rw [atNat_of_lt _ _ hn, stored_eq, hgb n hn]
    simp only
    have hsn : s.testBit n = σ.testBit n := by rw [hs, Nat.testBit_mod_two_pow]; simp [hn]
    rw [hbits n hn, hsn]
  · rw [materialize_eq, materialize_eq, scaleLanes_eq, hC w le_rfl, hT w le_rfl, Nat.min_self, hgp, hgn]
    unfold gPin gNext
    simp only [hspw, hashStage_w, Nat.mod_mod]
    rw [classSum_identity]
    unfold gRes
    simp only [hspw, hashStage_w]
    exact peelDiv_label hw R _ Δ σ

end Evaluator

end Kriterion.CRT.SliceC
