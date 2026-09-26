/-
**The hidden hop's guesses: the generic lemmas** (P2b).

Both guesses of the hidden hop (`CrtStageOneGuess`, `CrtStageTwoGuess`) are proved as corollaries of independence
(route (2)): the quantity a touch must hit (a label XOR `Δ`, a hidden digest answer, the key
answer, the low bits of `t`) is a coordinate of the tape that is uniform and independent of the adversary's view, and
the touch asks it to lie in a set of at most `k` values determined by the view. This file holds the two generic forms:

* `outer_split_le`: for a law that splits as (view, residual) with the residual uniform on a finite type and
  independent of the view, the conditional mass of "the residual lies in a view-determined set of at most `k` values" is
  at most `k / #R`;
* `outer_fine_le`: the same through a finer view: the law splits as (fine view, residual), the adversary's view is a
  function of the fine view, and the event forces the residual into a set of at most `k` values fixed by the fine view;
* `outer_table_le`: the same when the residual is one non-site position of the answer table (`Indep` form,
  `Laws/ReplayOn.lean`), with the view any function of the coins and the table that does not read that position;
* `indep_uniform_family`, `indep_swapped_family`, `swappedTableLaw_fill`: the swapped table law, read along an injective
  family of non-site positions, is those readings uniform and independent of the rest; in bind form, the swapped table
  is its own cold part refilled with uniform answers at those positions (the form `conversion_law` consumes).
-/

import Proof.Privacy.CRT.Laws.ReplayOn

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.HiddenGuess

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Laws (Indep Ignores)
open scoped ENNReal

noncomputable section

/-! ### A split law -/

open Classical in
/-- **A uniform residual independent of the view** lies in a view-determined set of at most `k` values with
conditional mass at most `k / #R`. -/
theorem outer_split_le {Ω V R : Type} [Fintype R] [Nonempty R] (μ : PMF Ω) (split : Ω → V × R)
    (hsplit : μ.map split =
      (μ.map fun ω => (split ω).1).bind fun v => (PMF.uniformOfFintype R).map fun r => (v, r))
    (P : V → R → Prop) (k : ℕ) (few : ∀ v, (Finset.univ.filter (P v)).card ≤ k) (v : V) :
    μ.toOuterMeasure {ω | (split ω).1 = v ∧ P (split ω).1 (split ω).2} ≤
      ((k : ℝ≥0∞) / Fintype.card R) * μ.toOuterMeasure {ω | (split ω).1 = v} := by
  have lhs : μ.toOuterMeasure {ω | (split ω).1 = v ∧ P (split ω).1 (split ω).2} =
      (μ.map split).toOuterMeasure {p | p.1 = v ∧ P p.1 p.2} := by
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  have rhs : μ.toOuterMeasure {ω | (split ω).1 = v} = (μ.map fun ω => (split ω).1) v := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  rw [lhs, rhs, hsplit, PMF.toOuterMeasure_bind_apply]
  have inner : ∀ v', ((PMF.uniformOfFintype R).map fun r => (v', r)).toOuterMeasure {p | p.1 = v ∧ P p.1 p.2} ≤
      if v' = v then (k : ℝ≥0∞) / Fintype.card R else 0 := by
    intro v'
    rw [PMF.toOuterMeasure_map_apply]
    by_cases same : v' = v
    · subst same
      rw [if_pos rfl, PMF.toOuterMeasure_uniformOfFintype_apply]
      refine ENNReal.div_le_div_right ?_ _
      have card : Fintype.card ((fun r => (v', r)) ⁻¹' {p : V × R | p.1 = v' ∧ P p.1 p.2}) =
          (Finset.univ.filter (P v')).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext r
        simp
      rw [card]
      exact_mod_cast few v'
    · rw [if_neg same]
      have empty : ((fun r => (v', r)) ⁻¹' {p : V × R | p.1 = v ∧ P p.1 p.2}) = ∅ := by
        ext r
        simp [same]
      rw [empty, MeasureTheory.measure_empty]
  calc ∑' v', (μ.map fun ω => (split ω).1) v' *
        ((PMF.uniformOfFintype R).map fun r => (v', r)).toOuterMeasure {p | p.1 = v ∧ P p.1 p.2}
      ≤ ∑' v', (μ.map fun ω => (split ω).1) v' * (if v' = v then (k : ℝ≥0∞) / Fintype.card R else 0) :=
        ENNReal.tsum_le_tsum fun v' => mul_le_mul' le_rfl (inner v')
    _ = ((k : ℝ≥0∞) / Fintype.card R) * (μ.map fun ω => (split ω).1) v := by
        rw [tsum_eq_single v fun v' ne => by rw [if_neg ne, mul_zero], if_pos rfl, mul_comm]

open Classical in
/-- **A guess through a finer view.** If the tape splits as (fine view, residual) with the residual uniform and
independent of the fine view, the coarse view is a function of the fine one, and every touch forces the residual into
a set of at most `k` values determined by the fine view, then the touch has conditional mass at most `k / #R` given the
coarse view. (Conditioning on a finer view and summing over its fibres.) -/
theorem outer_fine_le {Ω V W R : Type} [Fintype R] [Nonempty R] (μ : PMF Ω) (view : Ω → V) (fine : Ω → W)
    (coarse : W → V) (hview : ∀ ω, view ω = coarse (fine ω)) (res : Ω → R)
    (hsplit : μ.map (fun ω => (fine ω, res ω)) =
      (μ.map fine).bind fun w => (PMF.uniformOfFintype R).map fun r => (w, r))
    (event : Ω → Prop) (P : W → R → Prop) (k : ℕ) (few : ∀ w, (Finset.univ.filter (P w)).card ≤ k)
    (hevent : ∀ ω, event ω → P (fine ω) (res ω)) (v : V) :
    μ.toOuterMeasure {ω | view ω = v ∧ event ω} ≤ ((k : ℝ≥0∞) / Fintype.card R) * μ.toOuterMeasure {ω | view ω = v} := by
  classical
  have sub : {ω | view ω = v ∧ event ω} ⊆
      (fun ω => (fine ω, res ω)) ⁻¹' {p : W × R | coarse p.1 = v ∧ P p.1 p.2} := by
    intro ω hω
    exact ⟨(hview ω) ▸ hω.1, hevent ω hω.2⟩
  have viewSet : μ.toOuterMeasure {ω | view ω = v} = (μ.map fine).toOuterMeasure {w | coarse w = v} := by
    rw [PMF.toOuterMeasure_map_apply]
    congr 1
    ext ω
    simp [hview ω]
  refine le_trans (MeasureTheory.measure_mono sub) ?_
  rw [← PMF.toOuterMeasure_map_apply, hsplit, viewSet, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun w => ?_
  have inner : ((PMF.uniformOfFintype R).map fun r => (w, r)).toOuterMeasure {p : W × R | coarse p.1 = v ∧ P p.1 p.2}
      ≤ ((k : ℝ≥0∞) / Fintype.card R) * Set.indicator {w | coarse w = v} (fun _ => (1 : ℝ≥0∞)) w := by
    rw [PMF.toOuterMeasure_map_apply]
    by_cases same : coarse w = v
    · rw [Set.indicator_of_mem (show w ∈ {w | coarse w = v} from same), mul_one,
        PMF.toOuterMeasure_uniformOfFintype_apply]
      refine ENNReal.div_le_div_right ?_ _
      have card : Fintype.card ((fun r => (w, r)) ⁻¹' {p : W × R | coarse p.1 = v ∧ P p.1 p.2}) =
          (Finset.univ.filter (P w)).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext r
        simp [same]
      rw [card]
      exact_mod_cast few w
    · have empty : ((fun r => (w, r)) ⁻¹' {p : W × R | coarse p.1 = v ∧ P p.1 p.2}) = ∅ := by
        ext r
        simp [same]
      rw [empty, MeasureTheory.measure_empty]
      exact zero_le
  calc (μ.map fine) w * ((PMF.uniformOfFintype R).map fun r => (w, r)).toOuterMeasure
        {p : W × R | coarse p.1 = v ∧ P p.1 p.2}
      ≤ (μ.map fine) w * (((k : ℝ≥0∞) / Fintype.card R) *
          Set.indicator {w | coarse w = v} (fun _ => (1 : ℝ≥0∞)) w) := mul_le_mul' le_rfl inner
    _ = ((k : ℝ≥0∞) / Fintype.card R) * Set.indicator {w | coarse w = v} (μ.map fine) w := by
        by_cases same : coarse w = v
        · rw [Set.indicator_of_mem (show w ∈ {w | coarse w = v} from same),
            Set.indicator_of_mem (show w ∈ {w | coarse w = v} from same)]
          ring
        · rw [Set.indicator_of_notMem (show w ∉ {w | coarse w = v} from same),
            Set.indicator_of_notMem (show w ∉ {w | coarse w = v} from same)]
          ring

/-! ### One non-site position of the answer table -/

open Classical in
/-- **One non-site position of the table**, uniform and independent of the rest (`Indep`), lies in a
view-determined set of at most `k` answers with conditional mass at most `k / #(Block × Block)`, when the view does
not read that position. -/
theorem outer_table_le {C V : Type} (coinsLaw : PMF C) (μT : PMF TagTable) (pos : Fin (2 ^ 40))
    (indep : Indep μT {pos} (PMF.uniformOfFintype (Block × Block)) (fun T => T pos) (fun _ => True))
    (view : C → TagTable → V) (ignores : ∀ c, Ignores {pos} (view c))
    (P : C → V → Block × Block → Prop) (k : ℕ) (few : ∀ c v, (Finset.univ.filter (P c v)).card ≤ k) (v : V) :
    (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure
        {ω | view ω.1 ω.2 = v ∧ P ω.1 v (ω.2 pos)} ≤
      ((k : ℝ≥0∞) / Fintype.card (Block × Block)) *
        (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure {ω | view ω.1 ω.2 = v} := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  -- the event as a Boolean program on the table, read through `Indep`
  let G : Block × Block → TagTable → PMF Bool := fun a T => PMF.pure (decide (view c T = v ∧ P c v a))
  have ignoresG : ∀ a, True → Ignores {pos} (G a) := fun a _ T T' agree => by
    simp only [G, ignores c T T' agree]
  have law := indep Bool G ignoresG
  have atTrue := congrArg (fun p : PMF Bool => p true) law
  simp only [G] at atTrue
  have lhsEq : μT.toOuterMeasure ((fun T => (c, T)) ⁻¹' {ω : C × TagTable | view ω.1 ω.2 = v ∧ P ω.1 v (ω.2 pos)}) =
      (μT.bind fun T => PMF.pure (decide (view c T = v ∧ P c v (T pos)))) true := by
    rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v ∧ P c v (T pos)
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have viewEq : μT.toOuterMeasure ((fun T => (c, T)) ⁻¹' {ω : C × TagTable | view ω.1 ω.2 = v}) =
      (μT.bind fun T => PMF.pure (decide (view c T = v))) true := by
    rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun T => ?_
    by_cases h : view c T = v
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [lhsEq, atTrue, viewEq, PMF.bind_apply, tsum_fintype]
  -- `∑ a, 1/N · μT{view = v ∧ P a} ≤ k/N · μT{view = v}`
  set X := (μT.bind fun T => PMF.pure (decide (view c T = v))) true
  have each : ∀ a : Block × Block, (μT.bind fun T => PMF.pure (decide (view c T = v ∧ P c v a))) true =
      if P c v a then X else 0 := by
    intro a
    by_cases h : P c v a
    · simp [X, h]
    · simp [h]
  calc ∑ a, (PMF.uniformOfFintype (Block × Block)) a *
        (μT.bind fun T => PMF.pure (decide (view c T = v ∧ P c v a))) true
      = ∑ a, ((Fintype.card (Block × Block) : ℝ≥0∞))⁻¹ * (if P c v a then X else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [each, PMF.uniformOfFintype_apply]
    _ = ((Fintype.card (Block × Block) : ℝ≥0∞))⁻¹ * ((Finset.univ.filter (P c v)).card * X) := by
        rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Fintype.card (Block × Block) : ℝ≥0∞))⁻¹ * ((k : ℝ≥0∞) * X) :=
        mul_le_mul' le_rfl (mul_le_mul' (by exact_mod_cast few c v) le_rfl)
    _ = ((k : ℝ≥0∞) / Fintype.card (Block × Block)) * X := by
        rw [ENNReal.div_eq_inv_mul, mul_assoc]

/-! ### An injective family of non-site positions -/

section Family

variable {κ : Type} [Fintype κ] [DecidableEq κ]

open Classical in
/-- Refill a table at the positions `pos k` with `f k` (`Split.overwrite`, same text). -/
def fillAt (pos : κ → Fin (2 ^ 40)) (f : κ → Block × Block) (A : TagTable) : TagTable := fun i =>
  if h : ∃ k, pos k = i then f (Classical.choose h) else A i

theorem fillAt_comp (pos : κ → Fin (2 ^ 40)) (inj : Function.Injective pos) (f : κ → Block × Block) (A : TagTable) :
    fillAt pos f A ∘ pos = f := by
  funext k
  have h : ∃ k', pos k' = pos k := ⟨k, rfl⟩
  show (if h' : ∃ k', pos k' = pos k then f (Classical.choose h') else A (pos k)) = f k
  rw [dif_pos h, inj (Classical.choose_spec h)]

theorem fillAt_fillAt (pos : κ → Fin (2 ^ 40)) (f g : κ → Block × Block) (A : TagTable) :
    fillAt pos f (fillAt pos g A) = fillAt pos f A := by
  funext i
  unfold fillAt
  by_cases h : ∃ k, pos k = i
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, dif_neg h]

theorem fillAt_self (pos : κ → Fin (2 ^ 40)) (A : TagTable) : fillAt pos (A ∘ pos) A = A := by
  funext i
  unfold fillAt
  by_cases h : ∃ k, pos k = i
  · rw [dif_pos h]
    exact congrArg A (Classical.choose_spec h)
  · rw [dif_neg h]

theorem fillAt_apply_of_not_mem (pos : κ → Fin (2 ^ 40)) (f : κ → Block × Block) (A : TagTable) (i : Fin (2 ^ 40))
    (off : i ∉ Set.range pos) : fillAt pos f A i = A i := by
  unfold fillAt
  rw [dif_neg fun h => off (by obtain ⟨k, hk⟩ := h; exact ⟨k, hk⟩)]

/-- Refill a table along the family and return the old readings: an involution of `(table, readings)` pairs. -/
def swapFamily (pos : κ → Fin (2 ^ 40)) (pair : TagTable × (κ → Block × Block)) : TagTable × (κ → Block × Block) :=
  (fillAt pos pair.2 pair.1, pair.1 ∘ pos)

theorem swapFamily_involutive (pos : κ → Fin (2 ^ 40)) (inj : Function.Injective pos) :
    Function.Involutive (swapFamily pos) := by
  rintro ⟨A, f⟩
  show (fillAt pos (A ∘ pos) (fillAt pos f A), fillAt pos f A ∘ pos) = (A, f)
  rw [fillAt_fillAt, fillAt_self, fillAt_comp pos inj]

/-- **A uniform table read along an injective family**: the readings are uniform and independent of the rest. -/
theorem indep_uniform_family (pos : κ → Fin (2 ^ 40)) (inj : Function.Injective pos) :
    Indep (PMF.uniformOfFintype TagTable) (Set.range pos) (PMF.uniformOfFintype (κ → Block × Block))
      (fun T => T ∘ pos) (fun _ => True) := by
  intro β G ignores
  have ignoresFill : ∀ f g A, G f (fillAt pos g A) = G f A := fun f g A =>
    ignores f trivial _ _ fun i off => fillAt_apply_of_not_mem pos g A i off
  let e : (TagTable × (κ → Block × Block)) ≃ (TagTable × (κ → Block × Block)) :=
    Function.Involutive.toPerm _ (swapFamily_involutive pos inj)
  have product : ∀ (H : TagTable → (κ → Block × Block) → PMF β),
      (PMF.uniformOfFintype TagTable).bind (fun A => (PMF.uniformOfFintype (κ → Block × Block)).bind (H A)) =
        (PMF.uniformOfFintype (TagTable × (κ → Block × Block))).bind fun pair => H pair.1 pair.2 := by
    intro H
    rw [← Kriterion.ArgoMAC.Phase3.Glue.uniform_product, PMF.bind_bind]
    refine congrArg _ (funext fun A => ?_)
    rw [PMF.bind_map]
    rfl
  calc (PMF.uniformOfFintype TagTable).bind (fun T => G (T ∘ pos) T)
      = (PMF.uniformOfFintype TagTable).bind (fun A => (PMF.uniformOfFintype (κ → Block × Block)).bind
          fun g => G (A ∘ pos) (fillAt pos g A)) := by
        refine congrArg _ (funext fun A => ?_)
        simp only [ignoresFill, PMF.bind_const]
    _ = (PMF.uniformOfFintype (TagTable × (κ → Block × Block))).bind fun pair =>
          G ((e pair).2) ((e pair).1) := by
        rw [product]
        rfl
    _ = ((PMF.uniformOfFintype (TagTable × (κ → Block × Block))).map e).bind fun pair => G pair.2 pair.1 := by
        rw [PMF.bind_map]
        rfl
    _ = (PMF.uniformOfFintype (TagTable × (κ → Block × Block))).bind fun pair => G pair.2 pair.1 := by
        rw [Kriterion.ArgoMAC.Phase3.Glue.uniform_equiv e]
    _ = (PMF.uniformOfFintype (κ → Block × Block)).bind fun f => (PMF.uniformOfFintype TagTable).bind (G f) := by
        rw [← product (fun A f => G f A), PMF.bind_comm]

/-- **The swapped table read along an injective family of non-site positions**: uniform readings, independent of
the rest. -/
theorem indep_swapped_family (layout : SiteLayout) (pos : κ → Fin (2 ^ 40)) (inj : Function.Injective pos)
    (away : ∀ site ∈ layout.sites, ∀ k, pos k ∉ (siteTags layout site).map tagPos) :
    Indep (swappedTableLaw layout) (Set.range pos) (PMF.uniformOfFintype (κ → Block × Block)) (fun T => T ∘ pos)
      (fun _ => True) := by
  rw [Kriterion.CRT.Privacy.Laws.swappedTableLaw_eq]
  refine Kriterion.CRT.Privacy.Laws.indep_foldl layout _ _ _ _ ?_ _ _ (indep_uniform_family pos inj) ?_
  · intro T T' agree
    funext k
    exact agree _ ⟨k, rfl⟩
  · rintro site member i ⟨k, rfl⟩
    exact away site member k

/-- **The swapped table is its own cold part refilled with uniform answers along the family** (bind form). -/
theorem swappedTableLaw_fill (layout : SiteLayout) (pos : κ → Fin (2 ^ 40)) (inj : Function.Injective pos)
    (away : ∀ site ∈ layout.sites, ∀ k, pos k ∉ (siteTags layout site).map tagPos) :
    (swappedTableLaw layout).bind (fun A => (PMF.uniformOfFintype (κ → Block × Block)).map fun f => fillAt pos f A)
      = swappedTableLaw layout := by
  have law := indep_swapped_family layout pos inj away (TagTable) (fun f A => PMF.pure (fillAt pos f A))
    (fun f _ A A' agree => by
      simp only
      congr 1
      funext i
      by_cases hit : i ∈ Set.range pos
      · obtain ⟨k, rfl⟩ := hit
        rw [show fillAt pos f A (pos k) = f k from congrFun (fillAt_comp pos inj f A) k,
          show fillAt pos f A' (pos k) = f k from congrFun (fillAt_comp pos inj f A') k]
      · rw [fillAt_apply_of_not_mem pos f A i hit, fillAt_apply_of_not_mem pos f A' i hit]
        exact agree i hit)
  have self : (fun T : TagTable => (PMF.pure (fillAt pos (T ∘ pos) T) : PMF TagTable)) = PMF.pure := by
    funext T
    rw [fillAt_self]
  simp only at law
  rw [self, PMF.bind_pure] at law
  calc (swappedTableLaw layout).bind (fun A => (PMF.uniformOfFintype (κ → Block × Block)).map fun f => fillAt pos f A)
      = (swappedTableLaw layout).bind (fun A => (PMF.uniformOfFintype (κ → Block × Block)).bind
          fun f => PMF.pure (fillAt pos f A)) := by
        rfl
    _ = (PMF.uniformOfFintype (κ → Block × Block)).bind (fun f => (swappedTableLaw layout).bind
          fun A => PMF.pure (fillAt pos f A)) := PMF.bind_comm _ _ _
    _ = swappedTableLaw layout := law.symm

end Family

end

end Kriterion.CRT.Privacy.HiddenGuess
