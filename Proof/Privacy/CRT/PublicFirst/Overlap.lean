/-
**P7, the public-first hop `G1U → HW`: flagged games and the overlap bound** (ports of xinshu's
`Proof/Privacy/Phase3/UntilBadIff.lean`, `PublicFirst/Overlap.lean` and the first section of
`PublicFirst/MiddleOff.lean`, generic in the games, stated for the CRT hop shapes of `Glue/Shapes.lean`).

* `untilBad_iff`, `coreUntilBad_iff`: the CRT `UntilBad` and `CoreUntilBad` are exactly the advantage bound (the flags
  live on the one-bit outcome, so the flag-down masses can be taken to be `min(first b, second b)`). Hence a
  `GameCoreUntilBad` hop may be proved through any middle game.
* `Below game flagged` (the flag-down part of a flagged game `PMF (Option Bool)` is below a game), `FlagMono`,
  `advantage_le_of_overlap` (a flagged game below both games bounds their advantage by its flag mass) and
  `advantage_le_of_overlap_tv` (two flagged games, one below each game: the first's flag mass plus their total
  variation distance).

Every proof is xinshu's, re-elaborated against the CRT shapes; nothing is `sorry`.
-/

import Proof.Privacy.CRT.Glue.Shapes
import Proof.Privacy.Phase3.Basic

namespace Kriterion.CRT.Privacy.PublicFirst

open Cryptography
open scoped ENNReal

noncomputable section

/-! ### 1. The hop shapes are advantage bounds -/

theorem pmf_bool_false (law : PMF Bool) : law false = 1 - law true := by
  have total := law.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at total
  have swapped : (1 : ℝ≥0∞) = law false + law true := by
    rw [← total]; ring
  exact (ENNReal.sub_eq_of_eq_add (PMF.apply_ne_top law _) swapped).symm

/-- A law on `Bool × Bool` from its four masses. -/
def flaggedLaw (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun outcome => match outcome with
    | (true, false) => downTrue
    | (true, true) => upTrue
    | (false, false) => downFalse
    | (false, true) => upFalse) (by
      rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
      simpa [add_comm, add_left_comm, add_assoc] using total)

theorem flaggedLaw_fst (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) (outcome : Bool) :
    (flaggedLaw upTrue upFalse downTrue downFalse total).map Prod.fst outcome
      = if outcome then downTrue + upTrue else downFalse + upFalse := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]
  cases outcome <;> simp [flaggedLaw, add_comm]

theorem flaggedLaw_bad (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) :
    (flaggedLaw upTrue upFalse downTrue downFalse total).toOuterMeasure badSet = upTrue + upFalse := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  simp [flaggedLaw, badSet, Set.indicator, add_comm]

/-- A `PMF Bool` is determined by its mass at `true`. -/
theorem pmf_bool_ext {first second : PMF Bool} (same : first true = second true) : first = second := by
  refine PMF.ext fun outcome => ?_
  cases outcome
  · rw [pmf_bool_false first, pmf_bool_false second, same]
  · exact same

/-- **Every advantage bound is an identical-until-bad pair.** -/
theorem untilBad_of_advantage_le {first second : PMF Bool} {error : ℝ}
    (bound : Assumptions.advantage first second ≤ error) : UntilBad first second error := by
  set a := first true
  set b := second true
  have aLe : a ≤ 1 := PMF.coe_le_one first true
  have bLe : b ≤ 1 := PMF.coe_le_one second true
  have aTop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top aLe
  have split (x y : ℝ≥0∞) (small : min x y ≤ x) : min x y + (x - min x y) = x :=
    add_tsub_cancel_of_le small
  have totalOf (x : ℝ≥0∞) (y z : ℝ≥0∞) (xLe : x ≤ 1) :
      min x y + (x - min x y) + (min (1 - x) z + ((1 - x) - min (1 - x) z)) = 1 := by
    rw [split _ _ (min_le_left _ _), split _ _ (min_le_left _ _)]
    exact add_tsub_cancel_of_le xLe
  refine ⟨flaggedLaw (a - min a b) ((1 - a) - min (1 - a) (1 - b)) (min a b) (min (1 - a) (1 - b))
      (totalOf a b (1 - b) aLe),
    flaggedLaw (b - min a b) ((1 - b) - min (1 - a) (1 - b)) (min a b) (min (1 - a) (1 - b))
      (by rw [min_comm a b, min_comm (1 - a) (1 - b)]; exact totalOf b a (1 - a) bLe),
    ?_, ?_, ?_, ?_⟩
  · refine pmf_bool_ext ?_
    rw [flaggedLaw_fst, if_pos rfl, split _ _ (min_le_left _ _)]
  · refine pmf_bool_ext ?_
    rw [flaggedLaw_fst, if_pos rfl, add_tsub_cancel_of_le (min_le_right _ _)]
  · intro outcome
    cases outcome <;> rfl
  · rw [flaggedLaw_bad]
    refine le_trans ?_ bound
    unfold Assumptions.advantage
    rcases le_total b a with ba | ab
    · have oneLe : 1 - a ≤ 1 - b := tsub_le_tsub_left ba 1
      rw [min_eq_right ba, min_eq_left oneLe, tsub_self, add_zero,
        ENNReal.toReal_sub_of_le ba aTop]
      exact le_abs_self _
    · have oneLe : 1 - b ≤ 1 - a := tsub_le_tsub_left ab 1
      rw [min_eq_left ab, min_eq_right oneLe, tsub_self, zero_add,
        ENNReal.toReal_sub_of_le oneLe (ENNReal.sub_ne_top ENNReal.one_ne_top),
        ENNReal.toReal_sub_of_le aLe ENNReal.one_ne_top,
        ENNReal.toReal_sub_of_le bLe ENNReal.one_ne_top]
      rw [abs_sub_comm]
      calc (1 : ℝ≥0∞).toReal - a.toReal - ((1 : ℝ≥0∞).toReal - b.toReal) = b.toReal - a.toReal := by
            ring
        _ ≤ |b.toReal - a.toReal| := le_abs_self _

/-- **`UntilBad` is exactly the advantage bound.** -/
theorem untilBad_iff {first second : PMF Bool} {error : ℝ} :
    UntilBad first second error ↔ Assumptions.advantage first second ≤ error :=
  ⟨fun bound => bound.advantage_le, untilBad_of_advantage_le⟩

/-- **`CoreUntilBad` is exactly the advantage bound** (the trivial core). -/
theorem coreUntilBad_iff {first second : PMF Bool} {error : ℝ} :
    CoreUntilBad first second error ↔ Assumptions.advantage first second ≤ error := by
  refine ⟨fun bound => bound.untilBad.advantage_le, fun bound => ?_⟩
  obtain ⟨firstFlagged, secondFlagged, firstEq, secondEq, agree, bad⟩ :=
    untilBad_of_advantage_le bound
  exact ⟨Unit, PMF.pure (), PMF.pure (), fun _ => secondFlagged, firstFlagged, rfl, firstEq,
    by rw [PMF.pure_bind]; exact secondEq, by intro outcome; rw [PMF.pure_bind]; exact agree outcome,
    bad⟩

/-! ### 2. Flagged games and the overlap bound -/

/-- The flag-down part of a flagged game is below a game. -/
def Below (game : PMF Bool) (flagged : PMF (Option Bool)) : Prop :=
  ∀ b, flagged (some b) ≤ game b

/-- A flagged game is below another (more flags raised): its flag-down part is smaller. -/
def FlagMono (upper lower : PMF (Option Bool)) : Prop :=
  ∀ b, lower (some b) ≤ upper (some b)

theorem Below.trans {game : PMF Bool} {upper lower : PMF (Option Bool)} (below : Below game upper)
    (mono : FlagMono upper lower) : Below game lower :=
  fun b => (mono b).trans (below b)

/-- The three masses of a flagged game sum to one. -/
theorem flagged_total (flagged : PMF (Option Bool)) :
    flagged none + flagged (some true) + flagged (some false) = 1 := by
  have total := flagged.tsum_coe
  rw [tsum_fintype] at total
  rw [← total]
  simp only [Fintype.sum_option, Fintype.sum_bool]
  ring

/-- **The overlap bound.** A flagged game below both games bounds their advantage by its flag mass. -/
theorem advantage_le_of_overlap {first second : PMF Bool} {flagged : PMF (Option Bool)}
    (firstBelow : Below first flagged) (secondBelow : Below second flagged) :
    Assumptions.advantage first second ≤ (flagged none).toReal := by
  have total := flagged_total flagged
  have finite (x : Option Bool) : flagged x ≠ ⊤ := PMF.apply_ne_top _ _
  have totalReal : (flagged none).toReal + (flagged (some true)).toReal
      + (flagged (some false)).toReal = 1 := by
    rw [← ENNReal.toReal_add (finite _) (finite _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩) (finite _), total,
      ENNReal.toReal_one]
  have lowerTrue (game : PMF Bool) (below : Below game flagged) :
      (flagged (some true)).toReal ≤ (game true).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (below true)
  have upperTrue (game : PMF Bool) (below : Below game flagged) :
      (game true).toReal ≤ 1 - (flagged (some false)).toReal := by
    have falseLe : (flagged (some false)).toReal ≤ (game false).toReal :=
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) (below false)
    have gameTotal : (game true).toReal + (game false).toReal = 1 := by
      rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
      have sum := game.tsum_coe
      rw [tsum_fintype, Fintype.sum_bool] at sum
      rw [sum, ENNReal.toReal_one]
    linarith
  have a1 := lowerTrue first firstBelow
  have a2 := upperTrue first firstBelow
  have b1 := lowerTrue second secondBelow
  have b2 := upperTrue second secondBelow
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

theorem toOuterMeasure_true_none (law : PMF (Option Bool)) :
    law.toOuterMeasure {some true, none} = law (some true) + law none := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp [Set.indicator, Fintype.sum_option, add_comm]

/-- An event's mass moves by at most the total-variation distance. -/
theorem mass_le_add_etvDist {A : Type} (first second : PMF A) (event : Set A) :
    first.toOuterMeasure event ≤ second.toOuterMeasure event + first.etvDist second := by
  rw [PMF.etvDist_comm, Kriterion.ArgoMAC.Security.Phase3.etvDist_eq_tsum_tsub,
    PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun point => ?_
  by_cases inside : point ∈ event
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside]
    exact le_add_tsub
  · rw [Set.indicator_of_notMem inside]
    exact zero_le

/-- **Two games above two flagged games** are within the first's flag mass plus the flagged games'
total-variation distance. -/
theorem advantage_le_of_overlap_tv {first second : PMF Bool} {upper lower : PMF (Option Bool)}
    (firstBelow : Below first upper) (secondBelow : Below second lower) :
    Assumptions.advantage first second ≤ (upper none).toReal + (upper.etvDist lower).toReal := by
  have dFinite : upper.etvDist lower ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.etvDist_le_one _ _)
  have singleton := mass_le_add_etvDist upper lower {some true}
  have pair := mass_le_add_etvDist lower upper {some true, none}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at singleton
  rw [toOuterMeasure_true_none, toOuterMeasure_true_none, PMF.etvDist_comm] at pair
  have upperTotal := flagged_total upper
  have lowerTotal := flagged_total lower
  have firstFalse := pmf_bool_false first
  have secondFalse := pmf_bool_false second
  have fin : ∀ x : Option Bool, upper x ≠ ⊤ := fun x => PMF.apply_ne_top _ _
  have finL : ∀ x : Option Bool, lower x ≠ ⊤ := fun x => PMF.apply_ne_top _ _
  have s1 : (upper (some true)).toReal ≤ (lower (some true)).toReal + (upper.etvDist lower).toReal := by
    rw [← ENNReal.toReal_add (finL _) dFinite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finL _, dFinite⟩) singleton
  have s2 : (lower (some true)).toReal + (lower none).toReal ≤
      (upper (some true)).toReal + (upper none).toReal + (upper.etvDist lower).toReal := by
    rw [← ENNReal.toReal_add (finL _) (finL _), ← ENNReal.toReal_add (fin _) (fin _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨fin _, fin _⟩) dFinite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨fin _, fin _⟩, dFinite⟩) pair
  have u : (upper none).toReal + (upper (some true)).toReal + (upper (some false)).toReal = 1 := by
    rw [← ENNReal.toReal_add (fin _) (fin _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨fin _, fin _⟩) (fin _), upperTotal,
      ENNReal.toReal_one]
  have l : (lower none).toReal + (lower (some true)).toReal + (lower (some false)).toReal = 1 := by
    rw [← ENNReal.toReal_add (finL _) (finL _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finL _, finL _⟩) (finL _), lowerTotal,
      ENNReal.toReal_one]
  have f : (first true).toReal + (first false).toReal = 1 := by
    rw [firstFalse, ENNReal.toReal_sub_of_le (PMF.coe_le_one _ _) ENNReal.one_ne_top,
      ENNReal.toReal_one]
    ring
  have s : (second true).toReal + (second false).toReal = 1 := by
    rw [secondFalse, ENNReal.toReal_sub_of_le (PMF.coe_le_one _ _) ENNReal.one_ne_top,
      ENNReal.toReal_one]
    ring
  have b1 : (upper (some true)).toReal ≤ (first true).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (firstBelow true)
  have b2 : (upper (some false)).toReal ≤ (first false).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (firstBelow false)
  have b3 : (lower (some true)).toReal ≤ (second true).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (secondBelow true)
  have b4 : (lower (some false)).toReal ≤ (second false).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (secondBelow false)
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

/-! ### 3. Sums against binds and maps (xinshu's `FullRel.lean`, `SparseStep.lean`, `LiftGuess.lean`, generic) -/

theorem tsum_bind_mul {α β : Type} (μ : PMF α) (f : α → PMF β) (h : β → ℝ≥0∞) :
    ∑' o, (μ.bind f) o * h o = ∑' a, μ a * ∑' o, f a o * h o := by
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun o => ?_
  ring

/-- `∑ (μ.map g) · f = ∑ μ · (f ∘ g)`. -/
theorem tsum_map_mul {α β : Type} (μ : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' o, (μ.map g) o * f o = ∑' a, μ a * f (g a) := by
  classical
  simp only [PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (g a)]
  · rw [if_pos rfl]
  · intro o different
    rw [if_neg different, zero_mul]

/-- An event's mass as a weighted sum. -/
theorem toOuterMeasure_eq_tsum {A : Type} (μ : PMF A) (event : Set A) [DecidablePred (· ∈ event)] :
    μ.toOuterMeasure event = ∑' x, μ x * (if x ∈ event then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases inside : x ∈ event
  · rw [Set.indicator_of_mem inside, if_pos inside, mul_one]
  · rw [Set.indicator_of_notMem inside, if_neg inside, mul_zero]

end

end Kriterion.CRT.Privacy.PublicFirst
