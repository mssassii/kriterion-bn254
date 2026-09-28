/-
**The row normalization's flag** (P8, part of `CrtFlagMass`).

The middle game's wrap reveal includes `H8.normBadSrc`: one of the stage-1 source's two hidden cells of a digit
(`zC0`, `yC4`, never published) is zero. Under the uniform source these cells are uniform and independent of
everything the source publishes (`publish_withHidden`), so against every weight on the published value the flag has
mass at most `182/p` times the weight (`normFlag_le`): a union bound over the 182 cells, each zero with probability
`1/p`.
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Core.BmrNorm
import Proof.Privacy.CRT.Glue.Budget

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.PublicFirst
open scoped ENNReal

noncomputable section

namespace NormFlag

/-- The hidden cells of a source, `(zC0, yC4)` per digit. -/
def hiddenOf (s : Entry.Source) : BMR.Scales := fun d => ((s.rows d).zC0, (s.rows d).yC4)

/-- A source with its hidden cells replaced. -/
def withHidden (s : Entry.Source) (h : BMR.Scales) : Entry.Source :=
  { s with rows := fun d => ⟨(s.rows d).xC0, (h d).2, (h d).1⟩ }

theorem hiddenOf_withHidden (s : Entry.Source) (h : BMR.Scales) : hiddenOf (withHidden s h) = h := rfl

theorem withHidden_withHidden (s : Entry.Source) (h h' : BMR.Scales) :
    withHidden (withHidden s h) h' = withHidden s h' := rfl

theorem withHidden_hiddenOf (s : Entry.Source) : withHidden s (hiddenOf s) = s := rfl

/-- The sources with zero hidden cells. -/
abbrev Rest := {s : Entry.Source // hiddenOf s = 0}

/-- **A source is a rest and its hidden cells.** -/
def restEquiv : Entry.Source ≃ Rest × BMR.Scales where
  toFun s := (⟨withHidden s 0, rfl⟩, hiddenOf s)
  invFun x := withHidden x.1.1 x.2
  left_inv s := rfl
  right_inv x := by
    obtain ⟨⟨r, zero⟩, h⟩ := x
    refine Prod.ext (Subtype.ext ?_) rfl
    show withHidden (withHidden r h) 0 = r
    rw [withHidden_withHidden, ← zero, withHidden_hiddenOf]

/-- The published value does not read the hidden cells. -/
theorem publish_withHidden (s : Entry.Source) (h : BMR.Scales) : Entry.publish (withHidden s h) = Entry.publish s := rfl

theorem normBadSrc_withHidden (s : Entry.Source) (h : BMR.Scales) :
    H8.normBadSrc (withHidden s h) ↔ ¬ BMR.GoodScales h := by
  unfold H8.normBadSrc BMR.GoodScales withHidden
  simp only [not_forall, not_and_or, ne_eq, not_not]
  exact Iff.rfl

instance restFintype : Fintype Rest := Fintype.ofFinite _

instance restNonempty : Nonempty Rest := ⟨⟨withHidden (Classical.arbitrary _) 0, rfl⟩⟩

/-- **One hidden cell is zero with probability `1/p`**, so all 182 of them are nonzero but with probability
`182/p`. -/
theorem badMass_le [FieldCertificate] :
    ∑' h : BMR.Scales, PMF.uniformOfFintype BMR.Scales h * (if BMR.GoodScales h then 0 else 1) ≤
      ENNReal.ofReal normError := by
  classical
  have cell : ∀ (d : Fin 91) (k : Fin 2),
      (PMF.uniformOfFintype BMR.Scales).toOuterMeasure
        {h | (if k = 0 then (h d).1 else (h d).2) = 0} = (baseFieldModulus : ℝ≥0∞)⁻¹ := by
    intro d k
    let projection : BMR.Scales →+ BaseField :=
      { toFun := fun h => if k = 0 then (h d).1 else (h d).2
        map_zero' := by split <;> rfl
        map_add' := fun a b => by split <;> rfl }
    have surj : Function.Surjective projection := fun target =>
      ⟨fun _ => (target, target), by show (if k = 0 then target else target) = target; split <;> rfl⟩
    have law := BMR.WrapMass.uniform_map_addHom projection surj
    have mass := congrArg (fun μ : PMF BaseField => μ.toOuterMeasure {0}) law
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply,
      ZMod.card] at mass
    exact mass
  have union : {h : BMR.Scales | ¬ BMR.GoodScales h} ⊆
      ⋃ x : Fin 91 × Fin 2, {h | (if x.2 = 0 then (h x.1).1 else (h x.1).2) = 0} := by
    intro h bad
    simp only [Set.mem_setOf_eq, BMR.GoodScales, not_forall, not_and_or, ne_eq, not_not] at bad
    obtain ⟨d, zero | zero⟩ := bad
    · exact Set.mem_iUnion.mpr ⟨(d, 0), by simp [zero]⟩
    · exact Set.mem_iUnion.mpr ⟨(d, 1), by simp [zero]⟩
  have asMass : ∑' h : BMR.Scales, PMF.uniformOfFintype BMR.Scales h * (if BMR.GoodScales h then 0 else 1) =
      (PMF.uniformOfFintype BMR.Scales).toOuterMeasure {h | ¬ BMR.GoodScales h} := by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun h => ?_
    by_cases good : BMR.GoodScales h
    · simp [good]
    · simp [good]
  rw [asMass]
  refine (MeasureTheory.measure_mono union).trans ((MeasureTheory.measure_iUnion_fintype_le _ _).trans ?_)
  simp only [cell, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  unfold normError frac
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast p_pos), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    baseFieldModulus_eq, div_eq_mul_inv]

/-- **The normalization flag against a weight on the published value**: at most `182/p` times the weight. -/
theorem normFlag_le [FieldCertificate] [GroupCertificate] (weight : Entry.Public → ℝ≥0∞)
    [Fintype Entry.Source] [Nonempty Entry.Source] :
    ∑' s, PMF.uniformOfFintype Entry.Source s * (weight (Entry.publish s) * (if H8.normBadSrc s then 1 else 0)) ≤
      ENNReal.ofReal normError * ∑' s, PMF.uniformOfFintype Entry.Source s * weight (Entry.publish s) := by
  classical
  have split : ∀ g : Entry.Source → ℝ≥0∞, ∑' s, PMF.uniformOfFintype Entry.Source s * g s =
      ∑' r : Rest, PMF.uniformOfFintype Rest r * ∑' h, PMF.uniformOfFintype BMR.Scales h * g (withHidden r.1 h) := by
    intro g
    rw [← BMR.tsum_uniform_prod (fun x : Rest × BMR.Scales => g (withHidden x.1.1 x.2))]
    exact (BMR.tsum_uniform_equiv restEquiv.symm g).symm
  rw [split, split]
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun r => ?_
  simp only [publish_withHidden]
  have inner : ∑' h, PMF.uniformOfFintype BMR.Scales h *
      (weight (Entry.publish r.1) * (if H8.normBadSrc (withHidden r.1 h) then 1 else 0)) =
      weight (Entry.publish r.1) * ∑' h, PMF.uniformOfFintype BMR.Scales h * (if BMR.GoodScales h then 0 else 1) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun h => ?_
    by_cases good : BMR.GoodScales h
    · have notBad : ¬ H8.normBadSrc (withHidden r.1 h) := fun bad => (normBadSrc_withHidden r.1 h).mp bad good
      rw [if_neg notBad, if_pos good]
      ring
    · have bad : H8.normBadSrc (withHidden r.1 h) := (normBadSrc_withHidden r.1 h).mpr good
      rw [if_pos bad, if_neg good]
      ring
  rw [inner, BMR.tsum_uniform_const]
  calc PMF.uniformOfFintype Rest r * (weight (Entry.publish r.1) *
        ∑' h, PMF.uniformOfFintype BMR.Scales h * (if BMR.GoodScales h then 0 else 1))
      ≤ PMF.uniformOfFintype Rest r * (weight (Entry.publish r.1) * ENNReal.ofReal normError) := by
        gcongr
        exact badMass_le
    _ = ENNReal.ofReal normError * (PMF.uniformOfFintype Rest r * weight (Entry.publish r.1)) := by ring

end NormFlag

end

end Kriterion.CRT.Privacy.Flags
