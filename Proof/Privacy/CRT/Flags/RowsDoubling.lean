/-
**The doubling flag of the true rows** (P8, `CrtFlagMass`'s doubling part).

The middle game flags a target row with `z = 0` (`H8.rowsDoubling`). A true row is `realRowOf T K ρ` (xinshu's
`trueRows_eq`), with `T` the digit's multiple of the input and `K` its clamped offset, and its `z` is `0` in two cases:
`T = K` (the row `(0, 0, 0)`), and `T + K = 0` (the lift of the point at infinity). So the event is that some digit
point `T + K` is `2 T` or `0`: two targets per digit. Under the simulator's point law each target is hit with
probability at most `1/#Point` (`clamp_anyHit_le`), `2 · 91` in all; the construction's good tails are within
`91/#Point` of it (`bn254_digitPoints_good_etvDist_le`). The mass is at most `273/#Point ≤ 273/(r − 1)`.
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.Phase3.OpeningBound

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3
open scoped ENNReal

noncomputable section

namespace RowsDoubling

variable [FieldCertificate] [GroupCertificate]

/-- A true row with `z = 0` is a doubling (`T = K`) or a lift of the point at infinity (`T + K = 0`). -/
theorem realRowOf_z_eq_zero {T K : Point} {rho : BaseField} (nonzero : rho ≠ 0)
    (zero : (realRowOf T K rho).z = 0) : T = K ∨ T + K = 0 := by
  by_cases same : T = K
  · exact Or.inl same
  · right
    unfold realRowOf at zero
    rw [if_neg same] at zero
    cases sum : T + K with
    | zero => rfl
    | some x y valid =>
        rw [sum] at zero
        exact absurd zero (mul_ne_zero nonzero (pointMultiplier_ne_zero T K same))

/-- The digit points of a doubling flag hit `2 T` or `0`. -/
theorem doubling_points (multiples : Fin 91 → Point) (sample : GoodTails × (Fin 91 → NonZeroBase))
    (flag : H8.rowsDoubling (realRowsOf multiples sample)) :
    ∃ digit, realPoints radixMap multiples sample.1.1 digit = multiples digit + multiples digit ∨
      realPoints radixMap multiples sample.1.1 digit = 0 := by
  obtain ⟨digit, zero⟩ := flag
  refine ⟨digit, ?_⟩
  rcases realRowOf_z_eq_zero (sample.2 digit).nonzero zero with same | sum
  · left
    show multiples digit + clampOffsets radixMap sample.1.1 digit = _
    rw [← same]
  · right
    exact sum

/-- **Two targets per digit under the construction's point law: at most `273/#Point`.** -/
theorem twoTargets_real_le [Fintype Point] (multiples : Fin 91 → Point) (output : Point)
    (hits : horner radixMap 91 multiples = output)
    [Nonempty {tail : Fin 90 → Point // GoodTail radixMap tail}]
    [Nonempty {tail : Fin 90 → Point // NoHit radixMap output multiples tail}] :
    ((PMF.uniformOfFintype {tail : Fin 90 → Point // GoodTail radixMap tail}).map
        (fun tail => realPoints radixMap multiples tail.1)).toOuterMeasure
        {points | ∃ digit, points digit = multiples digit + multiples digit ∨ points digit = 0}
      ≤ (273 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  let ideal := (PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output)
  let real := (PMF.uniformOfFintype {tail : Fin 90 → Point // GoodTail radixMap tail}).map
    (fun tail => realPoints radixMap multiples tail.1)
  let hit : Set (Fin 91 → Point) :=
    {points | ∃ digit, points digit = multiples digit + multiples digit ∨ points digit = 0}
  have split : {points : Fin 91 → Point | ∃ digit, points digit = multiples digit + multiples digit ∨
        points digit = 0}
      = {points | ∃ digit, points digit = multiples digit + multiples digit} ∪
        {points | ∃ digit, points digit = (fun _ => (0 : Point)) digit} := by
    ext points
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨digit, first | second⟩
      · exact Or.inl ⟨digit, first⟩
      · exact Or.inr ⟨digit, second⟩
    · rintro (⟨digit, first⟩ | ⟨digit, second⟩)
      · exact ⟨digit, Or.inl first⟩
      · exact ⟨digit, Or.inr second⟩
  have idealMass : ((PMF.uniformOfFintype (Fin 90 → Point)).map
      (clampPoints radixMap output)).toOuterMeasure
        {points | ∃ digit, points digit = multiples digit + multiples digit ∨ points digit = 0}
      ≤ (182 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [split]
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    have first := bn254_doubling_le multiples output
    have second := clamp_anyHit_le (n := 89) radixMap radixMap_injective output (fun _ => (0 : Point))
    simp only [Nat.reduceAdd, Nat.cast_ofNat] at second
    calc _ ≤ (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ + (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ :=
          add_le_add first second
      _ = (182 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by rw [← add_mul]; norm_num
  have good := bn254_digitPoints_good_etvDist_le multiples output hits
  have main := le_trans (toOuterMeasure_le_add_etvDist _ _ hit) (add_le_add idealMass good)
  have total : (182 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ + (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹
      = (273 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [← add_mul]
    norm_num
  rw [total] at main
  convert main using 3
  · rfl
  · congr 1
    exact uniform_instance _ _

/-- `c / #Point ≤ c / (r − 1)`, in the budget's spelling. -/
theorem count_le_frac (c : ℕ) :
    (c * (Fintype.card Point : ℝ≥0∞)⁻¹).toReal ≤ frac c (BudgetData.r - 1) := by
  have order := scalarFieldModulus_le_card_point
  have same : BudgetData.r = scalarFieldModulus := by
    unfold BudgetData.r scalarFieldModulus
    rfl
  have one : 1 ≤ scalarFieldModulus := by
    unfold scalarFieldModulus
    norm_num
  have large : (1 : ℝ) < scalarFieldModulus := by
    have : 1 < scalarFieldModulus := by unfold scalarFieldModulus; norm_num
    exact_mod_cast this
  have cardReal : (scalarFieldModulus : ℝ) ≤ (Fintype.card Point : ℝ) := by exact_mod_cast order
  unfold frac
  rw [same, Nat.cast_sub one, Nat.cast_one, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith)

end RowsDoubling

open RowsDoubling in
/-- **The doubling flag of the true rows** (for `CrtFlagMass`): at a valid input, the rows kernel of `crtEntry` draws
rows with some `z = 0` with probability at most `exceptionalError = 273/(r − 1)`. -/
theorem crtRowsDoubling_le [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput)
    (Q : Point) (valid : (Instance.crtEntry.scheme inferInstance inferInstance).function scalar u = some Q) :
    ((PublicFirst.viewHere Instance.crtEntry).realRows scalar u Q).toOuterMeasure
        {r | ∃ targets, r = some targets ∧ H8.rowsDoubling targets}
      ≤ ENNReal.ofReal exceptionalError := by
  classical
  change (decodePoint u).map (scalarMultiplication scalar.value) = some Q at valid
  obtain ⟨point, decoded, rfl⟩ := Option.map_eq_some_iff.mp valid
  set multiples := multiplesOf scalar point with hmultiples
  have hits : horner radixMap 91 multiples = scalar.value • point := horner_multiplesOf scalar point
  have := noHitNonempty multiples _ hits
  let flagged : Set (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)) :=
    {r | ∃ targets, r = some targets ∧ H8.rowsDoubling targets}
  let hit : Set (Fin 91 → Point) :=
    {points | ∃ digit, points digit = multiples digit + multiples digit ∨ points digit = 0}
  have inside : (fun sample : GoodTails × (Fin 91 → NonZeroBase) => some (realRowsOf multiples sample)) ⁻¹' flagged
      ⊆ Prod.fst ⁻¹' ((fun tail : GoodTails => realPoints radixMap multiples tail.1) ⁻¹' hit) := by
    rintro sample ⟨targets, same, flag⟩
    cases same
    exact doubling_points multiples sample flag
  have mass : (Security.Phase3.realRows scalar u (scalarMultiplication scalar.value point)).toOuterMeasure flagged
      ≤ (273 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [realRows_law scalar u point decoded]
    erw [PMF.toOuterMeasure_map_apply]
    refine le_trans (MeasureTheory.measure_mono inside) ?_
    rw [← PMF.toOuterMeasure_map_apply, productPMF_map_fst, ← PMF.toOuterMeasure_map_apply]
    exact twoTargets_real_le multiples _ hits
  have finite : (273 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  refine le_trans mass ?_
  rw [ENNReal.le_ofReal_iff_toReal_le finite (show 0 ≤ exceptionalError from frac_nonneg _ _)]
  exact count_le_frac 273

end

end Kriterion.CRT.Privacy.Flags
