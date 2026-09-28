import Construction.CRT.Label
import Mathlib.Data.BitVec
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.NormNum

/-!
Uniformity of the low 104 bits of a raw, uniformly distributed 128-bit answer.

The weighted statements keep the residual raw block independent of the frozen
view.  They do not assert uniformity after arbitrary conditioning on that block.
This module is a leaf: no existing privacy game imports it yet.
-/

namespace Kriterion.CRT.Narrow

open scoped BigOperators ENNReal

noncomputable section

/-- The public label type has its own finite enumeration. -/
instance labelFintype : Fintype Label :=
  Fintype.ofEquiv (Fin (2 ^ labelBits)) BitVec.equivFin.symm.toEquiv

-- Keep this instance local: the challenge already supplies a Block instance.
-- Fintype instances are subsingletons, so this choice does not change the law.
-- CHECK: compile an import together with Cryptography.Primitives to verify that
-- the local raw instance and the challenge's existing instance elaborate together.
local instance rawBlockFintype : Fintype RawBlock :=
  Fintype.ofEquiv (Fin (2 ^ 128)) BitVec.equivFin.symm.toEquiv

@[simp] theorem card_label : Fintype.card Label = 2 ^ labelBits := by
  exact (Fintype.card_congr
    (BitVec.equivFin : Label ≃+* Fin (2 ^ labelBits)).toEquiv).trans
      (Fintype.card_fin _)

@[simp] theorem card_rawBlock : Fintype.card RawBlock = 2 ^ 128 := by
  exact (Fintype.card_congr
    (BitVec.equivFin : RawBlock ≃+* Fin (2 ^ 128)).toEquiv).trans
      (Fintype.card_fin _)

/-- XOR by a lifted label difference carries one projection fibre to another. -/
def clipFibreEquiv (first second : Label) :
    {x : RawBlock // clip x = first} ≃ {x : RawBlock // clip x = second} where
  toFun x := ⟨x.1 ^^^ embed (first ^^^ second), by
    rw [clip_xor_embed, x.2]
    simp [← BitVec.xor_assoc]⟩
  invFun x := ⟨x.1 ^^^ embed (first ^^^ second), by
    rw [clip_xor_embed, x.2, BitVec.xor_comm first second]
    simp [← BitVec.xor_assoc]⟩
  left_inv x := by
    apply Subtype.ext
    simp [BitVec.xor_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [BitVec.xor_assoc]

/-- Every low-bit label has exactly the 24 high-bit choices as raw preimages. -/
theorem card_clip_fibre (label : Label) :
    Fintype.card {x : RawBlock // clip x = label} = 2 ^ (128 - labelBits) := by
  classical
  have same : ∀ other : Label,
      Fintype.card {x : RawBlock // clip x = other}
        = Fintype.card {x : RawBlock // clip x = label} :=
    fun other => Fintype.card_congr (clipFibreEquiv other label)
  have total : 2 ^ 128 = 2 ^ labelBits *
      Fintype.card {x : RawBlock // clip x = label} := by
    calc
      2 ^ 128 = Fintype.card RawBlock := card_rawBlock.symm
      _ = Fintype.card (Σ l : Label, {x : RawBlock // clip x = l}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv clip).symm
      _ = ∑ l : Label, Fintype.card {x : RawBlock // clip x = l} :=
        Fintype.card_sigma
      _ = ∑ _l : Label, Fintype.card {x : RawBlock // clip x = label} :=
        Finset.sum_congr rfl fun l _ => same l
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_label]
  apply Nat.mul_left_cancel (Nat.two_pow_pos labelBits)
  calc
    2 ^ labelBits * Fintype.card {x : RawBlock // clip x = label} = 2 ^ 128 :=
      total.symm
    _ = 2 ^ labelBits * 2 ^ (128 - labelBits) := by norm_num [labelBits]

/-- Finset form expected by the existing `HiddenGuess.outer_fine_le` API, with
the raw residual type retained and `k = 2^24`. -/
theorem clip_fiber_filter_card (label : Label) :
    (Finset.univ.filter (fun delta : RawBlock => clip delta = label)).card
      = 2 ^ (128 - labelBits) := by
  classical
  -- CHECK: the uncompiled subtype/card rewrite must retain this predicate's orientation.
  rw [← Fintype.card_subtype]
  exact card_clip_fibre label

/- The following two helpers are the small fibre-counting argument already used
in Core/WrapMass and Phase3/Basic.  Keeping them private avoids importing either
consumer and its old, full-width conversion infrastructure. -/
private theorem uniform_map_apply {A B : Type*} [Fintype A] [Nonempty A]
    [DecidableEq B] (g : A → B) (point : B) :
    ((PMF.uniformOfFintype A).map g) point
      = (Fintype.card {x : A // g x = point} : ℝ≥0∞) *
        (Fintype.card A : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [tsum_fintype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [eq_comm]

private theorem uniform_map_of_fibre_equiv {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [DecidableEq B]
    (g : A → B)
    (shift : ∀ first second : B,
      {x : A // g x = first} ≃ {x : A // g x = second}) :
    (PMF.uniformOfFintype A).map g = PMF.uniformOfFintype B := by
  classical
  obtain ⟨base⟩ := (inferInstance : Nonempty B)
  have fibreCard : ∀ point : B,
      Fintype.card {x : A // g x = point} = Fintype.card {x : A // g x = base} :=
    fun point => Fintype.card_congr (shift point base)
  have total : Fintype.card A = Fintype.card B *
      Fintype.card {x : A // g x = base} := by
    calc
      Fintype.card A = Fintype.card (Σ point : B, {x : A // g x = point}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv g).symm
      _ = ∑ point : B, Fintype.card {x : A // g x = point} := Fintype.card_sigma
      _ = ∑ _point : B, Fintype.card {x : A // g x = base} :=
        Finset.sum_congr rfl fun point _ => fibreCard point
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have fibrePos : 0 < Fintype.card {x : A // g x = base} := by
    rcases Nat.eq_zero_or_pos (Fintype.card {x : A // g x = base}) with zero | pos
    · have : Fintype.card A = 0 := by rw [total, zero, mul_zero]
      exact absurd this Fintype.card_ne_zero
    · exact pos
  refine PMF.ext fun point => ?_
  rw [uniform_map_apply, PMF.uniformOfFintype_apply, fibreCard point, total,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm ((Fintype.card B : ℝ≥0∞)⁻¹), ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr fibrePos.ne')
      (ENNReal.natCast_ne_top _), one_mul]

/-- A full raw answer projects to an exactly uniform conversion label. -/
theorem uniform_clip :
    (PMF.uniformOfFintype RawBlock).map clip = PMF.uniformOfFintype Label :=
  uniform_map_of_fibre_equiv clip clipFibreEquiv

private theorem uniform_fst {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] [DecidableEq A] :
    (PMF.uniformOfFintype (A × B)).map Prod.fst = PMF.uniformOfFintype A := by
  classical
  refine uniform_map_of_fibre_equiv Prod.fst fun a a' => ?_
  exact {
    toFun := fun p => ⟨(a', p.1.2), rfl⟩
    invFun := fun p => ⟨(a, p.1.2), rfl⟩
    left_inv := fun p => Subtype.ext (Prod.ext p.2.symm rfl)
    right_inv := fun p => Subtype.ext (Prod.ext p.2.symm rfl) }

/-- The label read from the first raw answer block is uniform; the second raw
block remains part of the original answer space. -/
theorem uniform_answer_clip :
    (PMF.uniformOfFintype (RawBlock × RawBlock)).map (fun answer => clip answer.1)
      = PMF.uniformOfFintype Label := by
  -- CHECK: elaborate the polymorphic fst map after rewriting map composition.
  change (PMF.uniformOfFintype (RawBlock × RawBlock)).map (clip ∘ Prod.fst) = _
  rw [← PMF.map_comp, uniform_fst, uniform_clip]

theorem uniform_clip_apply (label : Label) :
    ((PMF.uniformOfFintype RawBlock).map clip) label = (2 ^ labelBits : ℝ≥0∞)⁻¹ := by
  rw [uniform_clip, PMF.uniformOfFintype_apply, card_label, Nat.cast_pow,
    Nat.cast_ofNat]

/-- The `k / #R` coefficient obtained with the raw residual `R = RawBlock`
and the exact fibre size `k = 2^24` is the narrow guessing coefficient. -/
theorem clip_fibre_ratio :
    (2 ^ (128 - labelBits) : ℝ≥0∞) / (Fintype.card RawBlock : ℝ≥0∞)
      = (2 ^ labelBits : ℝ≥0∞)⁻¹ := by
  calc
    _ = ((PMF.uniformOfFintype RawBlock).map clip) 0 := by
      rw [uniform_map_apply, card_clip_fibre, div_eq_mul_inv, Nat.cast_pow,
        Nat.cast_ofNat]
    _ = _ := uniform_clip_apply 0

/-- Projection preserves independence from an arbitrary frozen view law. -/
theorem bind_map_uniform_clip {View : Type*} (view : PMF View) :
    (view.bind fun v => (PMF.uniformOfFintype RawBlock).map fun delta => (v, clip delta))
      = view.bind fun v => (PMF.uniformOfFintype Label).map fun label => (v, label) := by
  have inner : (fun (v : View) => (PMF.uniformOfFintype RawBlock).map fun delta => (v, clip delta))
      = fun (v : View) => (PMF.uniformOfFintype Label).map fun label => (v, label) := by
    funext v
    change (PMF.uniformOfFintype RawBlock).map ((Prod.mk v) ∘ clip) = _
    rw [← PMF.map_comp, uniform_clip]
  rw [inner]

/-- A single projection fibre has probability 2^-104 even when its event is
weighted by an arbitrary nonnegative (possibly infinite) constant. -/
theorem weighted_clip_fibre (label : Label) (weight : ℝ≥0∞) :
    (∑' delta : RawBlock, PMF.uniformOfFintype RawBlock delta *
      (if clip delta = label then weight else 0))
      = weight * (2 ^ labelBits : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ = weight * ((PMF.uniformOfFintype RawBlock).map clip) label := by
      rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro delta
      by_cases same : clip delta = label
      · simp [same, mul_comm]
      · have other : label ≠ clip delta := fun h => same h.symm
        simp [same, other]
    _ = _ := by rw [uniform_clip_apply]

/-- The weighted fibre form used for conditional guessing: the guess and weight
may depend on all of `View`; the full raw residual is still uniform and independent
of that view.  This is an exact identity, with no division by a view's mass. -/
theorem weighted_clip_guess {View : Type*} (view : PMF View)
    (guess : View → Label) (weight : View → ℝ≥0∞) :
    (∑' v, ∑' delta : RawBlock, view v * PMF.uniformOfFintype RawBlock delta *
      (if clip delta = guess v then weight v else 0))
      = (∑' v, view v * weight v) * (2 ^ labelBits : ℝ≥0∞)⁻¹ := by
  classical
  -- CHECK: the ENNReal sum-distribution rewrites below are source-checked only.
  calc
    _ = ∑' v, view v * (∑' delta : RawBlock, PMF.uniformOfFintype RawBlock delta *
        (if clip delta = guess v then weight v else 0)) := by
      apply tsum_congr
      intro v
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro delta
      exact mul_assoc _ _ _
    _ = ∑' v, view v * (weight v * (2 ^ labelBits : ℝ≥0∞)⁻¹) := by
      simp_rw [weighted_clip_fibre]
    _ = _ := by
      simp only [← mul_assoc]
      exact ENNReal.tsum_mul_right

/-- Any event forcing one projected residual has at most the corresponding
weighted guessing mass.  The event may inspect the high bits too. -/
theorem weighted_clip_event_le {View : Type*} (view : PMF View)
    (guess : View → Label) (weight : View → ℝ≥0∞)
    (event : View → RawBlock → Prop) [∀ v delta, Decidable (event v delta)]
    (forces : ∀ v delta, event v delta → clip delta = guess v) :
    (∑' v, ∑' delta : RawBlock, view v * PMF.uniformOfFintype RawBlock delta *
      (if event v delta then weight v else 0))
      ≤ (∑' v, view v * weight v) * (2 ^ labelBits : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ ≤ ∑' v, ∑' delta : RawBlock, view v * PMF.uniformOfFintype RawBlock delta *
        (if clip delta = guess v then weight v else 0) := by
      apply ENNReal.tsum_le_tsum
      intro v
      apply ENNReal.tsum_le_tsum
      intro delta
      by_cases hit : event v delta
      · simp only [if_pos hit, if_pos (forces v delta hit), le_refl]
      · simp [hit]
    _ = _ := weighted_clip_guess view guess weight

end

end Kriterion.CRT.Narrow
