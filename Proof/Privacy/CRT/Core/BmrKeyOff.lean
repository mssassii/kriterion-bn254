/-
**The curve mask off the curve, at the P45 level**.

Off the curve, fix P45's hint-free cells (`Source × Cold u`) outside the two-sided wrap window. The coins that give
these cells are `bmrEquivOff.symm (cells, r)`, one for each residual `r`. None of them wraps (`hint_false_of_window`),
so the evaluator's curve values are the ideal delivered values, and the curve check's value at `u` is
`t' = t + mask·d` with `d = x³ + 3 − y² ≠ 0` (`CurveMembership.evaluateEncoded`). Hence the bridge key of the fibre
coin is `keyOf u cells − mask·d` (`bridge_fibre`), where `keyOf u cells` is computed from the cells alone and the
curve mask is a coordinate of the residual. Under the uniform residual the mask is uniform on the `p − 1` nonzero
values, so at most `⌈p / 2^128⌉` of them give `bridge.val % 2^128 = ℓ`, and the fibre fraction is at most
`2/2^128 + 1/(p − 1)` (`keyLabel_fibre`).
-/

import Proof.Privacy.CRT.Core.BmrIdealOff

namespace Kriterion.CRT.Privacy.BmrOff

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.BMR
open scoped ENNReal

noncomputable section

section Fibre

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)] [FieldCertificate]

/-- The curve check's polynomial `d = x³ + 3 − y²` at `u` (nonzero exactly off the curve). -/
def curveGap (u : AffineInput) : BaseField := u.x ^ 3 + 3 - u.y ^ 2

theorem curveGap_ne_zero {u : AffineInput} (off : ¬ OnCurve u) : curveGap u ≠ 0 := by
  intro zero
  apply off
  unfold OnCurve
  unfold curveGap at zero
  linear_combination -zero

/-- **The evaluator's curve value from P45's cells**: the curve check at `u` on the ideal delivered values of the five
curve encodings. -/
def keyOf (u : AffineInput) (cells : Source T × Cold T u) : BaseField :=
  CurveMembership.evaluate cells.1.2.2 u fun element => deliveredIdeal u cells.1.1 cells.2 (curveEnc element)

/-- The curve mask of a residual off the curve. -/
def residualMask (r : ResidualOff) : BaseField := r.2.2.2.1

/-- A coordinate value, read as a field element. -/
theorem coordValue_cast (u : AffineInput) (element : CurveMembership.Element) :
    ((Kriterion.CRT.Privacy.coordValue u (coordOf (curveEnc element)) : ℕ) : BaseField) =
      CurveMembership.coordValue u element := by
  rcases element with x | y
  · show ((if (0 : ℕ) = 0 then u.x.val else u.y.val : ℕ) : BaseField) = u.x
    rw [if_pos rfl, ZMod.natCast_val, ZMod.cast_id', id]
  · show ((if (1 : ℕ) = 0 then u.x.val else u.y.val : ℕ) : BaseField) = u.y
    rw [if_neg one_ne_zero, ZMod.natCast_val, ZMod.cast_id', id]

/-- The five curve encodings' CRT values lie outside the two-sided window. -/
def CurveWindowFree (u : AffineInput) (cells : Source T × Cold T u) : Prop :=
  ∀ element, ¬ InWindow T (evalInt u cells.1.1 cells.2 (curveEnc element))

/-- **The bridge key of a fibre coin**: off the window at the curve encodings, `t = t'(cells) − mask·d`. -/
theorem bridge_fibre (facts : TableFacts T) (ctx : Context) (u : AffineInput) (cells : Source T × Cold T u)
    (window : CurveWindowFree u cells) (r : ResidualOff) :
    ((bmrEquivOff T ctx u).symm (cells, r)).bridge = keyOf u cells - residualMask r * curveGap u := by
  set e := bmrEquivOff T ctx u
  set c := e.symm (cells, r)
  have image : e c = (cells, r) := e.apply_symm_apply _
  have parts := bmrEquivOff_join ctx u c
  have joinEq : join ctx c = cells.1.1 := by
    rw [← parts.1]
    exact congrArg (fun x => x.1.1.1) image
  have coldEq : coldOf u c = cells.2 := by
    rw [← parts.2]
    exact congrArg (fun x => x.1.2) image
  have tableEq : curveTable c = cells.1.2.2 := congrArg (fun x => x.1.1.2.2) image
  have maskEq : c.curveMask = residualMask r := congrArg (fun x => x.2.2.2.2.1) image
  have noWrap : ∀ element, hint c (curveEnc element) = false := by
    intro element
    apply hint_false_of_window facts ctx u
    rw [joinEq, coldEq]
    exact window element
  have deliv : (fun element => deliveredIdeal u cells.1.1 cells.2 (curveEnc element)) =
      CurveMembership.delivered c.r1 c.r2 (curveK c) u := by
    funext element
    have := (noWrap_delivered facts ctx u c (curveEnc element) (noWrap element)).2
    rw [joinEq, coldEq] at this
    rw [this, coordValue_cast]
    unfold CurveMembership.delivered
    rcases element with x | y
    · rfl
    · rfl
  have evaluated : keyOf u cells = c.bridge + c.curveMask * curveGap u := by
    unfold keyOf
    rw [deliv, ← tableEq]
    exact CurveMembership.evaluateEncoded c.bridge c.curveMask c.r1 c.r2 (curveK c) u
  rw [evaluated, maskEq]
  ring

end Fibre

/-! ### The fraction of the fibre with a given key label -/

section Count

variable [FieldCertificate]

/-- the key-label error: `2/2^128 + 1/(p − 1)`. -/
def keyError : ℝ≥0∞ := ENNReal.ofReal (2 / 2 ^ 128 + 1 / ((BN254.baseFieldModulus : ℝ) - 1))

/-- The curve mask and the rest of an off-curve residual. -/
def maskSplit : ResidualOff ≃ {m : BaseField // m ≠ 0} × ((Fin 91 → Fin 4 → BaseField) × (Fin 91 → BaseField) ×
    (Fin 91 → Fin 7 → BaseField)) where
  toFun r := (r.2.2.2, (r.1, r.2.1, r.2.2.1))
  invFun p := (p.2.1, p.2.2.1, p.2.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The curve mask of a uniform residual is uniform on the nonzero values. -/
theorem uniform_residualMask :
    (PMF.uniformOfFintype ResidualOff).map (fun r => r.2.2.2) = PMF.uniformOfFintype {m : BaseField // m ≠ 0} := by
  have factor : (fun r : ResidualOff => r.2.2.2) = Prod.fst ∘ maskSplit := rfl
  rw [factor, ← PMF.map_comp, uniform_map_equiv, uniform_map_fst]

theorem card_nonzero : Fintype.card {m : BaseField // m ≠ 0} = BN254.baseFieldModulus - 1 := by
  have h := Fintype.card_subtype_compl (α := BaseField) (fun m => m = 0)
  rw [Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card (α := BaseField), Nat.card_zmod] at h
  exact h

theorem natCard_nonzero : Nat.card {m : BaseField // m ≠ 0} = BN254.baseFieldModulus - 1 := by
  rw [Nat.card_eq_fintype_card]
  exact card_nonzero

/-- `card_nonzero` at every `Fintype` instance. -/
theorem card_nonzero' (inst : Fintype {m : BaseField // m ≠ 0}) :
    @Fintype.card {m : BaseField // m ≠ 0} inst = BN254.baseFieldModulus - 1 := by
  rw [← @Nat.card_eq_fintype_card _ inst]
  exact natCard_nonzero

/-- At most `⌊(p − 1)/2^128⌋ + 1` field elements have a given low part. -/
theorem card_low_le (ℓ : ℕ) (f : {m : BaseField // m ≠ 0} → BaseField) (inj : Function.Injective f) :
    Fintype.card {m : {m : BaseField // m ≠ 0} // (f m).val % 2 ^ 128 = ℓ} ≤
      (BN254.baseFieldModulus - 1) / 2 ^ 128 + 1 := by
  classical
  rw [Fintype.card_subtype]
  refine le_trans (Finset.card_le_card_of_injOn (fun m => (f m).val / 2 ^ 128)
    (t := Finset.range ((BN254.baseFieldModulus - 1) / 2 ^ 128 + 1)) ?_ ?_) ?_
  · intro m _
    simp only [Finset.coe_range, Set.mem_Iio]
    have lt := ZMod.val_lt (f m)
    have le : (f m).val ≤ BN254.baseFieldModulus - 1 := Nat.le_sub_one_of_lt lt
    exact Nat.lt_succ_of_le (Nat.div_le_div_right le)
  · intro m hm m' hm' same
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm hm'
    have vals : (f m).val = (f m').val := by
      rw [← Nat.div_add_mod (f m).val (2 ^ 128), ← Nat.div_add_mod (f m').val (2 ^ 128), hm, hm']
      simp only at same
      rw [same]
    exact inj (ZMod.val_injective _ vals)
  · simp

theorem natCard_low_le (ℓ : ℕ) (f : {m : BaseField // m ≠ 0} → BaseField) (inj : Function.Injective f) :
    Nat.card {m : {m : BaseField // m ≠ 0} // (f m).val % 2 ^ 128 = ℓ} ≤
      (BN254.baseFieldModulus - 1) / 2 ^ 128 + 1 := by
  rw [Nat.card_eq_fintype_card]
  exact card_low_le ℓ f inj

/-- `card_low_le` for the set form, at every `Fintype` instance. -/
theorem card_low_le' (ℓ : ℕ) (f : {m : BaseField // m ≠ 0} → BaseField) (inj : Function.Injective f)
    (inst : Fintype ↑{m : {m : BaseField // m ≠ 0} | (f m).val % 2 ^ 128 = ℓ}) :
    @Fintype.card ↑{m : {m : BaseField // m ≠ 0} | (f m).val % 2 ^ 128 = ℓ} inst ≤
      (BN254.baseFieldModulus - 1) / 2 ^ 128 + 1 := by
  have h := natCard_low_le ℓ f inj
  rw [← @Nat.card_eq_fintype_card _ inst]
  exact (Nat.card_congr (Equiv.refl _ : ↑{m : {m : BaseField // m ≠ 0} | (f m).val % 2 ^ 128 = ℓ} ≃
    {m : {m : BaseField // m ≠ 0} // (f m).val % 2 ^ 128 = ℓ})).trans_le h

/-- The real bound: `(⌊(p − 1)/2^128⌋ + 1)/(p − 1) ≤ 2/2^128 + 1/(p − 1)`. -/
theorem count_bound :
    (((BN254.baseFieldModulus - 1) / 2 ^ 128 + 1 : ℕ) : ℝ≥0∞) / ((BN254.baseFieldModulus - 1 : ℕ) : ℝ≥0∞) ≤
      keyError := by
  have two : 2 ≤ BN254.baseFieldModulus := (Fact.out : Nat.Prime BN254.baseFieldModulus).two_le
  generalize hp : BN254.baseFieldModulus = p at two ⊢
  unfold keyError
  rw [hp]
  have pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast two
    linarith
  have castSub : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have divLe : (((p - 1) / 2 ^ 128 : ℕ) : ℝ) ≤ ((p : ℝ) - 1) / 2 ^ 128 := by
    rw [← castSub]
    have h := Nat.cast_div_le (α := ℝ) (m := p - 1) (n := 2 ^ 128)
    rw [Nat.cast_pow, Nat.cast_ofNat] at h
    exact h
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by
      rw [Ne, Nat.cast_eq_zero]; omega)) (Or.inl (ENNReal.natCast_ne_top _))]
  rw [show (((p - 1 : ℕ)) : ℝ≥0∞) = ENNReal.ofReal ((p : ℝ) - 1) from by
    rw [← castSub, ENNReal.ofReal_natCast]]
  rw [← ENNReal.ofReal_mul (by positivity), show ((((p - 1) / 2 ^ 128 + 1 : ℕ)) : ℝ≥0∞) =
    ENNReal.ofReal ((((p - 1) / 2 ^ 128 : ℕ) : ℝ) + 1) from by
      rw [← ENNReal.ofReal_natCast]
      push_cast
      rfl]
  refine ENNReal.ofReal_le_ofReal ?_
  have expand : (2 / 2 ^ 128 + 1 / ((p : ℝ) - 1)) * ((p : ℝ) - 1) = 2 * ((p : ℝ) - 1) / 2 ^ 128 + 1 := by
    field_simp
  rw [expand]
  have : ((p : ℝ) - 1) / 2 ^ 128 ≤ 2 * ((p : ℝ) - 1) / 2 ^ 128 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  linarith

end Count

section Main

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)] [FieldCertificate]

/-- **The key-label fraction of a fibre off the curve**: for window-free P45 cells, the uniform residual gives the
fibre coin a bridge key with `val % 2^128 = ℓ` with mass at most `keyError`. -/
theorem keyLabel_fibre (facts : TableFacts T) (ctx : Context) (u : AffineInput) (off : ¬ OnCurve u)
    (cells : Source T × Cold T u) (window : CurveWindowFree u cells) (ℓ : ℕ) :
    (PMF.uniformOfFintype ResidualOff).toOuterMeasure
        {r | (((bmrEquivOff T ctx u).symm (cells, r)).bridge).val % 2 ^ 128 = ℓ} ≤ keyError := by
  classical
  set f : {m : BaseField // m ≠ 0} → BaseField := fun m => keyOf u cells - m.1 * curveGap u
  have inj : Function.Injective f := by
    intro m m' same
    have eq : m.1 * curveGap u = m'.1 * curveGap u := by
      have := congrArg (fun x => keyOf u cells - x) same
      simp only [f, sub_sub_cancel] at this
      exact this
    exact Subtype.ext (mul_right_cancel₀ (curveGap_ne_zero off) eq)
  have setEq : {r : ResidualOff | (((bmrEquivOff T ctx u).symm (cells, r)).bridge).val % 2 ^ 128 = ℓ} =
      (fun r : ResidualOff => r.2.2.2) ⁻¹' {m | (f m).val % 2 ^ 128 = ℓ} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_preimage, f]
    rw [bridge_fibre facts ctx u cells window r]
    rfl
  rw [setEq, ← PMF.toOuterMeasure_map_apply, uniform_residualMask, PMF.toOuterMeasure_uniformOfFintype_apply,
    card_nonzero' _]
  refine le_trans ?_ count_bound
  gcongr
  exact_mod_cast card_low_le' ℓ f inj _

end Main

/-! ### The weighted form: the curve mask is uniform given the off-curve output -/

section Weighted

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)] [FieldCertificate]

/-- The hint-free cells of an off-curve output. -/
def cellsOfOut {u : AffineInput} (o : OutOff T u) : Source T × Cold T u := (o.1.1, o.2)

theorem realOutOff_eq (ctx : Context) (u : AffineInput) (c : Coins T) :
    realOutOff ctx u c = (((bmrEquivOff T ctx u c).1.1, hint c), (bmrEquivOff T ctx u c).1.2) := rfl

theorem cellsOfOut_real (ctx : Context) (u : AffineInput) (c : Coins T) :
    cellsOfOut (realOutOff ctx u c) = (bmrEquivOff T ctx u c).1 := rfl

/-- The residual without its curve mask. -/
abbrev OtherOff := (Fin 91 → Fin 4 → BaseField) × (Fin 91 → BaseField) × (Fin 91 → Fin 7 → BaseField)

/-- **Given window-free curve encodings, the off-curve output does not read the curve mask.** -/
theorem realOutOff_mask (facts : TableFacts T) (ctx : Context) (u : AffineInput) (cells : Source T × Cold T u)
    (free : CurveWindowFree u cells) (o : OtherOff) (m m' : {m : BaseField // m ≠ 0}) :
    realOutOff ctx u ((bmrEquivOff T ctx u).symm (cells, maskSplit.symm (m, o))) =
      realOutOff ctx u ((bmrEquivOff T ctx u).symm (cells, maskSplit.symm (m', o))) := by
  set e := bmrEquivOff T ctx u
  have image : ∀ m, e (e.symm (cells, maskSplit.symm (m, o))) = (cells, maskSplit.symm (m, o)) :=
    fun m => e.apply_symm_apply _
  have curveHint : ∀ m element, hint (e.symm (cells, maskSplit.symm (m, o))) (curveEnc element) = false := by
    intro m element
    apply hint_false_of_window facts ctx u
    have parts := bmrEquivOff_join ctx u (e.symm (cells, maskSplit.symm (m, o)))
    rw [← parts.1, ← parts.2]
    show ¬ InWindow T (evalInt u (e (e.symm (cells, maskSplit.symm (m, o)))).1.1.1
      (e (e.symm (cells, maskSplit.symm (m, o)))).1.2 (curveEnc element))
    rw [image m]
    exact free element
  have hints : hint (e.symm (cells, maskSplit.symm (m, o))) = hint (e.symm (cells, maskSplit.symm (m', o))) := by
    funext enc
    rcases enc with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y))
    · rfl
    · rw [show (Sum.inl (Sum.inr x) : Enc) = curveEnc (.inl x) from rfl, curveHint, curveHint]
    · rfl
    · rw [show (Sum.inr (Sum.inr y) : Enc) = curveEnc (.inr y) from rfl, curveHint, curveHint]
  rw [realOutOff_eq, realOutOff_eq, hints]
  show (((e (e.symm (cells, maskSplit.symm (m, o)))).1.1, _), (e (e.symm (cells, maskSplit.symm (m, o)))).1.2) =
    (((e (e.symm (cells, maskSplit.symm (m', o)))).1.1, _), (e (e.symm (cells, maskSplit.symm (m', o)))).1.2)
  rw [image m, image m']

/-- The number of nonzero masks whose fibre coin has a given key label is at most `keyError · (p − 1)`. -/
theorem mask_count_le (facts : TableFacts T) (ctx : Context) (u : AffineInput) (off : ¬ OnCurve u)
    (cells : Source T × Cold T u) (free : CurveWindowFree u cells) (o : OtherOff) (ℓ : ℕ) :
    (((Finset.univ.filter fun m : {m : BaseField // m ≠ 0} =>
        (((bmrEquivOff T ctx u).symm (cells, maskSplit.symm (m, o))).bridge).val % 2 ^ 128 = ℓ).card : ℕ) :
          ℝ≥0∞) ≤ keyError * ((BN254.baseFieldModulus - 1 : ℕ) : ℝ≥0∞) := by
  classical
  set f : {m : BaseField // m ≠ 0} → BaseField := fun m => keyOf u cells - m.1 * curveGap u
  have inj : Function.Injective f := by
    intro m m' same
    have eq : m.1 * curveGap u = m'.1 * curveGap u := by
      have := congrArg (fun x => keyOf u cells - x) same
      simp only [f, sub_sub_cancel] at this
      exact this
    exact Subtype.ext (mul_right_cancel₀ (curveGap_ne_zero off) eq)
  have filterEq : (Finset.univ.filter fun m : {m : BaseField // m ≠ 0} =>
      (((bmrEquivOff T ctx u).symm (cells, maskSplit.symm (m, o))).bridge).val % 2 ^ 128 = ℓ) =
      Finset.univ.filter fun m => (f m).val % 2 ^ 128 = ℓ := by
    refine Finset.filter_congr fun m _ => ?_
    rw [bridge_fibre facts ctx u cells free]
    rfl
  have low := natCard_low_le ℓ f inj
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at low
  have pos : ((BN254.baseFieldModulus - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    have two : 2 ≤ BN254.baseFieldModulus := (Fact.out : Nat.Prime BN254.baseFieldModulus).two_le
    rw [Ne, Nat.cast_eq_zero]
    omega
  have bound := count_bound
  rw [ENNReal.div_le_iff_le_mul (Or.inl pos) (Or.inl (ENNReal.natCast_ne_top _))] at bound
  rw [filterEq]
  refine le_trans ?_ bound
  exact_mod_cast low

/-- Summing a bound over the middle coordinate of a triple product. -/
theorem sum_triple_le {A Mk O : Type} [Fintype A] [Fintype Mk] [Fintype O] (φ ψ : A → Mk → O → ℝ≥0∞) (k : ℝ≥0∞)
    (each : ∀ a o, ∑ m, φ a m o ≤ k * ∑ m, ψ a m o) :
    ∑ x : A × (Mk × O), φ x.1 x.2.1 x.2.2 ≤ k * ∑ x : A × (Mk × O), ψ x.1 x.2.1 x.2.2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_comm (f := fun m o => ψ a m o),
    Finset.mul_sum]
  exact Finset.sum_le_sum fun o _ => each a o

open Classical in
/-- **The key label is rare given the off-curve output**, at window-free curve encodings: summed against any weight
of the off-curve output, the coins with `bridge.val % 2^128 = ℓ` weigh at most `keyError` of all coins. -/
theorem keyLabel_weighted (facts : TableFacts T) (ctx : Context) (u : AffineInput) (off : ¬ OnCurve u)
    (F : OutOff T u → ℝ≥0∞) (ℓ : ℕ) :
    ∑ c : Coins T, F (realOutOff ctx u c) *
        (if CurveWindowFree u (cellsOfOut (realOutOff ctx u c)) ∧ (c.bridge).val % 2 ^ 128 = ℓ then 1 else 0) ≤
      keyError * ∑ c : Coins T, F (realOutOff ctx u c) := by
  set e := bmrEquivOff T ctx u
  let E : (Source T × Cold T u) × ({m : BaseField // m ≠ 0} × OtherOff) ≃ Coins T :=
    (Equiv.prodCongr (Equiv.refl _) maskSplit.symm).trans e.symm
  have Eapply : ∀ cells m o, E (cells, (m, o)) = e.symm (cells, maskSplit.symm (m, o)) := fun _ _ _ => rfl
  have cellsE : ∀ cells m o, cellsOfOut (realOutOff ctx u (E (cells, (m, o)))) = cells := by
    intro cells m o
    rw [cellsOfOut_real, Eapply]
    exact congrArg Prod.fst (e.apply_symm_apply _)
  have reindex : ∀ g : Coins T → ℝ≥0∞,
      ∑ c, g c = ∑ x : (Source T × Cold T u) × ({m : BaseField // m ≠ 0} × OtherOff), g (E (x.1, (x.2.1, x.2.2))) :=
    fun g => (Fintype.sum_equiv E _ _ fun _ => rfl).symm
  rw [reindex, reindex]
  refine sum_triple_le (fun cells m o => F (realOutOff ctx u (E (cells, (m, o)))) *
      (if CurveWindowFree u (cellsOfOut (realOutOff ctx u (E (cells, (m, o))))) ∧
        ((E (cells, (m, o))).bridge).val % 2 ^ 128 = ℓ then 1 else 0))
    (fun cells m o => F (realOutOff ctx u (E (cells, (m, o))))) keyError fun cells o => ?_
  by_cases free : CurveWindowFree u cells
  · obtain ⟨m0⟩ := (inferInstance : Nonempty {m : BaseField // m ≠ 0})
    have hF : ∀ m, F (realOutOff ctx u (E (cells, (m, o)))) = F (realOutOff ctx u (E (cells, (m0, o)))) :=
      fun m => by rw [Eapply, Eapply, realOutOff_mask facts ctx u cells free o m m0]
    have lhs : ∑ m, F (realOutOff ctx u (E (cells, (m, o)))) *
        (if CurveWindowFree u (cellsOfOut (realOutOff ctx u (E (cells, (m, o))))) ∧
          ((E (cells, (m, o))).bridge).val % 2 ^ 128 = ℓ then 1 else 0) =
        F (realOutOff ctx u (E (cells, (m0, o)))) *
          (((Finset.univ.filter fun m : {m : BaseField // m ≠ 0} =>
            (((bmrEquivOff T ctx u).symm (cells, maskSplit.symm (m, o))).bridge).val % 2 ^ 128 = ℓ).card : ℕ) :
              ℝ≥0∞) := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hF m, cellsE]
      by_cases hit : ((E (cells, (m, o))).bridge).val % 2 ^ 128 = ℓ
      · rw [if_pos ⟨free, hit⟩, if_pos (by rw [← Eapply]; exact hit)]
        simp
      · rw [if_neg (fun both => hit both.2), if_neg (by rw [← Eapply]; exact hit)]
        simp
    have rhs : ∑ m, F (realOutOff ctx u (E (cells, (m, o)))) =
        ((BN254.baseFieldModulus - 1 : ℕ) : ℝ≥0∞) * F (realOutOff ctx u (E (cells, (m0, o)))) := by
      rw [Finset.sum_congr rfl fun m _ => hF m, Finset.sum_const, Finset.card_univ, card_nonzero' _, nsmul_eq_mul]
    show ∑ m, F (realOutOff ctx u (E (cells, (m, o)))) *
        (if CurveWindowFree u (cellsOfOut (realOutOff ctx u (E (cells, (m, o))))) ∧
          ((E (cells, (m, o))).bridge).val % 2 ^ 128 = ℓ then 1 else 0) ≤
      keyError * ∑ m, F (realOutOff ctx u (E (cells, (m, o))))
    rw [lhs, rhs, ← mul_assoc, mul_comm (F _), mul_comm keyError]
    gcongr ?_ * _
    rw [mul_comm]
    exact mask_count_le facts ctx u off cells free o ℓ
  · have zero : ∀ m, F (realOutOff ctx u (E (cells, (m, o)))) *
        (if CurveWindowFree u (cellsOfOut (realOutOff ctx u (E (cells, (m, o))))) ∧
          ((E (cells, (m, o))).bridge).val % 2 ^ 128 = ℓ then 1 else 0) = 0 := by
      intro m
      rw [cellsE, if_neg (fun both => free both.1), mul_zero]
    show ∑ m, F (realOutOff ctx u (E (cells, (m, o)))) *
        (if CurveWindowFree u (cellsOfOut (realOutOff ctx u (E (cells, (m, o))))) ∧
          ((E (cells, (m, o))).bridge).val % 2 ^ 128 = ℓ then 1 else 0) ≤
      keyError * ∑ m, F (realOutOff ctx u (E (cells, (m, o))))
    rw [Finset.sum_congr rfl fun m _ => zero m, Finset.sum_const_zero]
    exact zero_le

end Weighted

/-! ### The normalized layer: the key label given the normalized output

The normalized rows of a digit are the unscaled rows at the scales `(ρ, κ)` read off its two collector offsets
`(K_z, K_c)` (`rowKey`), so at a fixed key the normalized output is a conversion of P45's output at the fixed context
of those scales (`nRealOutOff_key`), and the key itself is read back from that output's row cells (`recoverKey_real`).
Summing over the keys, `keyLabel_weighted` applies at each fixed context (`nKeyLabel_weighted`). -/

section Normalized

variable {T : CrtTable} [∀ i, NeZero (T.modulus i)]

/-- The two collector offsets `(K_z, K_c)` of each digit. -/
def rowKey (c : Coins T) : Scales := fun d => (rowOffset c (d, .inl .rowZ_x9), rowOffset c (d, .inl .rowY_cubic))

/-- The normalizing scales `(ρ, κ)` of a key. -/
def keyScales (nctx : NContext) (k : Scales) : Scales := fun d =>
  (Rows.scaleOf (nctx.rows d).z.constant (k d).1, Rows.scaleOf (nctx.rows d).y.xSquared (k d).2)

/-- The published row data of a fixed-context row at a key: its `X` constant, the key's flags, the sign of `κ`. -/
def keyRow (nctx : NContext) (k : Scales) (d : Fin 91) (g : RowGamma) : NormRow :=
  { xC0 := g.xC0, zFlag := Rows.zeroFlag (k d).1, sFlag := Rows.zeroFlag (k d).2,
    sign := Rows.signBit (keyScales nctx k d).2 }

/-- The conversion of a fixed-context off-curve output at a key. -/
def keyConvOff (nctx : NContext) (k : Scales) {u : AffineInput} (o : OutOff T u) : NOutOff T u :=
  (((o.1.1.1, fun d => keyRow nctx k d (o.1.1.2.1 d), o.1.1.2.2), o.1.2), o.2)

/-- The key read back from a fixed-context output at scales `s`: `K_z = ρ z₀ − zC0`, `K_c = κ s₄ − yC4`. -/
def recoverKey (nctx : NContext) (s : Scales) {u : AffineInput} (o : OutOff T u) : Scales := fun d =>
  ((s d).1 * (nctx.rows d).z.constant - (o.1.1.2.1 d).zC0,
    (s d).2 * (nctx.rows d).y.xSquared - (o.1.1.2.1 d).yC4)

/-- The window-free curve encodings of a normalized off-curve output. -/
def nFree (u : AffineInput) (o : NOutOff T u) : Prop :=
  ∀ element, ¬ InWindow T (evalInt u o.1.1.1 o.2 (curveEnc element))

theorem nSlope_key (nctx : NContext) (c : Coins T) :
    nSlope nctx c = slope (fsContext nctx (keyScales nctx (rowKey c))) c := by
  funext e
  rcases e with ((⟨d, x⟩ | x) | (⟨d, y⟩ | y)) <;> rfl

theorem nJoin_key (nctx : NContext) (c : Coins T) :
    nJoin nctx c = join (fsContext nctx (keyScales nctx (rowKey c))) c := by
  funext e i
  unfold nJoin join
  rw [nSlope_key]

theorem nGamma_key (nctx : NContext) (c : Coins T) (d : Fin 91) :
    nGamma nctx c d = keyRow nctx (rowKey c) d (gamma (fsContext nctx (keyScales nctx (rowKey c))) c d) := rfl

/-- **The normalized output is the converted output at the fixed context of its key.** -/
theorem nRealOutOff_key (nctx : NContext) (u : AffineInput) (c : Coins T) :
    nRealOutOff nctx u c =
      keyConvOff nctx (rowKey c) (realOutOff (fsContext nctx (keyScales nctx (rowKey c))) u c) := by
  unfold nRealOutOff keyConvOff realOutOff
  rw [nJoin_key]
  rfl

/-- **The key is read back from the fixed-context output**, at any scales. -/
theorem recoverKey_real (nctx : NContext) (s : Scales) (u : AffineInput) (c : Coins T) :
    recoverKey nctx s (realOutOff (fsContext nctx s) u c) = rowKey c := by
  funext d
  unfold recoverKey realOutOff gamma FieldMacToECMac.garbleRow Biquadratic.garbleY Biquadratic.garbleZ fsContext
    Rows.scaled Rows.multiply rowKey
  simp only [Prod.mk.injEq]
  constructor <;> ring

variable [FieldCertificate]

open Classical in
/-- **The key label is rare given the normalized off-curve output**, at window-free curve encodings. -/
theorem nKeyLabel_weighted (facts : TableFacts T) (nctx : NContext) (u : AffineInput) (off : ¬ OnCurve u)
    (F : NOutOff T u → ℝ≥0∞) (ℓ : ℕ) :
    ∑ c : Coins T, F (nRealOutOff nctx u c) *
        (if nFree u (nRealOutOff nctx u c) ∧ (c.bridge).val % 2 ^ 128 = ℓ then 1 else 0) ≤
      keyError * ∑ c : Coins T, F (nRealOutOff nctx u c) := by
  have part : ∀ G : Coins T → ℝ≥0∞, ∑ c, G c = ∑ k : Scales, ∑ c, (if rowKey c = k then G c else 0) := by
    intro G
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp
  rw [part, part, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have eachL : ∀ c, (if rowKey c = k then F (nRealOutOff nctx u c) *
      (if nFree u (nRealOutOff nctx u c) ∧ (c.bridge).val % 2 ^ 128 = ℓ then 1 else 0) else 0) =
      (fun o : OutOff T u => if recoverKey nctx (keyScales nctx k) o = k then F (keyConvOff nctx k o) else 0)
          (realOutOff (fsContext nctx (keyScales nctx k)) u c) *
        (if CurveWindowFree u (cellsOfOut (realOutOff (fsContext nctx (keyScales nctx k)) u c)) ∧
          (c.bridge).val % 2 ^ 128 = ℓ then 1 else 0) := by
    intro c
    simp only [recoverKey_real]
    by_cases hk : rowKey c = k
    · rw [if_pos hk, if_pos hk, nRealOutOff_key, hk]
      rfl
    · rw [if_neg hk, if_neg hk, zero_mul]
  have eachR : ∀ c, (if rowKey c = k then F (nRealOutOff nctx u c) else 0) =
      (fun o : OutOff T u => if recoverKey nctx (keyScales nctx k) o = k then F (keyConvOff nctx k o) else 0)
          (realOutOff (fsContext nctx (keyScales nctx k)) u c) := by
    intro c
    simp only [recoverKey_real]
    by_cases hk : rowKey c = k
    · rw [if_pos hk, if_pos hk, nRealOutOff_key, hk]
    · rw [if_neg hk, if_neg hk]
  rw [Finset.sum_congr rfl fun c _ => eachL c, Finset.sum_congr rfl fun c _ => eachR c]
  exact keyLabel_weighted facts (fsContext nctx (keyScales nctx k)) u off
    (fun o : OutOff T u => if recoverKey nctx (keyScales nctx k) o = k then F (keyConvOff nctx k o) else 0) ℓ

end Normalized

end

end Kriterion.CRT.Privacy.BmrOff
