/-
**The normalized rows decode** (`Construction/CRT/Rows.lean`).

* the unscaled rows' normalizing coefficients are nonzero for every on-curve offset
  (`z0_ne_zero`, `s4_ne_zero`: `a ≠ 0`, `b ≠ 0`, `b² ≠ 27` because `3` is not a square);
* the normalized rows publish their `Z` and sign-row constants as the flags (`garbleZ_norm`,
  `garbleY_norm`), so the evaluator's values are the rows evaluated at the input
  (`evaluateNormRow_encoded`);
* `(−1)^ν κ = τ²` with `τ = κ^((p+1)/4)` (`signed_signBit`), so the corrected values are the old
  rows `Coordinates.rows K φ ρ τ` evaluated at the input, except that digit zero's sign row carries an
  extra square `x²` (`corrected_some`, `corrected_none`), which the decoder does not see
  (`decodeHomogeneous_scale_y`).
-/

import Proof.Correctness.JacobianMixed
import Proof.Privacy.Phase3.OnCurveNonzero
import Construction.CRT.Rows

namespace Kriterion.CRT.Rows

open Kriterion Kriterion.BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-! ### Algebra of the scales -/

theorem evaluate_multiply (factor : BaseField) (coefficients : Coordinates.Coefficients) (input : AffineInput) :
    Coordinates.evaluate (multiply factor coefficients) input = factor * Coordinates.evaluate coefficients input := by
  simp only [Coordinates.evaluate, multiply]
  ring

theorem flagValue_zeroFlag_ne_zero [FieldCertificate] (k : BaseField) : k + flagValue (zeroFlag k) ≠ 0 := by
  by_cases zero : k = 0
  · simp [flagValue, zeroFlag, zero]
  · simpa [flagValue, zeroFlag, zero] using zero

theorem add_flagValue_of_ne [FieldCertificate] (k : BaseField) (ne : k ≠ 0) : k + flagValue (zeroFlag k) = k := by
  simp [flagValue, zeroFlag, ne]

theorem scaleOf_ne_zero [FieldCertificate] (c k : BaseField) (hc : c ≠ 0) : scaleOf c k ≠ 0 :=
  mul_ne_zero (flagValue_zeroFlag_ne_zero k) (inv_ne_zero hc)

theorem scaleOf_mul [FieldCertificate] (c k : BaseField) (hc : c ≠ 0) :
    scaleOf c k * c = k + flagValue (zeroFlag k) := by
  unfold scaleOf
  rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-! ### The unscaled rows' coefficients -/

/-- A square is never `27`: `(b/3)² = 3` would make `3` a square. -/
theorem sq_ne_twentySeven [FieldCertificate] (value : BaseField) : value ^ 2 ≠ 27 := by
  intro square
  apply Security.Phase3.three_not_square
  refine ⟨value * Biquadratic.inverseThree, ?_⟩
  have inv := Biquadratic.three_mul_inverseThree
  linear_combination (-(Biquadratic.inverseThree ^ 2)) * square +
    (-3 * (1 + 3 * Biquadratic.inverseThree)) * inv

/-- A digit endomorphism's base is nonzero. -/
theorem phi_ne_zero (phi : BaseField) (six : phi ^ 6 = 1) : phi ≠ 0 := by
  intro zero
  rw [zero] at six
  exact absurd six (by decide)

/-- **The `Z` row's constant is nonzero**: `1` for digit zero, `−a` otherwise. -/
theorem z0_ne_zero [FieldCertificate] (offset : AffineInput) (endomorphismBase : Option BaseField)
    (onCurve : OnCurve offset) : (unscaledRows offset endomorphismBase).z.constant ≠ 0 := by
  cases endomorphismBase with
  | none => simp [unscaledRows, Coordinates.scale]
  | some phi =>
    simpa [unscaledRows, Coordinates.scale, Coordinates.zCoefficients] using
      Security.Phase3.onCurve_x_ne_zero offset onCurve

/-- **The sign row's `x²` coefficient is nonzero**: `b` for digit zero, `3ab(27 − b²)φ⁸` otherwise. -/
theorem s4_ne_zero [FieldCertificate] (offset : AffineInput) (endomorphismBase : Option BaseField)
    (onCurve : OnCurve offset) (valid : ∀ phi, endomorphismBase = some phi → phi ^ 6 = 1) :
    (unscaledRows offset endomorphismBase).y.xSquared ≠ 0 := by
  cases endomorphismBase with
  | none => simpa [unscaledRows, zeroSign] using Security.Phase3.onCurve_y_ne_zero offset onCurve
  | some phi =>
    have phiNe := phi_ne_zero phi (valid phi rfl)
    have threeNe : (3 : BaseField) ≠ 0 := left_ne_zero_of_mul_eq_one Biquadratic.three_mul_inverseThree
    have factorNe : (27 : BaseField) - offset.y ^ 2 ≠ 0 := sub_ne_zero.mpr (sq_ne_twentySeven offset.y).symm
    simp only [unscaledRows, Coordinates.scale, Coordinates.signCoefficients, one_pow, mul_one]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero threeNe
      (Security.Phase3.onCurve_x_ne_zero offset onCurve))
      (Security.Phase3.onCurve_y_ne_zero offset onCurve)) factorNe) (pow_ne_zero _ (pow_ne_zero _ phiNe))

/-- The unscaled rows carry only the monomials their tables read. -/
theorem unscaledRows_sparse (offset : AffineInput) (endomorphismBase : Option BaseField) :
    FieldMacToECMac.SparseRow (unscaledRows offset endomorphismBase) := by
  cases endomorphismBase <;> simp [FieldMacToECMac.SparseRow, unscaledRows, zeroSign, Coordinates.scale,
    Coordinates.xCoefficients, Coordinates.signCoefficients, Coordinates.zCoefficients]

theorem scaled_sparse (rho kappa : BaseField) (rows : Coordinates.Rows) (sparse : FieldMacToECMac.SparseRow rows) :
    FieldMacToECMac.SparseRow (scaled rho kappa rows) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sparse
  simp [FieldMacToECMac.SparseRow, scaled, multiply, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ### The published constants are the flags -/

theorem rhoOf_ne_zero [FieldCertificate] (rows : Coordinates.Rows) (K : Biquadratic.Values)
    (zNe : rows.z.constant ≠ 0) : rhoOf rows K ≠ 0 := scaleOf_ne_zero _ _ zNe

theorem kappaOf_ne_zero [FieldCertificate] (rows : Coordinates.Rows) (K : Biquadratic.Values)
    (sNe : rows.y.xSquared ≠ 0) : kappaOf rows K ≠ 0 := scaleOf_ne_zero _ _ sNe

/-- **The `Z` row publishes `ε_Z`.** -/
theorem garbleZ_norm [FieldCertificate] (rows : Coordinates.Rows) (K : Biquadratic.Values)
    (zNe : rows.z.constant ≠ 0) :
    Biquadratic.garbleZ (normRows rows K).z.constant K = { c0 := flagValue (zeroFlag (K (.inl .rowZ_x9))) } := by
  have product := scaleOf_mul rows.z.constant (K (.inl .rowZ_x9)) zNe
  simp only [Biquadratic.garbleZ, normRows, scaled, multiply, Biquadratic.ZGamma.mk.injEq]
  unfold rhoOf
  linear_combination product

/-- **The sign row publishes `ε_S`.** -/
theorem garbleY_norm [FieldCertificate] (rows : Coordinates.Rows) (K : Biquadratic.Values)
    (sNe : rows.y.xSquared ≠ 0) :
    Biquadratic.garbleY (normRows rows K).y.xSquared K = { c4 := flagValue (zeroFlag (K (.inl .rowY_cubic))) } := by
  have product := scaleOf_mul rows.y.xSquared (K (.inl .rowY_cubic)) sNe
  simp only [Biquadratic.garbleY, normRows, scaled, multiply, Biquadratic.YGamma.mk.injEq]
  unfold kappaOf
  linear_combination product

/-- The corrected value of a digit: the normalized rows at the input, the sign row signed. -/
def corrected (rows : Coordinates.Rows) (K : Biquadratic.Values) (input : AffineInput) :
    FieldMacToECMac.HomogeneousValue :=
  { x := Coordinates.evaluate (normRows rows K).x input
    y := signed (signBit (kappaOf rows K)) (Coordinates.evaluate (normRows rows K).y input)
    z := Coordinates.evaluate (normRows rows K).z input }

/-- **The evaluator's value of a digit on the curve** is the corrected value. -/
theorem evaluateNormRow_encoded [FieldCertificate] (rows : Coordinates.Rows) (K : Biquadratic.Values)
    (x : Biquadratic.XRandomness) (y : Biquadratic.YRandomness) (z : Biquadratic.ZRandomness)
    (input : AffineInput) (onCurve : OnCurve input) (zNe : rows.z.constant ≠ 0)
    (sNe : rows.y.xSquared ≠ 0) (sparse : FieldMacToECMac.SparseRow rows) :
    evaluateNormRow (garbleNormRow rows K) input (Biquadratic.delivered (normRows rows K) x y z K input) =
      corrected rows K input := by
  have xRow := Biquadratic.evaluateEncodedX (normRows rows K) x y z K input
  have yRow := Biquadratic.evaluateEncodedY (normRows rows K) x y z K input onCurve
  have zRow := Biquadratic.evaluateEncodedZ (normRows rows K) x y z K input
  rw [garbleY_norm rows K sNe] at yRow
  rw [garbleZ_norm rows K zNe] at zRow
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := scaled_sparse (rhoOf rows K) (kappaOf rows K) rows sparse
  have ex : Coordinates.evaluate (normRows rows K).x input = (normRows rows K).x.constant +
      (normRows rows K).x.x * input.x + (normRows rows K).x.y * input.y +
      (normRows rows K).x.xSquared * input.x ^ 2 := by
    simp only [Coordinates.evaluate]
    rw [show (normRows rows K).x.xy = 0 from h1, show (normRows rows K).x.ySquared = 0 from h2]
    ring
  have ey : Coordinates.evaluate (normRows rows K).y input = (normRows rows K).y.constant +
      (normRows rows K).y.y * input.y + (normRows rows K).y.xSquared * input.x ^ 2 +
      (normRows rows K).y.ySquared * input.y ^ 2 := by
    simp only [Coordinates.evaluate]
    rw [show (normRows rows K).y.x = 0 from h3, show (normRows rows K).y.xy = 0 from h4]
    ring
  have ez : Coordinates.evaluate (normRows rows K).z input =
      (normRows rows K).z.constant + (normRows rows K).z.x * input.x := by
    simp only [Coordinates.evaluate]
    rw [show (normRows rows K).z.y = 0 from h5, show (normRows rows K).z.xy = 0 from h6,
      show (normRows rows K).z.xSquared = 0 from h7, show (normRows rows K).z.ySquared = 0 from h8]
    ring
  have hx : (garbleNormRow rows K).xC0 = (Biquadratic.garbleX (normRows rows K).x.constant K).c0 := by
    simp only [garbleNormRow]
  have hs : (garbleNormRow rows K).sFlag = zeroFlag (K (.inl .rowY_cubic)) := by simp only [garbleNormRow]
  have hz : (garbleNormRow rows K).zFlag = zeroFlag (K (.inl .rowZ_x9)) := by simp only [garbleNormRow]
  have hn : (garbleNormRow rows K).sign = signBit (kappaOf rows K) := by simp only [garbleNormRow]
  unfold evaluateNormRow
  rw [hx, hs, hz, hn]
  rw [xRow, yRow, zRow]
  unfold corrected
  rw [ex, ey, ez]

/-! ### The sign correction -/

/-- `τ = κ^((p+1)/4)`, the square root the correction realizes. -/
def tauOf (kappa : BaseField) : BaseField := Garbling.fieldPower kappa Garbling.rootExponent

theorem tauOf_ne_zero [FieldCertificate] (kappa : BaseField) (ne : kappa ≠ 0) : tauOf kappa ≠ 0 := by
  unfold tauOf
  rw [JacobianMixed.fieldPower_eq _ _ JacobianMixed.rootExponent_lt]
  exact pow_ne_zero _ ne

theorem two_ne_zero_base : (2 : BaseField) ≠ 0 := by decide

/-- The quadratic character of a nonzero element is `±1`. -/
theorem character_cases [FieldCertificate] (kappa : BaseField) (ne : kappa ≠ 0) :
    kappa ^ Garbling.characterExponent = 1 ∨ kappa ^ Garbling.characterExponent = -1 := by
  have sq : (kappa ^ Garbling.characterExponent) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, JacobianMixed.two_characterExponent]
    exact ZMod.pow_card_sub_one_eq_one ne
  exact sq_eq_one_iff.mp sq

/-- `τ² = χ(κ) κ`. -/
theorem tauOf_sq [FieldCertificate] (kappa : BaseField) :
    tauOf kappa ^ 2 = kappa ^ Garbling.characterExponent * kappa := by
  unfold tauOf
  have exponent : Garbling.rootExponent * 2 = Garbling.characterExponent + 1 := by
    unfold Garbling.rootExponent Garbling.characterExponent baseFieldModulus
    norm_num
  rw [JacobianMixed.fieldPower_eq _ _ JacobianMixed.rootExponent_lt, ← pow_mul, exponent, pow_succ]

/-- **`(−1)^ν κ s = τ² s`**: the correction makes the sign row's scale the square `τ²`. -/
theorem signed_signBit [FieldCertificate] (kappa value : BaseField) (ne : kappa ≠ 0) :
    signed (signBit kappa) (kappa * value) = tauOf kappa ^ 2 * value := by
  rw [tauOf_sq]
  unfold signed signBit
  rw [JacobianMixed.fieldPower_eq _ _ JacobianMixed.characterExponent_lt]
  rcases character_cases kappa ne with one | minus
  · have notMinus : ¬ (kappa ^ Garbling.characterExponent = -1) := by
      rw [one]
      intro same
      have two : (2 : BaseField) = 0 := by linear_combination same
      exact two_ne_zero_base two
    rw [if_neg (by simpa using notMinus), one]
    ring
  · rw [if_pos (by simpa using minus), minus]
    ring

/-! ### The corrected values are the old rows' values -/

theorem corrected_eq [FieldCertificate] (rows : Coordinates.Rows) (K : Biquadratic.Values) (input : AffineInput)
    (sNe : rows.y.xSquared ≠ 0) :
    corrected rows K input =
      { x := rhoOf rows K ^ 2 * Coordinates.evaluate rows.x input
        y := tauOf (kappaOf rows K) ^ 2 * Coordinates.evaluate rows.y input
        z := rhoOf rows K * Coordinates.evaluate rows.z input } := by
  unfold corrected normRows scaled
  simp only [evaluate_multiply]
  rw [signed_signBit _ _ (kappaOf_ne_zero rows K sNe)]

/-- For a nonzero digit the corrected value is the old rows' value at `(ρ, τ)`. -/
theorem corrected_some [FieldCertificate] (offset : AffineInput) (phi : BaseField) (K : Biquadratic.Values)
    (input : AffineInput) (sNe : (unscaledRows offset (some phi)).y.xSquared ≠ 0) :
    corrected (unscaledRows offset (some phi)) K input =
      FieldMacToECMac.evaluateRow (Coordinates.rows offset (some phi) (rhoOf (unscaledRows offset (some phi)) K)
        (tauOf (kappaOf (unscaledRows offset (some phi)) K))) input := by
  rw [corrected_eq _ _ _ sNe]
  simp only [FieldMacToECMac.evaluateRow, Coordinates.rows, unscaledRows, Coordinates.evaluateScaleSome, one_pow,
    one_mul, pow_one]

/-- For digit zero the corrected value is the old rows' value at `(ρ, τ)` with the sign row times `x²`. -/
theorem corrected_none [FieldCertificate] (offset : AffineInput) (K : Biquadratic.Values) (input : AffineInput)
    (sNe : (unscaledRows offset none).y.xSquared ≠ 0) :
    corrected (unscaledRows offset none) K input =
      { x := (FieldMacToECMac.evaluateRow (Coordinates.rows offset none (rhoOf (unscaledRows offset none) K)
          (tauOf (kappaOf (unscaledRows offset none) K))) input).x
        y := input.x ^ 2 * (FieldMacToECMac.evaluateRow (Coordinates.rows offset none
          (rhoOf (unscaledRows offset none) K) (tauOf (kappaOf (unscaledRows offset none) K))) input).y
        z := (FieldMacToECMac.evaluateRow (Coordinates.rows offset none (rhoOf (unscaledRows offset none) K)
          (tauOf (kappaOf (unscaledRows offset none) K))) input).z } := by
  rw [corrected_eq _ _ _ sNe, FieldMacToECMac.evaluateRowsNone]
  have ex : Coordinates.evaluate (unscaledRows offset none).x input = offset.x := by
    show Coordinates.evaluate (Coordinates.scale none 1 2 offset.x (Coordinates.xCoefficients offset)) input = _
    rw [Coordinates.evaluateScaleNone]
    ring
  have ey : Coordinates.evaluate (unscaledRows offset none).y input = offset.y * input.x ^ 2 := by
    show Coordinates.evaluate (zeroSign offset) input = _
    unfold Coordinates.evaluate zeroSign
    ring
  have ez : Coordinates.evaluate (unscaledRows offset none).z input = 1 := by
    show Coordinates.evaluate (Coordinates.scale none 1 1 1 (Coordinates.zCoefficients offset)) input = _
    rw [Coordinates.evaluateScaleNone]
    ring
  rw [ex, ey, ez]
  congr 1 <;> ring

/-! ### The decoder does not see a square factor of the sign row -/

theorem fieldPower_character_mul_sq [FieldCertificate] (c value : BaseField) (ne : c ≠ 0) :
    Garbling.fieldPower (c ^ 2 * value) Garbling.characterExponent =
      Garbling.fieldPower value Garbling.characterExponent := by
  rw [JacobianMixed.fieldPower_eq _ _ JacobianMixed.characterExponent_lt,
    JacobianMixed.fieldPower_eq _ _ JacobianMixed.characterExponent_lt, mul_pow, ← pow_mul,
    JacobianMixed.two_characterExponent, ZMod.pow_card_sub_one_eq_one ne, one_mul]

/-- **Scaling the sign row by a nonzero square does not change the decode.** -/
theorem decodeHomogeneous_scale_y [FieldCertificate] [GroupCertificate] (value : FieldMacToECMac.HomogeneousValue)
    (c : BaseField) (ne : c ≠ 0) (exceptionDigit tripleDigit : Digit) (inputPoint : Point) :
    Garbling.decodeHomogeneous { x := value.x, y := c ^ 2 * value.y, z := value.z } exceptionDigit tripleDigit
        inputPoint =
      Garbling.decodeHomogeneous value exceptionDigit tripleDigit inputPoint := by
  unfold Garbling.decodeHomogeneous
  simp only
  have zeroIff : c ^ 2 * value.y = 0 ↔ value.y = 0 := by
    constructor
    · intro zero
      exact (mul_eq_zero.mp zero).resolve_left (pow_ne_zero 2 ne)
    · intro zero
      rw [zero, mul_zero]
  by_cases zZero : value.z = 0
  · simp only [zZero, if_true]
  · simp only [zZero, if_false]
    by_cases yZero : value.y = 0
    · simp only [yZero, mul_zero, if_true]
    · rw [if_neg (fun zero => yZero (zeroIff.mp zero)), if_neg yZero, fieldPower_character_mul_sq _ _ ne]

end Kriterion.CRT.Rows
