/-
**The rows kernel of the normalized rows** (`HW`'s target rows) and its opening bound (`HW → H`).

The construction normalizes each digit's rows by scales read off its own row offsets (`Construction/CRT/Rows.lean`);
the public-first core (`Core/BmrNorm.lean`) shows that the evaluator's corrected target rows are distributed as the
unscaled rows at independent uniform scales `(ρ, τ)`, the sign row at `τ²`: `BMR.nTargets` at the coins' row
randomizers (`normTrueRows`, `normRealRows`). Against the old kernel (`Security.Phase3.realRows`) the only change is
digit zero's sign row, `τ² b x²` instead of `τ² b`: it is the lift of `K` at `(ρ, τ x)` (`x ≠ 0` on the curve), so
the opening's kernel bound carries over digit by digit with the sign multiplier `x` at digit zero
(`normRows_etvDist_le`, `455/#Point`), and so does the doubling mass (`normRowsDoubling_le`, `364/#Point`).
-/

import Proof.Privacy.Phase3.OpeningBound
import Proof.Privacy.CRT.Core.BmrNorm
import Construction.CRT.Entry
import Proof.Privacy.CRT.Flags.RowsDoubling

set_option maxRecDepth 8000

namespace Kriterion.CRT.Privacy.NormRows

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3
open Kriterion.ArgoMAC.Scheme (Coins)
open scoped ENNReal

noncomputable section

/-! ### 1. The kernel -/

/-- The unscaled rows of the scheme's coins. -/
def nctxOf (scalar : NonZeroScalar) (coins : Coins) : BMR.NContext :=
  ⟨fun d => Rows.unscaledOf (Entry.outputKeysOf scalar coins) d⟩

/-- The row randomizers `(ρ, τ)` of the scheme's coins (unused by the construction; the kernel's scales). -/
def scalesOf (coins : Coins) : Fin 91 → NonZeroBase × NonZeroBase :=
  fun d => ((coins.pointRandomness.get d).rho, (coins.pointRandomness.get d).tau)

/-- **The corrected true rows** of the coins at the input. -/
def normTrueRows (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput) :
    Fin 91 → FieldMacToECMac.HomogeneousValue :=
  BMR.nTargets (nctxOf scalar coins) input (scalesOf coins)

/-- **The rows kernel of `HW`**: the corrected true rows under the coins' law. -/
def normRealRows [FieldCertificate] (scalar : NonZeroScalar) : RowsKernel := fun input _ =>
  letI : Fintype Coins := Fintype.ofFinite Coins
  (PMF.uniformOfFintype Coins).map fun coins => some (normTrueRows scalar coins input)

variable [FieldCertificate] [GroupCertificate]

/-! ### 2. The corrected rows as real rows -/

/-- The zero digits of a scalar. -/
def zeros (scalar : NonZeroScalar) (d : Fin 91) : Bool := decide ((digitsOf scalar).get d = .zero)

/-- **The normalized real row**: at a zero digit the lift of `K` at `(ρ, τ x)`, else the real row. -/
def normRealRowOf (zero : Bool) (x : BaseField) (T K : Point) (rho tau : BaseField) :
    FieldMacToECMac.HomogeneousValue :=
  if zero then lift K rho (tau * x) else realRowOf T K rho tau

/-- The normalized real rows of a (tail, randomiser pairs) sample. -/
def normRealRowsOf (multiples : Fin 91 → Point) (zero : Fin 91 → Bool) (x : BaseField)
    (sample : GoodTails × (Fin 91 → NonZeroBase × NonZeroBase)) : Fin 91 → FieldMacToECMac.HomogeneousValue :=
  fun digit => normRealRowOf (zero digit) x (multiples digit) (clampOffsets radixMap sample.1.1 digit)
    (sample.2 digit).1.value (sample.2 digit).2.value

/-- A nonzero digit's corrected row is the old row. -/
theorem nTargets_some (offset input : AffineInput) (phi : BaseField) (rho tau : NonZeroBase) :
    (⟨rho.value ^ 2 * Coordinates.evaluate (Rows.unscaledRows offset (some phi)).x input,
      tau.value ^ 2 * Coordinates.evaluate (Rows.unscaledRows offset (some phi)).y input,
      rho.value * Coordinates.evaluate (Rows.unscaledRows offset (some phi)).z input⟩ :
        FieldMacToECMac.HomogeneousValue) =
      FieldMacToECMac.evaluateRow (Coordinates.rows offset (some phi) rho.value tau.value) input := by
  rw [FieldMacToECMac.evaluateRowsSome]
  simp only [Rows.unscaledRows, Coordinates.evaluateScaleSome, one_pow, one_mul, pow_one]
  rfl

/-- The key of a digit of the scheme's coins. -/
theorem outputKey_get (scalar : NonZeroScalar) (coins : Coins) (d : Fin 91) :
    (Entry.outputKeysOf scalar coins).get d =
      { digit := (digitsOf scalar).get d, offset := coins.offsets.values.get d } :=
  outputKeys_get scalar coins.offsets d

/-- **The corrected true rows are the normalized real rows** of the coins' tail and randomisers. -/
theorem normTrueRows_eq (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    normTrueRows scalar coins input = normRealRowsOf (multiplesOf scalar point) (zeros scalar) input.x (tailRho coins) := by
  funext d
  have keyEq := outputKey_get scalar coins d
  have pointEq := values_point _ coins.offsetsClamped d
  unfold normTrueRows normRealRowsOf normRealRowOf BMR.nTargets
  simp only [nctxOf, scalesOf, Rows.unscaledOf]
  rw [keyEq]
  simp only
  unfold zeros
  by_cases hz : (digitsOf scalar).get d = .zero
  · rw [if_pos (decide_eq_true hz), hz]
    rw [show clampOffsets radixMap (tailRho coins).1.1 d = (coins.offsets.values.get d).point from pointEq.symm,
      JacobianMixed.affineOffsetPoint_eq]
    simp only [digitEndomorphismBase, Rows.unscaledRows, Rows.zeroSign, Coordinates.scale, Coordinates.evaluate,
      JacobianMixed.affinePoint, lift, tailRho, rhoOf, FieldMacToECMac.HomogeneousValue.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  · rw [if_neg (fun same => hz (of_decide_eq_true same))]
    have trow := trueRow_eq { digit := (digitsOf scalar).get d, offset := coins.offsets.values.get d }
      (coins.pointRandomness.get d).rho (coins.pointRandomness.get d).tau input point decoded
    simp only at trow
    cases selected : digitEndomorphismBase ((digitsOf scalar).get d) with
    | none =>
      exfalso
      apply hz
      revert selected
      cases (digitsOf scalar).get d <;> simp [digitEndomorphismBase]
    | some phi =>
      rw [selected] at trow
      rw [nTargets_some, trow, pointEq]
      rfl

/-! ### 3. The kernel's law and the opening bound -/

/-- **The normalized kernel's law**: uniform good tails and uniform randomisers through `normRealRowsOf`. -/
theorem normRealRows_law (scalar : NonZeroScalar) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (target : Point) :
    @Eq (PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) (normRealRows scalar input target)
      ((productPMF (PMF.uniformOfFintype GoodTails)
          (PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase))).map
        fun sample => some (normRealRowsOf (multiplesOf scalar point) (zeros scalar) input.x sample)) := by
  letI : Fintype Coins := Fintype.ofFinite Coins
  have factor : (fun coins : Coins => (some (normTrueRows scalar coins input) :
        Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
      = (fun sample => some (normRealRowsOf (multiplesOf scalar point) (zeros scalar) input.x sample)) ∘ tailRho := by
    funext coins
    exact congrArg some (normTrueRows_eq scalar coins input point decoded)
  show ((PMF.uniformOfFintype Coins).map (fun coins : Coins => (some (normTrueRows scalar coins input) :
      Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) : PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) = _
  rw [factor, ← PMF.map_comp, tailRho_law]

/-- The sign multiplier of the lifted rows: `x` at a zero digit. -/
def normSignMultiplier (multiples : Fin 91 → Point) (zero : Fin 91 → Bool) (x : BaseField) (tail : Fin 90 → Point)
    (digit : Fin 91) : BaseField :=
  if zero digit then x else safeSignMultiplier multiples tail digit

theorem normSignMultiplier_ne_zero (multiples : Fin 91 → Point) (zero : Fin 91 → Bool) (x : BaseField)
    (xNe : x ≠ 0) (tail : Fin 90 → Point) (digit : Fin 91) : normSignMultiplier multiples zero x tail digit ≠ 0 := by
  unfold normSignMultiplier
  split
  · exact xNe
  · exact safeSignMultiplier_ne_zero _ _ _

/-- The normalized real rows with the exceptional rows replaced by lifts. -/
def liftedNormOf (multiples : Fin 91 → Point) (zero : Fin 91 → Bool) (x : BaseField)
    (sample : GoodTails × (Fin 91 → NonZeroBase × NonZeroBase)) : Fin 91 → FieldMacToECMac.HomogeneousValue :=
  fun digit => lift (realPoints radixMap multiples sample.1.1 digit)
    ((sample.2 digit).1.value * safeMultiplier multiples sample.1.1 digit)
    ((sample.2 digit).2.value * normSignMultiplier multiples zero x sample.1.1 digit)

theorem normRealRowsOf_eq_lifted (multiples : Fin 91 → Point) (zero : Fin 91 → Bool) (x : BaseField)
    (zeroMultiple : ∀ digit, zero digit = true → multiples digit = 0) (tail : GoodTails)
    (noException : ∀ digit, ¬ ExceptionalPair (multiples digit) (clampOffsets radixMap tail.1 digit))
    (rho : Fin 91 → NonZeroBase × NonZeroBase) :
    normRealRowsOf multiples zero x (tail, rho) = liftedNormOf multiples zero x (tail, rho) := by
  funext digit
  have notDouble : multiples digit ≠ clampOffsets radixMap tail.1 digit :=
    fun same => noException digit (Or.inl same)
  have notTriple : multiples digit ≠
      clampOffsets radixMap tail.1 digit + clampOffsets radixMap tail.1 digit :=
    fun same => noException digit (Or.inr same)
  unfold normRealRowsOf liftedNormOf normRealRowOf normSignMultiplier
  by_cases z : zero digit = true
  · have zeroT := zeroMultiple digit z
    simp only [z, if_true]
    have realZero : realPoints radixMap multiples tail.1 digit = clampOffsets radixMap tail.1 digit := by
      show multiples digit + clampOffsets radixMap tail.1 digit = _
      rw [zeroT, zero_add]
    have safe : safeMultiplier multiples tail.1 digit = 1 := by
      unfold safeMultiplier
      rw [zeroT]
      split
      · rfl
      · rfl
    rw [realZero, safe, mul_one]
  · simp only [z, if_false, Bool.false_eq_true]
    simp only [safeMultiplier, safeSignMultiplier, if_neg notDouble, if_neg notTriple]
    exact realRowOf_lift _ _ _ _ (clampOffsets_ne_zero tail digit) notDouble notTriple

/-- A zero digit's multiple is the identity. -/
theorem zeroMultiple (scalar : NonZeroScalar) (point : Point) (digit : Fin 91) (z : zeros scalar digit = true) :
    multiplesOf scalar point digit = 0 := by
  have hz : (digitsOf scalar).get digit = .zero := of_decide_eq_true z
  unfold multiplesOf
  rw [hz]
  exact Module.zero_smul point

/-- **The normalized kernel is within `455 / #Point` of the simulator's** at a valid input and its output. -/
theorem normRows_etvDist_le (scalar : NonZeroScalar) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    @PMF.etvDist (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))
        (normRealRows scalar input (scalar.value • point)) (simulatedRows input (scalar.value • point))
      ≤ 455 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  have inputOnCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  have xNe := Security.Phase3.onCurve_x_ne_zero input inputOnCurve
  set multiples := multiplesOf scalar point
  have hits := horner_multiplesOf scalar point
  rw [normRealRows_law scalar input point decoded, simulatedRows_law]
  set tails := PMF.uniformOfFintype GoodTails
  set rhos := PMF.uniformOfFintype (Fin 91 → NonZeroBase × NonZeroBase)
  refine le_trans (PMF.etvDist_triangle _
    ((productPMF tails rhos).map fun sample => some (liftedNormOf multiples (zeros scalar) input.x sample)) _) ?_
  have doubling : ((productPMF tails rhos).map
        fun sample => some (normRealRowsOf multiples (zeros scalar) input.x sample)).etvDist
      ((productPMF tails rhos).map fun sample => some (liftedNormOf multiples (zeros scalar) input.x sample))
      ≤ 273 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    simp only [productPMF, PMF.map_bind, PMF.map_comp]
    refine le_trans (etvDist_bind_le_differ _ _ _) ?_
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (doubling_mass_le multiples _ hits)
    intro tail member
    by_contra noDouble
    apply member.1
    congr 1
    funext rho
    simp only [Function.comp_apply]
    rw [normRealRowsOf_eq_lifted multiples (zeros scalar) input.x (zeroMultiple scalar point) tail
      (fun digit same => noDouble ⟨digit, same⟩) rho]
  have lifted : ((productPMF tails rhos).map
        fun sample => some (liftedNormOf multiples (zeros scalar) input.x sample))
      = ((tails.map fun tail => realPoints radixMap multiples tail.1).bind fun points =>
          rhos.map fun rho => some fun digit =>
            lift (points digit) (rho digit).1.value (rho digit).2.value) := by
    simp only [productPMF, PMF.map_bind, PMF.map_comp, PMF.bind_map]
    congr 1
    funext tail
    have law := lifts_law' (realPoints radixMap multiples tail.1)
      (safeMultiplier multiples tail.1) (normSignMultiplier multiples (zeros scalar) input.x tail.1)
      (safeMultiplier_ne_zero multiples tail.1) (normSignMultiplier_ne_zero multiples (zeros scalar) input.x xNe tail.1)
    have mapped := congrArg (PMF.map some) law
    simp only [PMF.map_comp] at mapped
    exact mapped
  have simulated : ((productPMF tails rhos).map fun sample => some (simRowsOf (scalar.value • point)
        sample))
      = ((tails.map fun tail => clampPoints radixMap (scalar.value • point) tail.1).bind
          fun points => rhos.map fun rho => some fun digit =>
            lift (points digit) (rho digit).1.value (rho digit).2.value) := by
    simp only [productPMF, PMF.map_bind, PMF.map_comp, PMF.bind_map]
    rfl
  have kernel : ((productPMF tails rhos).map
        fun sample => some (liftedNormOf multiples (zeros scalar) input.x sample)).etvDist
      ((productPMF tails rhos).map fun sample => some (simRowsOf (scalar.value • point) sample))
      ≤ 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [lifted, simulated]
    exact le_trans (PMF.etvDist_bind_right_le _ _ _) (points_etvDist_le multiples _ hits)
  calc _ ≤ 273 * (Fintype.card Point : ℝ≥0∞)⁻¹ + 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ :=
        add_le_add doubling kernel
    _ = 455 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by rw [← add_mul]; norm_num

/-! ### 4. The doubling flag of the normalized kernel -/

/-- A flagged normalized row (`z = 0` or `y = 0`) is at a nonzero digit with an exceptional digit point. -/
theorem normDoubling_points (multiples : Fin 91 → Point) (zero : Fin 91 → Bool) (x : BaseField) (xNe : x ≠ 0)
    (sample : GoodTails × (Fin 91 → NonZeroBase × NonZeroBase))
    (flag : ∃ d, (normRealRowsOf multiples zero x sample d).z = 0 ∨ (normRealRowsOf multiples zero x sample d).y = 0) :
    ∃ digit, Exceptional (multiples digit) (realPoints radixMap multiples sample.1.1 digit) ∨
      realPoints radixMap multiples sample.1.1 digit = 0 := by
  obtain ⟨digit, zeroRow⟩ := flag
  unfold normRealRowsOf normRealRowOf at zeroRow
  by_cases z : zero digit = true
  · exfalso
    simp only [z, if_true] at zeroRow
    have kNe := clampOffsets_ne_zero sample.1 digit
    have signNe : (sample.2 digit).2.value * x ≠ 0 := mul_ne_zero (sample.2 digit).2.nonzero xNe
    generalize clampOffsets radixMap sample.1.1 digit = K at kNe zeroRow
    cases K with
    | zero => exact kNe rfl
    | some kx ky kValid =>
      rcases zeroRow with zz | yy
      · exact (sample.2 digit).1.nonzero zz
      · exact Security.Phase3.lift_not_triple _ _ signNe ⟨yy, (sample.2 digit).1.nonzero⟩
  · simp only [z, if_false, Bool.false_eq_true] at zeroRow
    refine ⟨digit, ?_⟩
    rcases Flags.RowsDoubling.realRowOf_exceptional (sample.2 digit).1.nonzero (sample.2 digit).2.nonzero
        (clampOffsets_ne_zero sample.1 digit) zeroRow with same | sum | triple
    · left; left
      show multiples digit + clampOffsets radixMap sample.1.1 digit = _
      rw [← same]
    · right
      exact sum
    · left; right
      show multiples digit + clampOffsets radixMap sample.1.1 digit = _
      rw [triple]
      set K := clampOffsets radixMap sample.1.1 digit
      exact (threeHalves_double K).symm

end

end Kriterion.CRT.Privacy.NormRows
