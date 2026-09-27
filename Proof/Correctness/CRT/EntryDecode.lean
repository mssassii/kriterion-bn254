/-
C7 part D: release-r1's decode chain (`Proof/Correctness/JacobianMixed.lean`) for a result whose
exception digits come from any gadget with the unlock property "a vanishing row unlocks its
digit". In release-r1 the digits come from the permutation gadget (`expectedResult`); in
configuration E they come from the per-label hash digest (`Construction/CRT/Digest.lean`). The row
algebra, the zero-row analysis and the Horner reconstruction are release-r1's, reused through its
public lemmas; the private helpers are restated here.
-/

import Proof.Correctness.JacobianMixed

namespace Kriterion.CRT.EntryDecode

open Kriterion Kriterion.BN254 Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.JacobianMixed

private theorem twoNe : (2 : BaseField) ≠ 0 := by decide

/-- A row with `Z = 0 = X` pins the input to the digit's doubling input (release-r1's
`exceptionDigitCorrect`, without its last step, which reads the permutation gadget). -/
theorem zeroRow_exceptional [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (index : Fin FieldMacToECMac.outputMacCount)
    (inputOnCurve : OnCurve input)
    (offsetOnCurve : OnCurve (keys.get index).offset.coordinates)
    (zZeroRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).z = 0)
    (xZeroRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).x = 0) :
    ∃ phi, digitEndomorphismBase (keys.get index).digit = some phi ∧
      input = Exception.exceptionalInput phi (keys.get index).offset.coordinates := by
  have rhoNe : (randomness.get index).rho.value ≠ 0 := (randomness.get index).rho.nonzero
  rw [rowsForOutputKeys_get] at zZeroRow xZeroRow
  cases selected : digitEndomorphismBase (keys.get index).digit with
  | none =>
      rw [selected, FieldMacToECMac.evaluateRowsNone] at zZeroRow
      exact absurd zZeroRow rhoNe
  | some phi =>
      rw [selected, FieldMacToECMac.evaluateRowsSome] at zZeroRow xZeroRow
      have phiSix : phi ^ 6 = 1 := digitEndomorphismBasePowSix _ phi selected
      have tOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input) := by
        simpa [FieldMacToECMac.transformedInput] using
          Coordinates.transformedOnCurve phi phiSix input inputOnCurve
      have zZero : (randomness.get index).rho.value *
          Coordinates.evaluate (Coordinates.zCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 := zZeroRow
      have sameX : (FieldMacToECMac.transformedInput phi input).x =
          (keys.get index).offset.coordinates.x := by
        rw [Coordinates.evaluateZ] at zZero
        exact sub_eq_zero.mp ((mul_eq_zero.mp zZero).resolve_left rhoNe)
      have xZero : (randomness.get index).rho.value ^ 2 *
          Coordinates.evaluate (Coordinates.xCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 := xZeroRow
      rw [Coordinates.exceptionalX _ _ offsetOnCurve tOnCurve sameX] at xZero
      have kyNe : (keys.get index).offset.coordinates.y ≠ 0 := noAffineYZero _ offsetOnCurve
      have sameY : (FieldMacToECMac.transformedInput phi input).y =
          (keys.get index).offset.coordinates.y :=
        (sub_eq_zero.mp
          ((mul_eq_zero.mp ((mul_eq_zero.mp xZero).resolve_left
            (pow_ne_zero 2 rhoNe))).resolve_left (mul_ne_zero twoNe kyNe))).symm
      have xValue : input.x = phi ^ 2 * (keys.get index).offset.coordinates.x := by
        have base : phi ^ 4 * input.x = (keys.get index).offset.coordinates.x := sameX
        calc input.x = phi ^ 6 * input.x := by rw [phiSix, one_mul]
          _ = phi ^ 2 * (phi ^ 4 * input.x) := by ring
          _ = phi ^ 2 * (keys.get index).offset.coordinates.x := by rw [base]
      have yValue : input.y = phi ^ 3 * (keys.get index).offset.coordinates.y := by
        have base : phi ^ 3 * input.y = (keys.get index).offset.coordinates.y := sameY
        calc input.y = phi ^ 6 * input.y := by rw [phiSix, one_mul]
          _ = phi ^ 3 * (phi ^ 3 * input.y) := by ring
          _ = phi ^ 3 * (keys.get index).offset.coordinates.y := by rw [base]
      refine ⟨phi, rfl, ?_⟩
      obtain ⟨inputX, inputY⟩ := input
      simp only [Exception.exceptionalInput, AffineInput.mk.injEq]
      exact ⟨xValue, yValue⟩

/-- A row with `S = 0 ≠ Z` pins the input to the digit's second exceptional input `φ⁻¹(2K)`
(release-r1's `tripleDigitCorrect` without its last step). -/
theorem signZero_triple [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (index : Fin FieldMacToECMac.outputMacCount)
    (inputOnCurve : OnCurve input)
    (offsetOnCurve : OnCurve (keys.get index).offset.coordinates)
    (zNeRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).z ≠ 0)
    (sZeroRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).y = 0) :
    ∃ phi, digitEndomorphismBase (keys.get index).digit = some phi ∧
      input = Exception.tripleInput phi (keys.get index).offset.coordinates := by
  have tauNe : (randomness.get index).tau.value ≠ 0 := (randomness.get index).tau.nonzero
  rw [rowsForOutputKeys_get] at zNeRow sZeroRow
  cases selected : digitEndomorphismBase (keys.get index).digit with
  | none =>
      rw [selected, FieldMacToECMac.evaluateRowsNone] at sZeroRow
      exact absurd sZeroRow (mul_ne_zero (pow_ne_zero 2 tauNe) (noAffineYZero _ offsetOnCurve))
  | some phi =>
      rw [selected, FieldMacToECMac.evaluateRowsSome] at zNeRow sZeroRow
      have phiSix : phi ^ 6 = 1 := digitEndomorphismBasePowSix _ phi selected
      have tOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input) := by
        simpa [FieldMacToECMac.transformedInput] using
          Coordinates.transformedOnCurve phi phiSix input inputOnCurve
      have zNe : (randomness.get index).rho.value *
          Coordinates.evaluate (Coordinates.zCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) ≠ 0 := zNeRow
      have xNe : (FieldMacToECMac.transformedInput phi input).x ≠
          (keys.get index).offset.coordinates.x := by
        intro same
        apply zNe
        rw [Coordinates.exceptionalZ _ _ same, mul_zero]
      have sZero : (randomness.get index).tau.value ^ 2 *
          Coordinates.evaluate (Coordinates.signCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 := sZeroRow
      rw [signValue _ _ offsetOnCurve tOnCurve xNe] at sZero
      have sumYNe := noAffineYZero _
        (sumOnCurve_of_X_ne _ _ offsetOnCurve tOnCurve xNe)
      have lineZero : Coordinates.tangentLine (keys.get index).offset.coordinates
          (FieldMacToECMac.transformedInput phi input) = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp ((mul_eq_zero.mp sZero).resolve_left (pow_ne_zero 2 tauNe))).resolve_right
            sumYNe)
      have doubled := tangentZero_double _ _ offsetOnCurve tOnCurve xNe lineZero
      have xValue : input.x = phi ^ 2 * (Exception.doubleOffset
          (keys.get index).offset.coordinates).x := by
        have base : phi ^ 4 * input.x = (Exception.doubleOffset
            (keys.get index).offset.coordinates).x := congrArg AffineInput.x doubled
        calc input.x = phi ^ 6 * input.x := by rw [phiSix, one_mul]
          _ = phi ^ 2 * (phi ^ 4 * input.x) := by ring
          _ = _ := by rw [base]
      have yValue : input.y = phi ^ 3 * (Exception.doubleOffset
          (keys.get index).offset.coordinates).y := by
        have base : phi ^ 3 * input.y = (Exception.doubleOffset
            (keys.get index).offset.coordinates).y := congrArg AffineInput.y doubled
        calc input.y = phi ^ 6 * input.y := by rw [phiSix, one_mul]
          _ = phi ^ 3 * (phi ^ 3 * input.y) := by ring
          _ = _ := by rw [base]
      refine ⟨phi, rfl, ?_⟩
      obtain ⟨inputX, inputY⟩ := input
      simp only [Exception.tripleInput, Exception.exceptionalInput, AffineInput.mk.injEq]
      exact ⟨xValue, yValue⟩

private theorem optionMapMOfFnZip {n : Nat} {α β γ : Type}
    (f : Fin n → α) (g : Fin n → β) (h : Fin n → γ) (decode : α × β → Option γ)
    (decoded : ∀ index, decode (f index, g index) = some (h index)) :
    (List.zip (List.ofFn f) (List.ofFn g)).mapM decode = some (List.ofFn h) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.zip_cons_cons, List.mapM_cons,
        decoded]
      rw [inductionHypothesis (fun index => f index.succ) (fun index => g index.succ)
        (fun index => h index.succ) (fun index => decoded index.succ)]
      rfl

private theorem zipOfFn {n : Nat} {α β : Type} (f : Fin n → α) (g : Fin n → β) :
    List.zip (List.ofFn f) (List.ofFn g) = List.ofFn fun index => (f index, g index) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.zip_cons_cons,
        inductionHypothesis]

/-- The unlock property of a gadget: a row with `Z = 0 = X` unlocks its digit in the first half,
a row with `S = 0 ≠ Z` in the second. -/
def Unlocks (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (digits : Fin FieldMacToECMac.outputMacCount → Digit × Digit) : Prop :=
  ∀ index,
    ((FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).z = 0 →
      (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).x = 0 →
      (digits index).1 = (keys.get index).digit) ∧
    ((FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).z ≠ 0 →
      (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).y = 0 →
      (digits index).2 = (keys.get index).digit)

/-- All 91 rows decode together, for any gadget with the unlock property. -/
theorem decodeRows [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (inputOnCurve : OnCurve input)
    (digits : Fin FieldMacToECMac.outputMacCount → Digit × Digit)
    (unlocks : Unlocks keys randomness input digits) :
    Garbling.decodePointMacs (FieldMacToECMac.evaluateRows (FieldMacToECMac.rowsForOutputKeys keys randomness) input)
        (Vector.ofFn fun index => (digits index).1) (Vector.ofFn fun index => (digits index).2)
        (affinePoint input inputOnCurve) =
      some ((Vector.ofFn fun index =>
        digitScalar (keys.get index).digit • affinePoint input inputOnCurve +
          (keys.get index).offset.point).toList) := by
  simp only [Garbling.decodePointMacs, FieldMacToECMac.evaluateRows, Vector.toList_ofFn]
  rw [zipOfFn]
  apply optionMapMOfFnZip
  intro index
  have rowEq := rowsForOutputKeys_get keys randomness index
  show Garbling.decodeHomogeneous
      (FieldMacToECMac.evaluateRow ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input)
      (digits index).1 (digits index).2 (affinePoint input inputOnCurve) = _
  have first := (unlocks index).1
  have second := (unlocks index).2
  rw [rowEq] at first second ⊢
  exact decodeEvaluateOutputKeyRow (keys.get index) (randomness.get index).rho
    (randomness.get index).tau input inputOnCurve _ _ first second

/-- **The decode chain**: with the rows evaluated at the input and digits from a gadget with the
unlock property, the result decodes to the scalar multiple of the input point. -/
theorem decodeResult_eq [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (offsets : FieldMacToECMac.SuccessfulOffsets) (clamped : offsets.IsClamped)
    (randomness : FieldMacToECMac.Randomness) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point)
    (digits : Fin FieldMacToECMac.outputMacCount → Digit × Digit)
    (unlocks : Unlocks (FieldMacToECMac.outputKeys construction scalar offsets) randomness input digits) :
    Garbling.decodeResult
        { point := input
          pointMacs := FieldMacToECMac.evaluateRows
            (FieldMacToECMac.rowsForOutputKeys (FieldMacToECMac.outputKeys construction scalar offsets)
              randomness) input
          exceptionDigits := Vector.ofFn fun index => (digits index).1
          tripleDigits := Vector.ofFn fun index => (digits index).2 } =
      some (scalarMultiplication scalar point) := by
  have inputOnCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  have pointEq : affinePoint input inputOnCurve = point :=
    affinePoint_eq_of_decode input point decoded inputOnCurve
  unfold Garbling.decodeResult
  simp only [decoded]
  rw [← pointEq, decodeRows _ randomness input inputOnCurve digits unlocks]
  simp only [Option.map_some]
  rw [outputKeyPoints scalar offsets clamped (affinePoint input inputOnCurve)]
  exact congrArg some
    (construction.correct scalar (successfulOffsetRandomness offsets)
      (affinePoint input inputOnCurve))

end Kriterion.CRT.EntryDecode
