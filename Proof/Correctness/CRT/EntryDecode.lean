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

/-- A vanishing row pins the input to the digit's exceptional input (release-r1's
`exceptionDigitCorrect`, without its last step, which reads the permutation gadget). -/
theorem zeroRow_exceptional [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (index : Fin FieldMacToECMac.outputMacCount)
    (inputOnCurve : OnCurve input)
    (offsetOnCurve : OnCurve (keys.get index).offset.coordinates)
    (zeroRow : FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input = ⟨0, 0, 0⟩) :
    ∃ phi, digitEndomorphismBase (keys.get index).digit = some phi ∧
      input = Exception.exceptionalInput phi (keys.get index).offset.coordinates := by
  have rhoNe : (randomness.get index).rho.value ≠ 0 := (randomness.get index).rho.nonzero
  have rowEq : (FieldMacToECMac.rowsForOutputKeys keys randomness).get index =
      Coordinates.rows (keys.get index).offset.coordinates
        (digitEndomorphismBase (keys.get index).digit) (randomness.get index).rho.value := by
    simp [FieldMacToECMac.rowsForOutputKeys]
  rw [rowEq] at zeroRow
  cases selected : digitEndomorphismBase (keys.get index).digit with
  | none =>
      rw [selected, FieldMacToECMac.evaluateRowsNone] at zeroRow
      have zZero : (randomness.get index).rho.value = 0 :=
        congrArg FieldMacToECMac.HomogeneousValue.z zeroRow
      exact absurd zZero rhoNe
  | some phi =>
      rw [selected, FieldMacToECMac.evaluateRowsSome] at zeroRow
      have phiSix : phi ^ 6 = 1 := digitEndomorphismBasePowSix _ phi selected
      have tOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input) := by
        simpa [FieldMacToECMac.transformedInput] using
          Coordinates.transformedOnCurve phi phiSix input inputOnCurve
      have zZero : (randomness.get index).rho.value *
          Coordinates.evaluate (Coordinates.zCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 :=
        congrArg FieldMacToECMac.HomogeneousValue.z zeroRow
      have sameX : (FieldMacToECMac.transformedInput phi input).x =
          (keys.get index).offset.coordinates.x := by
        rw [Coordinates.evaluateZ] at zZero
        exact sub_eq_zero.mp ((mul_eq_zero.mp zZero).resolve_left rhoNe)
      have xZero : (randomness.get index).rho.value ^ 2 *
          Coordinates.evaluate (Coordinates.xCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 :=
        congrArg FieldMacToECMac.HomogeneousValue.x zeroRow
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

/-- The unlock property of a gadget: a vanishing row unlocks its digit. -/
def Unlocks (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (digits : Fin FieldMacToECMac.outputMacCount → Digit) : Prop :=
  ∀ index, FieldMacToECMac.evaluateRow
      ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input = ⟨0, 0, 0⟩ →
    digits index = (keys.get index).digit

/-- All 91 rows decode together, for any gadget with the unlock property. -/
theorem decodeRows [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (inputOnCurve : OnCurve input)
    (digits : Fin FieldMacToECMac.outputMacCount → Digit) (unlocks : Unlocks keys randomness input digits) :
    Garbling.decodePointMacs (FieldMacToECMac.evaluateRows (FieldMacToECMac.rowsForOutputKeys keys randomness) input)
        (Vector.ofFn digits) (affinePoint input inputOnCurve) =
      some ((Vector.ofFn fun index =>
        digitScalar (keys.get index).digit • affinePoint input inputOnCurve +
          (keys.get index).offset.point).toList) := by
  simp only [Garbling.decodePointMacs, FieldMacToECMac.evaluateRows, Vector.toList_ofFn]
  apply optionMapMOfFnZip
  intro index
  have rowEq : (FieldMacToECMac.rowsForOutputKeys keys randomness).get index =
      Coordinates.rows (keys.get index).offset.coordinates
        (digitEndomorphismBase (keys.get index).digit) (randomness.get index).rho.value := by
    simp [FieldMacToECMac.rowsForOutputKeys]
  show Garbling.decodeHomogeneous
      (FieldMacToECMac.evaluateRow ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input)
      (digits index) (affinePoint input inputOnCurve) = _
  rw [rowEq]
  exact decodeEvaluateOutputKeyRow (keys.get index) (randomness.get index).rho input inputOnCurve _
    fun zero => unlocks index (by rw [rowEq]; exact zero)

/-- **The decode chain**: with the rows evaluated at the input and digits from a gadget with the
unlock property, the result decodes to the scalar multiple of the input point. -/
theorem decodeResult_eq [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (offsets : FieldMacToECMac.SuccessfulOffsets) (clamped : offsets.IsClamped)
    (randomness : FieldMacToECMac.Randomness) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point)
    (digits : Fin FieldMacToECMac.outputMacCount → Digit)
    (unlocks : Unlocks (FieldMacToECMac.outputKeys construction scalar offsets) randomness input digits) :
    Garbling.decodeResult
        { point := input
          pointMacs := FieldMacToECMac.evaluateRows
            (FieldMacToECMac.rowsForOutputKeys (FieldMacToECMac.outputKeys construction scalar offsets)
              randomness) input
          exceptionDigits := Vector.ofFn digits } =
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
