/-
C7: perfect correctness of the configuration-E entry (`Construction/CRT/Entry.lean`), for every
hash, coins and input.

* Off the curve the evaluator refuses before any query (`some none`), which is
  `checkedScalarMultiplication` there.
* On the curve: the replay delivers `slope_e · v + O_e` for every encoding
  (`EntryDelivery.published_delivery`, from `coord_delivery` on the real table);
  the curve encodings give `t' = t` (release-r1's `CurveMembership.evaluateEncodedOnCurve`), so the
  key and the masks are the garbler's; the row values are then release-r1's delivered element values
  (part B), the rows evaluate to `evaluateRows` (`FieldMacToECMac.evaluateHomogeneousEncoded`), the
  digest unlocks every exceptional digit (part C, `DigestUnlock`), and release-r1's decode chain
  gives the scalar multiple (part D, `EntryDecode.decodeResult_eq`).
-/

import Proof.Correctness.CRT.EntryDelivery
import Proof.Correctness.CRT.EntryDecode
import Proof.Correctness.CRT.DigestUnlock
import Proof.Correctness.Base7Termination

namespace Kriterion.CRT.EntryCorrect

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
open Kriterion.CRT Kriterion.CRT.Entry Kriterion.CRT.EntryDelivery

/-! ### The garbler's intermediate values at a hash -/

section Garbled

variable (H : HashN) (scalar : NonZeroScalar) (coins : Coins)

def gxOf : CoordGarbled table xCount :=
  (coordGarbleM table xCount 0 (clip (coins.inputDelta .x))
    (fun j => clip (atNat (coins.inputZero .x) 0 j))).eval H

def gyOf : CoordGarbled table yCount :=
  (coordGarbleM table yCount 1 (clip (coins.inputDelta .y))
    (fun j => clip (atNat (coins.inputZero .y) 0 j))).eval H

def masksOf : MaskValues digitCount := maskValues H (maskKey H coins.bridgeKey) digitCount

def entriesOf : Fin digitCount → Exception.Entry :=
  digestEntries H coordinateBitCount digitCount (zeroOf coins) (deltaOf coins)
    (fun o => ((outputKeysOf scalar coins).get o).digit)
    (fun o => ((outputKeysOf scalar coins).get o).offset.coordinates)
    (fun o => coins.exceptionPad.get o)

def offXOf : Fin xCount → BaseField := offsetsX (gxOf H coins).offset (masksOf H coins)
def offYOf : Fin yCount → BaseField := offsetsY (gyOf H coins).offset (masksOf H coins)
def KOf : FieldMacToECMac.DigitValues := digitValuesOf (offXOf H coins) (offYOf H coins)
def curveKOf : CurveMembership.Values := curveValuesOf (offXOf H coins) (offYOf H coins)
def rowsOf : FieldMacToECMac.Rows :=
  FieldMacToECMac.rowsForOutputKeys (outputKeysOf scalar coins) coins.pointRandomness
def pointOf : Fin digitCount → Biquadratic.Values :=
  pointSlopes (rowsOf scalar coins) coins.pointRandomness (KOf H coins)
def curveSlopesOf : CurveMembership.Values :=
  CurveMembership.slopes coins.curveR1 coins.curveR2 (curveKOf H coins)
def slXOf : Fin xCount → BaseField := slopesX (pointOf H scalar coins) (curveSlopesOf H coins)
def slYOf : Fin yCount → BaseField := slopesY (pointOf H scalar coins) (curveSlopesOf H coins)

/-- The published value of the garbling. -/
def pubOf : Entry.Public :=
  assemble scalar coins (gxOf H coins) (gyOf H coins) (masksOf H coins) (entriesOf H scalar coins)

theorem garbleCM_eval : (garbleCM scalar coins).eval H = (pubOf H scalar coins, coins.inputMacKey) := by
  simp only [garbleCM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_keyM, eval_maskAnswersM,
    eval_digestGarbleM]
  rfl

theorem pubOf_crtX : (pubOf H scalar coins).crtX = convVector (gxOf H coins).pub := rfl

theorem pubOf_curve : (pubOf H scalar coins).curve =
    CurveMembership.garble coins.bridgeKey coins.curveMask.value coins.curveR1 coins.curveR2
      (curveKOf H coins) := rfl

theorem pubOf_rows : (pubOf H scalar coins).rows = Vector.ofFn fun digit =>
    FieldMacToECMac.garbleRow ((rowsOf scalar coins).get digit) (KOf H coins digit) := rfl

theorem pubOf_exception : (pubOf H scalar coins).exception = Vector.ofFn (entriesOf H scalar coins) := rfl

theorem pubOf_crtY : (pubOf H scalar coins).crtY = convVector (gyOf H coins).pub := rfl

theorem pubOf_recX (e : Fin xCount) :
    ((pubOf H scalar coins).recX.get e).val =
      (gxOf H coins).records (fun e => (slXOf H scalar coins e).val) e := by
  dsimp only [pubOf, assemble]
  rw [vector_get_ofFn]
  exact toRecord_val _ (records_small _ _ e)

theorem pubOf_recY (e : Fin yCount) :
    ((pubOf H scalar coins).recY.get e).val =
      (gyOf H coins).records (fun e => (slYOf H scalar coins e).val) e := by
  dsimp only [pubOf, assemble]
  rw [vector_get_ofFn]
  exact toRecord_val _ (records_small _ _ e)

end Garbled

/-- The evaluator's Lamport blocks for an input. -/
def labelsFor (coins : Coins) (input : AffineInput) : GarbledCircuit.LamportSignature :=
  Lamport.selectedLabels (coins.inputMacKey.encode (BitInput.ofAffine input))

/-! ### Part A: the replay delivers -/

theorem val_mul_val_lt (a x : BaseField) : a.val * x.val < table.wrapBound := by
  show a.val * x.val < wrapBound baseFieldModulus
  unfold wrapBound
  have ha : a.val ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt a)
  have hx : x.val ≤ baseFieldModulus - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt x)
  have := Nat.mul_le_mul ha hx
  rw [sq]
  omega

theorem val_lt_two_pow (x : BaseField) : x.val < 2 ^ 254 :=
  lt_trans (ZMod.val_lt x) (by unfold baseFieldModulus; norm_num)

theorem toField_delivery (a x : BaseField) (offset : Nat) :
    toField (a.val * x.val + offset) = a * x + toField offset := by
  simp [toField]

theorem deliveredX_eq (H : HashN) (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput)
    (e : Fin xCount) :
    ((replayConv (pubOf H scalar coins) input (labelsFor coins input)).eval H).deliveredX e =
      slXOf H scalar coins e * input.x + toField ((gxOf H coins).offset e) := by
  have delivery := published_delivery H xCount 0 (clip (coins.inputDelta .x))
    (fun j => clip (atNat (coins.inputZero .x) 0 j))
    (fun e => (slXOf H scalar coins e).val) input.x.val (val_lt_two_pow _)
    (fun e => val_mul_val_lt _ _) (fun j => clip (labelX (labelsFor coins input) j))
    (fun j low => clip_labelX_honest _ _ _ (coins_key_x coins) input j low)
    (fun e => ((pubOf H scalar coins).recX.get e).val) (pubOf_recX H scalar coins) e
  rw [← toField_delivery, gxOf, ← delivery]
  simp only [replayConv, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [pubOf_crtX, gxOf]

theorem deliveredY_eq (H : HashN) (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput)
    (e : Fin yCount) :
    ((replayConv (pubOf H scalar coins) input (labelsFor coins input)).eval H).deliveredY e =
      slYOf H scalar coins e * input.y + toField ((gyOf H coins).offset e) := by
  have delivery := published_delivery H yCount 1 (clip (coins.inputDelta .y))
    (fun j => clip (atNat (coins.inputZero .y) 0 j))
    (fun e => (slYOf H scalar coins e).val) input.y.val (val_lt_two_pow _)
    (fun e => val_mul_val_lt _ _) (fun j => clip (labelY (labelsFor coins input) j))
    (fun j low => clip_labelY_honest _ _ _ (coins_key_y coins) input j low)
    (fun e => ((pubOf H scalar coins).recY.get e).val) (pubOf_recY H scalar coins) e
  rw [← toField_delivery, gyOf, ← delivery]
  simp only [replayConv, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [pubOf_crtY, gyOf]

/-! ### Index facts -/

theorem maskOf_x_curve (m : MaskValues digitCount) (e : Nat) (large : pointElementCountX ≤ e) :
    maskOf m 0 e = 0 := by
  unfold maskOf
  simp only [pointElementCountX, digitCount] at large
  simp only [↓reduceIte, show ¬ e < 4 * digitCount by simp only [digitCount]; omega]

theorem maskOf_y_curve (m : MaskValues digitCount) (e : Nat) (large : pointElementCountY ≤ e) :
    maskOf m 1 e = 0 := by
  unfold maskOf
  simp only [pointElementCountY, digitCount] at large
  simp only [one_ne_zero, ↓reduceIte, show ¬ e < 3 * digitCount by simp only [digitCount]; omega]

theorem joinX_curve (point : Fin pointElementCountX → BaseField) (curve : Fin curveElementCountX → BaseField)
    (k : Fin curveElementCountX) (bound : pointElementCountX + k.val < xCount) :
    joinX point curve ⟨pointElementCountX + k.val, bound⟩ = curve k := by
  unfold joinX
  have notLow : ¬ (pointElementCountX + k.val < pointElementCountX) := by omega
  rw [dif_neg notLow]
  exact congrArg curve (Fin.ext (by show pointElementCountX + k.val - pointElementCountX = k.val; omega))

theorem joinY_curve (point : Fin pointElementCountY → BaseField) (curve : Fin curveElementCountY → BaseField)
    (k : Fin curveElementCountY) (bound : pointElementCountY + k.val < yCount) :
    joinY point curve ⟨pointElementCountY + k.val, bound⟩ = curve k := by
  unfold joinY
  have notLow : ¬ (pointElementCountY + k.val < pointElementCountY) := by omega
  rw [dif_neg notLow]
  exact congrArg curve (Fin.ext (by show pointElementCountY + k.val - pointElementCountY = k.val; omega))

theorem curvePartX_slopesX (point : Fin digitCount → Biquadratic.Values) (curve : CurveMembership.Values)
    (element : CurveXElement) :
    curvePartX (slopesX point curve) (curveXElementIndex element) = curve (.inl element) := by
  unfold curvePartX slopesX
  rw [joinX_curve]
  exact Pipeline.curveXAssemble_slot curve element

theorem curvePartY_slopesY (point : Fin digitCount → Biquadratic.Values) (curve : CurveMembership.Values)
    (element : CurveYElement) :
    curvePartY (slopesY point curve) (curveYElementIndex element) = curve (.inr element) := by
  unfold curvePartY slopesY
  rw [joinY_curve]
  exact Pipeline.curveYAssemble_slot curve element

theorem pointPartX_slopesX (point : Fin digitCount → Biquadratic.Values) (curve : CurveMembership.Values)
    (digit : Fin digitCount) (element : XElement) :
    pointPartX (slopesX point curve) (xElementIndex digit element) = point digit (.inl element) := by
  unfold pointPartX slopesX joinX
  rw [dif_pos (xElementIndex digit element).isLt]
  exact Pipeline.pointXAssemble_digit point digit element

theorem pointPartY_slopesY (point : Fin digitCount → Biquadratic.Values) (curve : CurveMembership.Values)
    (digit : Fin digitCount) (element : YElement) :
    pointPartY (slopesY point curve) (yElementIndex digit element) = point digit (.inr element) := by
  unfold pointPartY slopesY joinY
  rw [dif_pos (yElementIndex digit element).isLt]
  exact Pipeline.pointYAssemble_digit point digit element

/-! ### The curve check releases `t` -/

theorem curveValues_delivered (H : HashN) (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput)
    (dX : Fin xCount → BaseField) (dY : Fin yCount → BaseField)
    (hX : ∀ e, dX e = slXOf H scalar coins e * input.x + toField ((gxOf H coins).offset e))
    (hY : ∀ e, dY e = slYOf H scalar coins e * input.y + toField ((gyOf H coins).offset e)) :
    curveValuesOf dX dY =
      CurveMembership.delivered coins.curveR1 coins.curveR2 (curveKOf H coins) input := by
  funext element
  cases element with
  | inl element =>
      have slope := curvePartX_slopesX (pointOf H scalar coins) (curveSlopesOf H coins) element
      simp only [curveValuesOf, Pipeline.curveValues, curvePartX, CurveMembership.delivered,
        CurveMembership.coordValue, curveKOf, hX, offXOf, offsetsX] at slope ⊢
      rw [maskOf_x_curve _ _ (by simp), sub_zero]
      unfold slXOf
      rw [slope]
      rfl
  | inr element =>
      have slope := curvePartY_slopesY (pointOf H scalar coins) (curveSlopesOf H coins) element
      simp only [curveValuesOf, Pipeline.curveValues, curvePartY, CurveMembership.delivered,
        CurveMembership.coordValue, curveKOf, hY, offYOf, offsetsY] at slope ⊢
      rw [maskOf_y_curve _ _ (by simp), sub_zero]
      unfold slYOf
      rw [slope]
      rfl

/-! ### Part B: the row values are release-r1's delivered element values -/

theorem rowValues_delivered (H : HashN) (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput)
    (out : ReplayOut)
    (hX : ∀ e, out.deliveredX e = slXOf H scalar coins e * input.x + toField ((gxOf H coins).offset e))
    (hY : ∀ e, out.deliveredY e = slYOf H scalar coins e * input.y + toField ((gyOf H coins).offset e))
    (hmasks : out.masks = maskFunction (masksOf H coins)) :
    rowValues out =
      FieldMacToECMac.delivered (rowsOf scalar coins) coins.pointRandomness (KOf H coins) input := by
  funext digit element
  cases element with
  | inl element =>
      have slope := pointPartX_slopesX (pointOf H scalar coins) (curveSlopesOf H coins) digit element
      simp only [rowValues, digitValuesOf, Pipeline.digitValues, pointPartX, maskX, hX, hmasks,
        maskFunction, dif_pos (show (xElementIndex digit element).val < pointElementCountX from
          (xElementIndex digit element).isLt), FieldMacToECMac.delivered, Biquadratic.delivered,
        Biquadratic.coordValue, KOf, offXOf, offsetsX] at slope ⊢
      unfold slXOf
      rw [slope]
      simp only [pointOf, pointSlopes, KOf, digitValuesOf, offXOf, offYOf]
      ring
  | inr element =>
      have slope := pointPartY_slopesY (pointOf H scalar coins) (curveSlopesOf H coins) digit element
      simp only [rowValues, digitValuesOf, Pipeline.digitValues, pointPartY, maskY, hY, hmasks,
        maskFunction, dif_pos (show (yElementIndex digit element).val < pointElementCountY from
          (yElementIndex digit element).isLt), FieldMacToECMac.delivered, Biquadratic.delivered,
        Biquadratic.coordValue, KOf, offYOf, offsetsY] at slope ⊢
      unfold slYOf
      rw [slope]
      simp only [pointOf, pointSlopes, KOf, digitValuesOf, offXOf, offYOf]
      ring

/-! ### The key and the masks are the garbler's -/

theorem replay_eval (H : HashN) (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    (replay pub input labels).eval H =
      { deliveredX := ((replayConv pub input labels).eval H).deliveredX
        deliveredY := ((replayConv pub input labels).eval H).deliveredY
        key := maskKey H (curveOutput pub input ((replayConv pub input labels).eval H))
        masks := maskFunction (maskValues H
          (maskKey H (curveOutput pub input ((replayConv pub input labels).eval H))) digitCount) } := by
  simp only [replay, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_keyM, eval_maskAnswersM]

theorem replay_eval_deliveredX (H : HashN) (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    ((replay pub input labels).eval H).deliveredX = ((replayConv pub input labels).eval H).deliveredX := by
  rw [replay_eval]

theorem replay_eval_deliveredY (H : HashN) (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    ((replay pub input labels).eval H).deliveredY = ((replayConv pub input labels).eval H).deliveredY := by
  rw [replay_eval]

theorem replay_eval_masks (H : HashN) (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    ((replay pub input labels).eval H).masks = maskFunction (maskValues H
      (maskKey H (curveOutput pub input ((replayConv pub input labels).eval H))) digitCount) := by
  rw [replay_eval]

theorem curveOutput_eq (H : HashN) (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput)
    (onCurve : OnCurve input) :
    curveOutput (pubOf H scalar coins) input
        ((replayConv (pubOf H scalar coins) input (labelsFor coins input)).eval H) = coins.bridgeKey := by
  unfold curveOutput
  rw [curveValues_delivered H scalar coins input _ _ (deliveredX_eq H scalar coins input)
    (deliveredY_eq H scalar coins input), pubOf_curve]
  exact CurveMembership.evaluateEncodedOnCurve _ _ _ _ _ _ onCurve

/-! ### The digest's labels are honest -/

theorem labelsOf_honest (coins : Coins) (input : AffineInput) :
    DigestUnlock.Honest (zeroOf coins) (deltaOf coins) (labelsOf (labelsFor coins input)) input := by
  intro coord position
  have low : position.val < 254 := position.isLt
  fin_cases coord
  · simp only [labelsOf, zeroOf, deltaOf, coordBit, coordNat, labelsFor, Fin.zero_eta, Fin.isValue,
      ↓reduceIte]
    rw [labelX_honest _ _ _ (coins_key_x coins) input position.val low]
    simp only [atNat, dif_pos (show position.val < coordinateBitCount from low)]
    split <;> simp_all
  · simp only [labelsOf, zeroOf, deltaOf, coordBit, coordNat, labelsFor, Fin.mk_one, Fin.isValue,
      one_ne_zero, ↓reduceIte]
    rw [labelY_honest _ _ _ (coins_key_y coins) input position.val low]
    simp only [atNat, dif_pos (show position.val < coordinateBitCount from low)]
    split <;> simp_all

/-! ### Correctness -/

/-- **On the curve the evaluator returns the scalar multiple.** -/
theorem evaluate_onCurve [FieldCertificate] [GroupCertificate] (H : HashN) (scalar : NonZeroScalar)
    (coins : Coins) (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    (evaluateCM (pubOf H scalar coins) input (labelsFor coins input)).eval H =
      some (some (scalarMultiplication scalar.value point)) := by
  have onCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  rw [eval_evaluateCM_of_decode H _ input _ point decoded]
  refine congrArg some ?_
  simp only [reachCM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_digestEvalM, resultOf]
  set out := (replay (pubOf H scalar coins) input (labelsFor coins input)).eval H with hout
  have hX : ∀ e, out.deliveredX e =
      slXOf H scalar coins e * input.x + toField ((gxOf H coins).offset e) := by
    intro e
    rw [hout, replay_eval_deliveredX]
    exact deliveredX_eq H scalar coins input e
  have hY : ∀ e, out.deliveredY e =
      slYOf H scalar coins e * input.y + toField ((gyOf H coins).offset e) := by
    intro e
    rw [hout, replay_eval_deliveredY]
    exact deliveredY_eq H scalar coins input e
  have hmasks : out.masks = maskFunction (masksOf H coins) := by
    rw [hout, replay_eval_masks, curveOutput_eq H scalar coins input onCurve]
    rfl
  have homog : FieldMacToECMac.evaluateHomogeneous ((pubOf H scalar coins).rows,
      (pubOf H scalar coins).exception) (rowValues out) input =
      FieldMacToECMac.evaluateRows (rowsOf scalar coins) input := by
    rw [rowValues_delivered H scalar coins input out hX hY hmasks]
    rw [← FieldMacToECMac.evaluateHomogeneousEncoded (outputKeysOf scalar coins) (rowsOf scalar coins)
      coins.pointRandomness (KOf H coins) coins.inputMacKey (fun _ _ _ => Equiv.refl _)
      coins.exceptionPad input onCurve (FieldMacToECMac.rowsForOutputKeysSparse _ _)]
    simp only [FieldMacToECMac.evaluateHomogeneous, FieldMacToECMac.garble, pubOf_rows]
  rw [homog]
  refine EntryDecode.decodeResult_eq scalar.value coins.offsets coins.offsetsClamped coins.pointRandomness
    input point decoded _ ?_
  intro index
  refine ⟨fun zZero xZero => ?_, fun zNe sZero => ?_⟩
  · obtain ⟨phi, selected, exceptional⟩ := EntryDecode.zeroRow_exceptional (outputKeysOf scalar coins)
      coins.pointRandomness input index onCurve ((outputKeysOf scalar coins).get index).offset.onCurve
      zZero xZero
    rw [pubOf_exception]
    simp only [vector_get_ofFn]
    exact DigestUnlock.digestUnlock_exceptional H coordinateBitCount digitCount (zeroOf coins)
      (deltaOf coins) (fun o => ((outputKeysOf scalar coins).get o).digit)
      (fun o => ((outputKeysOf scalar coins).get o).offset.coordinates)
      (fun o => coins.exceptionPad.get o) _ input (labelsOf_honest coins input) index phi selected
      exceptional
  · obtain ⟨phi, selected, triple⟩ := EntryDecode.signZero_triple (outputKeysOf scalar coins)
      coins.pointRandomness input index onCurve ((outputKeysOf scalar coins).get index).offset.onCurve
      zNe sZero
    rw [pubOf_exception]
    simp only [vector_get_ofFn]
    exact DigestUnlock.digestUnlock_triple H coordinateBitCount digitCount (zeroOf coins)
      (deltaOf coins) (fun o => ((outputKeysOf scalar coins).get o).digit)
      (fun o => ((outputKeysOf scalar coins).get o).offset.coordinates)
      (fun o => coins.exceptionPad.get o) _ input (labelsOf_honest coins input) index phi selected
      triple

/-- **Perfect correctness at every hash, coins and input.** -/
theorem entry_correct [FieldCertificate] [GroupCertificate] (H : HashN) (scalar : NonZeroScalar)
    (coins : Coins) (input : AffineInput) :
    (evaluateCM (pubOf H scalar coins) input (labelsFor coins input)).eval H =
      some (checkedScalarMultiplication scalar.value input) := by
  cases decoded : decodePoint input with
  | none =>
      unfold evaluateCM
      simp [decoded, checkedScalarMultiplication]
  | some point =>
      rw [evaluate_onCurve H scalar coins input point decoded]
      simp [checkedScalarMultiplication, decoded]

/-- **The configuration-E scheme is perfectly correct** (`Solution.perfectCorrectness`). -/
theorem perfectCorrectness (field : FieldCertificate) (group : @GroupCertificate field) :
    GarbledCircuit.PerfectCorrectness (@Entry.scheme field group) Prod.snd := by
  letI := field
  letI := group
  intro parameter scalar tape input
  simp only [Entry.scheme]
  rw [garbleCM_eval]
  exact entry_correct (schemeHash tape.2) scalar tape.1 input

end Kriterion.CRT.EntryCorrect
