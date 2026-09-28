/- Independent Round-6 integration audit: H6/H7 assembly without simulator imports. -/
import Proof.Privacy.CRT.Hidden.CaseConv
import Proof.Privacy.CRT.Hidden.CaseDigest
import Proof.Privacy.CRT.Hidden.StageOneCast
import Proof.Privacy.CRT.Hidden.StageOneKey
import Proof.Privacy.CRT.Hidden.CaseKeyOff
import Proof.Privacy.CRT.Hidden.Reach
import Proof.Privacy.CRT.Flags.CurveWindow
import Proof.Privacy.CRT.Flags.ConvCoincide
import Lean

set_option autoImplicit false

namespace NarrowPrivacyAudit

open Kriterion
open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open scoped ENNReal

theorem digestCase : StageTwo.GuessCase StageTwo.digestOther StageTwo.noExtra
    ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
  StageTwo.digestOther_case_of (DeltaView.deltaGivenView DeltaView.coordRelational DeltaView.tailRel)

theorem stageTwo : CrtStageTwoGuess Instance.crtEntry Entry.table
    (ENNReal.ofReal crtHiddenCharge) (ENNReal.ofReal hiddenWindowError) :=
  StageTwo.crtEntry_stageTwoGuess_of DeltaView.convHot_case digestCase StageTwo.keyOff_case
    ⟨DeltaView.inv_le_charge, StageTwo.CaseDigest.inv_le_charge, StageTwo.keyOff_error_le⟩
    Flags.crtCurveWindowMass

theorem stageOne : CrtStageOneGuess Instance.crtEntry (ENNReal.ofReal crtHiddenCharge) :=
  StageOneProof.crtEntry_stageOneGuess_of DeltaView.convHot_case ConvReach.convTagsReachable
    StageOneProof.neverCase StageOneProof.maskCase digestCase StageOneProof.finalCase StageOneProof.keyCase
    ⟨DeltaView.inv_le_charge, DeltaView.inv_le_charge, StageTwo.CaseDigest.inv_le_charge,
      StageTwo.CaseDigest.inv_le_charge, StageTwo.CaseDigest.inv_le_charge, StageOneProof.keyCase_le⟩

#print axioms stageOne
#print axioms stageTwo
#print axioms DeltaView.delta_guess_clip_le
#print axioms DeltaView.deltaGivenView
#print axioms Flags.crtConvNever
#print axioms chainError_budget

run_cmd do
  for name in [`NarrowPrivacyAudit.stageOne, `NarrowPrivacyAudit.stageTwo,
      `Kriterion.CRT.Privacy.DeltaView.delta_guess_clip_le,
      `Kriterion.CRT.Privacy.DeltaView.deltaGivenView,
      `Kriterion.CRT.Privacy.Flags.crtConvNever,
      `Kriterion.CRT.Privacy.chainError_budget] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "Narrow privacy-stage axiom check passed"

end NarrowPrivacyAudit
