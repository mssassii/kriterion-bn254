/-
**The privacy field of the CRT entry**.

`crtEntry_adaptivePrivacy_of` is the field from six rows passed as hypotheses: the stage guesses (H6, H7), H8's coincidence guess, core and flag mass at the shadow, and the
machine law (H11) with its simulator. Every other row is proved (`Glue/Instance.lean`).

`crtEntry_adaptivePrivacy` is the unconditional
field: `Assembly.privacy_of_leaves` derives the six rows from the leaves (every row Prop that unfolds to
`∀ [inst], …` is passed as `@h`, and every `have` is untyped), and `Assembly.crtPrivacy` applies it to the proved
leaves.
-/

import Proof.Privacy.CRT.Glue.Instance
import Proof.Privacy.CRT.Glue.MachineCrt
import Proof.Simulator.CRT.Stage1LawFinal
import Proof.Privacy.CRT.Hidden.CaseConv
import Proof.Privacy.CRT.Hidden.CaseDigest
import Proof.Privacy.CRT.Hidden.StageTwoTable
import Proof.Privacy.CRT.Hidden.StageOne
import Proof.Privacy.CRT.Hidden.StageOneTable
import Proof.Privacy.CRT.Core.BmrReal
import Proof.Privacy.CRT.Core.BmrKernel
import Proof.Privacy.CRT.Core.BmrCoins
import Proof.Privacy.CRT.Core.BmrSplitOff
import Proof.Privacy.CRT.Core.BmrKeyOff
import Proof.Privacy.CRT.Core.ConvSplit
import Proof.Privacy.CRT.Core.DigestSplit
import Proof.Privacy.CRT.Core.OffDecomp
import Proof.Privacy.CRT.Laws.CoreParts
import Proof.Privacy.CRT.Laws.MiddleCrt
import Proof.Privacy.CRT.Laws.LabelsSplit
import Proof.Privacy.CRT.Laws.Rest
import Proof.Privacy.CRT.Paths.Upper
import Proof.Privacy.CRT.Paths.DeltaGuess
import Proof.Privacy.CRT.Paths.LabelCoincide
import Proof.Privacy.CRT.Flags.ConvCoincide
import Proof.Privacy.CRT.Flags.KeyMaskHidden
import Proof.Privacy.CRT.Flags.CoincidenceSplit
import Proof.Privacy.CRT.Flags.CrtRows
import Proof.Privacy.CRT.Glue.ContainParts
import Proof.Privacy.CRT.Glue.ReplayPoints
import Proof.Privacy.CRT.Hidden.Reach
import Proof.Privacy.CRT.Hidden.StageOneCast
import Proof.Privacy.CRT.Hidden.StageOneKey
import Proof.Privacy.CRT.Hidden.CaseKeyOff
import Proof.Privacy.CRT.Flags.CurveWindow
import Proof.Privacy.CRT.Paths.StageOneFactors
import Proof.Privacy.CRT.Core.FinalCoincide
import Proof.Privacy.CRT.Core.BmrIdeal
import Proof.Privacy.CRT.Laws.CoreReads
import Proof.Privacy.CRT.Laws.CoreIdeal
import Proof.Privacy.CRT.Glue.OnDecomp
import Proof.Privacy.CRT.Flags.OnFinalFresh
import Proof.Privacy.CRT.Flags.Touch
import Proof.Privacy.CRT.Flags.OffFinalFresh
import Proof.Simulator.CRT.Stage1Retained

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.Final

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open scoped ENNReal

/-- **The privacy field of the CRT entry from six rows passed as hypotheses.** -/
theorem crtEntry_adaptivePrivacy_of (simulator : BoundedMachine.Simulator)
    (one : CrtStageOneGuess Instance.crtEntry (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess Instance.crtEntry Entry.table (ENNReal.ofReal crtHiddenCharge)
      (ENNReal.ofReal hiddenWindowError))
    (guess : Flags.CrtCoincidenceGuess Instance.crtEntry Entry.table (ENNReal.ofReal coincidenceError))
    (core : PublicFirst.CrtLiftCore Instance.crtEntry Entry.table @H8.crtShadow)
    (flag : PublicFirst.CrtFlagMass Instance.crtEntry @H8.crtShadow)
    (machine : CrtMachineHop Instance.crtEntry simulator) : CrtPrivacy Instance.crtEntry :=
  Instance.crtEntry_privacy_of_table simulator @one @two guess @core @flag @machine

end Kriterion.CRT.Privacy.Final

/-! ### The assembly: the rows from the proved leaves -/

namespace Kriterion.CRT.Assembly

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.SimMachine
open scoped ENNReal

/-- The type of a function's first argument (to state a leaf with the consumer's own instance terms). -/
abbrev argTy {α : Sort _} {β : Sort _} (_ : α → β) : Sort _ := α

/-- The type of a function's second argument. -/
abbrev arg2Ty {α : Sort _} {β : Sort _} {γ : Sort _} (_ : α → β → γ) : Sort _ := β

/-- H11's stage-1 law at the CRT simulator. -/
theorem stage1 :
    LawShape.Stage1Law Instance.crtEntry CrtTop.crtSimulator CrtBounded.samplers CrtTop.crtExtract := by
  rw [CrtTop.crtSimulator_eq]
  exact CrtStage1Law.stage1Law _ _ _ CrtTop.crt_within (CrtTop.ofProg_size _) (CrtTop.ofProg_cost _)

/-- H7's case `digestOther`. -/
theorem digestCase : StageTwo.GuessCase StageTwo.digestOther StageTwo.noExtra ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
  StageTwo.digestOther_case_of (DeltaView.deltaGivenView DeltaView.coordRelational DeltaView.tailRel)

/-- H7 from the bridge-key case and the curve window. -/
theorem h7_of {εKey : ℝ≥0∞} (keyCase : StageTwo.GuessCase StageTwo.keyOff StageTwo.notNearEdge εKey)
    (keyLe : εKey ≤ ENNReal.ofReal crtHiddenCharge) (window : StageTwo.CurveWindowMass) :
    CrtStageTwoGuess Instance.crtEntry Entry.table (ENNReal.ofReal crtHiddenCharge)
      (ENNReal.ofReal hiddenWindowError) :=
  StageTwo.crtEntry_stageTwoGuess_of DeltaView.convHot_case digestCase keyCase
    ⟨DeltaView.inv_le_charge, DeltaView.inv_le_charge, keyLe⟩ window

/-- H6 from the reach, the never-hot cast and the bridge-key case. -/
theorem h6_of {εNever εKey : ℝ≥0∞} (reach : StageOneProof.ConvTagsReachable)
    (never : StageOneProof.OneCase StageOneProof.NeverHotCast εNever)
    (key : StageOneProof.OneCase (fun τ => tagFamily τ = 10) εKey)
    (neverLe : εNever ≤ ENNReal.ofReal crtHiddenCharge) (keyLe : εKey ≤ ENNReal.ofReal crtHiddenCharge) :
    CrtStageOneGuess Instance.crtEntry (ENNReal.ofReal crtHiddenCharge) :=
  StageOneProof.crtEntry_stageOneGuess_of DeltaView.convHot_case reach never StageOneProof.maskCase digestCase
    StageOneProof.finalCase key
    ⟨DeltaView.inv_le_charge, neverLe, DeltaView.inv_le_charge, DeltaView.inv_le_charge, DeltaView.inv_le_charge,
      keyLe⟩

/-- H8's coincidence guess from the stage-one factors and the final coincidence. -/
theorem guess_of (factors : Paths.StageOneFactors) (final : Flags.CrtFinalCoincide) :
    Flags.CrtCoincidenceGuess Instance.crtEntry Entry.table (ENNReal.ofReal coincidenceError) :=
  Flags.crtCoincidenceGuess_of Flags.crtConvCoincide (Paths.crtDeltaGuess_of factors) Flags.crtKeyMaskHidden
    Paths.crtEntry_labelCoincide final

/-- P45 off the curve. -/
theorem bmrOff : H8.CrtBmrSplitOff Entry.table :=
  BmrOff.crtBmrSplitOff_of BmrSplit.crtKernel BmrSplit.crtKernel_off (BmrReal.realReading _) BmrSplit.coinsSplit

/-- P45 on the curve from the ideal reading. -/
theorem bmr_of (ideal : ∀ [FieldCertificate] [GroupCertificate], BmrSplit.IdealReading BmrSplit.crtKernel) :
    H8.CrtBmrSplit Entry.table :=
  BmrSplit.crtBmrSplit_of BmrSplit.crtKernel (BmrReal.realReading _) ideal BmrSplit.coinsSplit

/-- H8's core row. -/
theorem coreBelow_of (ideal : ∀ [FieldCertificate] [GroupCertificate], BmrSplit.IdealReading BmrSplit.crtKernel)
    (reads : Laws.RealReads Entry.table) (on : Laws.IdealFactorOn Entry.table)
    (off : Laws.IdealFactorOff Entry.table) :
    H8.CrtCoreBelow Instance.crtEntry Entry.table H8.crtRevealOn H8.crtRevealOff :=
  Laws.coreBelow_of_factors Entry.table (ConvSplit.crtConvSplit 0) (ConvSplit.crtConvSplit 1)
    DigestSplit.digestSplit (bmr_of ideal) bmrOff (Laws.crtRestSplit_of _ Laws.labelsSplit) reads on off

/-- **`CrtPrivacy crtEntry` from the leaves** (the touch
row is `Flags.crtTouchGuess` from H6, the core row, the on-curve decomposition `decomp` (which also feeds the middle
factor) and the two freshness leaves). -/
theorem privacy_of_leaves {εNever εKey1 εKey2 : ℝ≥0∞}
    (reach : StageOneProof.ConvTagsReachable)
    (never : StageOneProof.OneCase StageOneProof.NeverHotCast εNever)
    (key1 : StageOneProof.OneCase (fun τ => tagFamily τ = 10) εKey1)
    (neverLe : εNever ≤ ENNReal.ofReal crtHiddenCharge) (key1Le : εKey1 ≤ ENNReal.ofReal crtHiddenCharge)
    (key2 : StageTwo.GuessCase StageTwo.keyOff StageTwo.notNearEdge εKey2)
    (key2Le : εKey2 ≤ ENNReal.ofReal crtHiddenCharge) (window : StageTwo.CurveWindowMass)
    (factors : Paths.StageOneFactors) (final : Flags.CrtFinalCoincide)
    (ideal : ∀ [FieldCertificate] [GroupCertificate], BmrSplit.IdealReading BmrSplit.crtKernel)
    (reads : Laws.RealReads Entry.table) (on : Laws.IdealFactorOn Entry.table)
    (off : Laws.IdealFactorOff Entry.table)
    (decomp : argTy Laws.crtEntry_middleFactor)
    (onFresh : Flags.CrtOnFinalFresh) (offFresh : Flags.CrtOffFinalFresh)
    (retained : arg2Ty MachineCrt.crtEntry_machineHop_of) :
    CrtPrivacy Instance.crtEntry := by
  have one := @h6_of _ _ reach never key1 neverLe key1Le
  have two := @h7_of _ key2 key2Le window
  have coreB := @coreBelow_of ideal reads on off
  have middleF := @Laws.crtEntry_middleFactor @decomp
    (fun scalar u off source => OffDecomp.crtOffSplit scalar u off source)
  have core := @H8.crtLiftCore_of_factors Empty Empty Instance.crtEntry Kriterion.CRT.Entry.table @H8.crtShadow
    @H8.crtRevealOn @H8.crtRevealOff @middleF @coreB @Paths.crtEntry_upperFactor
  have touch := @Flags.crtTouchGuess @one @coreB @decomp onFresh offFresh
  have flag := @Flags.crtFlagMass_crt @touch
  have machine := @MachineCrt.crtEntry_machineHop_of @stage1 @retained
  exact Final.crtEntry_adaptivePrivacy_of CrtTop.crtSimulator @one @two (@guess_of factors final) @core @flag @machine

/-- **`CrtPrivacy crtEntry`, unconditional**: every leaf passed as its proved theorem. -/
theorem crtPrivacy : CrtPrivacy Instance.crtEntry :=
  @privacy_of_leaves _ _ _ ConvReach.convTagsReachable StageOneProof.neverCase StageOneProof.keyCase
    DeltaView.inv_le_charge StageOneProof.keyCase_le StageTwo.keyOff_case StageTwo.keyOff_error_le
    Flags.crtCurveWindowMass @Paths.stageOneFactors FinalCoincide.crtEntry_finalCoincide @BmrSplit.idealReading
    @Laws.realReads @Laws.idealFactorOn @Laws.idealFactorOff @OnDecompCrt.crtEntry_decomp Flags.crtOnFinalFresh
    Flags.crtOffFinalFresh @CrtStage1Retained.retained

end Kriterion.CRT.Assembly

namespace Kriterion.CRT.Privacy.Final

/-- **The privacy field of the CRT entry** (unconditional). -/
theorem crtEntry_adaptivePrivacy : CrtPrivacy Instance.crtEntry :=
  @Kriterion.CRT.Assembly.crtPrivacy

end Kriterion.CRT.Privacy.Final
