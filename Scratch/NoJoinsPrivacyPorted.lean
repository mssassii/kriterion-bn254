/-
No-joins (branch nojoins-p, parity base): axiom audit of the privacy leaves ported mechanically to the derived Lamport key
(the chunk-tree joins absorbed into the labels). Every theorem below compiles on `nojoins-p` without `sorry`.
The five declarations that need the new joint label law / fine view (LabelsSplit.tapeLabels_eq,
CoreReads.realRest_congr, DeltaViewFD.garbleCM_asked/garbleCM_eval/convAgree_of_convVector_eq) and the modules
behind them are not imported here. On the parity base `Hidden/StageOneCast` (the never-hot cast case) imports
`Laws/CoreReads` and is therefore behind `LabelsSplit` too; it is not audited here. Run with `lake env lean Scratch/NoJoinsPrivacyPorted.lean` after building
its imports.
-/
import Proof.Privacy.CRT.Core.ConvSplit
import Proof.Privacy.CRT.Core.SourceSplit
import Proof.Privacy.CRT.Core.KeyZeroCongr
import Proof.Privacy.CRT.Hidden.Reached
import Proof.Privacy.CRT.Hidden.StageOneKey
import Proof.Privacy.CRT.Hidden.CaseDigest
import Proof.Privacy.CRT.Hidden.CaseKeyOff
import Proof.Privacy.CRT.Flags.ConvCoincide
import Proof.Privacy.CRT.Paths.SameVisible
import Construction.CRT.BudgetFacts
import Lean

open Kriterion Kriterion.CRT Kriterion.CRT.Entry

#check @Kriterion.CRT.Privacy.Conv.conversion_law_fill
#check @Kriterion.CRT.Privacy.Flat.phi_uniform
#check @Kriterion.CRT.Privacy.Flat.source_crt_law
#check @Kriterion.CRT.Privacy.ConvSplit.crtConvSplit
#check @Kriterion.CRT.EntrySplit.publish_labels_split
#check @Kriterion.CRT.Privacy.KeyZero.keyOf_congr
#check @Kriterion.CRT.Privacy.BmrReal.realGarbled_pair
#check @Kriterion.CRT.Privacy.Align.replayConv_aligned
#check @Kriterion.CRT.Privacy.Align.garble_designed_reached
#check @Kriterion.CRT.Privacy.Align.crtEntry_designedReached
#check @Kriterion.CRT.Paths.crtEntry_sameVisible
#check @Kriterion.CRT.Privacy.Flags.crtConvNever
#check @Kriterion.CRT.Privacy.StageTwo.digestOther_case_of
#check @Kriterion.CRT.Privacy.StageTwo.maskOff_case
#check @Kriterion.CRT.Privacy.StageTwo.final_case
#check @Kriterion.CRT.Privacy.StageTwo.keyOff_case
#check @Kriterion.CRT.Privacy.StageOneProof.finalCase
#check @Kriterion.CRT.Privacy.StageOneProof.keyCase

run_cmd do
  for name in [`Kriterion.CRT.Privacy.Conv.conversion_law_fill,
      `Kriterion.CRT.Privacy.Flat.phi_uniform,
      `Kriterion.CRT.Privacy.Flat.source_crt_law,
      `Kriterion.CRT.Privacy.ConvSplit.crtConvSplit,
      `Kriterion.CRT.EntrySplit.publish_labels_split,
      `Kriterion.CRT.Privacy.KeyZero.keyOf_congr,
      `Kriterion.CRT.Privacy.BmrReal.realGarbled_pair,
      `Kriterion.CRT.Privacy.Align.replayConv_aligned,
      `Kriterion.CRT.Privacy.Align.garble_designed_reached,
      `Kriterion.CRT.Privacy.Align.crtEntry_designedReached,
      `Kriterion.CRT.Paths.crtEntry_sameVisible,
      `Kriterion.CRT.Privacy.Flags.crtConvNever,
      `Kriterion.CRT.Privacy.StageTwo.digestOther_case_of,
      `Kriterion.CRT.Privacy.StageTwo.maskOff_case,
      `Kriterion.CRT.Privacy.StageTwo.final_case,
      `Kriterion.CRT.Privacy.StageTwo.keyOff_case,
      `Kriterion.CRT.Privacy.StageOneProof.finalCase,
      `Kriterion.CRT.Privacy.StageOneProof.keyCase] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "No-joins ported privacy leaves: only propext, Classical.choice, Quot.sound"

set_option maxRecDepth 100000 in
example : ciphertextBytes = 135855 ∧ garbleBudget = 988438 ∧ evaluateBudget = 981506 := by
  rw [garbleBudget_eq, evaluateBudget_eq]
  decide +kernel
