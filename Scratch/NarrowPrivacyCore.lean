/-
Round-6 privacy-core audit. Run after the imported privacy leaves compile.
The raw residual and raw answer tables remain 128/256 bits; conversion labels
and the never-hot cast guess are 104 bits.
-/
import Proof.Privacy.CRT.Core.ConvSplit
import Proof.Privacy.CRT.Core.SourceSplit
import Proof.Privacy.CRT.Hidden.StageOneCast
import Construction.CRT.BudgetFacts
import Lean

open Kriterion Kriterion.CRT Kriterion.CRT.Entry

#check Kriterion.CRT.Privacy.Conv.conversion_law_fill
#check Kriterion.CRT.Privacy.Flat.phi_uniform
#check Kriterion.CRT.Privacy.ConvSplit.crtConvSplit
#check Kriterion.CRT.EntrySplit.publish_labels_split
#check Kriterion.CRT.Privacy.StageOneProof.neverCase
#check Kriterion.CRT.Narrow.card_clip_fibre

#print axioms Kriterion.CRT.Privacy.Conv.conversion_law_fill
#print axioms Kriterion.CRT.Privacy.Flat.phi_uniform
#print axioms Kriterion.CRT.Privacy.ConvSplit.crtConvSplit
#print axioms Kriterion.CRT.EntrySplit.publish_labels_split
#print axioms Kriterion.CRT.Privacy.StageOneProof.neverCase
#print axioms Kriterion.CRT.Narrow.card_clip_fibre

run_cmd do
  for name in [`Kriterion.CRT.Privacy.Conv.conversion_law_fill,
      `Kriterion.CRT.Privacy.Flat.phi_uniform,
      `Kriterion.CRT.Privacy.ConvSplit.crtConvSplit,
      `Kriterion.CRT.EntrySplit.publish_labels_split,
      `Kriterion.CRT.Privacy.StageOneProof.neverCase,
      `Kriterion.CRT.Narrow.card_clip_fibre] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "Narrow privacy-core axiom check passed: only propext, Classical.choice, Quot.sound"

example : Privacy.StageOneProof.OneCase Privacy.StageOneProof.NeverHotCast
    ((2 : ENNReal) ^ labelBits)⁻¹ := Privacy.StageOneProof.neverCase

example (label : Label) :
    (Finset.univ.filter (fun delta : Cryptography.Block => clip delta = label)).card = 2 ^ 24 := by
  simpa only [Narrow.labelBits] using Narrow.clip_fiber_filter_card label

/- Recheck the metric certificates (no chunk joins: 135,855 bytes). -/
example : ciphertextBytes = 135855 ∧ garbleBudget = 988438 ∧ evaluateBudget = 981506 := by
  rw [garbleBudget_eq, evaluateBudget_eq]
  decide +kernel
