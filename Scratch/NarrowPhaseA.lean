/-
Phase-A audit: construction, perfect correctness, source readback and exact
metrics.  This deliberately imports no Submission, privacy or simulator proof.
Run with `lake env lean Scratch/NarrowPhaseA.lean` after building its imports.
-/
import Proof.Correctness.CRT.EntryCorrect
import Proof.Correctness.CRT.SourceReads
import Construction.CRT.BudgetFacts
import Lean

open Kriterion Kriterion.CRT Kriterion.CRT.Entry

#check Kriterion.CRT.EntryCorrect.perfectCorrectness

#print axioms Kriterion.CRT.EntryCorrect.perfectCorrectness
#print axioms Kriterion.CRT.Entry.Wire.encoding_length
#print axioms Kriterion.CRT.Entry.garbleBudget_eq
#print axioms Kriterion.CRT.Entry.evaluateBudget_eq
#print axioms Kriterion.CRT.SourceReads.chunkPin_lanes
#print axioms Kriterion.CRT.SourceReads.stagePin_lanes

run_cmd do
  for name in [`Kriterion.CRT.EntryCorrect.perfectCorrectness,
      `Kriterion.CRT.Entry.Wire.encoding_length,
      `Kriterion.CRT.Entry.garbleBudget_eq,
      `Kriterion.CRT.Entry.evaluateBudget_eq,
      `Kriterion.CRT.SourceReads.chunkPin_lanes,
      `Kriterion.CRT.SourceReads.stagePin_lanes] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "Phase-A axiom check passed: only propext, Classical.choice, Quot.sound"

/-- Recompute from the construction definitions, not a copied score record. -/
set_option maxRecDepth 100000 in
example : ciphertextBytes = 148712 ∧ garbleBudget = 964502 ∧ evaluateBudget = 957536 := by
  decide +kernel

/-- Both query gates have at least 500 queries of headroom. -/
example : garbleBudget + 500 ≤ 1759967 ∧ evaluateBudget + 500 ≤ 1055879 := by
  rw [garbleBudget_eq, evaluateBudget_eq]
  decide +kernel

example : Entry.table.convBlocks = 3412 := by
  simpa only [convCount] using convBlocks_table
