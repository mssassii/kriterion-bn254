/-
No-joins audit (branch `nojoins`): construction, perfect correctness, source readback and exact
metrics after absorbing the chunk-tree joins into the Lamport labels. Imports no Submission,
privacy or simulator proof. Run with `lake env lean Scratch/NoJoinsAudit.lean` after building its
imports. Supersedes the numerals of `Scratch/NarrowPhaseA.lean` (148,712 B with chunk joins).
-/
import Proof.Correctness.CRT.EntryCorrect
import Proof.Correctness.CRT.SourceReads
import Construction.CRT.BudgetFacts
import Lean

open Kriterion Kriterion.CRT Kriterion.CRT.Entry

#check Kriterion.CRT.EntryCorrect.perfectCorrectness
#check @Kriterion.CRT.Absorb.coordEvalM_absorb
#check @Kriterion.CRT.EntryCorrect.garbleCM_eval

run_cmd do
  for name in [`Kriterion.CRT.EntryCorrect.perfectCorrectness,
      `Kriterion.CRT.EntryCorrect.garbleCM_eval,
      `Kriterion.CRT.Absorb.coordEvalM_absorb,
      `Kriterion.CRT.Entry.Wire.encoding_length,
      `Kriterion.CRT.Entry.garbleBudget_eq,
      `Kriterion.CRT.Entry.evaluateBudget_eq,
      `Kriterion.CRT.Entry.convBlocks_table,
      `Kriterion.CRT.SourceReads.chunkJoin_publish,
      `Kriterion.CRT.SourceReads.chunkPin_lanes,
      `Kriterion.CRT.SourceReads.stagePin_lanes] do
    let axioms ← Lean.collectAxioms name
    let illegal := axioms.filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "No-joins axiom check passed: only propext, Classical.choice, Quot.sound"

/- Recompute from the construction definitions, not a copied score record. -/
set_option maxRecDepth 100000 in
example : ciphertextBytes = 142940 ∧ garbleBudget = 964502 ∧ evaluateBudget = 957536 := by
  decide +kernel

/- 148,712 − 444 · 13 = 142,940: exactly the 2 · 222 chunk joins at 13 bytes. -/
example : ciphertextBytes + 2 * 222 * 13 = 148712 := by decide

/- Both query gates keep their headroom (counts unchanged by no-joins). -/
example : garbleBudget + 500 ≤ 1759967 ∧ evaluateBudget + 500 ≤ 1055879 := by
  rw [garbleBudget_eq, evaluateBudget_eq]
  decide +kernel

set_option maxRecDepth 100000 in
example : Entry.table.convBlocks = 3190 := by
  simpa only [convCount] using convBlocks_table

/- The source keeps its 1,467 join cells per coordinate (222 unread chunk-join cells). -/
set_option maxRecDepth 100000 in
example : Entry.joinCount = 1467 ∧ Entry.chunkJoinBase Entry.table.chunkCount = 222 := by
  decide +kernel
