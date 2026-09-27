/-
Audit of the entry: the metrics, the query budgets recomputed from their definitions, the byte
count measured by encoding a concrete public value, and the axioms.

1. The axioms of `Submission.solution` and of the theorems the README names.
2. The three metrics as the challenge's `Benchmark` module reads them.
3. The query budgets recomputed term by term from their definitions (`Entry.garbleBudget`,
   `Entry.evaluateBudget` in `Construction/CRT/Entry.lean`: sums over the 85 moduli of the table),
   not from the declared constants.
4. The byte count recomputed by encoding one concrete `Public` value (all fields zero) with the
   entry's own `Entry.Wire.encoding`, in the interpreter, and decoding it back.

The `#guard` lines fail the file if any figure differs from the expected one or a query budget
comes within `500` queries of its gate (garbling `≤ 1,759,967`, evaluation `≤ 1,055,879`).

Run after `lake build`: `lake env lean Scratch/Audit.lean`.
-/
import Submission
import Benchmark
import Lean

open Kriterion Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry

#print axioms Submission.solution

run_cmd do
  for name in [`Submission.solution, `Kriterion.CRT.EntryCorrect.perfectCorrectness,
      `Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy, `Kriterion.CRT.Assembly.crtPrivacy,
      `Kriterion.CRT.Assembly.privacy_of_leaves, `Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy_of,
      `Kriterion.CRT.Entry.Wire.encoding_length, `Kriterion.CRT.Entry.garbleBudget_eq,
      `Kriterion.CRT.Entry.evaluateBudget_eq] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "axiom check passed: only propext, Classical.choice, Quot.sound"

#print axioms Kriterion.CRT.EntryCorrect.perfectCorrectness
#print axioms Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy
#print axioms Kriterion.CRT.Assembly.crtPrivacy
#print axioms Kriterion.CRT.SimMachine.CrtTop.crtSimulator
#print axioms Kriterion.CRT.Entry.Wire.encoding_length
#print axioms Kriterion.CRT.Entry.garbleBudget_eq
#print axioms Kriterion.CRT.Entry.evaluateBudget_eq

#eval Kriterion.Benchmark.ciphertextBytes Submission.solution
#eval Kriterion.Benchmark.garbleQueries Submission.solution
#eval Kriterion.Benchmark.evaluateQueries Submission.solution

#eval Entry.garbleBudget
#eval Entry.evaluateBudget

/-- The expected numbers of this entry (85 moduli, table T9, pad slack 120, block-aligned cast
lanes, per-encoding 78-byte records with the wrap hint, sign rows with three published constants
per digit, the hash digest with two exceptional kinds). -/
def expectedBytes : Nat := 173472
def expectedGarble : Nat := 945076
def expectedEvaluate : Nat := 937418

#guard Kriterion.Benchmark.ciphertextBytes Submission.solution == expectedBytes
#guard Kriterion.Benchmark.garbleQueries Submission.solution == expectedGarble
#guard Kriterion.Benchmark.evaluateQueries Submission.solution == expectedEvaluate
#guard Entry.ciphertextBytes == expectedBytes
#guard Entry.garbleBudget == expectedGarble
#guard Entry.evaluateBudget == expectedEvaluate
#guard Entry.garbleBudget + 500 ≤ 1759967
#guard Entry.evaluateBudget + 500 ≤ 1055879
#guard Entry.table.convBlocks == convCount

/-- An all-zero public value, to measure the encoding by computation. -/
def zeroPublic : Entry.Public where
  curve := (0, 0, 0)
  rows := Vector.replicate PlanB.digitCount ⟨0, 0, 0⟩
  exception := Vector.replicate PlanB.digitCount (Vector.replicate 12 0)
  crtX := Vector.replicate convCount 0
  crtY := Vector.replicate convCount 0
  recX := Vector.replicate xCount 0
  recY := Vector.replicate yCount 0

#eval (Entry.Wire.encoding.encode zeroPublic).length
#guard (Entry.Wire.encoding.encode zeroPublic).length == expectedBytes
#guard (Entry.Wire.encoding.decode (Entry.Wire.encoding.encode zeroPublic)).isSome
