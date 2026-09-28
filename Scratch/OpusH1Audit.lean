/-
Opus H1 candidate audit (modulus 17 dropped; constant error closed against two units of work).

The expected numbers are **not** copied from the Lean constants: they come from the independent integer model
`Scratch/opus_budget_model.py` / `Scratch/opus_check_h1.py`, which first reproduces the pinned entry's
130,122 / 988,438 / 981,506 from the same formulas. The baseline audit `Scratch/Audit.lean` is left unchanged
as evidence for `e37c4db`.

1. Axioms of `Submission.solution` and of the theorems H1 touched.
2. The three metrics as the challenge's `Benchmark` module reads them, and the budgets recomputed from their
   definitions.
3. The table: 84 moduli, no 17, product equal to the generated `BudgetData.M`, `2 B ≤ M` and `2 M ≤ 256 ^ 78`.
4. The byte count measured by encoding two concrete public values (all zero; all maximal) and decoding back.
5. The statement of the closing inequality (`… + 2`).

Run after `lake build`: `lake env lean Scratch/OpusH1Audit.lean`.
-/
import Submission
import Benchmark
import Lean

open Kriterion Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry

#print axioms Submission.solution

run_cmd do
  for name in [`Submission.solution, `Kriterion.CRT.EntryCorrect.perfectCorrectness,
      `Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy, `Kriterion.CRT.Privacy.chainError_budget,
      `Kriterion.CRT.Privacy.chain_oracleAdaptivePrivacy, `Kriterion.CRT.Privacy.smudgeError_le,
      `Kriterion.CRT.BudgetData.chainConstant_le_two, `Kriterion.CRT.Entry.Wire.encoding_length,
      `Kriterion.CRT.Entry.garbleBudget_eq, `Kriterion.CRT.Entry.evaluateBudget_eq,
      `Kriterion.CRT.bn254Table_record_fits, `Kriterion.CRT.SliceC.bn254_correctTable] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "axiom check passed: only propext, Classical.choice, Quot.sound"

#check @Kriterion.CRT.Privacy.chainError_budget

#eval Kriterion.Benchmark.ciphertextBytes Submission.solution
#eval Kriterion.Benchmark.garbleQueries Submission.solution
#eval Kriterion.Benchmark.evaluateQueries Submission.solution

/-- Expected numbers from the independent model (84 moduli, otherwise the pinned configuration). -/
def expectedBytes : Nat := 129628
def expectedGarble : Nat := 985094
def expectedEvaluate : Nat := 978204

#guard Kriterion.Benchmark.ciphertextBytes Submission.solution == expectedBytes
#guard Kriterion.Benchmark.garbleQueries Submission.solution == expectedGarble
#guard Kriterion.Benchmark.evaluateQueries Submission.solution == expectedEvaluate
#guard Entry.ciphertextBytes == expectedBytes
#guard Entry.garbleBudget == expectedGarble
#guard Entry.evaluateBudget == expectedEvaluate
#guard Entry.garbleBudget + 500 ≤ 1759967
#guard Entry.evaluateBudget + 500 ≤ 1055879
#guard Entry.table.convBlocks == convCount
#guard convCount == 2937

/-! ### The table -/

#guard bn254Moduli.size == 84
#guard !(bn254Moduli.contains 17)
#guard bn254Moduli.toList == (BudgetData.moduli)
#guard bn254Table.product == BudgetData.M
#guard 2 * bn254Table.wrapBound ≤ bn254Table.product + 1
#guard 2 * bn254Table.product ≤ 256 ^ 78
#guard Nat.log2 bn254Table.product == 618

/-! ### Bytes by encoding -/

def zeroPublic : Entry.Public where
  curve := (0, 0, 0)
  rows := Vector.replicate PlanB.digitCount ⟨0, false, false, false⟩
  exception := Vector.replicate PlanB.digitCount (Vector.replicate 2 0)
  crtX := Vector.replicate convCount 0
  crtY := Vector.replicate convCount 0
  recX := Vector.replicate xCount 0
  recY := Vector.replicate yCount 0

def maxPublic : Entry.Public where
  curve := (-1, -1, -1)
  rows := Vector.replicate PlanB.digitCount ⟨-1, true, true, true⟩
  exception := Vector.replicate PlanB.digitCount (Vector.replicate 2 15)
  crtX := Vector.replicate convCount (-1)
  crtY := Vector.replicate convCount (-1)
  recX := Vector.replicate xCount ⟨256 ^ 78 - 1, by decide⟩
  recY := Vector.replicate yCount ⟨256 ^ 78 - 1, by decide⟩

#eval (Entry.Wire.encoding.encode zeroPublic).length
#guard (Entry.Wire.encoding.encode zeroPublic).length == expectedBytes
#guard (Entry.Wire.encoding.encode maxPublic).length == expectedBytes
#guard (Entry.Wire.encoding.decode (Entry.Wire.encoding.encode zeroPublic)).isSome
#guard (Entry.Wire.encoding.decode (Entry.Wire.encoding.encode maxPublic)).isSome
