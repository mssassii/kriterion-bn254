/-
Combined A1 + H1 audit. Astra integration of the independently verified schedules
and Opus modulus-removal/privacy closure, using expectations derived independently
by Scratch/check_combined.py. Baseline, A1 and H1 audits remain unchanged.

Checks Benchmark metrics, the budget definitions, both query gates, table and
record bounds, zero/maximal encodings, selected-row and simulator counts, and
axioms of the complete solution and changed proof obligations.
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
#eval Entry.garbleBudget
#eval Entry.evaluateBudget

/-- Expected numbers from the independent combined model (84 moduli, 26 width-9 rows). -/
def expectedBytes : Nat := 128276
def expectedGarble : Nat := 1061622
def expectedEvaluate : Nat := 1054788

#guard Kriterion.Benchmark.ciphertextBytes Submission.solution == expectedBytes
#guard Kriterion.Benchmark.garbleQueries Submission.solution == expectedGarble
#guard Kriterion.Benchmark.evaluateQueries Submission.solution == expectedEvaluate
#guard Entry.ciphertextBytes == expectedBytes
#guard Entry.garbleBudget == expectedGarble
#guard Entry.evaluateBudget == expectedEvaluate
#guard Entry.garbleBudget + 500 ≤ 1759967
#guard Entry.evaluateBudget + 500 ≤ 1055879
#guard Entry.table.convBlocks == convCount
#guard convCount == 2885

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

/- Selected schedule and finite simulator checks. -/
#guard Narrow.labelBits == 104
#guard (bn254Moduli.toList.filter fun m => selectiveWidth0 m == 9).length == 26
#guard Entry.joinCount == 1415
#guard Entry.pinCount == 198
#guard Kriterion.CRT.SimMachine.CrtStage1.pieces.length == 44579
#print axioms Kriterion.CRT.SliceC.bn254_selectiveFacts
#print axioms Kriterion.CRT.Privacy.ConvReach.stageZero_bound
#print axioms Kriterion.CRT.SimMachine.CrtTop.crtSimulator
