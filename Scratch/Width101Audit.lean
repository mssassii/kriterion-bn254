/-
Opus P1b audit: 101-bit conversion labels, packed conversion vectors, refined charge closed against two units.

Expected numbers come from `Scratch/opus_check_w101.py` (independent formulas, which first confirm that the query
counts do not depend on the label width in 101…104). Historical audits (`Audit`, `OpusH1Audit`, `CombinedAudit`,
`P1Audit`) are unchanged.

Run after `lake build` and `lake build Benchmark`: `lake env lean Scratch/Width101Audit.lean`.
-/
import Submission
import Benchmark
import Lean

open Kriterion Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry

#print axioms Submission.solution

run_cmd do
  for name in [`Submission.solution, `Kriterion.CRT.EntryCorrect.perfectCorrectness,
      `Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy, `Kriterion.CRT.Privacy.chainError_budget,
      `Kriterion.CRT.Privacy.chain_oracleAdaptivePrivacy, `Kriterion.CRT.Privacy.crtHiddenCharge_le,
      `Kriterion.CRT.Privacy.crtHiddenCharge_eq, `Kriterion.CRT.BudgetData.chainConstant_le_two,
      `Kriterion.CRT.BudgetData.hiddenQuery_le, `Kriterion.CRT.Entry.Wire.encoding_length,
      `Kriterion.CRT.Narrow.packedLabels_length, `Kriterion.CRT.Narrow.unpackAt_packNat,
      `Kriterion.CRT.SimMachine.CrtWire.packed_bits, `Kriterion.CRT.SimMachine.CrtPieces.pieces_bits,
      `Kriterion.CRT.Entry.garbleBudget_eq, `Kriterion.CRT.Entry.evaluateBudget_eq,
      `Kriterion.CRT.bn254Table_record_fits, `Kriterion.CRT.SliceC.bn254_correctTable,
      `Kriterion.CRT.SimMachine.CrtTop.crtSimulator] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "axiom check passed: only propext, Classical.choice, Quot.sound"

#check @Kriterion.CRT.Privacy.chainError_budget
#check @Kriterion.CRT.Privacy.crtHiddenCharge_eq
#check @Kriterion.CRT.Privacy.crtHiddenCharge_le

#eval Kriterion.Benchmark.ciphertextBytes Submission.solution
#eval Kriterion.Benchmark.garbleQueries Submission.solution
#eval Kriterion.Benchmark.evaluateQueries Submission.solution

def expectedBytes : Nat := 126114
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

/-! ### Width, table and counts -/

#guard Narrow.labelBits == 101
#guard Kriterion.CRT.laneCount == 101
#guard Entry.table.convBlocks == convCount
#guard convCount == 2885
#guard Narrow.packedBytes convCount == 36424
#guard Kriterion.CRT.SimMachine.CrtStage1.convPad == 7
#guard bn254Moduli.size == 84
#guard !(bn254Moduli.contains 17)
#guard bn254Table.product == BudgetData.M
#guard 2 * bn254Table.wrapBound ≤ bn254Table.product + 1
#guard 2 * bn254Table.product ≤ 256 ^ 78
#guard (bn254Moduli.toList.filter fun m => selectiveWidth0 m == 9).length == 26
#guard Entry.joinCount == 1415
#guard Entry.pinCount == 198
#guard Kriterion.CRT.SimMachine.CrtStage1.pieces.length == 43393

/-! ### Bytes by encoding: zero and maximal public values, and a packed round trip -/

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

/-- A varied label vector: label `i` is `i · (2^90 + 12345)` (mod `2^101`). -/
def variedLabels : Vector Narrow.Label convCount := Vector.ofFn fun i => BitVec.ofNat 101 (i.val * (2 ^ 90 + 12345))

#eval (Entry.Wire.encoding.encode zeroPublic).length
#guard (Entry.Wire.encoding.encode zeroPublic).length == expectedBytes
#guard (Entry.Wire.encoding.encode maxPublic).length == expectedBytes
#guard (Entry.Wire.encoding.decode (Entry.Wire.encoding.encode zeroPublic)).isSome
#guard (Entry.Wire.encoding.decode (Entry.Wire.encoding.encode maxPublic)).isSome
#guard ((Narrow.packedLabels convCount).decode ((Narrow.packedLabels convCount).encode variedLabels)).map
    (fun r => r.1.toList.map BitVec.toNat) == some (variedLabels.toList.map BitVec.toNat)
#guard ((Narrow.packedLabels convCount).decode ((Narrow.packedLabels convCount).encode (Vector.replicate convCount (-1)))).map
    (fun r => r.1.toList.all fun l => l.toNat == 2 ^ 101 - 1) == some true
