/- Opus W1 audit: the hidden hop's window term charged at its proved size and modulus 41 traded for 17 (618-bit
records). Independent expectations: Scratch/opus_check_w1.py (evidence/w1-model.log). Historical audits keep their
original expectations. -/
import Submission
import Benchmark
import Lean

open Kriterion Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry

#print axioms Submission.solution

run_cmd do
  for name in [`Submission.solution, `Kriterion.CRT.EntryCorrect.perfectCorrectness,
      `Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy, `Kriterion.CRT.Privacy.chainError_budget,
      `Kriterion.CRT.Privacy.chain_oracleAdaptivePrivacy, `Kriterion.CRT.Privacy.smudgeError_le,
      `Kriterion.CRT.Privacy.hiddenWindowError_le, `Kriterion.CRT.Privacy.Flags.crtCurveWindowMass,
      `Kriterion.CRT.BudgetData.chainConstant_le_two, `Kriterion.CRT.Entry.Wire.encoding_length,
      `Kriterion.CRT.Entry.garbleBudget_eq, `Kriterion.CRT.Entry.evaluateBudget_eq,
      `Kriterion.CRT.bn254Table_record_fits_bits, `Kriterion.CRT.SliceC.bn254_correctTable,
      `Kriterion.CRT.Privacy.ConvReach.rows_ok] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "axiom check passed: only propext, Classical.choice, Quot.sound"

#check @Kriterion.CRT.Privacy.chainError_budget
#check @Kriterion.CRT.Privacy.hiddenWindowError_le

#eval Kriterion.Benchmark.ciphertextBytes Submission.solution
#eval Kriterion.Benchmark.garbleQueries Submission.solution
#eval Kriterion.Benchmark.evaluateQueries Submission.solution

def expectedBytes : Nat := 125450
def expectedGarble : Nat := 1060976
def expectedEvaluate : Nat := 1054152

#guard Kriterion.Benchmark.ciphertextBytes Submission.solution == expectedBytes
#guard Kriterion.Benchmark.garbleQueries Submission.solution == expectedGarble
#guard Kriterion.Benchmark.evaluateQueries Submission.solution == expectedEvaluate
#guard Entry.ciphertextBytes == expectedBytes
#guard Entry.garbleBudget == expectedGarble
#guard Entry.evaluateBudget == expectedEvaluate
#guard Entry.garbleBudget + 500 ≤ 1759967
#guard Entry.evaluateBudget + 500 ≤ 1055879
#guard Entry.table.convBlocks == convCount
#guard convCount == 2881

/-! ### The table -/

#guard bn254Moduli.size == 84
#guard bn254Moduli.contains 17
#guard !(bn254Moduli.contains 41)
#guard bn254Moduli.toList == (BudgetData.moduli)
#guard bn254Table.product == BudgetData.M
#guard 2 * bn254Table.wrapBound ≤ bn254Table.product + 1
#guard 2 * bn254Table.product ≤ 2 ^ 618
#guard !(2 * bn254Table.product ≤ 2 ^ 617)
#guard Nat.log2 bn254Table.product == 616
#guard recordBits == 618

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
  recX := Vector.replicate xCount ⟨2 ^ 618 - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩
  recY := Vector.replicate yCount ⟨2 ^ 618 - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩

#eval (Entry.Wire.encoding.encode zeroPublic).length
#guard (Entry.Wire.encoding.encode zeroPublic).length == expectedBytes
#guard (Entry.Wire.encoding.encode maxPublic).length == expectedBytes
#guard (Entry.Wire.encoding.decode (Entry.Wire.encoding.encode zeroPublic)).isSome
#guard (Entry.Wire.encoding.decode (Entry.Wire.encoding.encode maxPublic)).isSome
#guard match Entry.Wire.encoding.decode (Entry.Wire.encoding.encode maxPublic ++ [137, 42]) with
  | none => false
  | some (decoded, tail) => Entry.Wire.encoding.encode decoded == Entry.Wire.encoding.encode maxPublic && tail == [137, 42]

example (value : Entry.Public) (tail : List (Fin 256)) :
    Entry.Wire.encoding.decode (Entry.Wire.encoding.encode value ++ tail) = some (value, tail) :=
  Entry.Wire.encoding.decode_encode value tail

#guard Entry.publicBits == 1003595
#guard Entry.paddingBits == 5
#guard Entry.publicBits + Entry.paddingBits == 8 * expectedBytes

/-! ### Schedule and simulator -/

#guard Narrow.labelBits == 101
#guard (bn254Moduli.toList.filter fun m => selectiveWidth0 m == 9).length == 26
#guard Entry.joinCount == 1413
#guard Entry.pinCount == 198
#guard Kriterion.CRT.SimMachine.CrtStage1.pieces.length ==
  3 + 2 * PlanB.digitCount + 2 * PlanB.digitCount + xCount + yCount +
    2 * (Entry.joinCount - (254 - Entry.table.chunkCount) + Entry.pinCount * Narrow.labelBits)
#guard Kriterion.CRT.SimMachine.CrtStage1.pieces.length == 43387
#print axioms Kriterion.CRT.SliceC.bn254_selectiveFacts
#print axioms Kriterion.CRT.SimMachine.CrtTop.crtSimulator

/-! ### The privacy constant -/

example : Kriterion.CRT.Privacy.crtHiddenCharge =
    1 / 2 ^ 101 + 1 / ((Kriterion.BN254.baseFieldModulus : ℝ) - 1) :=
  Kriterion.CRT.Privacy.crtHiddenCharge_eq
#print axioms Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy
