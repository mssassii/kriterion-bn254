/-
Narrow simulator audit: symbolic machine cost and the independently compiled replay/source
interfaces. Run after building its imports. This never evaluates the unrolled machine.
No chunk joins (branch nojoins-p): the wire omits the 2 · 222 chunk joins (45,156 pieces); the chunk
trees read the never-written zero cell `Layout.zeroJoin`, retained as zero from the zero start RAM.
-/
import Proof.Simulator.CRT.MachineCost
import Proof.Simulator.CRT.ReplayMachine
import Proof.Simulator.CRT.Stage1Final
import Proof.Simulator.CRT.Stage1Retained
import Proof.Simulator.CRT.SourceCells
import Lean

open Kriterion.CRT.SimMachine

#check CrtTop.crt_within
#check Machine.agree_replay
#check CrtSource.sourceHolds_extract

#print axioms CrtTop.crt_within
#print axioms Machine.agree_replay
#print axioms CrtConv.pin_bits
#print axioms CrtWire.wire_bits
#print axioms CrtSource.sourceHolds_extract

run_cmd do
  for name in [`Kriterion.CRT.SimMachine.CrtTop.crt_within,
      `Kriterion.CRT.SimMachine.Machine.agree_replay,
      `Kriterion.CRT.SimMachine.agree_castBlock,
      `Kriterion.CRT.SimMachine.agree_treeEvalBlock,
      `Kriterion.CRT.SimMachine.agree_conversionReplay,
      `Kriterion.CRT.SimMachine.exec_truthWordBlock,
      `Kriterion.CRT.SimMachine.CrtConv.pin_bits,
      `Kriterion.CRT.SimMachine.CrtWire.wire_bits,
      `Kriterion.CRT.SimMachine.CrtSource.sourceHolds_extract,
      `Kriterion.CRT.SimMachine.CrtConv.conv_bits,
      `Kriterion.CRT.SimMachine.CrtPieces.pieces_bits,
      `Kriterion.CRT.SimMachine.SourceCells.chunkJoins,
      `Kriterion.CRT.SimMachine.CrtValidStart.validStart_of_prefix,
      `Kriterion.CRT.SimMachine.CrtStage1Retained.retained_finalOf,
      `Kriterion.CRT.SimMachine.CrtStage1Retained.retained,
      `Kriterion.CRT.SimMachine.CrtSize.size_program] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "Narrow simulator axiom check passed: only propext, Classical.choice, Quot.sound"

example : Kriterion.CRT.SimMachine.CrtStage1.pieces.length = 45156 := CrtSize.pieces_length
-- every chunk-tree join cell of both coordinates is the zero cell
example (κ c n : Nat) : (Machine.coordCells κ).chunkJoin c n = Layout.zeroJoin := rfl
example : Kriterion.CRT.labelBits = 104 := rfl
example : Kriterion.CRT.laneCount = 104 := rfl
example : Kriterion.CRT.castAnswers 14 = 6 := by decide +kernel

-- Recompute only this small arithmetic expression, never the program.
example : 276 + 182 + 2 * (1450 - 222) + 400 * 104 + 642 = 45156 := by decide +kernel
-- the sampler still draws all 1,450 join cells per coordinate (222 unread, unserialized chunk-join cells)
example : 2 * (1450 + 1728) * 104 = 661024 := by decide +kernel
example : (508 + 2) * 128 = 65280 := by decide +kernel
