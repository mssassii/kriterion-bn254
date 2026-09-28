/-
**The CRT machine's design** (M7): the top-level code layout, the two fuels, and the cost bound
`size + 1 + firstFuel + secondFuel ≤ 2 ^ 60`, over the size and cost of each block.

The layout is release-r1's (`Construction/Simulator/Design.lean`), with the valid arm's blocks replaced:

| slots | contents |
|---|---|
| `0, 1` | pop the two protocol tag bits |
| `2 ..` | stage 1 (M2: sample the source, write the Lamport key, serialize `Wire.encoding`), then `halt` |
| next | the stage-2 prefix (release-r1's parse and label selection), then `branch rFlag` |
| next | the invalid arm (release-r1's label emission), then `halt` |
| next | the valid arm: the replay (conversion, body, key, non-collector masks), the rows (release-r1's tail points, Horner and head clamp, the randomiser pairs, the two-scale lifts), the collector solve, the 273 preimages with their fourth blocks, the 546 programs, the label emission; then `halt` |
| last | reject `halt` |

Every block has one cost on every non-aborting path (release-r1's padded `ite`), so a stage that does not abort
halts after exactly its fuel; the second fuel takes the costlier arm.

The replay's and stage 1's sizes and costs are parameters here (their blocks are being written); every other block's
are the machine's own (`blocks_*` below). `totalCost_le` holds whenever the two parameters are below `2 ^ 55`; the
design estimates are about `2 ^ 32` for both.
-/

import Construction.Simulator.Stage2
import Construction.Simulator.Stage1
import Construction.Simulator.CRT.Solve
import Construction.Simulator.CRT.Preimages
import Construction.Simulator.CRT.Programs

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

namespace Design

/-! ### Blocks -/

/-- The size and the cost of one block. -/
structure Block where
  size : Nat
  cost : Nat

/-- A program's size and cost. -/
def Block.ofProg (program : Prog) : Block := ⟨program.size, program.cost⟩

/-- **The machine's blocks**, in code order. -/
structure Blocks where
  stage1 : Block
  prefixBlock : Block
  invalid : Block
  replay : Block
  rows : Block
  solve : Block
  preimages : Block
  programs : Block
  emit : Block

/-- The valid arm's size. -/
def validSize (b : Blocks) : Nat :=
  b.replay.size + b.rows.size + b.solve.size + b.preimages.size + b.programs.size + b.emit.size

/-- The valid arm's cost. -/
def validCost (b : Blocks) : Nat :=
  b.replay.cost + b.rows.cost + b.solve.cost + b.preimages.cost + b.programs.cost + b.emit.cost

/-! ### The top-level layout -/

def stage1Base : Nat := 2
def stage1Halt (b : Blocks) : Nat := stage1Base + b.stage1.size
def stage2Base (b : Blocks) : Nat := stage1Halt b + 1
def branchAt (b : Blocks) : Nat := stage2Base b + b.prefixBlock.size
def invalidBase (b : Blocks) : Nat := branchAt b + 1
def invalidHalt (b : Blocks) : Nat := invalidBase b + b.invalid.size
def validBase (b : Blocks) : Nat := invalidHalt b + 1
def validHalt (b : Blocks) : Nat := validBase b + validSize b
def rejectAt (b : Blocks) : Nat := validHalt b + 1

/-- The code table has `size + 1` slots. -/
def size (b : Blocks) : Nat := rejectAt b

/-- Stage 1: two pops, stage 1, halt. -/
def firstFuel (b : Blocks) : Nat := 2 + b.stage1.cost + 1

/-- Stage 2: two pops, the prefix, the branch, the costlier arm, halt. -/
def secondFuel (b : Blocks) : Nat := 2 + b.prefixBlock.cost + 1 + max (validCost b) b.invalid.cost + 1

/-- **The simulator's charge**, `size + 1 + firstFuel + secondFuel`. -/
def totalCost (b : Blocks) : Nat := size b + 1 + firstFuel b + secondFuel b

/-- Every block's size and cost are at most `bound`. -/
def Blocks.Within (b : Blocks) (bound : Nat) : Prop :=
  ∀ block ∈ [b.stage1, b.prefixBlock, b.invalid, b.replay, b.rows, b.solve, b.preimages, b.programs, b.emit],
    block.size ≤ bound ∧ block.cost ≤ bound

/-- The charge is at most `17` times the largest block, plus `14`. -/
theorem totalCost_le_of (b : Blocks) (bound : Nat) (within : b.Within bound) :
    totalCost b ≤ 17 * bound + 14 := by
  have h := fun block (member : block ∈ [b.stage1, b.prefixBlock, b.invalid, b.replay, b.rows, b.solve,
      b.preimages, b.programs, b.emit]) => within block member
  have s1 := h b.stage1 (by simp)
  have s2 := h b.prefixBlock (by simp)
  have s3 := h b.invalid (by simp)
  have s4 := h b.replay (by simp)
  have s5 := h b.rows (by simp)
  have s6 := h b.solve (by simp)
  have s7 := h b.preimages (by simp)
  have s8 := h b.programs (by simp)
  have s9 := h b.emit (by simp)
  unfold totalCost size rejectAt validHalt validBase invalidHalt invalidBase branchAt stage2Base stage1Halt
    stage1Base firstFuel secondFuel validSize validCost
  have : max (b.replay.cost + b.rows.cost + b.solve.cost + b.preimages.cost + b.programs.cost + b.emit.cost)
      b.invalid.cost ≤ 6 * bound := max_le (by omega) (by omega)
  omega

/-- **The cost bound**, whenever every block is below `2 ^ 55`. -/
theorem totalCost_le (b : Blocks) (within : b.Within (2 ^ 55)) : totalCost b ≤ 2 ^ 60 := by
  have := totalCost_le_of b _ within
  omega

/-! ### The blocks the machine already has -/

theorem size_solvePrefix : Solve.solvePrefix.size = 5 := rfl
theorem cost_solvePrefix : Solve.solvePrefix.cost = 5 := rfl
theorem size_rowX (d : Nat) : (Solve.rowX d).size = 23 := rfl
theorem cost_rowX (d : Nat) : (Solve.rowX d).cost = 23 := rfl
theorem size_rowY (d : Nat) : (Solve.rowY d).size = 29 := rfl
theorem cost_rowY (d : Nat) : (Solve.rowY d).cost = 29 := rfl
theorem size_rowZ (d : Nat) : (Solve.rowZ d).size = 9 := rfl
theorem cost_rowZ (d : Nat) : (Solve.rowZ d).cost = 9 := rfl

/-- One digit of the solve (row by row: a single `rfl` on the whole digit makes `whnf` time out). -/
theorem size_solveDigit (d : Nat) : (Solve.solveDigit d).size = 66 := by
  simp only [Solve.solveDigit, Prog.seqList, Prog.size_seq, size_solvePrefix, size_rowX, size_rowY, size_rowZ,
    Prog.size]

theorem cost_solveDigit (d : Nat) : (Solve.solveDigit d).cost = 66 := by
  simp only [Solve.solveDigit, Prog.seqList, Prog.cost_seq, cost_solvePrefix, cost_rowX, cost_rowY, cost_rowZ,
    Prog.cost]

theorem size_solve : Solve.solve.size = 91 * 66 := Prog.size_rep _ _ _ fun _ _ => size_solveDigit _
theorem cost_solve : Solve.solve.cost = 91 * 66 := Prog.cost_rep _ _ _ fun _ _ => cost_solveDigit _

theorem size_preimageSite (d c : Nat) : (Preimages.preimageSite d c).size = 236623 + (6 + 7 * 128) := by
  simp only [Preimages.preimageSite, Preimages.fourthCoin, Prog.size_seq, Opening.size_preimageOne,
    Stage1.size_wordCell]

theorem cost_preimageSite (d c : Nat) : (Preimages.preimageSite d c).cost = 169548 + (6 + 5 * 128) := by
  simp only [Preimages.preimageSite, Preimages.fourthCoin, Prog.cost_seq, Opening.cost_preimageOne,
    Stage1.cost_wordCell]

theorem size_preimages : Preimages.preimages.size = 91 * (3 * (236623 + (6 + 7 * 128))) :=
  Prog.size_rep _ _ _ fun _ _ => Prog.size_rep _ _ _ fun _ _ => size_preimageSite _ _

theorem cost_preimages : Preimages.preimages.cost = 91 * (3 * (169548 + (6 + 5 * 128))) :=
  Prog.cost_rep _ _ _ fun _ _ => Prog.cost_rep _ _ _ fun _ _ => cost_preimageSite _ _

/-- The rows: release-r1's tail points, Horner and head clamp, lambdas and lifts. -/
def rowsProgram : Prog := Prog.seqList [Opening.tail, Opening.horner, Opening.lambdas, Opening.lifts]

theorem size_rows : rowsProgram.size = 90 * 589865 + (3 + 90 * 397 + 439) + 91 * (2 * 457743) + 91 * 33 := by
  simp only [rowsProgram, Prog.seqList, Prog.size_seq, Opening.size_tail, Opening.size_horner,
    Opening.size_lambdas, Opening.size_lifts, Prog.size]

theorem cost_rows : rowsProgram.cost = 90 * 459290 + (3 + 90 * 397 + 415) + 91 * (2 * 327692) + 91 * 33 := by
  simp only [rowsProgram, Prog.seqList, Prog.cost_seq, Opening.cost_tail, Opening.cost_horner,
    Opening.cost_lambdas, Opening.cost_lifts, Prog.cost]

/-- **The blocks**, with the replay and stage 1 as parameters. -/
def blocks (stage1 replay : Block) : Blocks where
  stage1 := stage1
  prefixBlock := ⟨9692 + (labelCount * 11 + 4) + 5, 5109 + (labelCount * 11 + 4) + 5⟩
  invalid := ⟨labelCount * (2 + 3 * 128), labelCount * (2 + 3 * 128)⟩
  replay := replay
  rows := ⟨90 * 589865 + (3 + 90 * 397 + 439) + 91 * (2 * 457743) + 91 * 33,
    90 * 459290 + (3 + 90 * 397 + 415) + 91 * (2 * 327692) + 91 * 33⟩
  solve := ⟨91 * 66, 91 * 66⟩
  preimages := ⟨91 * (3 * (236623 + (6 + 7 * 128))), 91 * (3 * (169548 + (6 + 5 * 128)))⟩
  programs := ⟨91 * (3 * 18), 91 * (3 * 18)⟩
  emit := ⟨labelCount * (2 + 3 * 128), labelCount * (2 + 3 * 128)⟩

theorem blocks_prefix (stage1 replay : Block) :
    (blocks stage1 replay).prefixBlock = Block.ofProg Request.prefixProgram := by
  simp only [blocks, Block.ofProg, Request.size_prefixProgram, Request.cost_prefixProgram]

theorem blocks_invalid (stage1 replay : Block) : (blocks stage1 replay).invalid = Block.ofProg Stage2.invalid := by
  simp only [blocks, Block.ofProg, Stage2.size_invalid, Stage2.cost_invalid]

theorem blocks_rows (stage1 replay : Block) : (blocks stage1 replay).rows = Block.ofProg rowsProgram := by
  simp only [blocks, Block.ofProg, size_rows, cost_rows]

theorem blocks_solve (stage1 replay : Block) : (blocks stage1 replay).solve = Block.ofProg Solve.solve := by
  simp only [blocks, Block.ofProg, size_solve, cost_solve]

theorem blocks_preimages (stage1 replay : Block) :
    (blocks stage1 replay).preimages = Block.ofProg Preimages.preimages := by
  simp only [blocks, Block.ofProg, size_preimages, cost_preimages]

theorem blocks_programs (stage1 replay : Block) :
    (blocks stage1 replay).programs = Block.ofProg (Programs.programs Preimages.programCells) := by
  simp only [blocks, Block.ofProg, Programs.size_programs, Programs.cost_programs]

theorem blocks_emit (stage1 replay : Block) : (blocks stage1 replay).emit = Block.ofProg Request.emitLabels := by
  simp only [blocks, Block.ofProg, Request.size_emitLabels, Request.cost_emitLabels]

/-- **The cost bound of the CRT machine**, whenever stage 1 and the replay are below `2 ^ 55`. -/
theorem blocks_totalCost_le (stage1 replay : Block) (stage1Small : stage1.size ≤ 2 ^ 55 ∧ stage1.cost ≤ 2 ^ 55)
    (replaySmall : replay.size ≤ 2 ^ 55 ∧ replay.cost ≤ 2 ^ 55) :
    totalCost (blocks stage1 replay) ≤ 2 ^ 60 := by
  apply totalCost_le
  intro block member
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same | same <;> subst same <;>
    first
    | exact stage1Small
    | exact replaySmall
    | (simp only [labelCount]; constructor <;> norm_num)
    | (constructor <;> norm_num)

end Design

end Kriterion.CRT.SimMachine
