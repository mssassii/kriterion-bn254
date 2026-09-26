/-
**The CRT simulator machine** (M7): one closed `BoundedMachine.Simulator`, assembled as release-r1's
(`Construction/Simulator.lean`) from the structured programs of stage 1 (`CrtStage1.program`), the stage-2 prefix
(`Request.prefixProgram`), the invalid arm (`Stage2.invalid`) and the valid arm (`validArm replay`: the replay,
the rows, the collector solve, the preimages with their fourth blocks, the programs, the label emission), at the
layout of `Design.lean`.

The replay program is a parameter, and so is the cost bound `within` (discharged by
`Design.blocks_totalCost_le` from the two blocks' bounds). The hash-only entry needs no ordinals: every query and
program is a hash (kind 4), whose index register is ignored.
-/

import Construction.Simulator.Stage2
import Construction.Simulator.CRT.Design
import Construction.Simulator.CRT.Stage1

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

namespace CrtTop

/-- **The valid arm** around a replay program. -/
def validArm (replay : Prog) : Prog :=
  Prog.seqList [replay, Design.rowsProgram, Solve.solve, Preimages.preimages,
    Programs.programs Preimages.programCells, Request.emitLabels]

/-! The machine is generic in its two blocks' sizes and costs (`stage1Block`, `replayBlock`): every proof about it
works with them as variables, so no kernel check ever computes the size of the stage-1 program or of the replay;
`crtMachine` instantiates them with the programs' own. -/

variable (stage1Block replayBlock : Design.Block) (replay : Prog)

/-- The machine's blocks. -/
def blocks : Design.Blocks := Design.blocks stage1Block replayBlock

/-- **The top-level code**, slot by slot. -/
def code (pc : Nat) : NInstr :=
  let b := blocks stage1Block replayBlock
  if pc = 0 then .pop 0 (Design.rejectAt b) 1 (Design.rejectAt b)
  else if pc = 1 then .pop 0 (Design.rejectAt b) Design.stage1Base (Design.stage2Base b)
  else if pc < Design.stage1Halt b then emit CrtStage1.program Design.stage1Base (pc - Design.stage1Base)
  else if pc = Design.stage1Halt b then .halt
  else if pc < Design.branchAt b then emit Request.prefixProgram (Design.stage2Base b) (pc - Design.stage2Base b)
  else if pc = Design.branchAt b then .branch rFlag (Design.invalidBase b) (Design.validBase b)
  else if pc < Design.invalidHalt b then emit Stage2.invalid (Design.invalidBase b) (pc - Design.invalidBase b)
  else if pc = Design.invalidHalt b then .halt
  else if pc < Design.validHalt b then emit (validArm replay) (Design.validBase b) (pc - Design.validBase b)
  else .halt

theorem size_lt (within : Design.totalCost (blocks stage1Block replayBlock) ≤ 2 ^ 60) :
    Design.size (blocks stage1Block replayBlock) < 2 ^ 256 := by
  unfold Design.totalCost at within
  have : (2 : Nat) ^ 60 < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  omega

/-- **The simulator** at given blocks. -/
def machine (within : Design.totalCost (blocks stage1Block replayBlock) ≤ 2 ^ 60) : Simulator :=
  assemble (Design.size (blocks stage1Block replayBlock)) (code stage1Block replayBlock replay)
    (size_lt stage1Block replayBlock within)
    (Design.firstFuel (blocks stage1Block replayBlock)) (Design.secondFuel (blocks stage1Block replayBlock)) (by
      unfold Design.totalCost at within
      exact within)

/-- **The CRT simulator** around a replay program. -/
def crtMachine (within : Design.totalCost (blocks (Design.Block.ofProg CrtStage1.program)
    (Design.Block.ofProg replay)) ≤ 2 ^ 60) : Simulator :=
  machine (Design.Block.ofProg CrtStage1.program) (Design.Block.ofProg replay) replay within

end CrtTop

end Kriterion.CRT.SimMachine
