/-
**The CRT simulator** (M7): the concrete machine `crtSimulator` around release-r1's replay, its cost bound
`crt_within` (from the per-block bounds `CrtSize.size_program`, `CostFacts.replay_within` and
`Design.blocks_totalCost_le`), and the read-back `crtExtract` of the retained memory.

Every proof here passes block sizes through generic `rfl` lemmas (`ofProg_size`, `ofProg_cost`). A defeq
check on a concrete program's `size` or `cost` would make the kernel evaluate it.
-/

import Proof.Simulator.CRT.Stage1Size
import Proof.Simulator.CRT.ReplayCost
import Proof.Simulator.CRT.LawShape
import Proof.Simulator.CRT.Stage1Source
import Proof.Privacy.CRT.EntryInstance
import Construction.Simulator.CRT.Simulator

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

namespace CrtTop

/-- A program's block has the program's size (generic, so the kernel never sees a concrete program). -/
theorem ofProg_size (program : Prog) : (Design.Block.ofProg program).size = program.size := rfl

/-- A program's block has the program's cost. -/
theorem ofProg_cost (program : Prog) : (Design.Block.ofProg program).cost = program.cost := rfl

/-- **The CRT machine fits**: `size + 1 + firstFuel + secondFuel ≤ 2 ^ 60`. -/
theorem crt_within : Design.totalCost (blocks (Design.Block.ofProg CrtStage1.program)
    (Design.Block.ofProg Machine.replay)) ≤ 2 ^ 60 :=
  Design.blocks_totalCost_le _ _
    ⟨(ofProg_size _).trans_le CrtSize.size_program, (ofProg_cost _).trans_le CrtSize.cost_program⟩
    ⟨(ofProg_size _).trans_le CostFacts.replay_within.1, (ofProg_cost _).trans_le CostFacts.replay_within.2⟩

/-- **The CRT simulator.** -/
def crtSimulator : Simulator := crtMachine Machine.replay crt_within

/-- The simulator as the generic machine of `Runs.lean` (by definition). -/
theorem crtSimulator_eq : crtSimulator = machine (Design.Block.ofProg CrtStage1.program)
    (Design.Block.ofProg Machine.replay) Machine.replay crt_within := rfl

/-- **The read-back of the retained memory**: the source the stage-1 cells hold. -/
def crtExtract : LawShape.Extract Privacy.Instance.crtEntry := fun _ _ memory => CrtSource.extract memory.ram

end CrtTop

end Kriterion.CRT.SimMachine
