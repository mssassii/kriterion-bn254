/-
Symbolic cost certificate for the concrete CRT simulator, independent of the privacy-law
assembly. No concrete unrolled program is evaluated: sizes pass through generic projections.
-/

import Proof.Simulator.CRT.Stage1Size
import Proof.Simulator.CRT.ReplayCost
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

end CrtTop

end Kriterion.CRT.SimMachine
