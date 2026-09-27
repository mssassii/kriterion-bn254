/-
Stage 2's invalid arm (`f_k u = none`): emit the `508` selected labels. No oracle instruction. The common prefix
(parse, label selection) is `Request.prefixProgram`; the CRT machine's valid arm is `CrtTop.validArm`
(`Construction/Simulator/CRT/Simulator.lean`).
-/

import Construction.Simulator.Request

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks Prog

namespace Stage2

/-- The arm for an undefined output. -/
def invalid : Prog := Request.emitLabels

theorem size_invalid : invalid.size = labelCount * (2 + 3 * 128) := Request.size_emitLabels
theorem cost_invalid : invalid.cost = labelCount * (2 + 3 * 128) := Request.cost_emitLabels

end Stage2

end Kriterion.ArgoMAC.PlanB.SimMachine
