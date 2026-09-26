/-
**The protocol's parse of a stage-2 result**, shared by the valid arm (`Stage2Valid.lean`) and the
stage-2 start (`Stage2Start.lean`): release-r1's `finishK`, generic in the oracle's indices.
-/

import Proof.Simulator.Semantics
import Security.AdaptivePrivacy

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine GarbledCircuit Kriterion.ArgoMAC.PlanB.SimMachine

namespace CrtValid

/-- **The protocol's parse of a stage-2 result**: the 508 labels read off the response stack. -/
noncomputable def finishK {FI EI : Type} (final : Option (Memory × OState FI EI)) :
    PMF (Option (LamportSignature × OState FI EI)) :=
  match final with
  | none => PMF.pure none
  | some (last, updated) => PMF.pure ((SimulatorProtocol.words 128 508 (last.bits 3)).map
      fun labels => (labels, updated))

end CrtValid

end Kriterion.CRT.SimMachine
