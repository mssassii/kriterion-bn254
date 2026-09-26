/-
**Stage1Law at the final memory**: `CrtStage1Final.finalOf` satisfies
`CrtStage1Law.FinalSpec` on the support of the draws, so the stage-1 kernel and `Stage1Law` hold with it.
-/

import Proof.Simulator.CRT.Stage1Law
import Proof.Simulator.CRT.Stage1Final

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine
open CrtStage1 CrtDraws CrtStored CrtSource CrtTail CrtStage1Final

namespace CrtStage1Law

variable [FieldCertificate]

/-- **`finalOf` is the tail's final memory** on the support of the draws. -/
theorem finalSpec_finalOf (start : Memory) : FinalSpec start (finalOf start) where
  run d member := (finalOf_spec start d (cellsValid_stored start d (drawValid_of_support d member))).1
  bits d member := (finalOf_spec start d (cellsValid_stored start d (drawValid_of_support d member))).2.1
  off d member := (finalOf_spec start d (cellsValid_stored start d (drawValid_of_support d member))).2.2.2.2.2.2
  small d member := (drawValid_of_support d member).small

section Machine

variable {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
  (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)
  (size1 : s1.size = CrtStage1.program.size) (cost1 : s1.cost = CrtStage1.program.cost)

include size1 cost1 in
/-- **The machine's stage-1 kernel**, at `finalOf`. -/
theorem stage1_form (parameter : Nat) (oracle : OState FI EI) :
    (LawShape.machineAbstract (FI := FI) (EI := EI) Privacy.Instance.crtEntry.encoding
        Privacy.Instance.crtEntry.bytes (CrtTop.machine s1 r replay within)).stage1 parameter oracle =
      drawLaw.map (Option.map (β := Privacy.Instance.crtEntry.Public ×
          Configuration ((CrtTop.machine s1 r replay within).size + 1) × OState FI EI) fun d =>
        (Entry.publish (CrtSource.sourceOf d), atPc (CrtTop.machine s1 r replay within)
          (Design.stage1Halt (CrtTop.blocks s1 r)) (finalOf (stage1Start parameter) d), oracle)) :=
  stage1_form_of s1 r replay within size1 cost1 parameter _ (finalSpec_finalOf _) oracle

include size1 cost1 in
/-- **The support of the machine's stage-1 kernel**, at `finalOf`. -/
theorem mem_support_stage1_final (parameter : Nat) (oracle : OState FI EI)
    (result : Privacy.Instance.crtEntry.Public × Configuration ((CrtTop.machine s1 r replay within).size + 1) ×
      OState FI EI)
    (member : some result ∈ ((LawShape.machineAbstract (FI := FI) (EI := EI) Privacy.Instance.crtEntry.encoding
        Privacy.Instance.crtEntry.bytes (CrtTop.machine s1 r replay within)).stage1 parameter oracle).support) :
    ∃ d, some d ∈ drawLaw.support ∧ result = (Entry.publish (CrtSource.sourceOf d),
      atPc (CrtTop.machine s1 r replay within) (Design.stage1Halt (CrtTop.blocks s1 r))
        (finalOf (stage1Start parameter) d), oracle) :=
  mem_support_stage1 s1 r replay within size1 cost1 parameter _ (finalSpec_finalOf _) oracle result member

end Machine

omit [FieldCertificate] in
/-- **`Stage1Law` for the CRT machine** (generic in the two blocks and the cost proof). -/
theorem stage1Law (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)
    (size1 : s1.size = CrtStage1.program.size) (cost1 : s1.cost = CrtStage1.program.cost) :
    LawShape.Stage1Law Privacy.Instance.crtEntry (CrtTop.machine s1 r replay within) CrtBounded.samplers
      (fun _ _ memory => CrtSource.extract memory.ram) :=
  stage1Law_of s1 r replay within size1 cost1 (fun field parameter => @finalOf field (stage1Start parameter))
    (fun field parameter => @finalSpec_finalOf field (stage1Start parameter))

end CrtStage1Law

end Kriterion.CRT.SimMachine
