/-
**The machine row of the CRT entry** (H11, `CrtMachineHop`).

`LawShape.machineLaw_of` gives `CrtMachineHop E simulator` from `Stage1Law`, `Stage2Law` and `SamplerCutoff`.
`Stage2Law` splits on the output into two arms (`stage2Law_of_arms`):

* `Stage2NoneArm`: at an undefined output the machine's stage 2 is route M's stage 2 of the extracted source
  (the labels only);
* `Stage2SomeArm`: at a target the same, through the replay, the rows, the solve, the preimages, the programs and the
  emission.

Both arms are stated for every stage-1 configuration in the support of the machine's stage 1, exactly as
`Stage2Law` quantifies. `crtEntry_machine` is the row at `crtEntry` from the named parts.
-/

import Proof.Simulator.CRT.LawShape
import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.SimMachine.MachineGlue

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC
open Kriterion.CRT.Privacy (lazyReader)
open Kriterion.CRT.SimMachine.LawShape

noncomputable section

variable {FI EI : Type} (E : Privacy.CrtEntry FI EI)

/-- **The invalid arm of `Stage2Law`**: at an undefined output. -/
def Stage2NoneArm [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers E)
    (extract : Extract E) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ),
    letI := Fintype.ofFinite FI
    letI := Fintype.ofFinite EI
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    ∀ result, some result ∈ ((machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage1 parameter
        LazyOracle.empty).support →
      ∀ input oracle,
        (routeMWith (E.view field group) (bounded field group) lazyReader).stage2
            (extract field group result.2.1.memory) input none oracle =
          (machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage2 result.2.1 input none oracle

/-- **The valid arm of `Stage2Law`**: at a target. -/
def Stage2SomeArm [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers E)
    (extract : Extract E) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ),
    letI := Fintype.ofFinite FI
    letI := Fintype.ofFinite EI
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    ∀ result, some result ∈ ((machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage1 parameter
        LazyOracle.empty).support →
      ∀ input (target : Point) oracle,
        (routeMWith (E.view field group) (bounded field group) lazyReader).stage2
            (extract field group result.2.1.memory) input (some target) oracle =
          (machineAbstract (FI := FI) (EI := EI) E.encoding E.bytes simulator).stage2 result.2.1 input (some target)
            oracle

/-- **`Stage2Law` from its two arms.** -/
theorem stage2Law_of_arms [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers E)
    (extract : Extract E) (none_arm : Stage2NoneArm E simulator bounded extract)
    (some_arm : Stage2SomeArm E simulator bounded extract) : Stage2Law E simulator bounded extract := by
  intro field group parameter result member input output oracle
  cases output with
  | none => exact none_arm field group parameter result member input oracle
  | some target => exact some_arm field group parameter result member input target oracle

/-- **The machine row from its named parts** (generic in the entry). -/
theorem machine_of_parts [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers E)
    (extract : Extract E) (stage1 : Stage1Law E simulator bounded extract)
    (none_arm : Stage2NoneArm E simulator bounded extract) (some_arm : Stage2SomeArm E simulator bounded extract)
    (cutoff : SamplerCutoff E bounded) : Privacy.CrtMachineHop E simulator :=
  machineLaw_of E simulator bounded extract stage1 (stage2Law_of_arms E simulator bounded extract none_arm some_arm)
    cutoff

/-- **H11 for the entry, from its named parts.** -/
theorem crtEntry_machine (simulator : BoundedMachine.Simulator) (bounded : BoundedSamplers Privacy.Instance.crtEntry)
    (extract : Extract Privacy.Instance.crtEntry) (stage1 : Stage1Law Privacy.Instance.crtEntry simulator bounded extract)
    (none_arm : Stage2NoneArm Privacy.Instance.crtEntry simulator bounded extract)
    (some_arm : Stage2SomeArm Privacy.Instance.crtEntry simulator bounded extract)
    (cutoff : SamplerCutoff Privacy.Instance.crtEntry bounded) :
    Privacy.CrtMachineHop Privacy.Instance.crtEntry simulator :=
  machine_of_parts Privacy.Instance.crtEntry simulator bounded extract @stage1 @none_arm @some_arm @cutoff

end

end Kriterion.CRT.SimMachine.MachineGlue
