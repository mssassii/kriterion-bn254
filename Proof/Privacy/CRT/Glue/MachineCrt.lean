/-
**The machine row of the CRT entry at the concrete machine** (H11): `CrtMachineHop crtEntry` at
the machine around the replay `Machine.replay`, from the glue (`MachineGlue.crtEntry_machine`).

| input of `crtEntry_machine` | source |
|---|---|
| bounded samplers | `CrtBounded.samplers` |
| extract | the source the stage-1 cells hold, `CrtSource.extract memory.ram` |
| `Stage1Law` | named hypothesis `stage1` (`Stage1Law.lean`) |
| `Stage2NoneArm` | `noneArm`: `stage2NoneArm_of_keys`, from the key cells of every stage-1 result |
| `Stage2SomeArm` | `someArm`: `machine_stage2_some` (the prefix, then the valid arm) and `CrtValid.valid_law`, from `ValidStart` at the memory the prefix leaves |
| `SamplerCutoff` | `SamplerBounds.samplerCutoff_crt` |

The machine is stated at a generic cost proof `within` (`sim within`); `CrtTop.crtSimulator` is
`sim crt_within` by definition (`crtSimulator_eq`), and `crtEntry_machineHop_of` states the row there.
-/

import Proof.Privacy.CRT.Glue.Machine
import Proof.Simulator.CRT.SamplerBounds
import Proof.Simulator.CRT.Stage2Invalid
import Proof.Simulator.CRT.Stage2Start
import Proof.Simulator.CRT.Stage2Valid
import Proof.Simulator.CRT.ValidStart
import Proof.Simulator.CRT.Machine

namespace Kriterion.CRT.SimMachine.MachineCrt

open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit Kriterion.ArgoMAC
  Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.CRT.Privacy (lazyReader)
open Kriterion.CRT.Privacy.Instance (crtEntry)

noncomputable section

/-- The cost bound of the machine around `Machine.replay`. -/
abbrev Within : Prop :=
  Design.totalCost (CrtTop.blocks (Design.Block.ofProg CrtStage1.program) (Design.Block.ofProg Machine.replay)) ≤
    2 ^ 60

/-- **The CRT machine** around `Machine.replay`, at a cost proof. -/
abbrev sim (within : Within) : Simulator :=
  CrtTop.machine (Design.Block.ofProg CrtStage1.program) (Design.Block.ofProg Machine.replay) Machine.replay within

/-- **The read-back of the retained memory** (`CrtTop.crtExtract`). -/
abbrev extract : LawShape.Extract crtEntry := CrtTop.crtExtract

/-- **Every stage-1 result starts the valid arm**: on a defined output, the memory the stage-2 prefix leaves satisfies
`ValidStart` for the extracted source (`validStart_of_prefix`, from what stage 1
leaves). -/
def StartsValid (simulator : Simulator) : Prop :=
  ∀ (field : FieldCertificate) (_group : @GroupCertificate field) (parameter : ℕ),
    letI := Fintype.ofFinite Empty
    letI := Fintype.ofFinite Empty
    letI := Classical.decEq Empty
    letI := Classical.decEq Empty
    ∀ result, some result ∈ ((LawShape.machineAbstract (FI := Empty) (EI := Empty) crtEntry.encoding crtEntry.bytes
        simulator).stage1 parameter LazyOracle.empty).support →
      ∀ (input : AffineInput) (target : Point) (middle : Memory),
        Request.prefixProgram.memSem (CrtStage2Start.stage2Start result.2.1.memory input (some target)) =
          PMF.pure (some middle) →
        CrtValid.ValidStart (Entry.publish (CrtSource.extract result.2.1.memory.ram)) input
          (Entry.labels (CrtSource.extract result.2.1.memory.ram) input) target middle

variable (within : Within)

/-- **The invalid arm** at the machine, from the key cells of every stage-1 result. -/
theorem noneArm
    (keysOf : CrtStage2Invalid.Stage1Holds crtEntry (sim within)
      (fun memory => CrtStage2Invalid.KeyCellsHold memory.ram)) :
    MachineGlue.Stage2NoneArm crtEntry (sim within) CrtBounded.samplers extract :=
  CrtStage2Invalid.stage2NoneArm_of_keys _ _ Machine.replay within CrtBounded.samplers keysOf

/-- **The valid arm** at the machine, from `ValidStart` at the memory the prefix leaves. -/
theorem someArm (startsOf : StartsValid (sim within)) :
    MachineGlue.Stage2SomeArm crtEntry (sim within) CrtBounded.samplers extract := by
  intro field group parameter result member input target oracle
  obtain ⟨middle, run, machineSide⟩ := @CrtStage2Start.machine_stage2_some field Empty Empty
    (Fintype.ofFinite Empty) (Fintype.ofFinite Empty) (Classical.decEq Empty) (Classical.decEq Empty)
    (Design.Block.ofProg CrtStage1.program) (Design.Block.ofProg Machine.replay) Machine.replay within rfl rfl
    result.2.1 input target oracle _ crtEntry.encoding crtEntry.bytes
  have start := startsOf field group parameter result member input target middle run
  have validSide := @CrtValid.valid_law field group Empty Empty (Fintype.ofFinite Empty) (Fintype.ofFinite Empty)
    (Classical.decEq Empty) (Classical.decEq Empty) (CrtSource.extract result.2.1.memory.ram) input target middle
    start oracle
  rw [machineSide]
  exact validSide.symm

/-- **H11 at the machine**, from the stage-1 law, the key cells and the valid arm's start. -/
theorem machineHop_of (stage1 : LawShape.Stage1Law crtEntry (sim within) CrtBounded.samplers extract)
    (keysOf : CrtStage2Invalid.Stage1Holds crtEntry (sim within)
      (fun memory => CrtStage2Invalid.KeyCellsHold memory.ram))
    (startsOf : StartsValid (sim within)) :
    Privacy.CrtMachineHop crtEntry (sim within) :=
  MachineGlue.crtEntry_machine (sim within) CrtBounded.samplers extract stage1 (noneArm within keysOf)
    (someArm within startsOf) SamplerBounds.samplerCutoff_crt

/-- **H11 at the machine from one stage-1 support fact**: a property `R` of every retained memory that gives the key
cells and the valid arm's start. -/
theorem machineHop_of_holds (R : Memory → Prop)
    (stage1 : LawShape.Stage1Law crtEntry (sim within) CrtBounded.samplers extract)
    (holds : CrtStage2Invalid.Stage1Holds crtEntry (sim within) R)
    (keys : ∀ memory, R memory → CrtStage2Invalid.KeyCellsHold memory.ram)
    (starts : ∀ memory, R memory → ∀ (field : FieldCertificate) (input : AffineInput) (target : Point)
      (middle : Memory),
      Request.prefixProgram.memSem (CrtStage2Start.stage2Start memory input (some target)) = PMF.pure (some middle) →
      CrtValid.ValidStart (Entry.publish (CrtSource.extract memory.ram)) input
        (Entry.labels (CrtSource.extract memory.ram) input) target middle) :
    Privacy.CrtMachineHop crtEntry (sim within) :=
  machineHop_of within stage1
    (fun field group parameter result member => keys _ (holds field group parameter result member))
    (fun field group parameter result member input target middle run =>
      starts _ (holds field group parameter result member) field input target middle run)

/-- **H11 at the machine from the stage-1 law and the retained-memory facts**: `CrtValidStart.Retained` of every stage-1 result gives the key cells (the invalid arm) and, through
`validStart_of_support`, the valid arm's start. -/
theorem machineHop_of_retained
    (stage1 : LawShape.Stage1Law crtEntry (sim within) CrtBounded.samplers extract)
    (retainedOf : CrtStage2Invalid.Stage1Holds crtEntry (sim within) CrtValidStart.Retained) :
    Privacy.CrtMachineHop crtEntry (sim within) :=
  machineHop_of within stage1
    (fun field group parameter result member => (retainedOf field group parameter result member).keys)
    (fun field group parameter =>
      CrtValidStart.validStart_of_support _ _ Machine.replay within retainedOf field group parameter)

/-- **H11 for the CRT entry at the CRT simulator**, from the stage-1 law and the retained-memory facts of every
stage-1 result. -/
theorem crtEntry_machineHop_of
    (stage1 : LawShape.Stage1Law crtEntry CrtTop.crtSimulator CrtBounded.samplers CrtTop.crtExtract)
    (retainedOf : CrtStage2Invalid.Stage1Holds crtEntry CrtTop.crtSimulator CrtValidStart.Retained) :
    Privacy.CrtMachineHop crtEntry CrtTop.crtSimulator := by
  rw [CrtTop.crtSimulator_eq] at stage1 retainedOf ⊢
  exact machineHop_of_retained CrtTop.crt_within stage1 retainedOf

end

end Kriterion.CRT.SimMachine.MachineCrt
