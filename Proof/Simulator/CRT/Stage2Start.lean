/-
**The start of stage 2 on the CRT machine** (shared by both arms of `LawShape.Stage2Law`).

The machine's stage 2 read as an abstract simulator (`LawShape.machineAbstract`) is the stage-2 prefix (release-r1's
`Request.prefixProgram`: the request parse, the label selection and the flag) followed by the arm the flag selects,
each arm followed by the protocol's parse of the response stack (`CrtValid.finishK`,
`Finish.lean`):

* `machine_stage2`: the general form, from `CrtTop.stage2_run`;
* `machine_stage2_some`: on a defined output the prefix leaves a memory `middle` with the flag set, and stage 2 is the
  valid arm from `middle` followed by the parse;
* `machine_stage2_none`: on an undefined output the flag is clear and stage 2 is the invalid arm (the label emission)
  from `middle` followed by the parse.
-/

import Proof.Simulator.CRT.Runs
import Proof.Simulator.CRT.Finish
import Proof.Simulator.CRT.LawShape
import Proof.Simulator.Stage2Invalid
import Proof.Simulator.Stage2Start
import Proof.Simulator.OracleUse

namespace Kriterion.CRT.SimMachine

namespace CrtStage2Start

open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit Kriterion.ArgoMAC
  Kriterion.ArgoMAC.PlanB.SimMachine

noncomputable section

/-- **The memory the prefix starts from**: the retained memory with the stage-2 request after its two tag bits on
stack `0` and an empty response stack. -/
def stage2Start [FieldCertificate] (memory : Memory) (input : AffineInput) (output : Option Point) : Memory :=
  Top.afterTag (stage2Memory memory input output) (stage2Rest input output)

section Stage2

variable [FieldCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
variable (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (CrtTop.blocks s1 r) ≤ 2 ^ 60)
  (sizeR : r.size = replay.size) (costR : r.cost = replay.cost)

/-- The machine's stage 2 is its run on the stage-2 request followed by the parse. -/
theorem machineAbstract_stage2 (machine : Simulator) (initial : Configuration (machine.size + 1))
    (input : AffineInput) (output : Option Point) (oracle : OState FI EI) {Public : Type}
    (encoding : Encoding Public) (bytes : Nat) :
    (LawShape.machineAbstract (FI := FI) (EI := EI) encoding bytes machine).stage2 initial input output oracle =
      (machine.run machine.secondFuel ⟨0, stage2Memory initial.memory input output⟩ oracle).bind
        fun result => match result with
          | none => PMF.pure none
          | some (encoded, updated, _) => CrtValid.finishK (some (encoded.memory, updated)) := by
  unfold LawShape.machineAbstract
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, CrtValid.finishK, Option.elimM]
  show PMF.bind _ _ = PMF.bind _ _
  refine congrArg (PMF.bind _) (funext fun result => ?_)
  rcases result with _ | ⟨encoded, updated, used⟩
  · rfl
  · show PMF.bind (PMF.pure (SimulatorProtocol.words 128 508 (encoded.memory.bits 3))) _ =
      PMF.pure ((SimulatorProtocol.words 128 508 (encoded.memory.bits 3)).map fun labels => (labels, updated))
    rw [PMF.pure_bind]
    cases SimulatorProtocol.words 128 508 (encoded.memory.bits 3) <;> rfl

include sizeR costR in
/-- **Stage 2 of the machine**: the prefix, then the arm the flag selects, then the parse. -/
theorem machine_stage2 (initial : Configuration ((CrtTop.machine s1 r replay within).size + 1))
    (input : AffineInput) (output : Option Point) (oracle : OState FI EI) {Public : Type}
    (encoding : Encoding Public) (bytes : Nat) :
    (LawShape.machineAbstract (FI := FI) (EI := EI) encoding bytes (CrtTop.machine s1 r replay within)).stage2
        initial input output oracle =
      (Request.prefixProgram.memSem (stage2Start initial.memory input output)).bind fun result => match result with
        | none => PMF.pure none
        | some middle =>
            if middle.registers rFlag = 0 then (Stage2.invalid.sem middle oracle).bind CrtValid.finishK
            else ((CrtTop.validArm replay).sem middle oracle).bind CrtValid.finishK := by
  rw [machineAbstract_stage2, CrtTop.machine_secondFuel,
    CrtTop.stage2_run s1 r replay within sizeR costR (stage2Memory initial.memory input output)
      (stage2Rest input output) (stage2Memory_request initial.memory input output) oracle,
    sem_noOracle _ prefix_noOracle, PMF.bind_map, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun result => ?_)
  cases result with
  | none => simp only [Function.comp_apply, Option.map_none, PMF.pure_bind]
  | some middle =>
      simp only [Function.comp_apply, Option.map_some]
      split
      · rw [PMF.bind_bind]
        refine congrArg (PMF.bind _) (funext fun final => ?_)
        rcases final with _ | ⟨last, updated⟩
        · rw [PMF.pure_bind]
          rfl
        · rw [PMF.pure_bind]
          rfl
      · rw [PMF.bind_bind]
        refine congrArg (PMF.bind _) (funext fun final => ?_)
        rcases final with _ | ⟨last, updated⟩
        · rw [PMF.pure_bind]
          rfl
        · rw [PMF.pure_bind]
          rfl

include sizeR costR in
/-- **Stage 2 on a defined output**: the prefix leaves a memory `middle` (with the flag set), and stage 2 is the valid
arm from `middle` followed by the parse. -/
theorem machine_stage2_some (initial : Configuration ((CrtTop.machine s1 r replay within).size + 1))
    (input : AffineInput) (target : Point) (oracle : OState FI EI) {Public : Type}
    (encoding : Encoding Public) (bytes : Nat) :
    ∃ middle, Request.prefixProgram.memSem (stage2Start initial.memory input (some target)) = PMF.pure (some middle) ∧
      (LawShape.machineAbstract (FI := FI) (EI := EI) encoding bytes (CrtTop.machine s1 r replay within)).stage2
          initial input (some target) oracle =
        ((CrtTop.validArm replay).sem middle oracle).bind CrtValid.finishK := by
  obtain ⟨middle, run, flag, _, _, _⟩ := prefix_middle initial.memory input target
  refine ⟨middle, run, ?_⟩
  rw [machine_stage2 s1 r replay within sizeR costR, show stage2Start initial.memory input (some target) =
    prefixStart initial.memory input target from rfl, run, PMF.pure_bind]
  simp only [if_neg flag]

include sizeR costR in
/-- **Stage 2 on an undefined output**: the prefix leaves a memory `middle` (with the flag clear), and stage 2 is the
invalid arm (the label emission) from `middle` followed by the parse. -/
theorem machine_stage2_none (initial : Configuration ((CrtTop.machine s1 r replay within).size + 1))
    (input : AffineInput) (oracle : OState FI EI) {Public : Type} (encoding : Encoding Public) (bytes : Nat) :
    ∃ middle, Request.prefixProgram.memSem (stage2Start initial.memory input none) = PMF.pure (some middle) ∧
      (LawShape.machineAbstract (FI := FI) (EI := EI) encoding bytes (CrtTop.machine s1 r replay within)).stage2
          initial input none oracle =
        (Stage2.invalid.sem middle oracle).bind CrtValid.finishK := by
  obtain ⟨middle, run, _, _, _, flag⟩ := memSem_prefix (stage2Start initial.memory input none)
    input.x.val input.y.val (coord_small _) (coord_small _) [false, false] false false 0 0
    (by simp [OutBits]) (afterTag_request initial.memory input none)
  have flagZero : middle.registers rFlag = 0 := by rw [flag]; rfl
  refine ⟨middle, run, ?_⟩
  rw [machine_stage2 s1 r replay within sizeR costR, run, PMF.pure_bind]
  simp only [if_pos flagZero]

end Stage2

end

end CrtStage2Start

end Kriterion.CRT.SimMachine
