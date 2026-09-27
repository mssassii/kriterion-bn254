/-
**Stage 2's label emission and request memory**, for the CRT machine's two arms
(`Proof/Simulator/CRT/Stage2Invalid.lean`, `Stage2Valid.lean`):

* `memSem_emitLabels`: `Request.emitLabels` pushes the `508` label runs on stack `3`;
* `labelRuns_words`: the protocol parse of those runs is the label vector;
* `stage2Memory`, `stage2Rest`: the memory stage 2 starts from, and the request after the tag bits.
-/

import Proof.Simulator.Stage2Request

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

section Labels

variable [FieldCertificate]

/-- The `508` label runs, label `0` on top. -/
def labelRuns (ram : Word → Word) : List Bool :=
  (List.ofFn fun index : Fin 508 => bitRun (ram (word (labelBase + index.val))) 0 128).flatten

/-- The labels as blocks. -/
def labelVector (ram : Word → Word) : Vector Block 508 :=
  Vector.ofFn fun index : Fin 508 => BitVec.ofNat 128 (ram (word (labelBase + index.val))).toNat

theorem emitLabels_eq : Request.emitLabels =
    Prog.rep 508 fun index => emitWord (labelBase + 507 - index) 128 := by
  unfold Request.emitLabels labelCount
  rfl

/-- **The label emission.** -/
theorem memSem_emitLabels (memory : Memory) :
    ∃ after, Request.emitLabels.memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits 3 = labelRuns memory.ram ++ memory.bits 3 ∧
      ∀ stack, stack ≠ 3 → after.bits stack = memory.bits stack := by
  obtain ⟨after, run, emits⟩ := memSem_emitBlock 128 (by norm_num) (labelBase + 507) 508
    (by unfold labelBase; omega) memory
  refine ⟨after, by rw [emitLabels_eq]; exact run, emits.1, ?_, emits.2.2⟩
  rw [emits.2.1]
  congr 2

theorem labelRuns_words (ram : Word → Word) :
    SimulatorProtocol.words 128 508 (labelRuns ram) = some (labelVector ram) :=
  words_labelRuns 508 fun index => ram (word (labelBase + index.val))

end Labels

/-! ### The stage-2 run -/

section Run

variable [FieldCertificate]

/-- The memory stage 2 starts from: the retained configuration with the request on stack `0`
and an empty response stack. -/
def stage2Memory (memory : Memory) (input : AffineInput) (output : Option Point) : Memory :=
  { bits := Function.update (Function.update memory.bits 0
      ([false, true] ++ SimulatorProtocol.affine input ++ SimulatorProtocol.output output)) 3 [],
    registers := memory.registers, ram := memory.ram }

/-- The request after the two tag bits. -/
def stage2Rest (input : AffineInput) (output : Option Point) : List Bool :=
  SimulatorProtocol.affine input ++ SimulatorProtocol.output output

theorem stage2Memory_request (memory : Memory) (input : AffineInput) (output : Option Point) :
    (stage2Memory memory input output).bits 0 = false :: true :: stage2Rest input output := by
  simp [stage2Memory, stage2Rest]

theorem affine_lsbs (input : AffineInput) :
    SimulatorProtocol.affine input = lsbs 254 input.x.val ++ lsbs 254 input.y.val := by
  simp only [SimulatorProtocol.affine, bits_eq_lsbs]

theorem coord_small (value : BaseField) : value.val < 2 ^ 254 :=
  lt_trans value.val_lt (by unfold baseFieldModulus; norm_num)

theorem afterTag_request (memory : Memory) (input : AffineInput) (output : Option Point) :
    (Top.afterTag (stage2Memory memory input output) (stage2Rest input output)).bits 0 =
      lsbs 254 input.x.val ++ (lsbs 254 input.y.val ++ SimulatorProtocol.output output) := by
  simp [Top.afterTag, stage2Rest, affine_lsbs]

theorem afterTag_response (memory : Memory) (input : AffineInput) (output : Option Point) :
    (Top.afterTag (stage2Memory memory input output) (stage2Rest input output)).bits 3 = [] := by
  simp [Top.afterTag, stage2Memory]

theorem afterTag_ram (memory : Memory) (input : AffineInput) (output : Option Point) :
    (Top.afterTag (stage2Memory memory input output) (stage2Rest input output)).ram = memory.ram :=
  rfl

end Run

end

end Kriterion.ArgoMAC.PlanB.SimMachine
