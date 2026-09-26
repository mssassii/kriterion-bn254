/-
**The two protocol runs of the CRT machine** (M7), reduced to the laws of its structured programs (release-r1's
`Placement.lean` and `Runs.lean`, ported to `CrtTop.machine`).

* `stage1_run`: from the stage-1 request, the machine pops the tag, runs `CrtStage1.program` by its law and halts;
  a non-aborting run costs exactly `firstFuel`;
* `stage2_run`: from the stage-2 request, it pops the tag, runs the prefix, branches on `rFlag`, runs the selected
  arm and halts, within `secondFuel`.
-/

import Proof.Simulator.Runs
import Construction.Simulator.CRT.Simulator

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

namespace CrtTop

variable (s1 r : Design.Block) (replay : Prog) (within : Design.totalCost (blocks s1 r) ≤ 2 ^ 60)
  (size1 : s1.size = CrtStage1.program.size) (cost1 : s1.cost = CrtStage1.program.cost)
  (sizeR : r.size = replay.size) (costR : r.cost = replay.cost)

theorem machine_size : (machine s1 r replay within).size = Design.size (blocks s1 r) := rfl
theorem machine_firstFuel : (machine s1 r replay within).firstFuel = Design.firstFuel (blocks s1 r) := rfl
theorem machine_secondFuel : (machine s1 r replay within).secondFuel = Design.secondFuel (blocks s1 r) := rfl

theorem codeAt_machine {pc : Nat} (inside : pc ≤ Design.size (blocks s1 r)) :
    codeAt (machine s1 r replay within) pc = (code s1 r replay pc).toInstr (machine s1 r replay within).size := by
  rw [codeAt_of_lt _ (Nat.lt_succ_of_le inside)]
  simp only [machine, assemble, Vector.getElem_ofFn]

/-! ### The blocks' sizes and costs -/

omit within in
theorem prefix_size : (blocks s1 r).prefixBlock.size = Request.prefixProgram.size := by
  unfold blocks; rw [Design.blocks_prefix]; rfl
omit within in
theorem prefix_cost : (blocks s1 r).prefixBlock.cost = Request.prefixProgram.cost := by
  unfold blocks; rw [Design.blocks_prefix]; rfl
omit within in
theorem invalid_size : (blocks s1 r).invalid.size = Stage2.invalid.size := by
  unfold blocks; rw [Design.blocks_invalid]; rfl
omit within in
theorem invalid_cost : (blocks s1 r).invalid.cost = Stage2.invalid.cost := by
  unfold blocks; rw [Design.blocks_invalid]; rfl

omit within in
include sizeR in
theorem valid_size : Design.validSize (blocks s1 r) = (validArm replay).size := by
  unfold Design.validSize validArm blocks
  rw [Design.blocks_rows, Design.blocks_solve, Design.blocks_preimages, Design.blocks_programs, Design.blocks_emit]
  simp only [Design.Block.ofProg, Prog.seqList, Prog.size_seq, Prog.size]
  simp only [Design.blocks]
  omega

omit within in
include costR in
theorem valid_cost : Design.validCost (blocks s1 r) = (validArm replay).cost := by
  unfold Design.validCost validArm blocks
  rw [Design.blocks_rows, Design.blocks_solve, Design.blocks_preimages, Design.blocks_programs, Design.blocks_emit]
  simp only [Design.Block.ofProg, Prog.seqList, Prog.cost_seq, Prog.cost]
  simp only [Design.blocks]
  omega

omit within in
theorem invalid_le_valid : (blocks s1 r).invalid.cost ≤ Design.validCost (blocks s1 r) := by
  unfold Design.validCost blocks Design.blocks
  simp only
  omega

omit within in
/-- The layout facts, as linear arithmetic over the block sizes. -/
theorem layout :
    Design.stage1Halt (blocks s1 r) = 2 + (blocks s1 r).stage1.size ∧
      Design.stage2Base (blocks s1 r) = 3 + (blocks s1 r).stage1.size ∧
      Design.branchAt (blocks s1 r) = 3 + (blocks s1 r).stage1.size + (blocks s1 r).prefixBlock.size ∧
      Design.invalidBase (blocks s1 r) = 4 + (blocks s1 r).stage1.size + (blocks s1 r).prefixBlock.size ∧
      Design.invalidHalt (blocks s1 r) = 4 + (blocks s1 r).stage1.size + (blocks s1 r).prefixBlock.size +
        (blocks s1 r).invalid.size ∧
      Design.validBase (blocks s1 r) = 5 + (blocks s1 r).stage1.size + (blocks s1 r).prefixBlock.size +
        (blocks s1 r).invalid.size ∧
      Design.validHalt (blocks s1 r) = 5 + (blocks s1 r).stage1.size + (blocks s1 r).prefixBlock.size +
        (blocks s1 r).invalid.size + Design.validSize (blocks s1 r) ∧
      Design.rejectAt (blocks s1 r) = 6 + (blocks s1 r).stage1.size + (blocks s1 r).prefixBlock.size +
        (blocks s1 r).invalid.size + Design.validSize (blocks s1 r) ∧
      Design.size (blocks s1 r) = 6 + (blocks s1 r).stage1.size + (blocks s1 r).prefixBlock.size +
        (blocks s1 r).invalid.size + Design.validSize (blocks s1 r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Design.stage1Halt, Design.stage2Base, Design.branchAt, Design.invalidBase, Design.invalidHalt,
      Design.validBase, Design.validHalt, Design.rejectAt, Design.size, Design.stage1Base] <;> omega

/-! ### Where the blocks sit -/

include size1 in
theorem placed_stage1 : Placed (machine s1 r replay within) CrtStage1.program Design.stage1Base := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  have size1' : (blocks s1 r).stage1.size = CrtStage1.program.size := size1
  have base : Design.stage1Base = 2 := rfl
  refine ⟨by rw [machine_size, ← size1']; omega, fun offset inside => ?_⟩
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.stage1Base + offset ≠ 0 by omega), if_neg (show Design.stage1Base + offset ≠ 1 by omega),
    if_pos (show Design.stage1Base + offset < Design.stage1Halt (blocks s1 r) by omega),
    show Design.stage1Base + offset - Design.stage1Base = offset by omega]

theorem placed_prefix : Placed (machine s1 r replay within) Request.prefixProgram (Design.stage2Base (blocks s1 r)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  have sizeP := prefix_size s1 r
  refine ⟨by rw [machine_size, ← sizeP]; omega, fun offset inside => ?_⟩
  rw [← sizeP] at inside
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.stage2Base (blocks s1 r) + offset ≠ 0 by omega),
    if_neg (show Design.stage2Base (blocks s1 r) + offset ≠ 1 by omega),
    if_neg (show ¬ Design.stage2Base (blocks s1 r) + offset < Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show Design.stage2Base (blocks s1 r) + offset ≠ Design.stage1Halt (blocks s1 r) by omega),
    if_pos (show Design.stage2Base (blocks s1 r) + offset < Design.branchAt (blocks s1 r) by omega),
    show Design.stage2Base (blocks s1 r) + offset - Design.stage2Base (blocks s1 r) = offset by omega]

theorem placed_invalid : Placed (machine s1 r replay within) Stage2.invalid (Design.invalidBase (blocks s1 r)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  have sizeI := invalid_size s1 r
  refine ⟨by rw [machine_size, ← sizeI]; omega, fun offset inside => ?_⟩
  rw [← sizeI] at inside
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.invalidBase (blocks s1 r) + offset ≠ 0 by omega),
    if_neg (show Design.invalidBase (blocks s1 r) + offset ≠ 1 by omega),
    if_neg (show ¬ Design.invalidBase (blocks s1 r) + offset < Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show Design.invalidBase (blocks s1 r) + offset ≠ Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show ¬ Design.invalidBase (blocks s1 r) + offset < Design.branchAt (blocks s1 r) by omega),
    if_neg (show Design.invalidBase (blocks s1 r) + offset ≠ Design.branchAt (blocks s1 r) by omega),
    if_pos (show Design.invalidBase (blocks s1 r) + offset < Design.invalidHalt (blocks s1 r) by omega),
    show Design.invalidBase (blocks s1 r) + offset - Design.invalidBase (blocks s1 r) = offset by omega]

include sizeR in
theorem placed_valid : Placed (machine s1 r replay within) (validArm replay) (Design.validBase (blocks s1 r)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  have sizeV := valid_size s1 r replay sizeR
  refine ⟨by rw [machine_size, ← sizeV]; omega, fun offset inside => ?_⟩
  rw [← sizeV] at inside
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.validBase (blocks s1 r) + offset ≠ 0 by omega),
    if_neg (show Design.validBase (blocks s1 r) + offset ≠ 1 by omega),
    if_neg (show ¬ Design.validBase (blocks s1 r) + offset < Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show Design.validBase (blocks s1 r) + offset ≠ Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show ¬ Design.validBase (blocks s1 r) + offset < Design.branchAt (blocks s1 r) by omega),
    if_neg (show Design.validBase (blocks s1 r) + offset ≠ Design.branchAt (blocks s1 r) by omega),
    if_neg (show ¬ Design.validBase (blocks s1 r) + offset < Design.invalidHalt (blocks s1 r) by omega),
    if_neg (show Design.validBase (blocks s1 r) + offset ≠ Design.invalidHalt (blocks s1 r) by omega),
    if_pos (show Design.validBase (blocks s1 r) + offset < Design.validHalt (blocks s1 r) by omega),
    show Design.validBase (blocks s1 r) + offset - Design.validBase (blocks s1 r) = offset by omega]

/-! ### The hand-placed slots -/

theorem code_zero : codeAt (machine s1 r replay within) 0 =
    (NInstr.pop 0 (Design.rejectAt (blocks s1 r)) 1 (Design.rejectAt (blocks s1 r))).toInstr
      (machine s1 r replay within).size := by
  rw [codeAt_machine s1 r replay within (by rw [(layout s1 r).2.2.2.2.2.2.2.2]; omega)]
  unfold code
  rw [if_pos rfl]

theorem code_one : codeAt (machine s1 r replay within) 1 =
    (NInstr.pop 0 (Design.rejectAt (blocks s1 r)) Design.stage1Base (Design.stage2Base (blocks s1 r))).toInstr
      (machine s1 r replay within).size := by
  rw [codeAt_machine s1 r replay within (by rw [(layout s1 r).2.2.2.2.2.2.2.2]; omega)]
  unfold code
  rw [if_neg (show (1 : Nat) ≠ 0 by omega), if_pos rfl]

theorem code_stage1Halt : codeAt (machine s1 r replay within) (Design.stage1Halt (blocks s1 r)) =
    NInstr.halt.toInstr (machine s1 r replay within).size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.stage1Halt (blocks s1 r) ≠ 0 by omega),
    if_neg (show Design.stage1Halt (blocks s1 r) ≠ 1 by omega),
    if_neg (show ¬ Design.stage1Halt (blocks s1 r) < Design.stage1Halt (blocks s1 r) by omega), if_pos rfl]

theorem code_branch : codeAt (machine s1 r replay within) (Design.branchAt (blocks s1 r)) =
    (NInstr.branch rFlag (Design.invalidBase (blocks s1 r)) (Design.validBase (blocks s1 r))).toInstr
      (machine s1 r replay within).size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.branchAt (blocks s1 r) ≠ 0 by omega),
    if_neg (show Design.branchAt (blocks s1 r) ≠ 1 by omega),
    if_neg (show ¬ Design.branchAt (blocks s1 r) < Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show Design.branchAt (blocks s1 r) ≠ Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show ¬ Design.branchAt (blocks s1 r) < Design.branchAt (blocks s1 r) by omega), if_pos rfl]

theorem code_invalidHalt : codeAt (machine s1 r replay within) (Design.invalidHalt (blocks s1 r)) =
    NInstr.halt.toInstr (machine s1 r replay within).size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.invalidHalt (blocks s1 r) ≠ 0 by omega),
    if_neg (show Design.invalidHalt (blocks s1 r) ≠ 1 by omega),
    if_neg (show ¬ Design.invalidHalt (blocks s1 r) < Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show Design.invalidHalt (blocks s1 r) ≠ Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show ¬ Design.invalidHalt (blocks s1 r) < Design.branchAt (blocks s1 r) by omega),
    if_neg (show Design.invalidHalt (blocks s1 r) ≠ Design.branchAt (blocks s1 r) by omega),
    if_neg (show ¬ Design.invalidHalt (blocks s1 r) < Design.invalidHalt (blocks s1 r) by omega), if_pos rfl]

theorem code_validHalt : codeAt (machine s1 r replay within) (Design.validHalt (blocks s1 r)) =
    NInstr.halt.toInstr (machine s1 r replay within).size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  rw [codeAt_machine s1 r replay within (by omega)]
  unfold code
  rw [if_neg (show Design.validHalt (blocks s1 r) ≠ 0 by omega),
    if_neg (show Design.validHalt (blocks s1 r) ≠ 1 by omega),
    if_neg (show ¬ Design.validHalt (blocks s1 r) < Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show Design.validHalt (blocks s1 r) ≠ Design.stage1Halt (blocks s1 r) by omega),
    if_neg (show ¬ Design.validHalt (blocks s1 r) < Design.branchAt (blocks s1 r) by omega),
    if_neg (show Design.validHalt (blocks s1 r) ≠ Design.branchAt (blocks s1 r) by omega),
    if_neg (show ¬ Design.validHalt (blocks s1 r) < Design.invalidHalt (blocks s1 r) by omega),
    if_neg (show Design.validHalt (blocks s1 r) ≠ Design.invalidHalt (blocks s1 r) by omega),
    if_neg (show ¬ Design.validHalt (blocks s1 r) < Design.validHalt (blocks s1 r) by omega)]

/-! ### The runs -/

section Runs

variable [BN254.FieldCertificate] {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

open Kriterion.ArgoMAC.PlanB.SimMachine.Top (afterTag atPc_zero)

include size1 cost1 in
/-- **Stage 1.** -/
theorem stage1_run (memory : Memory) (rest : List Bool)
    (request : memory.bits 0 = false :: false :: rest) (oracle : OState FI EI) :
    (machine s1 r replay within).run (Design.firstFuel (blocks s1 r)) ⟨0, memory⟩ oracle =
      (CrtStage1.program.sem (afterTag memory rest) oracle).bind fun result => match result with
        | none => PMF.pure none
        | some (final, updated) =>
            PMF.pure (some (atPc (machine s1 r replay within) (Design.stage1Halt (blocks s1 r)) final, updated,
              Design.firstFuel (blocks s1 r))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  have size1' : (blocks s1 r).stage1.size = CrtStage1.program.size := size1
  have cost1' : (blocks s1 r).stage1.cost = CrtStage1.program.cost := cost1
  have fuelIs : Design.firstFuel (blocks s1 r) = (CrtStage1.program.cost + 1) + 1 + 1 := by
    simp only [Design.firstFuel, ← cost1']; omega
  have sizeIs : (machine s1 r replay within).size = Design.size (blocks s1 r) := rfl
  have pop0 := run_pop_bit (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within) (pc := 0) (by omega)
    (code_zero s1 r replay within) (CrtStage1.program.cost + 1 + 1) memory false (false :: rest) request oracle
  have second : ({ memory with bits := Function.update memory.bits 0 (false :: rest) } : Memory).bits 0 =
      false :: rest := by simp only [Function.update_self]
  have pop1 := run_pop_bit (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within) (pc := 1)
    (by rw [sizeIs]; omega) (code_one s1 r replay within) (CrtStage1.program.cost + 1) _ false rest second oracle
  have block := run_placed (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
    CrtStage1.program Design.stage1Base (placed_stage1 s1 r replay within size1)
  have exitIs : Design.stage1Base + CrtStage1.program.size = Design.stage1Halt (blocks s1 r) := by
    rw [← size1']; rfl
  rw [exitIs] at block
  have memoryEq : ({ ({ memory with bits := Function.update memory.bits 0 (false :: rest) } : Memory)
      with bits := Function.update (Function.update memory.bits 0 (false :: rest)) 0 rest } : Memory)
      = afterTag memory rest := by
    simp only [afterTag, Function.update_idem]
  rw [atPc_zero, fuelIs]
  rewrite [pop0]
  simp only [Bool.false_eq_true, if_false]
  rewrite [pop1]
  simp only [Bool.false_eq_true, if_false]
  rewrite [memoryEq, block, PMF.map_bind, PMF.map_bind]
  congr 1
  funext result
  cases result with
  | none => simp only [after, PMF.pure_map, Option.map_none]
  | some result =>
      rcases result with ⟨final, updated⟩
      have haltRun := run_halt (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
        (pc := Design.stage1Halt (blocks s1 r)) (by rw [sizeIs]; omega) (code_stage1Halt s1 r replay within) 0 final
        updated
      simp only [after]
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
      rewrite [haltRun, PMF.pure_map, PMF.pure_map, PMF.pure_map, Option.map_some, Option.map_some,
        Option.map_some]
      show PMF.pure (some (atPc (machine s1 r replay within) (Design.stage1Halt (blocks s1 r)) final, updated,
          1 + CrtStage1.program.cost + 1 + 1)) =
        PMF.pure (some (atPc (machine s1 r replay within) (Design.stage1Halt (blocks s1 r)) final, updated,
          CrtStage1.program.cost + 1 + 1 + 1))
      rw [show 1 + CrtStage1.program.cost + 1 + 1 = CrtStage1.program.cost + 1 + 1 + 1 by omega]

include sizeR costR in
/-- **Stage 2.** The prefix runs, then the arm selected by `rFlag` (the output tag), then halt. -/
theorem stage2_run (memory : Memory) (rest : List Bool)
    (request : memory.bits 0 = false :: true :: rest) (oracle : OState FI EI) :
    (machine s1 r replay within).run (Design.secondFuel (blocks s1 r)) ⟨0, memory⟩ oracle =
      (Request.prefixProgram.sem (afterTag memory rest) oracle).bind fun result => match result with
        | none => PMF.pure none
        | some (middle, midOracle) =>
            if middle.registers rFlag = 0 then
              (Stage2.invalid.sem middle midOracle).bind fun final => match final with
                | none => PMF.pure none
                | some (last, updated) => PMF.pure (some (atPc (machine s1 r replay within)
                    (Design.invalidHalt (blocks s1 r)) last, updated,
                    2 + Request.prefixProgram.cost + 1 + Stage2.invalid.cost + 1))
            else
              ((validArm replay).sem middle midOracle).bind fun final => match final with
                | none => PMF.pure none
                | some (last, updated) => PMF.pure (some (atPc (machine s1 r replay within)
                    (Design.validHalt (blocks s1 r)) last, updated, Design.secondFuel (blocks s1 r))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout s1 r
  have sizeP := prefix_size s1 r
  have costP := prefix_cost s1 r
  have sizeI := invalid_size s1 r
  have costI := invalid_cost s1 r
  have sizeV := valid_size s1 r replay sizeR
  have costV := valid_cost s1 r replay costR
  have small := invalid_le_valid s1 r
  have fuelIs : Design.secondFuel (blocks s1 r) =
      (Request.prefixProgram.cost + ((validArm replay).cost + 1 + 1)) + 1 + 1 := by
    unfold Design.secondFuel
    rw [max_eq_left small, costV, costP]
    omega
  have sizeIs : (machine s1 r replay within).size = Design.size (blocks s1 r) := rfl
  have pop0 := run_pop_bit (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within) (pc := 0) (by omega)
    (code_zero s1 r replay within) (Request.prefixProgram.cost + ((validArm replay).cost + 1 + 1) + 1) memory
    false (true :: rest) request oracle
  have second : ({ memory with bits := Function.update memory.bits 0 (true :: rest) } : Memory).bits 0 =
      true :: rest := by simp only [Function.update_self]
  have pop1 := run_pop_bit (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within) (pc := 1)
    (by rw [sizeIs]; omega) (code_one s1 r replay within)
    (Request.prefixProgram.cost + ((validArm replay).cost + 1 + 1)) _ true rest second oracle
  have block := run_placed (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
    Request.prefixProgram (Design.stage2Base (blocks s1 r)) (placed_prefix s1 r replay within)
  have exitIs : Design.stage2Base (blocks s1 r) + Request.prefixProgram.size = Design.branchAt (blocks s1 r) := by
    rw [← sizeP]; rfl
  rw [exitIs] at block
  have memoryEq : ({ ({ memory with bits := Function.update memory.bits 0 (true :: rest) } : Memory)
      with bits := Function.update (Function.update memory.bits 0 (true :: rest)) 0 rest } : Memory)
      = afterTag memory rest := by
    simp only [afterTag, Function.update_idem]
  rw [atPc_zero, fuelIs]
  rewrite [pop0]
  simp only [Bool.false_eq_true, if_false]
  rewrite [pop1]
  simp only [if_true]
  rewrite [memoryEq, block, PMF.map_bind, PMF.map_bind]
  congr 1
  funext result
  cases result with
  | none => simp only [after, PMF.pure_map, Option.map_none]
  | some result =>
      rcases result with ⟨middle, midOracle⟩
      simp only [after]
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
      have branch := run_branch (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
        (pc := Design.branchAt (blocks s1 r)) (by rw [sizeIs]; omega) rFlag (Design.invalidBase (blocks s1 r))
        (Design.validBase (blocks s1 r)) (code_branch s1 r replay within) ((validArm replay).cost + 1) middle
        midOracle
      rewrite [branch]
      by_cases zero : middle.registers rFlag = 0
      · rewrite [if_pos zero, if_pos zero]
        have arm := run_placed (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
          Stage2.invalid (Design.invalidBase (blocks s1 r)) (placed_invalid s1 r replay within)
        have exitI : Design.invalidBase (blocks s1 r) + Stage2.invalid.size = Design.invalidHalt (blocks s1 r) := by
          rw [← sizeI]; rfl
        rw [exitI] at arm
        rewrite [arm, PMF.map_bind, PMF.map_bind, PMF.map_bind, PMF.map_bind]
        congr 1
        funext final
        cases final with
        | none => simp only [after, PMF.pure_map, Option.map_none]
        | some final =>
            rcases final with ⟨last, updated⟩
            have haltRun := run_halt (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
              (pc := Design.invalidHalt (blocks s1 r)) (by rw [sizeIs]; omega) (code_invalidHalt s1 r replay within)
              ((validArm replay).cost - Stage2.invalid.cost) last updated
            simp only [after]
            rw [if_pos (by omega), show (validArm replay).cost + 1 - Stage2.invalid.cost =
              ((validArm replay).cost - Stage2.invalid.cost) + 1 by omega]
            rewrite [haltRun, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map, Option.map_some,
              Option.map_some, Option.map_some, Option.map_some, Option.map_some]
            show PMF.pure (some (atPc (machine s1 r replay within) (Design.invalidHalt (blocks s1 r)) last, updated,
                1 + Stage2.invalid.cost + 1 + Request.prefixProgram.cost + 1 + 1)) =
              PMF.pure (some (atPc (machine s1 r replay within) (Design.invalidHalt (blocks s1 r)) last, updated,
                2 + Request.prefixProgram.cost + 1 + Stage2.invalid.cost + 1))
            rw [show 1 + Stage2.invalid.cost + 1 + Request.prefixProgram.cost + 1 + 1 =
              2 + Request.prefixProgram.cost + 1 + Stage2.invalid.cost + 1 by omega]
      · rewrite [if_neg zero, if_neg zero]
        have arm := run_placed (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
          (validArm replay) (Design.validBase (blocks s1 r)) (placed_valid s1 r replay within sizeR)
        have exitV : Design.validBase (blocks s1 r) + (validArm replay).size = Design.validHalt (blocks s1 r) := by
          rw [← sizeV]; rfl
        rw [exitV] at arm
        rewrite [arm, PMF.map_bind, PMF.map_bind, PMF.map_bind, PMF.map_bind]
        congr 1
        funext final
        cases final with
        | none => simp only [after, PMF.pure_map, Option.map_none]
        | some final =>
            rcases final with ⟨last, updated⟩
            have haltRun := run_halt (FixedIndex := FI) (EncIndex := EI) (machine s1 r replay within)
              (pc := Design.validHalt (blocks s1 r)) (by rw [sizeIs]; omega) (code_validHalt s1 r replay within) 0
              last updated
            simp only [after]
            rw [if_pos (by omega), Nat.add_sub_cancel_left]
            rewrite [haltRun, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map, Option.map_some,
              Option.map_some, Option.map_some, Option.map_some, Option.map_some]
            show PMF.pure (some (atPc (machine s1 r replay within) (Design.validHalt (blocks s1 r)) last, updated,
                1 + (validArm replay).cost + 1 + Request.prefixProgram.cost + 1 + 1)) =
              PMF.pure (some (atPc (machine s1 r replay within) (Design.validHalt (blocks s1 r)) last, updated,
                Request.prefixProgram.cost + ((validArm replay).cost + 1 + 1) + 1 + 1))
            rw [show 1 + (validArm replay).cost + 1 + Request.prefixProgram.cost + 1 + 1 =
              Request.prefixProgram.cost + ((validArm replay).cost + 1 + 1) + 1 + 1 by omega]

end Runs

end CrtTop

end Kriterion.CRT.SimMachine
