/-
The machine-run steps the CRT machine's protocol runs are built from (`Proof/Simulator/CRT/Runs.lean`):
a halt (`run_halt`), a pop of a known bit (`run_pop_bit`), the memory after the tag pops (`Top.afterTag`),
and the start configuration (`Top.atPc_zero`).
-/

import Proof.Simulator.Semantics

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine

/-- A configuration's memory. -/
theorem atPc_memory (machine : Simulator) (pc : Nat) (memory : Memory) :
    (atPc machine pc memory).memory = memory := rfl

theorem optionT_mk_pure_some {α : Type} (value : α) :
    (OptionT.mk (PMF.pure (some value)) : OptionT PMF α) = pure value := rfl

section Halt

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- A halt stops the run, charging one. -/
theorem run_halt (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size)
    (code : codeAt machine pc = NInstr.halt.toInstr machine.size) (fuel : Nat)
    (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    machine.run (fuel + 1) (atPc machine pc memory) oracle =
      PMF.pure (some (atPc machine pc memory, oracle, 1)) := by
  have located := code_atPc machine inside memory
  rw [code] at located
  have arith := arithmetic_code_of machine (atPc machine pc memory).pc.isLt located
  rw [run_succ]
  unfold Simulator.step
  rw [located]
  dsimp only [NInstr.toInstr]
  unfold BoundedMachine.step
  rw [arith]
  simp [PMF.pure_map, PMF.pure_bind]

/-- A pop of a known bit. -/
theorem run_pop_bit (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size)
    {stack : Fin 4} {empty onZero onOne : Nat}
    (code : codeAt machine pc = (NInstr.pop stack empty onZero onOne).toInstr machine.size)
    (fuel : Nat) (memory : Memory) (bit : Bool) (rest : List Bool)
    (top : memory.bits stack = bit :: rest) (oracle : OState FixedIndex EncIndex) :
    machine.run (fuel + 1) (atPc machine pc memory) oracle =
      (machine.run fuel (atPc machine (if bit then onOne else onZero)
          { memory with bits := Function.update memory.bits stack rest }) oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) := by
  rw [run_succ, step_pop machine inside stack empty onZero onOne code memory oracle, PMF.pure_bind]
  simp only [top]

end Halt

namespace Top

/-- The memory after the tag pops. -/
def afterTag (memory : Memory) (rest : List Bool) : Memory :=
  { memory with bits := Function.update memory.bits 0 rest }

theorem atPc_zero (machine : Simulator) (memory : Memory) :
    (⟨0, memory⟩ : Configuration (machine.size + 1)) = atPc machine 0 memory := by
  simp only [atPc, label]
  congr

end Top

end Kriterion.ArgoMAC.PlanB.SimMachine
