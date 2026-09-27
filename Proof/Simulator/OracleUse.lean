/-
Which oracle instructions a block issues.

* `Prog.NoOracle`: a program with no oracle operation; its law is an oracle-free law on memory (`Prog.memSem`) and
  leaves the lazy oracle untouched (`sem_noOracle`). The samplers, the emissions, the stage-2 prefix and the invalid
  arm are `NoOracle`.
* `Prog.OpsSatisfy`: every operation of a program satisfies a predicate (`ValidOracle`: the query and program shapes
  on the operand registers `R12 … R15`).
-/

import Proof.Simulator.Runs
import Construction.Simulator.Stage2
import Construction.Simulator.Stage1
-- `Construction.PGS.Index` brings the Mathlib instances `Sampling.uniform_product`'s `classical` simp relies on.
import Construction.PGS.Index

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

/-! ### Oracle-free programs -/

/-- Does an operation touch the oracle? -/
def Op.isOracle : Op → Bool
  | .query .. | .lookup .. | .program .. => true
  | _ => false

/-- A program with no oracle operation. -/
def Prog.NoOracle : Prog → Prop
  | .op operation => operation.isOracle = false
  | .popBit _ _ | .skip _ | .abort _ => True
  | .seq first second => first.NoOracle ∧ second.NoOracle
  | .ite _ whenSet whenClear => whenSet.NoOracle ∧ whenClear.NoOracle

section MemoryLaw

variable [BN254.FieldCertificate]

/-- The law of a straight-line operation on memory alone (oracle operations abort). -/
noncomputable def Op.memSem (operation : Op) (memory : Memory) : PMF (Option Memory) :=
  match operation with
  | .constant target value => PMF.pure (some (setReg memory target value))
  | .arith operation target left right =>
      PMF.pure (some (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right))))
  | .load target address =>
      PMF.pure (some (setReg memory target (memory.ram (memory.registers address))))
  | .store address source =>
      PMF.pure (some (storeRam memory (memory.registers address) (memory.registers source)))
  | .push stack bit => PMF.pure (some (pushOn memory stack bit))
  | .pushBit stack source => PMF.pure (some (pushOn memory stack ((memory.registers source).getLsbD 0)))
  | .coin stack => (PMF.uniformOfFintype Bool).bind fun bit => PMF.pure (some (pushOn memory stack bit))
  | .pointAdd target left right =>
      match readPoint memory.registers left, readPoint memory.registers right with
      | some a, some b => PMF.pure (some (writePointMem memory target (a + b)))
      | _, _ => PMF.pure none
  | .query .. | .lookup .. | .program .. => PMF.pure none

/-- The law of an oracle-free program on memory alone. -/
noncomputable def Prog.memSem : Prog → Memory → PMF (Option Memory)
  | .op operation, memory => operation.memSem memory
  | .popBit stack target, memory => PMF.pure (some (popInto memory stack target))
  | .skip _, memory => PMF.pure (some memory)
  | .abort _, _ => PMF.pure none
  | .seq first second, memory => (first.memSem memory).bind fun result => match result with
      | none => PMF.pure none
      | some next => second.memSem next
  | .ite source whenSet whenClear, memory =>
      if memory.registers source = 0 then whenClear.memSem memory else whenSet.memSem memory

variable {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
  [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **An oracle-free program neither reads nor changes the oracle.** -/
theorem sem_noOracle : ∀ (program : Prog), program.NoOracle →
    ∀ (memory : Memory) (oracle : OState FixedIndex EncIndex),
      program.sem memory oracle = (program.memSem memory).map (Option.map fun next => (next, oracle))
  | .op operation, free, memory, oracle => by
      cases operation with
      | query => simp [Prog.NoOracle, Op.isOracle] at free
      | lookup => simp [Prog.NoOracle, Op.isOracle] at free
      | program => simp [Prog.NoOracle, Op.isOracle] at free
      | pointAdd target left right =>
          simp only [Prog.sem, Prog.memSem, Op.sem, Op.memSem]
          cases readPoint memory.registers left <;> cases readPoint memory.registers right <;>
            simp [PMF.pure_map]
      | coin stack => simp [Prog.sem, Prog.memSem, Op.sem, Op.memSem, PMF.map_bind, PMF.pure_map]
      | _ => simp [Prog.sem, Prog.memSem, Op.sem, Op.memSem, PMF.pure_map]
  | .popBit _ _, _, memory, oracle => by simp [Prog.sem, Prog.memSem, PMF.pure_map]
  | .skip _, _, memory, oracle => by simp [Prog.sem, Prog.memSem, PMF.pure_map]
  | .abort _, _, memory, oracle => by simp [Prog.sem, Prog.memSem, PMF.pure_map]
  | .seq first second, free, memory, oracle => by
      simp only [Prog.sem, Prog.memSem, andThen, PMF.map_bind]
      rw [sem_noOracle first free.1 memory oracle, PMF.bind_map]
      congr 1
      funext result
      cases result with
      | none => simp [PMF.pure_map]
      | some next => simp only [Function.comp_apply, Option.map_some]; exact sem_noOracle second free.2 next oracle
  | .ite source whenSet whenClear, free, memory, oracle => by
      simp only [Prog.sem, Prog.memSem]
      split
      · exact sem_noOracle whenClear free.2 memory oracle
      · exact sem_noOracle whenSet free.1 memory oracle

end MemoryLaw

theorem noOracle_rep (count : Nat) (body : Nat → Prog)
    (free : ∀ index, index < count → (body index).NoOracle) : (Prog.rep count body).NoOracle := by
  induction count with
  | zero => rw [Prog.rep]; trivial
  | succ count ih =>
      rw [Prog.rep]
      exact ⟨ih fun index bound => free index (by omega), free count (by omega)⟩

theorem noOracle_zeroRegs (registers : List Register) : (zeroRegs registers).NoOracle := by
  induction registers with
  | nil => trivial
  | cons register rest ih => exact ⟨rfl, ih⟩

theorem noOracle_sampleWord (width : Nat) : (sampleWord width).NoOracle :=
  ⟨rfl, noOracle_rep _ _ fun _ _ => ⟨⟨rfl, trivial⟩, rfl, rfl⟩⟩

theorem noOracle_bounded (width : Nat) (test use : Prog) (count : Nat)
    (freeTest : test.NoOracle) (freeUse : use.NoOracle) :
    (bounded width test count use).NoOracle :=
  ⟨⟨rfl, rfl, noOracle_rep _ _ fun _ _ =>
    ⟨noOracle_sampleWord width, freeTest, rfl, rfl, rfl, rfl, rfl⟩⟩, freeUse, trivial⟩

theorem noOracle_emitWord (address width : Nat) : (emitWord address width).NoOracle :=
  ⟨⟨rfl, rfl⟩, noOracle_rep _ _ fun _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem noOracle_emitZero (width : Nat) : (emitZero width).NoOracle :=
  ⟨rfl, noOracle_rep _ _ fun _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem noOracle_parseWord (address : Nat) : (Request.parseWord address).NoOracle :=
  ⟨rfl, noOracle_rep _ _ (fun _ _ => ⟨trivial, rfl, rfl, rfl⟩), rfl, rfl⟩

/-- **The stage-2 prefix has no oracle instruction.** -/
theorem prefix_noOracle : Request.prefixProgram.NoOracle :=
  ⟨⟨noOracle_parseWord _, noOracle_parseWord _, trivial, ⟨rfl, rfl⟩, trivial, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
      ⟨⟨noOracle_parseWord _, noOracle_parseWord _⟩, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
      noOracle_zeroRegs _⟩,
    ⟨noOracle_rep _ _ fun _ _ => ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩,
      noOracle_zeroRegs _⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- **The invalid arm has no oracle instruction.** -/
theorem invalid_noOracle : Stage2.invalid.NoOracle :=
  noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _

/-! ### The valid arm's oracle operations -/

/-- The oracle operations the valid arm may issue: fixed forward (`0`), EncPRF forward (`2`) and
hash (`4`) queries, and fixed forward (`0`) programs, on the fixed operands `R12 … R15`; no
lookup. -/
def ValidOracle : Op → Prop
  | .query kind index input first second =>
      (kind = 0 ∨ kind = 2 ∨ kind = 4) ∧ index = rIndex ∧ input = rInput ∧ first = rFirst ∧
        second = rSecond
  | .program kind index input first second =>
      kind = 0 ∧ index = rIndex ∧ input = rInput ∧ first = rFirst ∧ second = rSecond
  | .lookup .. => False
  | _ => True

/-- Every operation of a program satisfies `allowed`. -/
def Prog.OpsSatisfy (allowed : Op → Prop) : Prog → Prop
  | .op operation => allowed operation
  | .popBit _ _ | .skip _ | .abort _ => True
  | .seq first second => first.OpsSatisfy allowed ∧ second.OpsSatisfy allowed
  | .ite _ whenSet whenClear => whenSet.OpsSatisfy allowed ∧ whenClear.OpsSatisfy allowed

theorem opsSatisfy_of_noOracle {allowed : Op → Prop}
    (plain : ∀ operation : Op, operation.isOracle = false → allowed operation) :
    ∀ program : Prog, program.NoOracle → program.OpsSatisfy allowed
  | .op operation, free => plain operation free
  | .popBit _ _, _ | .skip _, _ | .abort _, _ => trivial
  | .seq first second, free =>
      ⟨opsSatisfy_of_noOracle plain first free.1, opsSatisfy_of_noOracle plain second free.2⟩
  | .ite _ whenSet whenClear, free =>
      ⟨opsSatisfy_of_noOracle plain whenSet free.1, opsSatisfy_of_noOracle plain whenClear free.2⟩

theorem validOracle_plain (operation : Op) (plain : operation.isOracle = false) :
    ValidOracle operation := by
  cases operation <;> simp_all [ValidOracle, Op.isOracle]

theorem opsSatisfy_rep {allowed : Op → Prop} (count : Nat) (body : Nat → Prog)
    (each : ∀ index, index < count → (body index).OpsSatisfy allowed) :
    (Prog.rep count body).OpsSatisfy allowed := by
  induction count with
  | zero => rw [Prog.rep]; trivial
  | succ count ih =>
      rw [Prog.rep]
      exact ⟨ih fun index bound => each index (by omega), each count (by omega)⟩

end Kriterion.ArgoMAC.PlanB.SimMachine
