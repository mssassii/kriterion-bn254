/-
**The laws of the emission blocks** that stage 1's serializer is built from: `emitWord address width` pushes the
low `width` bits of `RAM[address]`, least significant on top (`memSem_emitWord`), `emitZero width` pushes `width`
zero bits, and `Emits` composes them. The CRT serializer (`Proof/Simulator/CRT/Stage1Serial.lean`,
`Stage1Record.lean`) is proved with these.
-/

import Proof.Simulator.Stage1Cells

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks

noncomputable section

/-- `after` is `before` with `bits` pushed on top of stack `3`, and nothing else changed except
registers. -/
def Emits (before after : Memory) (bits : List Bool) : Prop :=
  after.ram = before.ram ∧ after.bits 3 = bits ++ before.bits 3 ∧
    ∀ stack, stack ≠ 3 → after.bits stack = before.bits stack

theorem Emits.trans {first middle last : Memory} {bits bits' : List Bool}
    (one : Emits first middle bits) (two : Emits middle last bits') :
    Emits first last (bits' ++ bits) :=
  ⟨two.1.trans one.1, by rw [two.2.1, one.2.1, List.append_assoc], fun stack other => by
    rw [two.2.2 stack other, one.2.2 stack other]⟩

theorem Emits.refl (memory : Memory) : Emits memory memory [] :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

section Serializer

variable [FieldCertificate]

omit [FieldCertificate] in
theorem emitStep_ram (memory : Memory) (bit : Nat) : (emitStep memory bit).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem emitStep_bits_other (memory : Memory) (bit : Nat) (stack : Fin 4) (other : stack ≠ 3) :
    (emitStep memory bit).bits stack = memory.bits stack := by
  simp only [emitStep, pushOn, setReg, Function.update_of_ne other]

omit [FieldCertificate] in
theorem emitFold_ram (memory : Memory) (width steps : Nat) :
    (emitFold memory width steps).ram = memory.ram := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [emitFold, emitStep_ram, ih]

omit [FieldCertificate] in
theorem emitFold_bits_other (memory : Memory) (width steps : Nat) (stack : Fin 4)
    (other : stack ≠ 3) : (emitFold memory width steps).bits stack = memory.bits stack := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [emitFold, emitStep_bits_other _ _ _ other, ih]

/-- **One emitted word.** -/
theorem memSem_emitWord (address width : Nat) (small : width ≤ 256) (memory : Memory) :
    ∃ after, (emitWord address width).memSem memory = PMF.pure (some after) ∧
      Emits memory after (bitRun (memory.ram (word address)) 0 width) := by
  refine ⟨emitFold (setReg (setReg memory rAddr (word address)) rAcc
    (memory.ram (word address))) width width, ?_, ?_, ?_, ?_⟩
  · unfold emitWord loadAt
    rw [memSem_seq]
    simp only [cst, Prog.memSem, Op.memSem, PMF.pure_bind, kleisli]
    rw [memSem_emitBits width small]
    simp only [setReg_registers, if_pos rfl, ite_true]
    rfl
  · rw [emitFold_ram]
    rfl
  · rw [emitFold_stack3, setReg_registers, if_pos rfl]
    rfl
  · intro stack other
    rw [emitFold_bits_other _ _ _ _ other]
    rfl

/-- **Emitted zero bits.** -/
theorem memSem_emitZero (width : Nat) (small : width ≤ 256) (memory : Memory) :
    ∃ after, (emitZero width).memSem memory = PMF.pure (some after) ∧
      Emits memory after (bitRun (word 0) 0 width) := by
  refine ⟨emitFold (setReg memory rAcc (word 0)) width width, ?_, ?_, ?_, ?_⟩
  · unfold emitZero
    rw [memSem_seq]
    simp only [cst, Prog.memSem, Op.memSem, PMF.pure_bind, kleisli]
    rw [memSem_emitBits width small]
  · rw [emitFold_ram]
    rfl
  · rw [emitFold_stack3, setReg_registers, if_pos rfl]
    rfl
  · intro stack other
    rw [emitFold_bits_other _ _ _ _ other]
    rfl

/-- **A block of emitting programs**, `block top, block (top − 1), …` run in that order: the
stack reads their bits from `top + 1 − count` upward. -/
theorem memSem_emitRep (block : Nat → Prog) (bits : (Word → Word) → Nat → List Bool)
    (law : ∀ (n : Nat) (memory : Memory), ∃ after, (block n).memSem memory = PMF.pure (some after) ∧
      Emits memory after (bits memory.ram n)) (top : Nat) :
    ∀ (count : Nat), count ≤ top + 1 → ∀ memory : Memory,
      ∃ after, (Prog.rep count fun index => block (top - index)).memSem memory =
          PMF.pure (some after) ∧
        Emits memory after (List.ofFn fun index : Fin count =>
          bits memory.ram (top + 1 - count + index.val)).flatten
  | 0, _, memory => ⟨memory, by rw [Prog.rep]; rfl, by
      simpa using Emits.refl memory⟩
  | count + 1, bound, memory => by
      obtain ⟨middle, run, emits⟩ := memSem_emitRep block bits law top count (by omega) memory
      obtain ⟨last, step, emitsLast⟩ := law (top - count) middle
      refine ⟨last, ?_, ?_⟩
      · rw [Prog.rep, memSem_seq, run, PMF.pure_bind]
        exact step
      · have joined := emits.trans emitsLast
        rw [emits.1] at joined
        convert joined using 1
        rw [List.ofFn_succ, List.flatten_cons]
        congr 2
        · congr 1
          simp only [Fin.val_zero]
          omega
        · congr 1
          funext index
          congr 1
          simp only [Fin.val_succ]
          omega

/-- **A block of emitted words**, addresses `top, top − 1, …` pushed in that order: the stack
reads the words from address `top + 1 − count` upward. -/
theorem memSem_emitBlock (width : Nat) (small : width ≤ 256) (top : Nat) :
    ∀ (count : Nat), count ≤ top + 1 → ∀ memory : Memory,
      ∃ after, (Prog.rep count fun index => emitWord (top - index) width).memSem memory =
          PMF.pure (some after) ∧
        Emits memory after (List.ofFn fun index : Fin count =>
          bitRun (memory.ram (word (top + 1 - count + index.val))) 0 width).flatten
  | 0, _, memory => ⟨memory, by rw [Prog.rep]; rfl, by
      simpa using Emits.refl memory⟩
  | count + 1, bound, memory => by
      obtain ⟨middle, run, emits⟩ := memSem_emitBlock width small top count (by omega) memory
      obtain ⟨last, step, emitsLast⟩ := memSem_emitWord (top - count) width small middle
      refine ⟨last, ?_, ?_⟩
      · rw [Prog.rep, memSem_seq, run, PMF.pure_bind]
        exact step
      · have joined := emits.trans emitsLast
        rw [emits.1] at joined
        convert joined using 1
        rw [List.ofFn_succ, List.flatten_cons]
        congr 2
        · congr 3
          simp only [Fin.val_zero]
          omega
        · congr 1
          funext index
          congr 3
          simp only [Fin.val_succ]
          omega

end Serializer

end

end Kriterion.ArgoMAC.PlanB.SimMachine
