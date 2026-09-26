/-
**Stage 1's deterministic tail** (M2): the serializer, the true labels, the clears.

`memSem_tail`: from a memory whose cells are in range, the tail pushes the wire of the extracted source on the
response stack, writes `Z_j ⊕ Δ` at every true-label cell, zeroes the record limbs and every register, and leaves
every other cell as it was.
-/

import Proof.Simulator.CRT.Stage1Source

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open CrtStage1 CrtDraws CrtStored CrtConv CrtPieces CrtRecord CrtSerial CrtSource

namespace CrtTail

noncomputable section

/-! ### The true labels -/

/-- The cell of true label `j`. -/
def trueCell (j : Nat) : Nat := keyBase + 2 * j + 1

/-- The true-label cells. -/
def TrueCell (address : Word) : Prop := ∃ j, j < labelCount ∧ address = word (trueCell j)

theorem exec_keyXor (j : Nat) (small : j < labelCount) (memory : Memory) :
    (keyXor j).exec memory = some (storeRam (setReg (setReg (setReg (setReg (setReg (setReg memory rAddr
      (word (keyBase + 2 * j))) rA (memory.ram (word (keyBase + 2 * j)))) rAddr (word (Layout.deltaCell (j / 254))))
      rB (memory.ram (word (Layout.deltaCell (j / 254))))) rA
      (memory.ram (word (keyBase + 2 * j)) ^^^ memory.ram (word (Layout.deltaCell (j / 254))))) rAddr
      (word (trueCell j))) (word (trueCell j))
      (memory.ram (word (keyBase + 2 * j)) ^^^ memory.ram (word (Layout.deltaCell (j / 254))))) := by
  rfl

theorem exec_keyTrue (memory : Memory) :
    ∃ after, keyTrue.exec memory = some after ∧
      (∀ j, j < labelCount → after.ram (word (trueCell j)) =
        memory.ram (word (keyBase + 2 * j)) ^^^ memory.ram (word (Layout.deltaCell (j / 254)))) ∧
      (∀ address, ¬ TrueCell address → after.ram address = memory.ram address) ∧ after.bits = memory.bits := by
  have evenAway : ∀ j k, j < labelCount → k < labelCount → word (keyBase + 2 * j) ≠ word (trueCell k) :=
    fun j k jb kb => word_ne (by unfold keyBase labelCount at *; omega) (by unfold trueCell keyBase labelCount at *; omega)
      (by unfold trueCell; omega)
  have deltaAway : ∀ j k, j < labelCount → k < labelCount → word (Layout.deltaCell (j / 254)) ≠ word (trueCell k) :=
    fun j k jb kb => word_ne (by unfold Layout.deltaCell labelCount at *; omega)
      (by unfold trueCell keyBase labelCount at *; omega) (by unfold Layout.deltaCell trueCell keyBase labelCount at *; omega)
  obtain ⟨after, run, done, off, bitsSame⟩ := Prog.exec_rep keyXor
    (fun n current => (∀ j, j < n → current.ram (word (trueCell j)) =
        memory.ram (word (keyBase + 2 * j)) ^^^ memory.ram (word (Layout.deltaCell (j / 254)))) ∧
      (∀ address, (∀ j, j < n → address ≠ word (trueCell j)) → current.ram address = memory.ram address) ∧
      current.bits = memory.bits) labelCount
    (fun n bound current ⟨done, off, bitsSame⟩ => by
      have evenSame : current.ram (word (keyBase + 2 * n)) = memory.ram (word (keyBase + 2 * n)) :=
        off _ fun j jb => evenAway n j bound (by omega)
      have deltaSame : current.ram (word (Layout.deltaCell (n / 254))) =
          memory.ram (word (Layout.deltaCell (n / 254))) :=
        off _ fun j jb => deltaAway n j bound (by omega)
      refine ⟨_, exec_keyXor n bound current, fun j jb => ?_, fun address away => ?_, bitsSame⟩
      · rw [ram_storeRam, ram_setReg, ram_setReg, ram_setReg, ram_setReg, ram_setReg, ram_setReg]
        by_cases last : j = n
        · subst last
          rw [Function.update_self, evenSame, deltaSame]
        · rw [Function.update_of_ne (word_ne (by unfold trueCell keyBase labelCount at *; omega)
            (by unfold trueCell keyBase labelCount at *; omega) (by unfold trueCell; omega)), done j (by omega)]
      · rw [ram_storeRam, ram_setReg, ram_setReg, ram_setReg, ram_setReg, ram_setReg, ram_setReg,
          Function.update_of_ne (away n (by omega)), off address fun j jb => away j (by omega)])
    memory ⟨fun j jb => absurd jb (by omega), fun _ _ => rfl, rfl⟩
  exact ⟨after, run, done, fun address outside => off address fun j jb same => outside ⟨j, jb, same⟩, bitsSame⟩

theorem det_keyTrue : keyTrue.OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial⟩

theorem trueCell_not_limb (j : Nat) (small : j < labelCount) : ¬ LimbCell (word (trueCell j)) :=
  not_limbCell _ (by unfold trueCell keyBase labelCount at *; omega)
    (Or.inr (by unfold trueCell keyBase tmpBase labelCount at *; omega))

theorem even_not_limb (j : Nat) (small : j < labelCount) : ¬ LimbCell (word (keyBase + 2 * j)) :=
  not_limbCell _ (by unfold keyBase labelCount at *; omega) (Or.inr (by unfold keyBase tmpBase; omega))

theorem delta_not_limb (j : Nat) (small : j < labelCount) : ¬ LimbCell (word (Layout.deltaCell (j / 254))) :=
  not_limbCell _ (by unfold Layout.deltaCell labelCount at *; omega)
    (Or.inr (by unfold Layout.deltaCell tmpBase; omega))

variable [FieldCertificate]

/-- **The tail**: the wire of the extracted source on the response stack, the true labels, the clears. -/
theorem memSem_tail (memory : Memory) (valid : CellsValid memory.ram) :
    ∃ final, tail.memSem memory = PMF.pure (some final) ∧
      final.bits 3 = byteBits (Entry.Wire.encoding.encode (Entry.publish (extract memory.ram))) ++ memory.bits 3 ∧
      (∀ stack, stack ≠ 3 → final.bits stack = memory.bits stack) ∧
      (∀ register, final.registers register = 0) ∧
      (∀ k, k < recordLimbCount → final.ram (word (recordLimb k)) = word 0) ∧
      (∀ j, j < labelCount → final.ram (word (trueCell j)) =
        memory.ram (word (keyBase + 2 * j)) ^^^ memory.ram (word (Layout.deltaCell (j / 254)))) ∧
      (∀ address, ¬ LimbCell address → ¬ TrueCell address → final.ram address = memory.ram address) := by
  obtain ⟨serialized, serialRun, serialOff, serialBits, serialOthers⟩ :=
    memSem_serialize memory (digitsSmall_of_valid memory.ram valid)
  obtain ⟨keyed, keyRun, keyCells, keyOff, keyBits⟩ := exec_keyTrue serialized
  obtain ⟨cleared, clearRun, clearZero, clearOff, clearBits⟩ := exec_clearLimbs keyed
  refine ⟨clearRegs cleared allRegisters, ?_, ?_, fun stack other => ?_, fun register => ?_, fun k kb => ?_,
    fun j jb => ?_, fun address notLimb notTrue => ?_⟩
  · unfold tail
    simp only [Prog.seqList]
    rw [memSem_seq, serialRun, PMF.pure_bind, kleisli, memSem_seq, memSem_eq_exec _ det_keyTrue, keyRun,
      PMF.pure_bind, kleisli, memSem_seq, memSem_eq_exec _ det_clearLimbs, clearRun, PMF.pure_bind, kleisli,
      memSem_seq, memSem_zeroRegs, PMF.pure_bind, kleisli]
    rfl
  · rw [(clearRegs_other _ _).2, clearBits, keyBits, serialBits,
      pieces_bits memory.ram (extract memory.ram) (sourceHolds_extract memory.ram valid)]
  · rw [(clearRegs_other _ _).2, clearBits, keyBits, serialOthers stack other]
  · rw [clearRegs_registers, if_pos (show register ∈ allRegisters from List.mem_finRange register)]
  · rw [(clearRegs_other _ _).1, clearZero k kb]
  · rw [(clearRegs_other _ _).1, clearOff _ (trueCell_not_limb j jb), keyCells j jb,
      serialOff _ (even_not_limb j jb), serialOff _ (delta_not_limb j jb)]
  · rw [(clearRegs_other _ _).1, clearOff _ notLimb, keyOff _ notTrue, serialOff _ notLimb]

end

end CrtTail

end Kriterion.CRT.SimMachine
