/-
**Deterministic execution of the arithmetic fragment of `Prog`.**

The CRT simulator's arithmetic blocks (`Construction/Simulator/CRT/Arith.lean`) use only
constants, arithmetic, loads, stores, pushes and pops. For such a program `Prog.exec` is a plain
function `Memory → Option Memory`, and the two semantics the machine proofs use reduce to it:

* `tree_eq_exec`: the query tree of the replay (`Prog.tree`, for every choice of index types, so
  it serves the CRT's empty index types and xinshu's instance alike) is the leaf `P.exec memory`;
* `memSem_eq_exec`: the oracle-free law of stage 1 and the opening (`Prog.memSem`) is the point
  mass on `P.exec memory`.

So every arithmetic lemma is proved once, on `exec`, and read off in both settings. `exec_rep` is
the loop rule for `Prog.rep`. The word lemmas (`eval_mul_word`, …) state when a word operation is
the natural-number operation (no wrap-around).
-/

import Proof.Simulator.Tree
import Proof.Simulator.OracleUse
import Construction.Simulator.CRT.Arith

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine

/-! ### The deterministic fragment -/

/-- A deterministic straight-line operation (no coin, no point addition, no oracle). -/
def Op.Det : Op → Prop
  | .constant .. | .arith .. | .load .. | .store .. | .push .. | .pushBit .. => True
  | _ => False

/-- One operation of the deterministic fragment, as a function (`none` outside the fragment). -/
def Op.exec : Op → Memory → Option Memory
  | .constant target value, memory => some (setReg memory target value)
  | .arith operation target left right, memory =>
      some (setReg memory target (operation.eval (memory.registers left) (memory.registers right)))
  | .load target address, memory =>
      some (setReg memory target (memory.ram (memory.registers address)))
  | .store address source, memory =>
      some (storeRam memory (memory.registers address) (memory.registers source))
  | .push stack bit, memory => some (pushOn memory stack bit)
  | .pushBit stack source, memory =>
      some (pushOn memory stack ((memory.registers source).getLsbD 0))
  | _, _ => none

/-- A program of the deterministic fragment, as a function. -/
def Prog.exec : Prog → Memory → Option Memory
  | .op operation, memory => operation.exec memory
  | .popBit stack target, memory => some (popInto memory stack target)
  | .skip _, memory => some memory
  | .abort _, _ => none
  | .seq first second, memory => (first.exec memory).bind second.exec
  | .ite source whenSet whenClear, memory =>
      if memory.registers source = 0 then whenClear.exec memory else whenSet.exec memory

theorem Prog.exec_seq (first second : Prog) (memory : Memory) :
    (Prog.seq first second).exec memory = (first.exec memory).bind second.exec := rfl

theorem Prog.exec_seq_some (first second : Prog) (memory middle : Memory)
    (runs : first.exec memory = some middle) :
    (Prog.seq first second).exec memory = second.exec middle := by
  rw [Prog.exec_seq, runs, Option.bind_some]

theorem Prog.exec_rep_zero (body : Nat → Prog) (memory : Memory) :
    (Prog.rep 0 body).exec memory = some memory := by
  rw [Prog.rep]; rfl

theorem Prog.exec_rep_succ (count : Nat) (body : Nat → Prog) (memory : Memory) :
    (Prog.rep (count + 1) body).exec memory =
      ((Prog.rep count body).exec memory).bind (body count).exec := by
  rw [Prog.rep]; rfl

/-- **The loop rule**: an invariant carried through every body carries through `rep`. -/
theorem Prog.exec_rep (body : Nat → Prog) (Inv : Nat → Memory → Prop) :
    ∀ (count : Nat),
      (∀ index, index < count → ∀ memory, Inv index memory →
        ∃ after, (body index).exec memory = some after ∧ Inv (index + 1) after) →
      ∀ memory, Inv 0 memory → ∃ after, (Prog.rep count body).exec memory = some after ∧ Inv count after
  | 0, _, memory, start => ⟨memory, Prog.exec_rep_zero body memory, start⟩
  | count + 1, step, memory, start => by
      obtain ⟨middle, run, holds⟩ :=
        Prog.exec_rep body Inv count (fun index bound => step index (by omega)) memory start
      obtain ⟨after, last, final⟩ := step count (by omega) middle holds
      exact ⟨after, by rw [Prog.exec_rep_succ, run, Option.bind_some, last], final⟩

theorem det_rep (count : Nat) (body : Nat → Prog)
    (each : ∀ index, index < count → (body index).OpsSatisfy Op.Det) :
    (Prog.rep count body).OpsSatisfy Op.Det := by
  induction count with
  | zero => rw [Prog.rep]; trivial
  | succ count ih =>
      rw [Prog.rep]
      exact ⟨ih fun index bound => each index (by omega), each count (by omega)⟩

/-! ### The two semantics reduce to `exec` -/

section Bridge

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **A deterministic block's query tree is the leaf of its execution.** -/
theorem tree_eq_exec : ∀ (program : Prog), program.OpsSatisfy Op.Det → ∀ (memory : Memory),
    program.tree (FixedIndex := FixedIndex) (EncIndex := EncIndex) memory = .pure (program.exec memory)
  | .op operation, det, memory => by
      cases operation
      all_goals first
        | exact (det : False).elim
        | rfl
  | .popBit _ _, _, _ => rfl
  | .skip _, _, _ => rfl
  | .abort _, _, _ => rfl
  | .seq first second, det, memory => by
      simp only [Prog.tree, Prog.exec]
      rw [tree_eq_exec first det.1 memory]
      cases first.exec memory with
      | none => rfl
      | some middle =>
          show bindOpt (.pure (some middle)) _ = _
          exact tree_eq_exec second det.2 middle
  | .ite source whenSet whenClear, det, memory => by
      simp only [Prog.tree, Prog.exec]
      split
      · exact tree_eq_exec whenClear det.2 memory
      · exact tree_eq_exec whenSet det.1 memory

/-- **A deterministic block's memory law is the point mass on its execution.** -/
theorem memSem_eq_exec : ∀ (program : Prog), program.OpsSatisfy Op.Det → ∀ (memory : Memory),
    program.memSem memory = PMF.pure (program.exec memory)
  | .op operation, det, memory => by
      cases operation
      all_goals first
        | exact (det : False).elim
        | rfl
  | .popBit _ _, _, _ => rfl
  | .skip _, _, _ => rfl
  | .abort _, _, _ => rfl
  | .seq first second, det, memory => by
      simp only [Prog.memSem, Prog.exec]
      rw [memSem_eq_exec first det.1 memory, PMF.pure_bind]
      cases first.exec memory with
      | none => rfl
      | some middle => exact memSem_eq_exec second det.2 middle
  | .ite source whenSet whenClear, det, memory => by
      simp only [Prog.memSem, Prog.exec]
      split
      · exact memSem_eq_exec whenClear det.2 memory
      · exact memSem_eq_exec whenSet det.1 memory

/-- A deterministic block that runs to `after`, followed by `rest`, as a tree. -/
theorem tree_seq_exec (first rest : Prog) (det : first.OpsSatisfy Op.Det) (memory after : Memory)
    (runs : first.exec memory = some after) :
    (Prog.seq first rest).tree (FixedIndex := FixedIndex) (EncIndex := EncIndex) memory =
      rest.tree after := by
  simp only [Prog.tree]
  rw [tree_eq_exec first det memory, runs]
  rfl

end Bridge

end Kriterion.ArgoMAC.PlanB.SimMachine

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

/-! ### Memory bookkeeping -/

theorem reg_setReg (memory : Memory) (target : Register) (value : Word) (index : Register) :
    (setReg memory target value).registers index =
      if index = target then value else memory.registers index := by
  simp only [setReg, Function.update_apply]

theorem ram_setReg (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).ram = memory.ram := rfl

theorem bits_setReg (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).bits = memory.bits := rfl

theorem reg_storeRam (memory : Memory) (address value : Word) :
    (storeRam memory address value).registers = memory.registers := rfl

theorem ram_storeRam (memory : Memory) (address value : Word) :
    (storeRam memory address value).ram = Function.update memory.ram address value := rfl

theorem bits_storeRam (memory : Memory) (address value : Word) :
    (storeRam memory address value).bits = memory.bits := rfl

/-! ### Words -/

theorem word_toNat {value : Nat} (small : value < 2 ^ 256) : (word value).toNat = value := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem word_inj {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) (same : word first = word second) : first = second := by
  rw [← word_toNat firstSmall, ← word_toNat secondSmall, same]

theorem word_ne {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) (different : first ≠ second) : word first ≠ word second :=
  fun same => different (word_inj firstSmall secondSmall same)

theorem eval_mul_word (first second : Nat) (small : first * second < 2 ^ 256) :
    Arithmetic.mul.eval (word first) (word second) = word (first * second) := by
  have firstSmall : first < 2 ^ 256 ∨ second = 0 := by
    rcases Nat.eq_zero_or_pos second with zero | pos
    · exact Or.inr zero
    · exact Or.inl (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ pos) small)
  apply BitVec.eq_of_toNat_eq
  show (word first * word second).toNat = _
  rw [BitVec.toNat_mul, word_toNat small]
  rcases firstSmall with fs | zero
  · have secondSmall : second < 2 ^ 256 ∨ first = 0 := by
      rcases Nat.eq_zero_or_pos first with zero | pos
      · exact Or.inr zero
      · exact Or.inl (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ pos) small)
    rcases secondSmall with ss | zero
    · rw [word_toNat fs, word_toNat ss, Nat.mod_eq_of_lt small]
    · subst zero; simp
  · subst zero; simp

theorem eval_add_word (first second : Nat) (small : first + second < 2 ^ 256) :
    Arithmetic.add.eval (word first) (word second) = word (first + second) := by
  apply BitVec.eq_of_toNat_eq
  show (word first + word second).toNat = _
  rw [BitVec.toNat_add, word_toNat (by omega), word_toNat (by omega), word_toNat small,
    Nat.mod_eq_of_lt small]

theorem eval_sub_word (first second : Nat) (below : second ≤ first) (small : first < 2 ^ 256) :
    Arithmetic.sub.eval (word first) (word second) = word (first - second) := by
  apply BitVec.eq_of_toNat_eq
  show (word first - word second).toNat = _
  rw [BitVec.toNat_sub, word_toNat small, word_toNat (by omega), word_toNat (by omega)]
  rw [show 2 ^ 256 - second + first = (first - second) + 2 ^ 256 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem eval_and_mask (value : Nat) (small : value < 2 ^ 256) :
    Arithmetic.and.eval (word value) (word limbMask) = word (value % 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  show (word value &&& word limbMask).toNat = _
  have maskSmall : limbMask < 2 ^ 256 := by unfold limbMask; norm_num
  rw [BitVec.toNat_and, word_toNat small, word_toNat maskSmall,
    word_toNat (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))]
  exact Nat.and_two_pow_sub_one_eq_mod value 128

theorem eval_shr_word (value shift : Nat) (small : value < 2 ^ 256) (shiftSmall : shift < 2 ^ 256) :
    Arithmetic.shiftRight.eval (word value) (word shift) = word (value / 2 ^ shift) := by
  apply BitVec.eq_of_toNat_eq
  show (word value >>> (word shift).toNat).toNat = _
  rw [BitVec.toNat_ushiftRight, word_toNat small, word_toNat shiftSmall, Nat.shiftRight_eq_div_pow,
    word_toNat (lt_of_le_of_lt (Nat.div_le_self _ _) small)]

theorem eval_less_word (first second : Nat) (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) :
    Arithmetic.less.eval (word first) (word second) = word (if first < second then 1 else 0) := by
  show (if (word first).toNat < (word second).toNat then 1 else 0) = _
  rw [word_toNat firstSmall, word_toNat secondSmall]
  split <;> rfl

end Kriterion.CRT.SimMachine
