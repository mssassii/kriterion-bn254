/-
**The pure parts of an odd modulus on the machine**: `exec_sigmaBlock` (the cell holds the
construction's `T.wordValue m v`).
-/

import Proof.Simulator.CRT.ReplayChunks
import Construction.Simulator.CRT.ReplayOdd

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### The word value -/

theorem exec_sigmaTerm (coordCell offset width t : Nat) (memory : Memory) (v : Nat)
    (coordVal : memory.ram (word coordCell) = word v) (vSmall : v < 2 ^ 256)
    (offsetSmall : offset < 2 ^ 256) (widthSmall : width < 256)
    (productSmall : (v / 2 ^ offset) % 2 ^ width * t < 2 ^ 256) :
    ∃ after, (sigmaTerm coordCell offset width t).exec memory = some after ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rA = word ((v / 2 ^ offset) % 2 ^ width * t) ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have divSmall : v / 2 ^ offset < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) vSmall
  refine ⟨_, rfl, rfl, rfl, ?_, fun register n1 n2 n3 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, coordVal]
    rw [eval_shr_word _ _ vSmall offsetSmall, eval_and_pow _ _ divSmall widthSmall,
      eval_mul_word _ _ productSmall]
  · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3]

/-- The chunk value of the machine. -/
def sigmaAlpha (v offset width : Nat) : Nat := (v / 2 ^ offset) % 2 ^ width

/-- The machine's partial word value after `k` chunks. -/
def sigmaPartial (m v : Nat) (offset width : Nat → Nat) (k : Nat) : Nat :=
  ∑ c ∈ range k, sigmaAlpha v (offset c) (width c) * (2 ^ offset c % m) % m

theorem exec_sigmaBlock (coordCell sigmaCell m count : Nat) (offset width : Nat → Nat)
    (memory : Memory) (v : Nat) (coordVal : memory.ram (word coordCell) = word v)
    (vSmall : v < 2 ^ 256) (mPos : 0 < m) (mSmall : m ≤ 2 ^ 10) (countSmall : count ≤ 2 ^ 10)
    (offsetSmall : ∀ c, c < count → offset c < 2 ^ 256) (widthSmall : ∀ c, c < count → width c ≤ 8)
    (sigmaSmall : sigmaCell < 2 ^ 256) :
    ∃ after, (sigmaBlock coordCell sigmaCell m count offset width).exec memory = some after ∧
      after.ram = Function.update memory.ram (word sigmaCell)
        (word (sigmaPartial m v offset width count)) ∧
      after.bits = memory.bits ∧
      ∀ register, ¬ sigmaClobbers register → after.registers register = memory.registers register := by
  have bound : ∀ k, sigmaPartial m v offset width k ≤ k * m := fun k => by
    unfold sigmaPartial
    calc ∑ c ∈ range k, sigmaAlpha v (offset c) (width c) * (2 ^ offset c % m) % m
        ≤ ∑ c ∈ range k, m := sum_le_sum fun c _ => (Nat.mod_lt _ mPos).le
      _ = k * m := by rw [sum_const, card_range, smul_eq_mul]
  obtain ⟨after, run, acc, ram, bits, regs⟩ := Prog.exec_rep
    (fun c => sigmaChunk coordCell m (offset c) (width c))
    (fun k current =>
      current.registers rAcc = word (sigmaPartial m v offset width k) ∧ current.ram = memory.ram ∧
        current.bits = memory.bits ∧
        ∀ register, ¬ sigmaClobbers register → register ≠ rAcc →
          current.registers register = memory.registers register)
    count
    (fun k kb current ⟨acc, ram, bits, regs⟩ => by
      have w8 := widthSmall k kb
      have alphaLt : sigmaAlpha v (offset k) (width k) < 2 ^ 8 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by norm_num) w8)
      have tLt : 2 ^ offset k % m < m := Nat.mod_lt _ mPos
      have productLt : sigmaAlpha v (offset k) (width k) * (2 ^ offset k % m) < 2 ^ 32 := by
        have := Nat.mul_lt_mul'' alphaLt tLt
        have : 2 ^ 8 * m ≤ 2 ^ 8 * 2 ^ 10 := Nat.mul_le_mul_left _ mSmall
        omega
      obtain ⟨m1, run1, ram1, bits1, a1, regs1⟩ := exec_sigmaTerm coordCell (offset k) (width k)
        (2 ^ offset k % m) current v (by rw [ram]; exact coordVal) vSmall (offsetSmall k kb)
        (by omega) (by unfold sigmaAlpha at productLt; omega)
      obtain ⟨m2, run2, c2, ram2, bits2, regs2⟩ := exec_barrett rA rC m 32 _ m1 (by decide) (by decide)
        (by decide) (by decide) (by decide) a1 (by unfold sigmaAlpha at productLt; exact productLt)
        mPos (by omega) (by norm_num)
      have accNow : m2.registers rAcc = word (sigmaPartial m v offset width k) := by
        rw [regs2 rAcc (by decide) (by decide) (by decide) (by decide),
          regs1 rAcc (by decide) (by decide) (by decide)]
        exact acc
      have sumSmall : sigmaPartial m v offset width k +
          (v / 2 ^ offset k) % 2 ^ width k * (2 ^ offset k % m) % m < 2 ^ 256 := by
        have := bound k
        have := Nat.mod_lt ((v / 2 ^ offset k) % 2 ^ width k * (2 ^ offset k % m)) mPos
        have : k * m ≤ 2 ^ 10 * 2 ^ 10 := Nat.mul_le_mul (by omega) mSmall
        omega
      refine ⟨setReg m2 rAcc (word (sigmaPartial m v offset width (k + 1))), ?_, ?_, ?_, ?_, ?_⟩
      · unfold sigmaChunk
        rw [Prog.exec_seq_some _ _ _ _ run1, Prog.exec_seq_some _ _ _ _ run2,
          exec_ar_last _ _ _ _ m2 _ _ accNow c2, eval_add_word _ _ sumSmall]
        congr 2
        unfold sigmaPartial
        rw [sum_range_succ]
        rfl
      · simp only [reg_setReg, ↓reduceIte]
      · simp only [ram_setReg]
        rw [ram2, ram1, ram]
      · simp only [bits_setReg]
        rw [bits2, bits1, bits]
      · intro register outside notAcc
        have ne : ∀ r, r ∈ [rA, rB, rC, rD, rE, rF, rAcc, rAddr] → register ≠ r :=
          fun r mem h => outside (h ▸ mem)
        simp only [reg_setReg, if_neg notAcc]
        rw [regs2 register (ne rC (by simp)) (ne rD (by simp)) (ne rE (by simp)) (ne rF (by simp)),
          regs1 register (ne rA (by simp)) (ne rB (by simp)) (ne rAddr (by simp))]
        exact regs register outside notAcc)
    (setReg memory rAcc (word 0))
    ⟨by simp [reg_setReg, sigmaPartial], rfl, rfl, fun register _ notAcc => by
      simp only [reg_setReg, if_neg notAcc]⟩
  refine ⟨storeRam (setReg after rAddr (word sigmaCell)) (word sigmaCell) (after.registers rAcc), ?_, ?_,
    ?_, fun register outside => ?_⟩
  · unfold sigmaBlock
    rw [exec_cst_seq, Prog.exec_seq_some _ _ _ _ run, exec_storeAt _ _ _ (by decide)]
  · simp only [ram_storeRam, ram_setReg]
    rw [acc, ram]
  · simp only [bits_storeRam, bits_setReg]
    exact bits
  · have ne : ∀ r, r ∈ [rA, rB, rC, rD, rE, rF, rAcc, rAddr] → register ≠ r :=
      fun r mem h => outside (h ▸ mem)
    simp only [reg_storeRam, reg_setReg, if_neg (ne rAddr (by simp))]
    rw [regs register outside (ne rAcc (by simp))]
    try simp only [reg_setReg, if_neg (ne rAcc (by simp))]

/-- The machine's word value is the construction's (`T.truth` with `2 ^ offset` reduced first). -/
theorem sigmaPartial_eq (T : CrtTable) (m v : Nat) :
    sigmaPartial m v T.chunkOffset T.chunkWidth T.chunkCount = T.wordValue m v := by
  unfold sigmaPartial CrtTable.wordValue
  rw [Fin.sum_univ_eq_sum_range (fun c => T.truth m c (T.chunkValue v c))]
  refine sum_congr rfl fun c _ => ?_
  unfold sigmaAlpha CrtTable.truth CrtTable.chunkValue
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

end Kriterion.CRT.SimMachine
