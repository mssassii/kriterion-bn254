/-
**One record on the wire** (M2): `recordProg κ e` computes the record of encoding `e` by Horner's rule over its 84
digits into five 128-bit limbs, then emits its 618 bits.

* `hornerSuffix`: `H(k) = Σ_{k ≤ i < 84} J_i Π_{k ≤ i' < i} m_{i'}`, with `H(k) = J_k + m_k H(k + 1)` and
  `H(0) = Σ_i J_i · radix_i`; `H(k) < 2 ^ 618` when every digit is below its modulus;
* `exec_clearLimbs`, `exec_hornerStep`, `exec_horner`: the limbs hold `H(0)` after the 84 steps;
* `memSem_recordProg`: the record program pushes `lsbs 618 (recordValue ram κ e)` and changes RAM only in the five
  limb cells.
-/

import Proof.Simulator.CRT.Stage1Pieces
import Proof.Simulator.CRT.Limbs
import Proof.Simulator.Stage1Serialize

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open CrtStage1 CrtConv

namespace CrtRecord

/-! ### Horner's rule on naturals -/

/-- The suffix Horner value `H(k)`. -/
def hornerSuffix (digit : Nat → Nat) (k : Nat) : Nat :=
  ∑ i ∈ Finset.Ico k moduliCount, digit i * ∏ j ∈ Finset.Ico k i, modulusAt j

/-- The suffix product `Π_{k ≤ j < 84} m_j`. -/
def suffixProduct (k : Nat) : Nat := ∏ j ∈ Finset.Ico k moduliCount, modulusAt j

theorem hornerSuffix_step (digit : Nat → Nat) (k : Nat) (small : k < moduliCount) :
    hornerSuffix digit k = digit k + modulusAt k * hornerSuffix digit (k + 1) := by
  unfold hornerSuffix
  rw [Finset.sum_eq_sum_Ico_succ_bot small, Finset.Ico_self, Finset.prod_empty, Nat.mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i member => ?_
  have inside := Finset.mem_Ico.mp member
  rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]
  ring

theorem hornerSuffix_top (digit : Nat → Nat) : hornerSuffix digit moduliCount = 0 := by
  simp [hornerSuffix]

theorem hornerSuffix_zero (digit : Nat → Nat) :
    hornerSuffix digit 0 = ∑ i ∈ Finset.range moduliCount, digit i * radixAt i := by
  unfold hornerSuffix radixAt
  rw [Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.range_eq_Ico]

theorem suffixProduct_step (k : Nat) (small : k < moduliCount) :
    suffixProduct k = modulusAt k * suffixProduct (k + 1) := by
  unfold suffixProduct
  rw [Finset.prod_eq_prod_Ico_succ_bot small]

theorem hornerSuffix_lt (digit : Nat → Nat) (small : ∀ i, i < moduliCount → digit i < modulusAt i) :
    ∀ n k, k + n = moduliCount → hornerSuffix digit k < suffixProduct k
  | 0, k, sum => by
      subst sum
      simp [hornerSuffix, suffixProduct]
  | n + 1, k, sum => by
      have inside : k < moduliCount := by omega
      have rest := hornerSuffix_lt digit small n (k + 1) (by omega)
      rw [hornerSuffix_step digit k inside, suffixProduct_step k inside]
      have head := small k inside
      calc digit k + modulusAt k * hornerSuffix digit (k + 1)
          < modulusAt k + modulusAt k * hornerSuffix digit (k + 1) := by omega
        _ = modulusAt k * (hornerSuffix digit (k + 1) + 1) := by ring
        _ ≤ modulusAt k * suffixProduct (k + 1) := Nat.mul_le_mul_left _ rest

theorem modulusAt_pos_fin : ∀ j : Fin 84, 0 < modulusAt j := by decide +kernel

theorem modulusAt_pos (j : Nat) (small : j < moduliCount) : 0 < modulusAt j :=
  modulusAt_pos_fin ⟨j, small⟩

theorem suffixProduct_le (k : Nat) (small : k ≤ moduliCount) : suffixProduct k ≤ suffixProduct 0 := by
  have split := Finset.prod_Ico_consecutive modulusAt (Nat.zero_le k) small
  unfold suffixProduct
  rw [← split]
  apply Nat.le_mul_of_pos_left
  apply Finset.prod_pos
  intro j member
  exact modulusAt_pos j (by have := (Finset.mem_Ico.mp member).2; omega)

/-- The product of the moduli is below `2 ^ 618`. -/
theorem suffixProduct_zero_lt : suffixProduct 0 < 2 ^ 618 := by
  unfold suffixProduct
  decide +kernel

theorem hornerSuffix_small (digit : Nat → Nat) (small : ∀ i, i < moduliCount → digit i < modulusAt i)
    (k : Nat) (inside : k ≤ moduliCount) : hornerSuffix digit k < 2 ^ 618 :=
  lt_of_lt_of_le (hornerSuffix_lt digit small (moduliCount - k) k (by omega))
    (le_trans (suffixProduct_le k inside) (le_of_lt suffixProduct_zero_lt))

theorem modulusAt_small : ∀ j : Fin 84, modulusAt j < 2 ^ 128 := by decide +kernel

/-! ### The limbs -/

theorem recordLimb_add (k : Nat) : recordLimb 0 + k = recordLimb k := by
  unfold recordLimb; omega

/-- The five limb cells. -/
def LimbCell (address : Word) : Prop := ∃ k, k < recordLimbCount ∧ address = word (recordLimb k)

theorem exec_clearLimbs (memory : Memory) :
    ∃ after, clearLimbs.exec memory = some after ∧
      (∀ k, k < recordLimbCount → after.ram (word (recordLimb k)) = word 0) ∧
      (∀ address, ¬ LimbCell address → after.ram address = memory.ram address) ∧ after.bits = memory.bits := by
  obtain ⟨after, run, holds⟩ := Prog.exec_rep (fun k => .seq (cst rA 0) (storeAt (recordLimb k) rA))
    (fun n current => (∀ k, k < n → current.ram (word (recordLimb k)) = word 0) ∧
      (∀ address, (∀ k, k < n → address ≠ word (recordLimb k)) → current.ram address = memory.ram address) ∧
      current.bits = memory.bits) recordLimbCount
    (fun n bound current ⟨done, off, bitsSame⟩ => by
      have nb : n < 5 := bound
      refine ⟨storeRam (setReg (setReg current rA (word 0)) rAddr (word (recordLimb n))) (word (recordLimb n))
        (word 0), rfl, fun k kb => ?_, fun address away => ?_, by rw [bits_storeRam, bits_setReg, bits_setReg,
        bitsSame]⟩
      · rw [ram_storeRam, ram_setReg, ram_setReg]
        by_cases last : k = n
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by unfold recordLimb tmpBase; omega)
            (by unfold recordLimb tmpBase; omega) (by unfold recordLimb; omega)), done k (by omega)]
      · rw [ram_storeRam, ram_setReg, ram_setReg, Function.update_of_ne (away n (by omega)),
          off address fun k kb => away k (by omega)])
    memory ⟨fun k kb => absurd kb (by omega), fun _ _ => rfl, rfl⟩
  obtain ⟨done, off, bitsSame⟩ := holds
  exact ⟨after, run, done, fun address outside => off address fun k kb same => outside ⟨k, kb, same⟩, bitsSame⟩

theorem limb_ne (k : Nat) (small : k < 5) (address : Nat) (bound : address < 2 ^ 256)
    (away : address < tmpBase ∨ tmpBase + 2 ^ 20 ≤ address) : word address ≠ word (recordLimb k) :=
  word_ne bound (by unfold recordLimb tmpBase; omega) (by unfold recordLimb tmpBase at *; omega)

theorem not_limbCell (address : Nat) (bound : address < 2 ^ 256)
    (away : address < tmpBase ∨ tmpBase + 2 ^ 20 ≤ address) : ¬ LimbCell (word address) := by
  rintro ⟨k, small, same⟩
  exact limb_ne k small address bound away same

theorem exec_hornerStep (κ e i : Nat) (memory : Memory) (X digit : Nat) (inside : i < moduliCount)
    (limbs : ∀ k, k < 5 → memory.ram (word (recordLimb k)) = word (limbOf X k))
    (digitCell : memory.ram (word (Layout.residueCell κ i e)) = word digit)
    (digitSmall : digit < modulusAt i) (XSmall : X < 2 ^ 640) :
    ∃ after, (hornerStep κ e i).exec memory = some after ∧
      (∀ k, k < 5 → after.ram (word (recordLimb k)) = word (limbOf (X * modulusAt i + digit) k)) ∧
      (∀ address, ¬ LimbCell address → after.ram address = memory.ram address) ∧ after.bits = memory.bits := by
  have mSmall : modulusAt i < 2 ^ 128 := modulusAt_small ⟨i, inside⟩
  set loaded := setReg (setReg memory rAddr (word (Layout.residueCell κ i e))) rC
    (memory.ram (word (Layout.residueCell κ i e))) with loadedDef
  set ready := setReg (setReg (setReg loaded rM (word (modulusAt i))) rMask (word limbMask)) rK128 (word 128)
    with readyDef
  have readyRam : ready.ram = memory.ram := rfl
  obtain ⟨after, run, cells, _, frame, bitsSame, _⟩ := exec_mulSmallAdd (recordLimb 0) recordLimbCount
    (limbOf X) (modulusAt i) digit ready (by unfold recordLimb recordLimbCount tmpBase; norm_num)
    (fun k kb => by rw [readyRam, recordLimb_add, limbs k kb])
    (limbOf_lt X)
    ⟨by rw [readyDef, reg_setReg, reg_setReg, reg_setReg]; rfl,
      by rw [readyDef, reg_setReg, reg_setReg]; rfl, by rw [readyDef, reg_setReg]; rfl⟩
    (by rw [readyDef, reg_setReg, reg_setReg, reg_setReg, loadedDef, reg_setReg]
        split_ifs <;> first | exact absurd ‹_› (by decide) | exact digitCell)
    mSmall (by omega)
  have value : limbValue (limbOf X) recordLimbCount = X := by
    rw [limbValue_limbOf, show 128 * recordLimbCount = 640 from rfl, Nat.mod_eq_of_lt XSmall]
  refine ⟨after, ?_, fun k kb => ?_, fun address outside => ?_, by rw [bitsSame]; rfl⟩
  · show ((loadAt rC (Layout.residueCell κ i e)).exec memory).bind
      (Prog.seq (setupConsts (modulusAt i)) (Prog.seq (mulSmallAdd (recordLimb 0) recordLimbCount) (.skip 0))).exec
        = some after
    rw [show (loadAt rC (Layout.residueCell κ i e)).exec memory = some loaded from rfl, Option.bind_some,
      Prog.exec_seq_some _ _ loaded ready rfl, Prog.exec_seq_some _ _ ready after run]
    rfl
  · rw [← recordLimb_add, cells k kb, value]
  · rw [frame address fun k kb same => outside ⟨k, kb, by rw [same, recordLimb_add]⟩, readyRam]

/-- **Horner's rule**: after the 84 steps the limbs hold the record `H(0)`. -/
theorem exec_horner (κ e : Nat) (memory : Memory) (digit : Nat → Nat)
    (small : ∀ i, i < moduliCount → digit i < modulusAt i)
    (cells : ∀ i, i < moduliCount → memory.ram (word (Layout.residueCell κ i e)) = word (digit i))
    (cellsAway : ∀ i, i < moduliCount → ¬ LimbCell (word (Layout.residueCell κ i e)))
    (zeroLimbs : ∀ k, k < 5 → memory.ram (word (recordLimb k)) = word 0) :
    ∃ after, (Prog.rep moduliCount fun n => hornerStep κ e (moduliCount - 1 - n)).exec memory = some after ∧
      (∀ k, k < 5 → after.ram (word (recordLimb k)) = word (limbOf (hornerSuffix digit 0) k)) ∧
      (∀ address, ¬ LimbCell address → after.ram address = memory.ram address) ∧ after.bits = memory.bits := by
  obtain ⟨after, run, limbs, off, bitsSame⟩ := Prog.exec_rep (fun n => hornerStep κ e (moduliCount - 1 - n))
    (fun n current => (∀ k, k < 5 →
        current.ram (word (recordLimb k)) = word (limbOf (hornerSuffix digit (moduliCount - n)) k)) ∧
      (∀ address, ¬ LimbCell address → current.ram address = memory.ram address) ∧ current.bits = memory.bits)
    moduliCount
    (fun n bound current ⟨limbs, off, bitsSame⟩ => by
      have nb : n < 84 := bound
      set i := moduliCount - 1 - n with iDef
      have iSmall : i < moduliCount := by unfold moduliCount at *; omega
      obtain ⟨next, run, limbsNext, offNext, bitsNext⟩ := exec_hornerStep κ e i current
        (hornerSuffix digit (moduliCount - n)) (digit i) iSmall limbs
        (by rw [off _ (cellsAway i iSmall), cells i iSmall]) (small i iSmall)
        (lt_trans (hornerSuffix_small digit small _ (by omega)) (Nat.pow_lt_pow_right (by norm_num) (by norm_num)))
      refine ⟨next, run, fun k kb => ?_, fun address outside => ?_, by rw [bitsNext, bitsSame]⟩
      · rw [limbsNext k kb, show moduliCount - (n + 1) = i by unfold moduliCount at *; omega,
          hornerSuffix_step digit i iSmall, show i + 1 = moduliCount - n by unfold moduliCount at *; omega,
          Nat.mul_comm, Nat.add_comm]
      · rw [offNext address outside, off address outside])
    memory ⟨fun k kb => by rw [Nat.sub_zero, hornerSuffix_top, zeroLimbs k kb]; simp [limbOf],
      fun _ _ => rfl, rfl⟩
  exact ⟨after, run, fun k kb => by rw [limbs k kb, Nat.sub_self], off, bitsSame⟩

/-! ### The emission -/

theorem lsbs_mod_le (width v x : Nat) (le : width ≤ v) : lsbs width (x % 2 ^ v) = lsbs width x := by
  unfold lsbs
  refine congrArg List.ofFn (funext fun index => ?_)
  simp [Nat.testBit_mod_two_pow, lt_of_lt_of_le index.isLt le]

/-- The five limbs' bits are the record's 618 bits. -/
theorem record_windows (n : Nat) :
    lsbs 128 (limbOf n 0) ++ (lsbs 128 (limbOf n 1) ++ (lsbs 128 (limbOf n 2) ++ (lsbs 128 (limbOf n 3) ++
      lsbs 106 (limbOf n 4)))) = lsbs 618 n := by
  unfold limbOf
  rw [lsbs_mod, lsbs_mod, lsbs_mod, lsbs_mod, lsbs_mod_le 106 128 _ (by norm_num)]
  rw [show 618 = 128 + (128 + (128 + (128 + 106))) from rfl, lsbs_add, lsbs_add, lsbs_add, lsbs_add]
  simp only [Nat.div_div_eq_div_mul, ← pow_add]
  norm_num

theorem det_clearLimbs : clearLimbs.OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨trivial, trivial, trivial⟩

theorem det_horner (κ e : Nat) :
    (Prog.rep moduliCount fun n => hornerStep κ e (moduliCount - 1 - n)).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, det_mulSmallAdd _ _, trivial⟩

variable [FieldCertificate]

/-- The record's emission: limb 4 first, limb 0 last. -/
theorem memSem_emitRecord (memory : Memory) :
    ∃ after, emitRecord.memSem memory = PMF.pure (some after) ∧
      Emits memory after (bitRun (memory.ram (word (recordLimb 0))) 0 128 ++
        (bitRun (memory.ram (word (recordLimb 1))) 0 128 ++ (bitRun (memory.ram (word (recordLimb 2))) 0 128 ++
          (bitRun (memory.ram (word (recordLimb 3))) 0 128 ++ bitRun (memory.ram (word (recordLimb 4))) 0 106)))) := by
  obtain ⟨m1, r1, e1⟩ := memSem_emitWord (recordLimb 4) 106 (by norm_num) memory
  obtain ⟨m2, r2, e2⟩ := memSem_emitWord (recordLimb 3) 128 (by norm_num) m1
  obtain ⟨m3, r3, e3⟩ := memSem_emitWord (recordLimb 2) 128 (by norm_num) m2
  obtain ⟨m4, r4, e4⟩ := memSem_emitWord (recordLimb 1) 128 (by norm_num) m3
  obtain ⟨m5, r5, e5⟩ := memSem_emitWord (recordLimb 0) 128 (by norm_num) m4
  refine ⟨m5, ?_, ?_⟩
  · unfold emitRecord
    simp only [Prog.seqList]
    rw [memSem_seq, r1, PMF.pure_bind, kleisli, memSem_seq, r2, PMF.pure_bind, kleisli, memSem_seq, r3,
      PMF.pure_bind, kleisli, memSem_seq, r4, PMF.pure_bind, kleisli, memSem_seq, r5, PMF.pure_bind, kleisli]
    rfl
  · have chain := ((((e1.trans e2).trans e3).trans e4).trans e5)
    rw [e4.1, e3.1, e2.1, e1.1] at chain
    simpa only [List.append_assoc] using chain

/-- **One record**: Horner's rule into the limbs, then the record's 618 bits; RAM changes only in the limbs. -/
theorem memSem_recordProg (κ e : Nat) (memory : Memory) (digit : Nat → Nat)
    (small : ∀ i, i < moduliCount → digit i < modulusAt i)
    (cells : ∀ i, i < moduliCount → memory.ram (word (Layout.residueCell κ i e)) = word (digit i))
    (cellsAway : ∀ i, i < moduliCount → ¬ LimbCell (word (Layout.residueCell κ i e))) :
    ∃ after, (recordProg κ e).memSem memory = PMF.pure (some after) ∧
      (∀ address, ¬ LimbCell address → after.ram address = memory.ram address) ∧
      after.bits 3 = lsbs 618 (hornerSuffix digit 0) ++ memory.bits 3 ∧
      ∀ stack, stack ≠ 3 → after.bits stack = memory.bits stack := by
  obtain ⟨cleared, clearRun, zeroes, clearOff, clearBits⟩ := exec_clearLimbs memory
  obtain ⟨summed, hornerRun, limbs, hornerOff, hornerBits⟩ := exec_horner κ e cleared digit small
    (fun i inside => by rw [clearOff _ (cellsAway i inside), cells i inside]) cellsAway zeroes
  obtain ⟨emitted, emitRun, emits⟩ := memSem_emitRecord summed
  refine ⟨emitted, ?_, fun address outside => ?_, ?_, fun stack other => ?_⟩
  · unfold recordProg
    simp only [Prog.seqList]
    rw [memSem_seq, memSem_eq_exec _ det_clearLimbs, clearRun, PMF.pure_bind, kleisli, memSem_seq,
      memSem_eq_exec _ (det_horner κ e), hornerRun, PMF.pure_bind, kleisli, memSem_seq, emitRun, PMF.pure_bind,
      kleisli]
    rfl
  · rw [emits.1, hornerOff address outside, clearOff address outside]
  · rw [emits.2.1, hornerBits, clearBits]
    have small' := hornerSuffix_small digit small 0 (by norm_num)
    rw [limbs 0 (by norm_num), limbs 1 (by norm_num), limbs 2 (by norm_num), limbs 3 (by norm_num),
      limbs 4 (by norm_num)]
    simp only [bitRun_ofNat _ _ (show 128 ≤ 256 by norm_num), bitRun_ofNat _ _ (show 106 ≤ 256 by norm_num)]
    rw [← record_windows]
  · rw [emits.2.2 stack other, hornerBits, clearBits]

end CrtRecord

end Kriterion.CRT.SimMachine
