/-
**One round of a stage** (package M4a, part 4): the bit label of round `n` lane by lane
(`roundBit`), the hot material, the branch on bit `n` of `s`, and the agreement of `roundReplay`
with `stageRoundM`.
-/

import Proof.Simulator.CRT.ReplayExtractExpand

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### Building a block bit by bit -/

/-- Bits `0 .. i - 1` of `D` are `f 0 .. f (i - 1)`; the others are zero. -/
def BitsUpTo (f : Nat → Bool) (i : Nat) (D : Word) : Prop :=
  ∀ k, D.getLsbD k = (decide (k < i) && f k)

theorem bitsUpTo_zero (f : Nat → Bool) : BitsUpTo f 0 (word 0) := by
  intro k
  simp [word]

theorem bitsUpTo_step (f : Nat → Bool) (i : Nat) (D : Word) (holds : BitsUpTo f i D) (x : Nat)
    (hx : x % 2 = 1 ↔ f i = true) (iSmall : i < 256) :
    BitsUpTo f (i + 1) (D ^^^ (word (x % 2 ^ 1) <<< i)) := by
  intro k
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, holds k, word, BitVec.getLsbD_ofNat]
  rcases Nat.lt_trichotomy k i with hk | rfl | hk
  · have h1 : k < i + 1 := by omega
    simp [hk, h1]
  · have hsmall : k < 256 := iSmall
    rcases Bool.eq_false_or_eq_true (f k) with h | h
    · have : x % 2 = 1 := hx.mpr h
      simp [hsmall, h, Nat.testBit_zero, this]
    · have : x % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
        · exact h0
        · exact absurd (hx.mp h1) (by simp [h])
      simp [hsmall, h, Nat.testBit_zero, this]
  · have h1 : ¬ k < i + 1 := by omega
    have h2 : ¬ k < i := by omega
    have hbit : (x % 2).testBit (k - i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
        (le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))))
    simp [h1, h2, hbit]

theorem bitsUpTo_laneBit {l : Nat} (A : Lanes l) (n : Nat) (D : Word)
    (holds : BitsUpTo (fun k => if h : k < laneCount then (A ⟨k, h⟩).val.testBit n else false)
      laneCount D) :
    D = labelWord (laneBit A n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [holds k, labelWord, BitVec.getLsbD_ofNat, BitVec.testBit_toNat, laneBit, BitVec.getLsbD_ofFnLE]
  by_cases hk' : k < laneCount
  · simp [hk', hk]
  · simp [hk', hk]

/-! ### The lanes of one round -/

theorem eval_shl_word (value : Word) (shift : Nat) (small : shift < 2 ^ 256) :
    Arithmetic.shiftLeft.eval value (word shift) = value <<< shift := by
  show value <<< (word shift).toNat = _
  rw [word_toNat small]

theorem exec_resHead (cells : StageCells) (rb n i : Nat) (memory : Memory) (q P T : Nat)
    (fReg : memory.registers rF = word q)
    (pinCell : memory.ram (word (cells.pinBase + i)) = word (P / 2)) (PEven : P % 2 = 0)
    (castCell : memory.ram (word (cells.castSumBase + 128 * n + i)) = word T)
    (rbLe : rb ≤ 128) (qSmall : q < 2 ^ 64) (PSmall : P < 2 ^ rb) (TSmall : T < 2 ^ rb) :
    ∃ after, (resHead cells rb n i).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rC = word ((P + 2 ^ rb - T) * q) ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have powRb : 2 ^ rb ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) rbLe
  have diffSmall : P + 2 ^ rb - T < 2 ^ 129 := by
    have : (2 : Nat) ^ 129 = 2 * 2 ^ 128 := by norm_num
    omega
  have prodSmall : (P + 2 ^ rb - T) * q < 2 ^ 193 :=
    calc (P + 2 ^ rb - T) * q < 2 ^ 129 * 2 ^ 64 := Nat.mul_lt_mul'' diffSmall qSmall
      _ = 2 ^ 193 := by norm_num
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notB notC notE notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, fReg, pinCell,
      castCell]
    rw [eval_add_word (P / 2) (P / 2) (by omega), show P / 2 + P / 2 = P by omega,
      eval_add_word P (2 ^ rb) (by omega), eval_sub_word _ T (by omega) (by omega),
      eval_mul_word _ q (by omega)]
  · simp only [reg_setReg, if_neg notB, if_neg notC, if_neg notE, if_neg notAddr]

theorem exec_resTail (cells : StageCells) (rb n i : Nat) (memory : Memory) (X R : Nat)
    (cReg : memory.registers rC = word X)
    (classCell : memory.ram (word (cells.classBase + 128 * n + i)) = word R)
    (rbLe : rb ≤ 128) (XSmall : X < 2 ^ 254) (RSmall : R < 2 ^ rb) :
    ∃ after, (resTail cells rb n i).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rC = word ((X + R) % 2 ^ rb) ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have powRb : 2 ^ rb ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) rbLe
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notB notC notE notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, cReg, classCell]
    rw [eval_add_word X R (by omega), eval_and_pow _ rb (by omega) (by omega)]
  · simp only [reg_setReg, if_neg notB, if_neg notC, if_neg notE, if_neg notAddr]

theorem exec_roundRes (cells : StageCells) (rb n i : Nat) (memory : Memory) (q P T R : Nat)
    (fReg : memory.registers rF = word q)
    (pinCell : memory.ram (word (cells.pinBase + i)) = word (P / 2)) (PEven : P % 2 = 0)
    (castCell : memory.ram (word (cells.castSumBase + 128 * n + i)) = word T)
    (classCell : memory.ram (word (cells.classBase + 128 * n + i)) = word R)
    (rbLe : rb ≤ 128) (qSmall : q < 2 ^ 64) (PSmall : P < 2 ^ rb) (TSmall : T < 2 ^ rb)
    (RSmall : R < 2 ^ rb) :
    ∃ after, (roundRes cells rb n i).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      after.registers rC = word (((P + 2 ^ rb - T) * q + R) % 2 ^ rb) ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have powRb : 2 ^ rb ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) rbLe
  have diffSmall : P + 2 ^ rb - T < 2 ^ 129 := by
    have : (2 : Nat) ^ 129 = 2 * 2 ^ 128 := by norm_num
    omega
  have prodSmall : (P + 2 ^ rb - T) * q < 2 ^ 193 :=
    calc (P + 2 ^ rb - T) * q < 2 ^ 129 * 2 ^ 64 := Nat.mul_lt_mul'' diffSmall qSmall
      _ = 2 ^ 193 := by norm_num
  obtain ⟨m1, run1, ram1, bits1, c1, regs1⟩ :=
    exec_resHead cells rb n i memory q P T fReg pinCell PEven castCell rbLe qSmall PSmall TSmall
  obtain ⟨m2, run2, ram2, bits2, c2, regs2⟩ := exec_resTail cells rb n i m1 _ R c1
    (by rw [ram1]; exact classCell) rbLe (by omega) RSmall
  refine ⟨m2, by rw [roundRes, Prog.exec_seq_some _ _ memory m1 run1, run2], by rw [ram2, ram1],
    by rw [bits2, bits1], c2, fun register notB notC notE notAddr => ?_⟩
  rw [regs2 register notB notC notE notAddr, regs1 register notB notC notE notAddr]

theorem exec_roundDiff (cells : StageCells) (w i : Nat) (memory : Memory) (C S : Nat)
    (cReg : memory.registers rC = word C)
    (subCell : memory.ram (word (cells.subBase + i)) = word S)
    (wSmall : w ≤ 64) (CSmall : C < 2 ^ 256) (SSmall : S < 2 ^ w) :
    ∃ after, (roundDiff cells w i).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      after.registers rE = word ((S + 2 ^ w - C % 2 ^ w) % 2 ^ w) ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have powW : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) wSmall
  have modLt := Nat.mod_lt C (Nat.two_pow_pos w)
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notB notC notE notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, cReg, subCell]
    rw [eval_and_pow C w CSmall (by omega), eval_add_word S (2 ^ w) (by omega),
      eval_sub_word _ _ (by omega) (by omega), eval_and_pow _ w (by omega) (by omega)]
  · simp only [reg_setReg, if_neg notB, if_neg notC, if_neg notE, if_neg notAddr]

theorem exec_bitInsert (n i : Nat) (memory : Memory) (E : Nat) (eReg : memory.registers rE = word E)
    (ESmall : E < 2 ^ 256) (nSmall : n < 256) (iSmall : i < 256) :
    ∃ after, (bitInsert n i).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      after.registers rD = memory.registers rD ^^^ (word (E / 2 ^ n % 2 ^ 1) <<< i) ∧
      ∀ register, register ≠ rB → register ≠ rD → register ≠ rE →
        after.registers register = memory.registers register := by
  have divSmall : E / 2 ^ n < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) ESmall
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notB notD notE => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, reduceIte, eReg]
    rw [eval_shr_word E n ESmall (by omega), eval_xor,
      show Arithmetic.and.eval (word (E / 2 ^ n)) (word 1) = word (E / 2 ^ n % 2 ^ 1) from
        eval_and_pow _ 1 divSmall (by norm_num),
      eval_shl_word _ i (by omega)]
  · simp only [reg_setReg, if_neg notB, if_neg notD, if_neg notE]

/-- **The lane-bit pack** (`lanePack base b`): `rD := laneBit lanes b` for lanes stored as
`word (lanes i).val` at `base + i`; RAM unchanged. -/
theorem exec_lanePack {l : Nat} (base b : Nat) (memory : Memory) (lanes : Lanes l)
    (laneCells : ∀ i : Fin laneCount, memory.ram (word (base + i.val)) = word (lanes i).val)
    (lSmall : l ≤ 256) (bSmall : b < 256) :
    ∃ after, (lanePack base b).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rD = labelWord (laneBit lanes b) ∧
      ∀ register, register ≠ rB → register ≠ rD → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have lc : laneCount = 104 := rfl
  have powL : 2 ^ l ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) lSmall
  set f : Nat → Bool := fun k => if h : k < laneCount then (lanes ⟨k, h⟩).val.testBit b else false
    with fDef
  set m0 := setReg memory rD (word 0) with m0Def
  obtain ⟨m1, run, ram1, bits1, acc1, regs1⟩ := Prog.exec_rep (packLane base b)
    (fun i current => current.ram = memory.ram ∧ current.bits = memory.bits ∧
      BitsUpTo f i (current.registers rD) ∧
      ∀ register, register ≠ rB → register ≠ rD → register ≠ rE → register ≠ rAddr →
        current.registers register = memory.registers register)
    laneCount (fun i bound current holds => by
      obtain ⟨ram, bits, acc, regs⟩ := holds
      set E := (lanes ⟨i, bound⟩).val with EDef
      have ESmall : E < 2 ^ 256 := by
        haveI : NeZero (2 ^ l) := ⟨by positivity⟩
        have := ZMod.val_lt (lanes ⟨i, bound⟩)
        omega
      set m2 := setReg (setReg current rAddr (word (base + i))) rE (current.ram (word (base + i)))
        with m2Def
      have e2 : m2.registers rE = word E := by
        rw [m2Def, reg_setReg, if_pos rfl, ram]; exact laneCells ⟨i, bound⟩
      obtain ⟨m3, run3, ram3, bits3, d3, regs3⟩ := exec_bitInsert b i m2 E e2 ESmall bSmall (by omega)
      have hx : E / 2 ^ b % 2 = 1 ↔ f i = true := by
        rw [fDef]
        simp only [dif_pos bound, EDef, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
      refine ⟨m3, ?_, by rw [ram3, m2Def, ram_setReg, ram_setReg, ram],
        by rw [bits3, m2Def, bits_setReg, bits_setReg, bits], ?_, fun register nB nD nE nAddr => ?_⟩
      · unfold packLane
        rw [exec_loadAt_seq, run3]
      · rw [d3, m2Def, reg_setReg, if_neg (by decide), reg_setReg, if_neg (by decide)]
        exact bitsUpTo_step f i _ acc (E / 2 ^ b) hx (by omega)
      · rw [regs3 register nB nD nE, m2Def, reg_setReg, if_neg nE, reg_setReg, if_neg nAddr,
          regs register nB nD nE nAddr])
    m0 ⟨by rw [m0Def, ram_setReg], by rw [m0Def, bits_setReg],
      by rw [m0Def, reg_setReg, if_pos rfl]; exact bitsUpTo_zero f,
      fun register _ nD _ _ => by rw [m0Def, reg_setReg, if_neg nD]⟩
  exact ⟨m1, by rw [lanePack, exec_cst_seq]; exact run, ram1, bits1,
    bitsUpTo_laneBit lanes b _ acc1, regs1⟩

theorem res_val {rb : Nat} (R P T : ZMod (2 ^ rb)) (q : Nat) :
    (R + (q : ZMod (2 ^ rb)) * (P - T)).val = ((P.val + 2 ^ rb - T.val) * q + R.val) % 2 ^ rb := by
  haveI : NeZero (2 ^ rb) := ⟨by positivity⟩
  have hT : T.val ≤ P.val + 2 ^ rb := by have := ZMod.val_lt T; omega
  have h : (((P.val + 2 ^ rb - T.val) * q + R.val : Nat) : ZMod (2 ^ rb)) =
      R + (q : ZMod (2 ^ rb)) * (P - T) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hT, Nat.cast_add, ZMod.natCast_self,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  rw [← h, ZMod.val_natCast]

/-- Lane `i` of `sub − reduce_w (R + q (P − T))`, as the machine computes it. -/
theorem lane_value {w rb : Nat} (sub : Lanes w) (R P T : Lanes rb) (q : Nat) (i : Fin laneCount) :
    ((sub - reduceTo w (materialize (R + scaleLanes q (P - T)))) i).val =
      ((sub i).val + 2 ^ w - (((P i).val + 2 ^ rb - (T i).val) * q + (R i).val) % 2 ^ rb % 2 ^ w) %
        2 ^ w := by
  rw [Pi.sub_apply, zmod_sub_val' (2 ^ w) (Nat.two_pow_pos w)]
  congr 3
  rw [reduceTo, ZMod.val_natCast, materialize_eq, Pi.add_apply,
    show scaleLanes q (P - T) i = (q : ZMod (2 ^ rb)) * (P i - T i) from rfl, res_val]

/-- **The lane loop of round `n`**: the bit plane `n` of `sub − reduce_w (R + q (P − T))` into `rD`. -/
theorem exec_roundLanes (cells : StageCells) (w rb : Nat) (rbLe : rb ≤ 128) (wSmall : w ≤ 64)
    (n : Nat) (nLt : n < w) (q : Nat) (qSmall : q < 2 ^ 64) (sub : Lanes w) (pin R T : Lanes rb)
    (m0 : Memory) (fReg : m0.registers rF = word q) (dReg : m0.registers rD = word 0)
    (pinCells : ∀ i : Fin laneCount, m0.ram (word (cells.pinBase + i.val)) = word ((pin i).val / 2))
    (pinEven : Parity.EvenLanes pin)
    (castCells : ∀ i : Fin laneCount,
      m0.ram (word (cells.castSumBase + 128 * n + i.val)) = word (T i).val)
    (classCells : ∀ i : Fin laneCount,
      m0.ram (word (cells.classBase + 128 * n + i.val)) = word (R i).val)
    (subCells : ∀ i : Fin laneCount, m0.ram (word (cells.subBase + i.val)) = word (sub i).val) :
    ∃ m1, (Prog.rep laneCount (roundLane cells w rb n)).exec m0 = some m1 ∧ m1.ram = m0.ram ∧
      m1.bits = m0.bits ∧
      m1.registers rD = labelWord (laneBit (sub - reduceTo w (materialize (R + scaleLanes q (pin - T)))) n) ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rD → register ≠ rE → register ≠ rAddr →
        m1.registers register = m0.registers register := by
  haveI : NeZero (2 ^ rb) := ⟨by positivity⟩
  haveI : NeZero (2 ^ w) := ⟨by positivity⟩
  have lc : laneCount = 104 := rfl
  have powW : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) wSmall
  have powRb : 2 ^ rb ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) rbLe
  set A := sub - reduceTo w (materialize (R + scaleLanes q (pin - T))) with ADef
  set f : Nat → Bool := fun k => if h : k < laneCount then (A ⟨k, h⟩).val.testBit n else false with fDef
  obtain ⟨m1, run, ram1, bits1, bits1', regs1⟩ := Prog.exec_rep (roundLane cells w rb n)
    (fun i current => current.ram = m0.ram ∧ current.bits = m0.bits ∧
      BitsUpTo f i (current.registers rD) ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rD → register ≠ rE → register ≠ rAddr →
        current.registers register = m0.registers register)
    laneCount (fun i bound current holds => by
      obtain ⟨ram, bits, acc, regs⟩ := holds
      have fNow : current.registers rF = word q := by
        rw [regs rF (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fReg
      obtain ⟨m2, run2, ram2, bits2, c2, regs2⟩ := exec_roundRes cells rb n i current q
        (pin ⟨i, bound⟩).val (T ⟨i, bound⟩).val (R ⟨i, bound⟩).val fNow
        (by rw [ram]; exact pinCells ⟨i, bound⟩) (pinEven ⟨i, bound⟩) (by rw [ram]; exact castCells ⟨i, bound⟩)
        (by rw [ram]; exact classCells ⟨i, bound⟩) rbLe qSmall (ZMod.val_lt _) (ZMod.val_lt _)
        (ZMod.val_lt _)
      set C := (((pin ⟨i, bound⟩).val + 2 ^ rb - (T ⟨i, bound⟩).val) * q + (R ⟨i, bound⟩).val) % 2 ^ rb
        with CDef
      have CSmall : C < 2 ^ 256 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos rb)) (le_trans powRb (by norm_num))
      obtain ⟨m3, run3, ram3, bits3, e3, regs3⟩ := exec_roundDiff cells w i m2 C (sub ⟨i, bound⟩).val c2
        (by rw [ram2, ram]; exact subCells ⟨i, bound⟩) wSmall CSmall (ZMod.val_lt _)
      set E := ((sub ⟨i, bound⟩).val + 2 ^ w - C % 2 ^ w) % 2 ^ w with EDef
      have ESmall : E < 2 ^ 256 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w)) (le_trans powW (by norm_num))
      obtain ⟨m4, run4, ram4, bits4, d4, regs4⟩ := exec_bitInsert n i m3 E e3 ESmall (by omega)
        (by omega)
      have laneE : (A ⟨i, bound⟩).val = E := by rw [ADef, lane_value]
      have hx : E / 2 ^ n % 2 = 1 ↔ f i = true := by
        rw [fDef]
        simp only [dif_pos bound, laneE, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
      refine ⟨m4, ?_, by rw [ram4, ram3, ram2, ram], by rw [bits4, bits3, bits2, bits], ?_,
        fun register nB nC nD nE nAddr => ?_⟩
      · unfold roundLane
        rw [Prog.exec_seq_some _ _ current m2 run2, Prog.exec_seq_some _ _ m2 m3 run3, run4]
      · rw [d4, regs3 rD (by decide) (by decide) (by decide) (by decide),
          regs2 rD (by decide) (by decide) (by decide) (by decide)]
        exact bitsUpTo_step f i _ acc (E / 2 ^ n) hx (by omega)
      · rw [regs4 register nB nD nE, regs3 register nB nC nE nAddr, regs2 register nB nC nE nAddr,
          regs register nB nC nD nE nAddr])
    m0 ⟨rfl, rfl, by rw [dReg]; exact bitsUpTo_zero f, fun _ _ _ _ _ _ => rfl⟩
  exact ⟨m1, run, ram1, bits1, bitsUpTo_laneBit A n _ bits1', regs1⟩

theorem exec_roundHot (cells : StageCells) (n : Nat) (memory : Memory) (bit J Y A : Label)
    (dReg : memory.registers rD = labelWord bit)
    (joinCell : memory.ram (word (cells.joinBase + n)) = labelWord J)
    (levelCell : memory.ram (word (cells.levelSumBase + n)) = labelWord Y)
    (activeCell : memory.ram (word cells.active) = labelWord A) :
    ∃ after, (roundHot cells n).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rD = labelWord (bit ^^^ J ^^^ Y) ∧
      after.registers rE = labelWord (A ^^^ (bit ^^^ J ^^^ Y)) ∧
      ∀ register, register ≠ rD → register ≠ rE → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, ?_, fun register notD notE notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, dReg, joinCell,
      levelCell, eval_xor, labelWord_xor]
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, dReg, joinCell,
      levelCell, activeCell, eval_xor, labelWord_xor]
  · simp only [reg_setReg, if_neg notD, if_neg notE, if_neg notAddr]

theorem exec_roundTest (cells : StageCells) (n : Nat) (memory : Memory) (value : Nat)
    (valueCell : memory.ram (word cells.value) = word value) (valueSmall : value < 2 ^ 256)
    (nSmall : n < 256) :
    ∃ after, (roundTest cells n).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rA = word (value / 2 ^ n % 2 ^ 1) ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have divSmall : value / 2 ^ n < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) valueSmall
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notA notB notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, valueCell]
    rw [eval_shr_word value n valueSmall (by omega),
      show Arithmetic.and.eval (word (value / 2 ^ n)) (word 1) = word (value / 2 ^ n % 2 ^ 1) from
        eval_and_pow _ 1 divSmall (by norm_num)]
  · simp only [reg_setReg, if_neg notA, if_neg notB, if_neg notAddr]

theorem exec_roundSet (cells : StageCells) (memory : Memory) (q : Nat) (D E : Word)
    (fReg : memory.registers rF = word q) (dReg : memory.registers rD = D)
    (eReg : memory.registers rE = E) (small : cells.nodeBase + q < 2 ^ 256) :
    ∃ after, (roundSet cells).exec memory = some after ∧
      after.ram = Function.update (Function.update (Function.update memory.ram (word cells.active) D)
        (word cells.slot) (word q)) (word (cells.nodeBase + q)) E ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register notB notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reg_storeRam, ram_storeRam,
      reduceIte, fReg, dReg, eReg]
    rw [eval_add_word q cells.nodeBase (by omega), Nat.add_comm q cells.nodeBase]
  · simp only [reg_setReg, reg_storeRam, if_neg notB, if_neg notAddr]

theorem exec_roundClear (cells : StageCells) (n : Nat) (memory : Memory) (q : Nat) (D E : Word)
    (fReg : memory.registers rF = word q) (dReg : memory.registers rD = D)
    (eReg : memory.registers rE = E) (small : cells.nodeBase + (q + 2 ^ n) < 2 ^ 256) :
    ∃ after, (roundClear cells n).exec memory = some after ∧
      after.ram = Function.update (Function.update (Function.update memory.ram (word cells.active) E)
        (word cells.slot) (word (q + 2 ^ n))) (word (cells.nodeBase + (q + 2 ^ n))) D ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rF → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register notB notF notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reg_storeRam, ram_storeRam,
      reduceIte, fReg, dReg, eReg]
    rw [eval_add_word q (2 ^ n) (by omega), eval_add_word (q + 2 ^ n) cells.nodeBase (by omega),
      Nat.add_comm (q + 2 ^ n) cells.nodeBase]
  · simp only [reg_setReg, reg_storeRam, if_neg notB, if_neg notF, if_neg notAddr]

theorem det_roundLane (cells : StageCells) (w rb n i : Nat) :
    (roundLane cells w rb n i).OpsSatisfy Op.Det := by
  unfold roundLane roundRes resHead resTail roundDiff bitInsert
  simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

theorem det_roundPrefix (cells : StageCells) (w rb n : Nat) :
    (roundPrefix cells w rb n).OpsSatisfy Op.Det := by
  unfold roundPrefix roundBit roundHot roundTest roundSet roundClear
  simp only [Prog.OpsSatisfy]
  refine ⟨⟨⟨trivial, trivial⟩, trivial, trivial, trivial,
    det_rep _ _ fun i _ => det_roundLane cells w rb n i, ⟨trivial, trivial⟩⟩, ?_⟩
  simp [Prog.OpsSatisfy, Op.Det, loadAt, storeAt, cst, ar]

/-- The level-`(n + 1)` slot closed in round `n`: the sibling of the path node. -/
def roundSlot (value n : Nat) : Nat := if value.testBit n then value % 2 ^ n else value % 2 ^ n + 2 ^ n

theorem roundSlot_lt (value n : Nat) : roundSlot value n < 2 ^ (n + 1) := by
  have := Nat.mod_lt value (Nat.two_pow_pos n)
  have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  unfold roundSlot; split_ifs <;> omega

theorem roundSlot_low (value n : Nat) : roundSlot value n % 2 ^ n = value % 2 ^ n := by
  unfold roundSlot
  split_ifs
  · exact Nat.mod_mod _ _
  · rw [Nat.add_mod_right, Nat.mod_mod]

theorem roundSlot_ne (value n : Nat) : roundSlot value n ≠ value % 2 ^ (n + 1) := by
  have split := SliceC.mod_two_pow_succ_split value n
  have := Nat.two_pow_pos n
  unfold roundSlot
  split_ifs at split ⊢ <;> omega

theorem word_bit_eq_zero (x : Nat) : word (x % 2 ^ 1) = 0 ↔ x % 2 = 0 := by
  have lt : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [pow_one]
  constructor
  · intro h
    have := word_inj (first := x % 2) (second := 0) (by omega) (by norm_num) h
    exact this
  · intro h; rw [h]; rfl

/-- **The branch of round `n`**: the kept child becomes active, the other is closed at
`roundSlot value n` with its label at its node. -/
theorem exec_roundBranch (cells : StageCells) (w n : Nat) (memory : Memory) (value : Nat) (hot A : Label)
    (fits : cells.nodeBase + 2 ^ w < 2 ^ 256) (nLt : n < w)
    (aReg : memory.registers rA = word (value / 2 ^ n % 2 ^ 1))
    (fReg : memory.registers rF = word (value % 2 ^ n))
    (dReg : memory.registers rD = labelWord hot)
    (eReg : memory.registers rE = labelWord (A ^^^ hot)) :
    ∃ after, (Prog.ite rA (roundSet cells) (roundClear cells n)).exec memory = some after ∧
      after.ram = Function.update (Function.update (Function.update memory.ram (word cells.active)
          (labelWord (if value.testBit n then hot else A ^^^ hot)))
        (word cells.slot) (word (roundSlot value n))) (word (cells.nodeBase + roundSlot value n))
          (labelWord (if value.testBit n then A ^^^ hot else hot)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rB → register ≠ rF → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have slotLt := roundSlot_lt value n
  have powLe : 2 ^ (n + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [exec_ite, aReg]
  by_cases hb : value.testBit n
  · have one : value / 2 ^ n % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb; exact hb
    rw [if_neg (by rw [word_bit_eq_zero]; omega)]
    have slotEq : roundSlot value n = value % 2 ^ n := by unfold roundSlot; rw [if_pos hb]
    obtain ⟨after, run, ram, bits, regs⟩ := exec_roundSet cells memory (value % 2 ^ n) _ _ fReg dReg eReg
      (by rw [← slotEq]; omega)
    refine ⟨after, run, ?_, bits, fun register nB _ nAddr => regs register nB nAddr⟩
    rw [ram, slotEq, if_pos hb, if_pos hb]
  · have zero : value / 2 ^ n % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb; omega
    rw [if_pos ((word_bit_eq_zero _).mpr zero)]
    have slotEq : roundSlot value n = value % 2 ^ n + 2 ^ n := by unfold roundSlot; rw [if_neg hb]
    obtain ⟨after, run, ram, bits, regs⟩ := exec_roundClear cells n memory (value % 2 ^ n) _ _ fReg
      dReg eReg (by rw [← slotEq]; omega)
    refine ⟨after, run, ?_, bits, regs⟩
    rw [ram, slotEq, if_neg hb, if_neg hb]

/-- **The bit label of round `n`** into `rD` and `bits[n]`. -/
theorem exec_roundBit (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb)
    (rbLe : rb ≤ 128) (wSmall : w ≤ 64) (n : Nat) (nLt : n < w) (value : Nat) (valueLt : value < 2 ^ w)
    (sub : Lanes w) (pin R T : Lanes rb) (m : Memory)
    (valueCell : m.ram (word cells.value) = word value)
    (pinCells : ∀ i : Fin laneCount, m.ram (word (cells.pinBase + i.val)) = word ((pin i).val / 2))
    (pinEven : Parity.EvenLanes pin)
    (castCells : ∀ i : Fin laneCount,
      m.ram (word (cells.castSumBase + 128 * n + i.val)) = word (T i).val)
    (classCells : ∀ i : Fin laneCount,
      m.ram (word (cells.classBase + 128 * n + i.val)) = word (R i).val)
    (subCells : ∀ i : Fin laneCount, m.ram (word (cells.subBase + i.val)) = word (sub i).val) :
    ∃ m1, (roundBit cells w rb n).exec m = some m1 ∧
      m1.ram = Function.update m.ram (word (cells.bitBase + n))
        (labelWord (laneBit (sub - reduceTo w (materialize (R + scaleLanes (value % 2 ^ n) (pin - T)))) n)) ∧
      m1.bits = m.bits ∧
      m1.registers rD =
        labelWord (laneBit (sub - reduceTo w (materialize (R + scaleLanes (value % 2 ^ n) (pin - T)))) n) ∧
      m1.registers rF = word (value % 2 ^ n) ∧
      ∀ register, register ≠ rB → register ≠ rC → register ≠ rD → register ≠ rE → register ≠ rF →
        register ≠ rAddr → m1.registers register = m.registers register := by
  have powW : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) wSmall
  have powN : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) nLt.le
  have qSmall : value % 2 ^ n < 2 ^ 64 := by have := Nat.mod_lt value (Nat.two_pow_pos n); omega
  set m0 := setReg (setReg (setReg (setReg (setReg m rAddr (word cells.value)) rF
    (m.ram (word cells.value))) rB (word (2 ^ n - 1))) rF (word (value % 2 ^ n))) rD (word 0) with m0Def
  have ram0 : m0.ram = m.ram := by simp only [m0Def, ram_setReg]
  obtain ⟨m1, run1, ram1, bits1, d1, regs1⟩ := exec_roundLanes cells w rb rbLe wSmall n nLt
    (value % 2 ^ n) qSmall sub pin R T m0
    (by rw [m0Def, reg_setReg, if_neg (by decide), reg_setReg, if_pos rfl])
    (by rw [m0Def, reg_setReg, if_pos rfl])
    (fun i => by rw [ram0]; exact pinCells i) pinEven (fun i => by rw [ram0]; exact castCells i)
    (fun i => by rw [ram0]; exact classCells i) (fun i => by rw [ram0]; exact subCells i)
  refine ⟨storeRam (setReg m1 rAddr (word (cells.bitBase + n))) (word (cells.bitBase + n))
    (m1.registers rD), ?_, ?_, ?_, ?_, ?_, fun register nB nC nD nE nF nAddr => ?_⟩
  · unfold roundBit
    rw [exec_loadAt_seq, exec_cst_seq,
      exec_ar_val _ _ _ _ _ _ (word value) (word (2 ^ n - 1))
        (by rw [reg_setReg, if_neg (by decide), reg_setReg, if_pos rfl, valueCell])
        (by rw [reg_setReg, if_pos rfl]),
      eval_and_pow value n (by omega) (by omega), exec_cst_seq, ← m0Def,
      Prog.exec_seq_some _ _ m0 m1 run1, exec_storeAt _ _ _ (by decide)]
  · rw [ram_storeRam, ram_setReg, ram1, ram0, d1]
  · rw [bits_storeRam, bits_setReg, bits1, m0Def]
    simp only [bits_setReg]
  · rw [reg_storeRam, reg_setReg, if_neg (by decide), d1]
  · rw [reg_storeRam, reg_setReg, if_neg (by decide),
      regs1 rF (by decide) (by decide) (by decide) (by decide) (by decide), m0Def, reg_setReg,
      if_neg (by decide), reg_setReg, if_pos rfl]
  · rw [reg_storeRam, reg_setReg, if_neg nAddr, regs1 register nB nC nD nE nAddr, m0Def]
    simp only [reg_setReg, if_neg nD, if_neg nF, if_neg nB, if_neg nAddr]

/-! ### The inputs of a stage -/

/-- The stage's inputs in RAM: the stage value, the remainder label's lanes, the joins, the pin. -/
structure StageInputs (cells : StageCells) (w rb value : Nat) (remainder : Lanes rb)
    (joins : Nat → Label) (pin : Lanes rb) (m : Memory) : Prop where
  valueCell : m.ram (word cells.value) = word value
  remCells : ∀ i : Fin laneCount, m.ram (word (cells.remBase + i.val)) = word (remainder i).val
  joinCells : ∀ n, 1 ≤ n → n < w → m.ram (word (cells.joinBase + n)) = labelWord (joins n)
  pinCells : ∀ i : Fin laneCount, m.ram (word (cells.pinBase + i.val)) = word ((pin i).val / 2)
  pinEven : Parity.EvenLanes pin

theorem not_sw_below (cells : StageCells) (w rb : Nat) (layout : StageLayout cells w rb) {k : Nat}
    (hk : k < cells.subBase) : ¬ stageWrites cells w rb (word k) := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have lc : laneCount = 104 := rfl
  have hw := Nat.two_pow_pos w
  intro h
  simp only [stageWrites, Writes.union, Writes.region, Writes.cell, Region.Holds] at h
  rcases h with ⟨a, ab, h⟩ | ⟨a, ab, h⟩ | ⟨a, ab, h⟩ | ⟨a, ab, h⟩ | ⟨a, ab, h⟩ | ⟨a, ab, h⟩ |
    ⟨a, ab, h⟩ | ⟨a, ab, h⟩ | h | h | ⟨a, ab, h⟩ | ⟨a, ab, h⟩ <;>
    exact absurd h (word_ne (by omega) (by omega) (by omega))

theorem StageInputs.at {cells : StageCells} {w rb value : Nat} {remainder : Lanes rb}
    {joins : Nat → Label} {pin : Lanes rb} {mStart m : Memory}
    (inputs : StageInputs cells w rb value remainder joins pin mStart) (layout : StageLayout cells w rb)
    (frame : Frame (stageWrites cells w rb) stageClobbers mStart m) :
    StageInputs cells w rb value remainder joins pin m := by
  have c1 := layout.c1; have c2 := layout.c2; have c3 := layout.c3; have c4 := layout.c4
  have lc : laneCount = 104 := rfl
  refine ⟨?_, fun i => ?_, fun n h1 h2 => ?_, fun i => ?_, inputs.pinEven⟩
  · rw [frame.ram _ (not_sw_below cells w rb layout c1)]; exact inputs.valueCell
  · rw [frame.ram _ (not_sw_below cells w rb layout (by have := i.isLt; omega))]
    exact inputs.remCells i
  · rw [frame.ram _ (not_sw_below cells w rb layout (by omega))]; exact inputs.joinCells n h1 h2
  · rw [frame.ram _ (not_sw_below cells w rb layout (by have := i.isLt; omega))]
    exact inputs.pinCells i

/-! ### The state after the deterministic part of a round -/

/-- The bit label `b_n^E` of round `n`. -/
def roundBitLabel {rb : Nat} (w : Nat) (sub : Lanes w) (pin : Lanes rb) (value n : Nat)
    (state : StageState rb) : Label :=
  laneBit (sub - reduceTo w (materialize (state.classSum n + scaleLanes (value % 2 ^ n)
    (pin - state.castSum n)))) n

/-- The hot material `b_n^E ⊕ J_n ⊕ Y_n` of round `n`. -/
def roundHotLabel {rb : Nat} (w : Nat) (sub : Lanes w) (pin : Lanes rb) (joins : Nat → Label)
    (value n : Nat) (state : StageState rb) : Label :=
  roundBitLabel w sub pin value n state ^^^ joins n ^^^ state.levelSum n

/-- The state after the deterministic part of round `n`: the kept child active, bit `n` known. -/
def roundState {rb : Nat} (w : Nat) (sub : Lanes w) (pin : Lanes rb) (joins : Nat → Label)
    (value n : Nat) (state : StageState rb) : StageState rb :=
  { state with
    active := if value.testBit n then roundHotLabel w sub pin joins value n state
      else state.active ^^^ roundHotLabel w sub pin joins value n state
    bits := fun k => if k = n then roundBitLabel w sub pin value n state else state.bits k }

/-- **The deterministic part of round `n`**: from the state with `n` levels closed and `n` bits
known to the state with bit `n` known, the kept child active, and the other child's label at its
node, its slot in `cells.slot`. -/
theorem exec_roundPrefix (cells : StageCells) (w rb value : Nat) (sub : Lanes w)
    (remainder : Lanes rb) (joins : Nat → Label) (pin : Lanes rb) (layout : StageLayout cells w rb)
    (rbLe : rb ≤ 128) (wSmall : w ≤ 64) (n : Nat) (nPos : 1 ≤ n) (nLt : n < w)
    (valueLt : value < 2 ^ w) (mStart : Memory)
    (inputs : StageInputs cells w rb value remainder joins pin mStart) (state : StageState rb)
    (m : Memory) (rel : StageRel cells w rb value sub n n mStart state m) :
    ∃ m1, (roundPrefix cells w rb n).exec m = some m1 ∧
      StageRel cells w rb value sub n (n + 1) mStart (roundState w sub pin joins value n state) m1 ∧
      m1.ram (word cells.slot) = word (roundSlot value n) ∧
      m1.ram (word (cells.nodeBase + roundSlot value n)) =
        labelWord (if value.testBit n then state.active ^^^ roundHotLabel w sub pin joins value n state
          else roundHotLabel w sub pin joins value n state) := by
  have c5 := layout.c5; have c6 := layout.c6; have c11 := layout.c11; have c12 := layout.c12
  have c13 := layout.c13; have c14 := layout.c14; have c15 := layout.c15; have c16 := layout.c16
  have c7 := layout.c7; have c8 := layout.c8; have c9 := layout.c9; have c10 := layout.c10
  have c1 := layout.c1; have c2 := layout.c2; have c3 := layout.c3; have c4 := layout.c4
  have lc : laneCount = 104 := rfl
  have powW : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) wSmall
  have powN1 : 2 ^ (n + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) nLt
  have slotLt := roundSlot_lt value n
  have inM := inputs.at layout rel.frame
  obtain ⟨m1, run1, ram1, bits1, d1, f1, regs1⟩ := exec_roundBit cells w rb layout rbLe wSmall n nLt
    value valueLt sub pin (state.classSum n) (state.castSum n) m inM.valueCell inM.pinCells inM.pinEven
    (fun i => (rel.sums n nLt.le i).2) (fun i => (rel.sums n nLt.le i).1) rel.subCells
  have off1 : ∀ k, k ≠ cells.bitBase + n → k < 2 ^ 256 → m1.ram (word k) = m.ram (word k) :=
    fun k hk kb => by rw [ram1, Function.update_of_ne (word_ne kb (by omega) hk)]
  obtain ⟨m2, run2, ram2, bits2, d2, e2, regs2⟩ := exec_roundHot cells n m1
    (roundBitLabel w sub pin value n state) (joins n) (state.levelSum n) state.active d1
    (by rw [off1 _ (by omega) (by omega)]; exact inM.joinCells n nPos nLt)
    (by rw [off1 _ (by omega) (by omega)]; exact rel.levelSums n nLt)
    (by rw [off1 _ (by omega) (by omega)]; exact rel.active)
  obtain ⟨m3, run3, ram3, bits3, a3, regs3⟩ := exec_roundTest cells n m2 value
    (by rw [ram2, off1 _ (by omega) (by omega)]; exact inM.valueCell) (by omega) (by omega)
  obtain ⟨m4, run4, ram4, bits4, regs4⟩ := exec_roundBranch cells w n m3 value
    (roundHotLabel w sub pin joins value n state) state.active (by omega) nLt a3
    (by rw [regs3 rF (by decide) (by decide) (by decide), regs2 rF (by decide) (by decide) (by decide)]
        exact f1)
    (by rw [regs3 rD (by decide) (by decide) (by decide)]; exact d2)
    (by rw [regs3 rE (by decide) (by decide) (by decide)]; exact e2)
  have hram : ∀ k, k ≠ cells.active → k ≠ cells.slot → k ≠ cells.nodeBase + roundSlot value n →
      k ≠ cells.bitBase + n → k < 2 ^ 256 → m4.ram (word k) = m.ram (word k) := by
    intro k h1 h2 h3 h4 kb
    rw [ram4, Function.update_of_ne (word_ne kb (by omega) h3),
      Function.update_of_ne (word_ne kb (by omega) h2), Function.update_of_ne (word_ne kb (by omega) h1),
      ram3, ram2, off1 k h4 kb]
  refine ⟨m4, ?_, ⟨fun L Lw => ?_, ?_, ?_, fun b bLt => ?_, fun α αb αNe => ?_, fun i => ?_,
    ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩, ?_, ?_⟩
  · unfold roundPrefix
    rw [Prog.exec_seq_some _ _ m m1 run1, Prog.exec_seq_some _ _ m1 m2 run2,
      Prog.exec_seq_some _ _ m2 m3 run3, run4]
  · rw [hram _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact rel.levelSums L Lw
  · exact rel.sums.transfer fun j jb i ib =>
      ⟨hram _ (by omega) (by omega) (by omega) (by omega) (by omega),
        hram _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · rw [ram4, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
      Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), Function.update_self]
    rfl
  · by_cases here : b = n
    · subst here
      rw [ram4, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
        Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
        Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), ram3, ram2, ram1,
        Function.update_self]
      show _ = labelWord (if b = b then _ else _)
      rw [if_pos rfl]
      rfl
    · rw [hram _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      show _ = labelWord (if b = n then _ else _)
      rw [if_neg here]
      exact rel.bits b (by omega)
  · have ne : α ≠ roundSlot value n := fun same => αNe (by rw [same, roundSlot_low])
    rw [hram _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact rel.leaves α αb αNe
  · rw [hram _ (by have := i.isLt; omega) (by have := i.isLt; omega) (by have := i.isLt; omega)
      (by have := i.isLt; omega) (by have := i.isLt; omega)]
    exact rel.subCells i
  · have sa := ne_of_sw outside (sw_active cells w rb)
    have ss := ne_of_sw outside (sw_slot cells w rb)
    have sn := ne_of_sw outside (sw_node cells w rb (x := roundSlot value n) (by omega))
    have sb := ne_of_sw outside (sw_bit cells w rb nLt)
    rw [ram4, Function.update_of_ne sn, Function.update_of_ne ss, Function.update_of_ne sa, ram3, ram2,
      ram1, Function.update_of_ne sb]
    exact rel.frame.ram address outside
  · rw [bits4, bits3, bits2, bits1, rel.frame.bits]
  · rw [regs4 register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rF (by simp))
      (ne_of_not_stage outside rAddr (by simp)),
      regs3 register (ne_of_not_stage outside rA (by simp)) (ne_of_not_stage outside rB (by simp))
      (ne_of_not_stage outside rAddr (by simp)),
      regs2 register (ne_of_not_stage outside rD (by simp)) (ne_of_not_stage outside rE (by simp))
      (ne_of_not_stage outside rAddr (by simp)),
      regs1 register (ne_of_not_stage outside rB (by simp)) (ne_of_not_stage outside rC (by simp))
      (ne_of_not_stage outside rD (by simp)) (ne_of_not_stage outside rE (by simp))
      (ne_of_not_stage outside rF (by simp)) (ne_of_not_stage outside rAddr (by simp))]
    exact rel.frame.registers register outside
  · rw [ram4, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), Function.update_self]
  · rw [ram4, Function.update_self]

end Kriterion.CRT.SimMachine
