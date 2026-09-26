/-
**The fraction reading of a pad integer**.

For a `B`-bit pad integer `u` (`B = 128 · count`, `count` limbs), the fraction reading takes the
base-`m` digits of `⌊u · m ^ S / 2 ^ B⌋`. The machine computes them top digit first, with no
division: pass `j` multiplies the `count`-limb integer `f_j = u · m ^ j mod 2 ^ B` by `m`; the
carry out is the next digit and the limbs become `f_(j+1)`.

* `frac_digit`: the carry of pass `j` is `⌊u · m ^ (j + 1) / 2 ^ B⌋ mod m` (by `Nat.div_add_mod`);
* `frac_digit_top`: that is digit `S - 1 - j` of `⌊u · m ^ S / 2 ^ B⌋`, so pass `j` reads the digit of
  encoding `S - 1 - j`;
* `exec_fracPass`, `exec_fracDigits`: the machine blocks, with their frame.
-/

import Proof.Simulator.CRT.Limbs

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! ### The arithmetic -/

/-- **One digit of the fraction reading.** For `f = u · m ^ j mod 2 ^ B`, the carry of `f · m`
past `2 ^ B` is `⌊u · m ^ (j + 1) / 2 ^ B⌋ mod m`. -/
theorem frac_digit (u m j B : Nat) :
    u * m ^ j % 2 ^ B * m / 2 ^ B = u * m ^ (j + 1) / 2 ^ B % m := by
  rcases Nat.eq_zero_or_pos m with zero | mPos
  · subst zero; simp
  have split : u * m ^ (j + 1) = (u * m ^ j % 2 ^ B * m) + (u * m ^ j / 2 ^ B * m) * 2 ^ B := by
    have := Nat.mod_add_div (u * m ^ j) (2 ^ B)
    rw [pow_succ]
    calc u * (m ^ j * m) = (u * m ^ j) * m := by ring
      _ = (u * m ^ j % 2 ^ B + 2 ^ B * (u * m ^ j / 2 ^ B)) * m := by rw [this]
      _ = _ := by ring
  rw [split, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
  exact (Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul
    (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by positivity)) mPos))).symm

/-- **The pass-`j` digit is digit `S - 1 - j`** of `⌊u · m ^ S / 2 ^ B⌋`. -/
theorem frac_digit_top (u m S j B : Nat) (below : j < S) :
    u * m ^ S / 2 ^ B / m ^ (S - 1 - j) % m = u * m ^ (j + 1) / 2 ^ B % m := by
  rcases Nat.eq_zero_or_pos m with zero | mPos
  · subst zero
    have zeroS : (0 : Nat) ^ S = 0 := zero_pow (by omega)
    simp [zeroS]
  rw [Nat.div_div_eq_div_mul, show u * m ^ S = u * m ^ (j + 1) * m ^ (S - 1 - j) by
      rw [Nat.mul_assoc, ← pow_add, show j + 1 + (S - 1 - j) = S by omega],
    Nat.mul_div_mul_right _ _ (by positivity)]

/-- The next remainder. -/
theorem frac_next (u m j B : Nat) :
    u * m ^ j % 2 ^ B * m % 2 ^ B = u * m ^ (j + 1) % 2 ^ B := by
  rw [Nat.mod_mul_mod, pow_succ, Nat.mul_assoc]

/-- Limbs below `count` see only the residue modulo `2 ^ (128 · count)`. -/
theorem limbOf_mod (value count k : Nat) (below : k < count) :
    limbOf (value % 2 ^ (128 * count)) k = limbOf value k := by
  have high := limbOf_add_high (value % 2 ^ (128 * count)) (value / 2 ^ (128 * count)) count k below
  rw [Nat.mod_add_div'] at high
  exact high.symm

/-! ### One pass -/

/-- **One pass of the fraction reading**: the limbs `f → f · m mod 2 ^ B`, the carry
`f · m / 2 ^ B` stored at `dst`. -/
theorem exec_fracPass (base count dst : Nat) (f m : Nat) (memory : Memory)
    (fits : base + count ≤ 2 ^ 256) (dstSmall : dst < 2 ^ 256)
    (dstOut : ∀ k, k < count → dst ≠ base + k)
    (cells : ∀ k, k < count → memory.ram (word (base + k)) = word (limbOf f k))
    (fSmall : f < 2 ^ (128 * count)) (consts : LimbConsts memory m) (mSmall : m < 2 ^ 128) :
    ∃ after, (fracPass base count dst).exec memory = some after ∧
      after.ram (word dst) = word (f * m / 2 ^ (128 * count)) ∧
      (∀ k, k < count → after.ram (word (base + k)) = word (limbOf (f * m % 2 ^ (128 * count)) k)) ∧
      (∀ address, (∀ k, k < count → address ≠ word (base + k)) → address ≠ word dst →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨mReg, maskReg, shiftReg⟩ := consts
  set start := setReg memory rC (word 0) with startDef
  have startConsts : LimbConsts start m := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [startDef, reg_setReg] <;>
      simp (config := { decide := true }) only [reduceIte] <;> assumption
  have limbsValue : limbValue (limbOf f) count = f := by
    rw [limbValue_limbOf, Nat.mod_eq_of_lt fSmall]
  obtain ⟨middle, run, limbs, carry, frame, bitsSame, regs⟩ :=
    exec_mulSmallAdd base count (limbOf f) m 0 start fits cells (limbOf_lt f) startConsts
      (by rw [startDef, reg_setReg, if_pos rfl]) mSmall (by norm_num)
  rw [limbsValue, Nat.add_zero] at limbs carry
  have runAll : (fracPass base count dst).exec memory =
      (storeAt dst rC).exec middle := by
    unfold fracPass
    rw [Prog.exec_seq_some _ _ memory start rfl, Prog.exec_seq_some _ _ start middle run]
  refine ⟨_, runAll, ?_, fun k bound => ?_, fun address off notDst => ?_, ?_, fun register notA notB notC notAddr => ?_⟩
  · show (storeRam (setReg middle rAddr (word dst)) _ _).ram (word dst) = _
    simp (config := { decide := true }) only [ram_storeRam, reg_setReg, reduceIte,
      Function.update_self]
    exact carry
  · show (storeRam (setReg middle rAddr (word dst)) _ _).ram (word (base + k)) = _
    simp (config := { decide := true }) only [ram_storeRam, reg_setReg, reduceIte, ram_setReg]
    rw [Function.update_of_ne (word_ne (by omega) dstSmall (fun same => dstOut k bound same.symm)),
      limbs k bound, limbOf_mod _ _ _ bound]
  · show (storeRam (setReg middle rAddr (word dst)) _ _).ram address = _
    simp (config := { decide := true }) only [ram_storeRam, reg_setReg, reduceIte, ram_setReg]
    rw [Function.update_of_ne notDst, frame address off]
    rfl
  · show (storeRam (setReg middle rAddr (word dst)) _ _).bits = _
    rw [bits_storeRam, bits_setReg, bitsSame]
    rfl
  · show (storeRam (setReg middle rAddr (word dst)) _ _).registers register = _
    rw [reg_storeRam, reg_setReg, if_neg notAddr, regs register notA notB notC notAddr, startDef,
      reg_setReg, if_neg notC]

theorem det_fracPass (base count dst : Nat) : (fracPass base count dst).OpsSatisfy Op.Det :=
  ⟨trivial, det_mulSmallAdd base count, trivial, trivial⟩

/-! ### All passes -/

/-- The loop invariant of `fracDigits` after `j` passes. -/
def FracInv (base count digits : Nat) (dst : Nat → Nat) (u m : Nat) (start : Memory) (j : Nat)
    (memory : Memory) : Prop :=
  (∀ i, i < j → memory.ram (word (dst i)) = word (u * m ^ (i + 1) / 2 ^ (128 * count) % m)) ∧
    (∀ k, k < count → memory.ram (word (base + k)) = word (limbOf (u * m ^ j % 2 ^ (128 * count)) k)) ∧
    (∀ address, (∀ k, k < count → address ≠ word (base + k)) →
      (∀ i, i < digits → address ≠ word (dst i)) → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
      memory.registers register = start.registers register

/-- **The fraction reading**: pass `j` stores `⌊u · m ^ (j + 1) / 2 ^ B⌋ mod m` at `dst j`, which
is digit `S - 1 - j` of `⌊u · m ^ S / 2 ^ B⌋` (`frac_digit_top`). -/
theorem exec_fracDigits (base count digits : Nat) (dst : Nat → Nat) (u m : Nat) (memory : Memory)
    (fits : base + count ≤ 2 ^ 256) (dstSmall : ∀ j, j < digits → dst j < 2 ^ 256)
    (dstOut : ∀ j, j < digits → ∀ k, k < count → dst j ≠ base + k)
    (dstInj : ∀ i j, i < digits → j < digits → i ≠ j → dst i ≠ dst j)
    (cells : ∀ k, k < count → memory.ram (word (base + k)) = word (limbOf u k))
    (uSmall : u < 2 ^ (128 * count)) (consts : LimbConsts memory m) (mSmall : m < 2 ^ 128) :
    ∃ after, (fracDigits base count digits dst).exec memory = some after ∧
      (∀ j, j < digits → after.ram (word (dst j)) =
        word (u * m ^ (j + 1) / 2 ^ (128 * count) % m)) ∧
      (∀ k, k < count → after.ram (word (base + k)) =
        word (limbOf (u * m ^ digits % 2 ^ (128 * count)) k)) ∧
      (∀ address, (∀ k, k < count → address ≠ word (base + k)) →
        (∀ j, j < digits → address ≠ word (dst j)) → after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨mReg, maskReg, shiftReg⟩ := consts
  obtain ⟨after, run, inv⟩ := Prog.exec_rep (fun j => fracPass base count (dst j))
    (FracInv base count digits dst u m memory) digits (fun j bound current holds => by
      obtain ⟨done, limbs, frame, bitsSame, regs⟩ := holds
      have constsNow : LimbConsts current m :=
        ⟨by rw [regs rM (by decide) (by decide) (by decide) (by decide), mReg],
          by rw [regs rMask (by decide) (by decide) (by decide) (by decide), maskReg],
          by rw [regs rK128 (by decide) (by decide) (by decide) (by decide), shiftReg]⟩
      obtain ⟨next, step, digit, limbsNext, frameNext, bitsNext, regsNext⟩ :=
        exec_fracPass base count (dst j) (u * m ^ j % 2 ^ (128 * count)) m current fits
          (dstSmall j bound) (dstOut j bound) limbs (Nat.mod_lt _ (by positivity)) constsNow mSmall
      refine ⟨next, step, fun i ib => ?_, fun k kb => ?_, fun address offLimbs offDst => ?_, ?_,
        fun register notA notB notC notAddr => ?_⟩
      · by_cases last : i = j
        · subst last
          rw [digit, frac_digit]
        · rw [frameNext _ (fun k kb => fun same => dstOut i (by omega) k kb (word_inj
              (dstSmall i (by omega)) (by omega) same))
            (fun same => dstInj i j (by omega) bound last (word_inj (dstSmall i (by omega))
              (dstSmall j bound) same)), done i (by omega)]
      · rw [limbsNext k kb, frac_next]
      · rw [frameNext address offLimbs (offDst j bound), frame address offLimbs offDst]
      · rw [bitsNext, bitsSame]
      · rw [regsNext register notA notB notC notAddr, regs register notA notB notC notAddr])
    memory ⟨fun i bound => absurd bound (by omega), fun k bound => by
        rw [pow_zero, Nat.mul_one, Nat.mod_eq_of_lt uSmall]; exact cells k bound,
      fun _ _ _ => rfl, rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨done, limbs, frame, bitsSame, regs⟩ := inv
  exact ⟨after, run, done, limbs, frame, bitsSame, regs⟩

theorem det_fracDigits (base count digits : Nat) (dst : Nat → Nat) :
    (fracDigits base count digits dst).OpsSatisfy Op.Det :=
  det_rep _ _ fun j _ => det_fracPass base count (dst j)

end Kriterion.CRT.SimMachine
