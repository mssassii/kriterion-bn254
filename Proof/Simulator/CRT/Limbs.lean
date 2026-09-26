/-
**`mulSmallAdd` over 128-bit limbs**.

`mulSmallAdd base count` replaces the `count`-limb integer `X` at `RAM[base …]` by
`(X · m + c) mod 2 ^ (128 · count)` and leaves the carry `(X · m + c) / 2 ^ (128 · count)` in
`rC`, when `m` and `c` are below `2 ^ 128` (`exec_mulSmallAdd`). Every product fits a word:
`limb · m + carry ≤ (2 ^ 128 - 1) ^ 2 + 2 ^ 128 - 1 < 2 ^ 256`.

Frame: the block writes the `count` limb cells and the registers `rA`, `rB`, `rC`, `rAddr`;
every other RAM cell, every other register and the stacks are unchanged.
-/

import Proof.Simulator.CRT.Exec

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! ### Limb arithmetic on `Nat` -/

/-- The integer of `count` little-endian 128-bit limbs. -/
def limbValue (limb : Nat → Nat) (count : Nat) : Nat :=
  ∑ k ∈ Finset.range count, limb k * 2 ^ (128 * k)

/-- Limb `k` of a natural number. -/
def limbOf (value k : Nat) : Nat := value / 2 ^ (128 * k) % 2 ^ 128

theorem limbValue_succ (limb : Nat → Nat) (count : Nat) :
    limbValue limb (count + 1) = limbValue limb count + limb count * 2 ^ (128 * count) := by
  unfold limbValue
  rw [Finset.sum_range_succ]

theorem limbValue_lt (limb : Nat → Nat) (small : ∀ k, limb k < 2 ^ 128) :
    ∀ count, limbValue limb count < 2 ^ (128 * count)
  | 0 => by simp [limbValue]
  | count + 1 => by
      rw [limbValue_succ]
      have ih := limbValue_lt limb small count
      have top : limb count * 2 ^ (128 * count) ≤ (2 ^ 128 - 1) * 2 ^ (128 * count) :=
        Nat.mul_le_mul_right _ (by have := small count; omega)
      have split : 2 ^ (128 * (count + 1)) = 2 ^ 128 * 2 ^ (128 * count) := by
        rw [Nat.mul_succ, pow_add, Nat.mul_comm]
      rw [split]
      have expand : (2 ^ 128 - 1) * 2 ^ (128 * count) + 2 ^ (128 * count) =
          2 ^ 128 * 2 ^ (128 * count) := by
        rw [Nat.sub_mul, one_mul]
        have : 2 ^ (128 * count) ≤ 2 ^ 128 * 2 ^ (128 * count) :=
          Nat.le_mul_of_pos_left _ (by positivity)
        omega
      omega

/-- The limbs below `i` do not see a multiple of `2 ^ (128 · i)`. -/
theorem limbOf_add_high (low high i k : Nat) (below : k < i) :
    limbOf (low + high * 2 ^ (128 * i)) k = limbOf low k := by
  unfold limbOf
  have split : 2 ^ (128 * i) = 2 ^ (128 * k) * (2 ^ 128 * 2 ^ (128 * (i - k - 1))) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [split, show high * (2 ^ (128 * k) * (2 ^ 128 * 2 ^ (128 * (i - k - 1)))) =
      (2 ^ 128 * (high * 2 ^ (128 * (i - k - 1)))) * 2 ^ (128 * k) by ring,
    Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- The step of the carry chain. -/
theorem carry_step (low high i : Nat) :
    (low + high * 2 ^ (128 * i)) / 2 ^ (128 * i) = low / 2 ^ (128 * i) + high :=
  Nat.add_mul_div_right _ _ (by positivity)

theorem div_succ_limb (value i : Nat) :
    value / 2 ^ (128 * (i + 1)) = value / 2 ^ (128 * i) / 2 ^ 128 := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ]

/-- A limb times a small multiplier plus a small carry fits a word, and its high part is a limb. -/
theorem limb_mul_add_lt (x m c : Nat) (xSmall : x < 2 ^ 128) (mSmall : m < 2 ^ 128)
    (cSmall : c < 2 ^ 128) : x * m + c < 2 ^ 256 ∧ (x * m + c) / 2 ^ 128 < 2 ^ 128 := by
  have prod : x * m ≤ (2 ^ 128 - 1) * (2 ^ 128 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have total : x * m + c < 2 ^ 128 * 2 ^ 128 := by
    have : (2 ^ 128 - 1) * (2 ^ 128 - 1) + (2 ^ 128 - 1) < 2 ^ 128 * 2 ^ 128 := by norm_num
    omega
  refine ⟨by rw [show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by norm_num]; exact total, ?_⟩
  exact Nat.div_lt_of_lt_mul total

/-! ### One limb -/

/-- The block constants of `mulSmallAdd` are in place. -/
def LimbConsts (memory : Memory) (m : Nat) : Prop :=
  memory.registers rM = word m ∧ memory.registers rMask = word limbMask ∧
    memory.registers rK128 = word 128

/-- **One limb** of `mulSmallAdd`. -/
theorem exec_limb (base k : Nat) (memory : Memory) (x m c : Nat)
    (xCell : memory.ram (word (base + k)) = word x) (consts : LimbConsts memory m)
    (cReg : memory.registers rC = word c) (xSmall : x < 2 ^ 128) (mSmall : m < 2 ^ 128)
    (cSmall : c < 2 ^ 128) :
    ∃ after, (mulSmallAddLimb base k).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (base + k)) (word ((x * m + c) % 2 ^ 128)) ∧
      after.registers rC = word ((x * m + c) / 2 ^ 128) ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨mReg, maskReg, shiftReg⟩ := consts
  obtain ⟨fits, _⟩ := limb_mul_add_lt x m c xSmall mSmall cSmall
  have prodFits : x * m < 2 ^ 256 := by omega
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte,
      xCell, mReg, maskReg, cReg]
    rw [eval_mul_word _ _ prodFits, eval_add_word _ _ fits, eval_and_mask _ fits]
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reg_storeRam,
      reduceIte, xCell, mReg, shiftReg, cReg]
    rw [eval_mul_word _ _ prodFits, eval_add_word _ _ fits, eval_shr_word _ _ fits (by norm_num)]
  · rfl
  · intro register notA notB notC notAddr
    simp only [reg_storeRam, reg_setReg, if_neg notA, if_neg notB, if_neg notC, if_neg notAddr]

/-! ### The whole pass -/

/-- The loop invariant of `mulSmallAdd` after `i` limbs. -/
def LimbInv (base count : Nat) (x : Nat → Nat) (m c : Nat) (start : Memory) (i : Nat)
    (memory : Memory) : Prop :=
  (∀ k, k < i → memory.ram (word (base + k)) =
      word (limbOf (limbValue x i * m + c) k)) ∧
    (∀ k, i ≤ k → k < count → memory.ram (word (base + k)) = word (x k)) ∧
    memory.registers rC = word ((limbValue x i * m + c) / 2 ^ (128 * i)) ∧
    (limbValue x i * m + c) / 2 ^ (128 * i) < 2 ^ 128 ∧
    (∀ address, (∀ k, k < count → address ≠ word (base + k)) → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
      memory.registers register = start.registers register

theorem limbOf_lt (value k : Nat) : limbOf value k < 2 ^ 128 := Nat.mod_lt _ (by positivity)

/-- **`mulSmallAdd`**: the limbs of `X · m + c` below `2 ^ (128 · count)`, the carry above. -/
theorem exec_mulSmallAdd (base count : Nat) (x : Nat → Nat) (m c : Nat) (memory : Memory)
    (fits : base + count ≤ 2 ^ 256)
    (cells : ∀ k, k < count → memory.ram (word (base + k)) = word (x k))
    (xSmall : ∀ k, x k < 2 ^ 128) (consts : LimbConsts memory m)
    (cReg : memory.registers rC = word c) (mSmall : m < 2 ^ 128) (cSmall : c < 2 ^ 128) :
    ∃ after, (mulSmallAdd base count).exec memory = some after ∧
      (∀ k, k < count → after.ram (word (base + k)) =
        word (limbOf (limbValue x count * m + c) k)) ∧
      after.registers rC = word ((limbValue x count * m + c) / 2 ^ (128 * count)) ∧
      (∀ address, (∀ k, k < count → address ≠ word (base + k)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have cellNe : ∀ j k, j < count → k < count → j ≠ k → word (base + j) ≠ word (base + k) :=
    fun j k jb kb ne => word_ne (by omega) (by omega) (by omega)
  obtain ⟨after, run, inv⟩ := Prog.exec_rep (mulSmallAddLimb base)
    (LimbInv base count x m c memory) count (fun i bound current holds => by
      obtain ⟨done, todo, carry, carrySmall, frame, bitsSame, regs⟩ := holds
      obtain ⟨mReg, maskReg, shiftReg⟩ := consts
      have constsNow : LimbConsts current m :=
        ⟨by rw [regs rM (by decide) (by decide) (by decide) (by decide), mReg],
          by rw [regs rMask (by decide) (by decide) (by decide) (by decide), maskReg],
          by rw [regs rK128 (by decide) (by decide) (by decide) (by decide), shiftReg]⟩
      have expand : (limbValue x i + x i * 2 ^ (128 * i)) * m + c =
          (limbValue x i * m + c) + (x i * m) * 2 ^ (128 * i) := by ring
      obtain ⟨next, step, ram, carryNext, bitsNext, regsNext⟩ :=
        exec_limb base i current (x i) m _ (todo i le_rfl bound) constsNow carry (xSmall i) mSmall
          carrySmall
      refine ⟨next, step, fun k kb => ?_, fun k lo hi => ?_, ?_, ?_, fun address off => ?_, ?_,
        fun register notA notB notC notAddr => ?_⟩
      · rw [ram, limbValue_succ, expand]
        by_cases last : k = i
        · subst last
          rw [Function.update_self]
          unfold limbOf
          rw [carry_step, Nat.add_comm (x k * m)]
        · rw [Function.update_of_ne (cellNe k i (by omega) bound last), done k (by omega),
            limbOf_add_high _ _ _ _ (by omega)]
      · rw [ram, Function.update_of_ne (cellNe k i (by omega) bound (by omega)), todo k (by omega) hi]
      · rw [carryNext, limbValue_succ, expand, div_succ_limb, carry_step, Nat.add_comm (x i * m)]
      · rw [limbValue_succ, expand, div_succ_limb, carry_step, Nat.add_comm _ (x i * m)]
        exact (limb_mul_add_lt (x i) m _ (xSmall i) mSmall carrySmall).2
      · rw [ram, Function.update_of_ne (off i bound), frame address off]
      · rw [bitsNext, bitsSame]
      · rw [regsNext register notA notB notC notAddr, regs register notA notB notC notAddr])
    memory ⟨fun k bound => absurd bound (by omega), fun k _ bound => cells k bound,
      by simp [limbValue, cReg], by simpa [limbValue] using cSmall, fun _ _ => rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  obtain ⟨done, _, carry, _, frame, bitsSame, regs⟩ := inv
  exact ⟨after, run, done, carry, frame, bitsSame, regs⟩

/-- `exec_mulSmallAdd`'s frame in the schema. -/
theorem frame_mulSmallAdd (base count : Nat) (memory after : Memory)
    (fits : base + count ≤ 2 ^ 256)
    (frame : ∀ address, (∀ k, k < count → address ≠ word (base + k)) →
      after.ram address = memory.ram address)
    (bitsSame : after.bits = memory.bits)
    (regs : ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
      after.registers register = memory.registers register) :
    Frame (mulSmallAddWrites base count) limbClobbers memory after where
  ram address outside := frame address fun k bound same => outside ⟨k, bound, same⟩
  bits := bitsSame
  registers register outside := regs register
    (fun h => outside (by simp [limbClobbers, Clobbers.ofList, h]))
    (fun h => outside (by simp [limbClobbers, Clobbers.ofList, h]))
    (fun h => outside (by simp [limbClobbers, Clobbers.ofList, h]))
    (fun h => outside (by simp [limbClobbers, Clobbers.ofList, h]))

theorem det_mulSmallAdd (base count : Nat) : (mulSmallAdd base count).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The value form: the limbs after `mulSmallAdd` spell `(X · m + c) mod 2 ^ (128 · count)`. -/
theorem limbValue_limbOf (value : Nat) :
    ∀ count, limbValue (limbOf value) count = value % 2 ^ (128 * count)
  | 0 => by simp [limbValue, Nat.mod_one]
  | count + 1 => by
      rw [limbValue_succ, limbValue_limbOf value count]
      unfold limbOf
      rw [Nat.mul_succ, pow_add, Nat.mod_mul]
      ring

end Kriterion.CRT.SimMachine
