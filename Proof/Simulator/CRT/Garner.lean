/-
**Garner's reconstruction on the machine** (`Construction/Simulator/CRT/Garner.lean`).

* The arithmetic: `garnerDigit` (the mixed-radix digits, by strong recursion, exactly as the
  machine computes them), `garnerValue T = Σ_(i<T) v_i · m_0 ⋯ m_(i-1)`, and the two facts that make
  it the CRT integer: `garnerValue_mod` (it has residue `L_i` modulo every `m_i`) and
  `garnerValue_lt` (it is below `M = m_0 ⋯ m_(T-1)`), under the side conditions of `GarnerTable`
  (positive moduli below `2 ^ 11` whose sum is at most `2 ^ 20`, each coprime to the product of
  the earlier ones).
* The machine: `exec_garnerDigits` (digit `i` at `vaddr + i`) and `exec_garnerHorner` (the limbs of
  `garnerValue T` at `zbase`), with their frames.
-/

import Proof.Simulator.CRT.Barrett
import Proof.Simulator.CRT.Limbs
import Proof.Simulator.CRT.FracDigits
import Construction.Simulator.CRT.Garner
import Proof.Simulator.ReplayBase
import Construction.CRT.Interface

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Finset

/-! ### The arithmetic -/

/-- Garner's digit `i` of the residues `L`, as the machine computes it. -/
def garnerDigit (mods L : Nat → Nat) (i : Nat) : Nat :=
  ((mods i * garnerLift - ∑ j : Fin i, garnerDigit mods L j * garnerCoef mods i j + L i) % mods i *
    garnerInv mods i) % mods i
termination_by i
decreasing_by exact j.isLt

theorem garnerDigit_eq (mods L : Nat → Nat) (i : Nat) :
    garnerDigit mods L i =
      ((mods i * garnerLift - ∑ j ∈ range i, garnerDigit mods L j * garnerCoef mods i j + L i) %
        mods i * garnerInv mods i) % mods i := by
  rw [garnerDigit, Fin.sum_univ_eq_sum_range (fun j => garnerDigit mods L j * garnerCoef mods i j)]

/-- The CRT integer of the first `count` digits. -/
def garnerValue (mods L : Nat → Nat) (count : Nat) : Nat :=
  ∑ i ∈ range count, garnerDigit mods L i * prefixProd mods i

/-- The side conditions on the modulus table. -/
structure GarnerTable (mods : Nat → Nat) (count : Nat) : Prop where
  pos : ∀ i, i < count → 0 < mods i
  small : ∀ i, i < count → mods i < 2 ^ 11
  sum : ∑ i ∈ range count, mods i ≤ garnerLift
  coprime : ∀ i, i < count → Nat.Coprime (prefixProd mods i) (mods i)

theorem prefixProd_succ (mods : Nat → Nat) (i : Nat) :
    prefixProd mods (i + 1) = prefixProd mods i * mods i := by
  unfold prefixProd
  rw [prod_range_succ]

theorem prefixProd_pos (mods : Nat → Nat) (count : Nat) (pos : ∀ i, i < count → 0 < mods i) :
    ∀ i, i ≤ count → 0 < prefixProd mods i
  | 0, _ => by simp [prefixProd]
  | i + 1, bound => by
      rw [prefixProd_succ]
      exact Nat.mul_pos (prefixProd_pos mods count pos i (by omega)) (pos i (by omega))

theorem garnerDigit_lt (mods L : Nat → Nat) (i : Nat) (pos : 0 < mods i) :
    garnerDigit mods L i < mods i := by
  rw [garnerDigit_eq]
  exact Nat.mod_lt _ pos

/-- The terms of digit `i` never exceed the offset `m_i · 2 ^ 20`. -/
theorem garner_terms_le (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (i : Nat) (bound : i < count) (k : Nat) (kBound : k ≤ i) :
    ∑ j ∈ range k, garnerDigit mods L j * garnerCoef mods i j ≤ mods i * garnerLift := by
  have each : ∀ j ∈ range k, garnerDigit mods L j * garnerCoef mods i j ≤ mods j * mods i := by
    intro j member
    have jBound : j < k := mem_range.mp member
    exact Nat.mul_le_mul (garnerDigit_lt mods L j (table.pos j (by omega))).le
      (Nat.mod_lt _ (table.pos i bound)).le
  calc ∑ j ∈ range k, garnerDigit mods L j * garnerCoef mods i j
      ≤ ∑ j ∈ range k, mods j * mods i := sum_le_sum each
    _ = (∑ j ∈ range k, mods j) * mods i := by rw [sum_mul]
    _ ≤ (∑ j ∈ range count, mods j) * mods i :=
        Nat.mul_le_mul_right _ (sum_le_sum_of_subset (fun x member => by
          simp only [mem_range] at member ⊢; omega))
    _ ≤ garnerLift * mods i := Nat.mul_le_mul_right _ table.sum
    _ = mods i * garnerLift := Nat.mul_comm _ _

/-- **Garner's step**: `v_i · P_i ≡ L_i - Σ_(j<i) v_j · P_j (mod m_i)`. -/
theorem garner_step (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (i : Nat) (bound : i < count) :
    ((garnerDigit mods L i * prefixProd mods i : Nat) : ZMod (mods i)) =
      (L i : ZMod (mods i)) - ∑ j ∈ range i, ((garnerDigit mods L j * prefixProd mods j : Nat) :
        ZMod (mods i)) := by
  haveI : NeZero (mods i) := ⟨(table.pos i bound).ne'⟩
  have terms := garner_terms_le mods L count table i bound i le_rfl
  have inverse : ((prefixProd mods i : Nat) : ZMod (mods i)) * ((garnerInv mods i : Nat) : ZMod (mods i)) = 1 := by
    unfold garnerInv
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ (table.coprime i bound)
  have lift : ((mods i * garnerLift : Nat) : ZMod (mods i)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have coefs : ((∑ j ∈ range i, garnerDigit mods L j * garnerCoef mods i j : Nat) : ZMod (mods i)) =
      ∑ j ∈ range i, ((garnerDigit mods L j * prefixProd mods j : Nat) : ZMod (mods i)) := by
    rw [Nat.cast_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold garnerCoef
    rw [Nat.cast_mul, Nat.cast_mul, ZMod.natCast_mod]
  rw [garnerDigit_eq, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_sub terms, lift, coefs]
  calc ((0 : ZMod (mods i)) - ∑ j ∈ range i, ((garnerDigit mods L j * prefixProd mods j : Nat) :
          ZMod (mods i)) + (L i : ZMod (mods i))) * ((garnerInv mods i : Nat) : ZMod (mods i)) *
        ((prefixProd mods i : Nat) : ZMod (mods i))
      = ((L i : ZMod (mods i)) - ∑ j ∈ range i, ((garnerDigit mods L j * prefixProd mods j : Nat) :
          ZMod (mods i))) * (((prefixProd mods i : Nat) : ZMod (mods i)) *
            ((garnerInv mods i : Nat) : ZMod (mods i))) := by ring
    _ = _ := by rw [inverse, mul_one]

/-- **The residues**: `garnerValue T ≡ L_i (mod m_i)` for every `i < T`. -/
theorem garnerValue_mod (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (i : Nat) (bound : i < count) :
    garnerValue mods L count % mods i = L i % mods i := by
  rw [← ZMod.natCast_eq_natCast_iff']
  unfold garnerValue
  rw [Nat.cast_sum, ← sum_range_add_sum_Ico _ (show i + 1 ≤ count by omega), sum_range_succ,
    garner_step mods L count table i bound]
  have high : ∑ j ∈ Ico (i + 1) count, ((garnerDigit mods L j * prefixProd mods j : Nat) :
      ZMod (mods i)) = 0 := by
    refine sum_eq_zero fun j member => ?_
    have jLow : i + 1 ≤ j := (mem_Ico.mp member).1
    have divides : mods i ∣ prefixProd mods j :=
      dvd_prod_of_mem _ (mem_range.mpr (by omega))
    rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr divides, mul_zero]
  rw [high]
  ring

/-- **The range**: `garnerValue T < m_0 ⋯ m_(T-1)`. -/
theorem garnerValue_lt (mods L : Nat → Nat) (count : Nat) (pos : ∀ i, i < count → 0 < mods i) :
    ∀ k, k ≤ count → garnerValue mods L k < prefixProd mods k
  | 0, _ => by simp [garnerValue, prefixProd]
  | k + 1, bound => by
      have ih := garnerValue_lt mods L count pos k (by omega)
      have digit := garnerDigit_lt mods L k (pos k (by omega))
      unfold garnerValue at *
      rw [sum_range_succ, prefixProd_succ]
      have step : garnerDigit mods L k * prefixProd mods k ≤ (mods k - 1) * prefixProd mods k :=
        Nat.mul_le_mul_right _ (by omega)
      have expand : (mods k - 1) * prefixProd mods k + prefixProd mods k =
          prefixProd mods k * mods k := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (pos k (by omega)),
          Nat.mul_comm]
      omega

/-- **Uniqueness**: any `Z' < M` with the same residues is `garnerValue`, so the machine's value is
the construction's CRT integer whatever its definition (package C4's `crt_spec` links them). -/
theorem garnerValue_unique (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (other : Nat) (otherLt : other < prefixProd mods count)
    (residues : ∀ i, i < count → other % mods i = L i % mods i) :
    other = garnerValue mods L count := by
  have divides : ∀ k, k ≤ count →
      (prefixProd mods k : ℤ) ∣ (other : ℤ) - (garnerValue mods L count : ℤ) := by
    intro k
    induction k with
    | zero => intro _; simp [prefixProd]
    | succ k ih =>
        intro bound
        rw [prefixProd_succ, Nat.cast_mul]
        have same : garnerValue mods L count % mods k = other % mods k := by
          rw [residues k (by omega), garnerValue_mod mods L count table k (by omega)]
        have modK : (mods k : ℤ) ∣ (other : ℤ) - (garnerValue mods L count : ℤ) :=
          (Nat.modEq_iff_dvd).mp same
        exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr (table.coprime k (by omega)))
          (ih (by omega)) modK
  have small : |(other : ℤ) - (garnerValue mods L count : ℤ)| < (prefixProd mods count : ℤ) := by
    have valueLt := garnerValue_lt mods L count table.pos count le_rfl
    rw [abs_lt]
    constructor <;> omega
  have zero := Int.eq_zero_of_abs_lt_dvd (divides count le_rfl) small
  omega

/-! ### Horner's rule -/

/-- The value after `t` Horner steps from the top digit. -/
def hornerVal (mods v : Nat → Nat) (count : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => hornerVal mods v count t * mods (count - 1 - t) + v (count - 1 - t)

/-- The Horner invariant: `H_t · P_(T - t) + Σ_(i < T - t) v_i · P_i = Σ_(i < T) v_i · P_i`. -/
theorem hornerVal_spec (mods v : Nat → Nat) (count : Nat) :
    ∀ t, t ≤ count → hornerVal mods v count t * prefixProd mods (count - t) +
      ∑ i ∈ range (count - t), v i * prefixProd mods i = ∑ i ∈ range count, v i * prefixProd mods i
  | 0, _ => by simp [hornerVal]
  | t + 1, bound => by
      have ih := hornerVal_spec mods v count t (by omega)
      have split : count - t = (count - 1 - t) + 1 := by omega
      rw [split, sum_range_succ, prefixProd_succ] at ih
      rw [show count - (t + 1) = count - 1 - t by omega, hornerVal, ← ih]
      ring

theorem hornerVal_final (mods L : Nat → Nat) (count : Nat) :
    hornerVal mods (garnerDigit mods L) count count = garnerValue mods L count := by
  have := hornerVal_spec mods (garnerDigit mods L) count count le_rfl
  simp only [Nat.sub_self, prefixProd, range_zero, prod_empty, sum_empty, mul_one,
    add_zero] at this
  exact this

theorem hornerVal_le (mods L : Nat → Nat) (count : Nat) (pos : ∀ i, i < count → 0 < mods i)
    (t : Nat) (bound : t ≤ count) :
    hornerVal mods (garnerDigit mods L) count t ≤ garnerValue mods L count := by
  have spec := hornerVal_spec mods (garnerDigit mods L) count t bound
  have prodPos := prefixProd_pos mods count pos (count - t) (by omega)
  unfold garnerValue
  calc hornerVal mods (garnerDigit mods L) count t
      ≤ hornerVal mods (garnerDigit mods L) count t * prefixProd mods (count - t) :=
        Nat.le_mul_of_pos_right _ prodPos
    _ ≤ _ := by omega

/-! ### Straight-line steps -/

theorem exec_loadAt_seq (target : Register) (address : Nat) (rest : Prog) (memory : Memory) :
    (Prog.seq (loadAt target address) rest).exec memory =
      rest.exec (setReg (setReg memory rAddr (word address)) target (memory.ram (word address))) := by
  show rest.exec (setReg (setReg memory rAddr (word address)) target
    ((setReg memory rAddr (word address)).ram
      ((setReg memory rAddr (word address)).registers rAddr))) = _
  rw [reg_setReg, if_pos rfl]
  rfl

theorem exec_storeAt (address : Nat) (source : Register) (memory : Memory) (other : source ≠ rAddr) :
    (storeAt address source).exec memory =
      some (storeRam (setReg memory rAddr (word address)) (word address) (memory.registers source)) := by
  show some (storeRam (setReg memory rAddr (word address))
    ((setReg memory rAddr (word address)).registers rAddr)
    ((setReg memory rAddr (word address)).registers source)) = _
  rw [reg_setReg, if_pos rfl, reg_setReg, if_neg other]

theorem exec_storeAt_seq (address : Nat) (source : Register) (rest : Prog) (memory : Memory)
    (other : source ≠ rAddr) :
    (Prog.seq (storeAt address source) rest).exec memory =
      rest.exec (storeRam (setReg memory rAddr (word address)) (word address)
        (memory.registers source)) := by
  rw [Prog.exec_seq, exec_storeAt address source memory other, Option.bind_some]

/-! ### Block 1 on the machine -/

/-- The registers the Garner blocks may change. -/
def garnerClobbers : Clobbers := Clobbers.ofList [rAcc, rOut, rA, rB, rC, rD, rE, rF, rAddr, rM]

theorem ne_of_not_garner {register : Register} (outside : ¬ garnerClobbers register)
    (other : Register) (inside : other ∈ [rAcc, rOut, rA, rB, rC, rD, rE, rF, rAddr, rM]) :
    register ≠ other := fun same => outside (by rw [same]; exact inside)

/-- One term: `rAcc := rAcc - v · c`. -/
theorem exec_garnerTerm (mods : Nat → Nat) (vaddr i j : Nat) (memory : Memory) (acc v : Nat)
    (accReg : memory.registers rAcc = word acc) (accSmall : acc < 2 ^ 256)
    (vCell : memory.ram (word (vaddr + j)) = word v) (vSmall : v < 2 ^ 128)
    (coefSmall : garnerCoef mods i j < 2 ^ 128) (below : v * garnerCoef mods i j ≤ acc) :
    ∃ after, (garnerTerm mods vaddr i j).exec memory = some after ∧
      after.registers rAcc = word (acc - v * garnerCoef mods i j) ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have prod : v * garnerCoef mods i j < 2 ^ 256 := by
    calc v * garnerCoef mods i j < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul'' vSmall coefSmall
      _ = 2 ^ 256 := by norm_num
  refine ⟨_, rfl, ?_, rfl, rfl, fun register notAcc notB notC notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, vCell, accReg]
    rw [eval_mul_word _ _ prod, eval_sub_word _ _ below accSmall]
  · simp only [reg_setReg, if_neg notAcc, if_neg notB, if_neg notC, if_neg notAddr]

/-- The terms of digit `i`: `rAcc := m_i · 2 ^ 20 - Σ_(j<k) v_j · c_ij`. -/
theorem exec_garnerTerms (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (vaddr i : Nat) (bound : i < count) (memory : Memory)
    (accReg : memory.registers rAcc = word (mods i * garnerLift))
    (digits : ∀ j, j < i → memory.ram (word (vaddr + j)) = word (garnerDigit mods L j)) :
    ∀ k, k ≤ i → ∃ after, (Prog.rep k (garnerTerm mods vaddr i)).exec memory = some after ∧
      after.registers rAcc =
        word (mods i * garnerLift - ∑ j ∈ range k, garnerDigit mods L j * garnerCoef mods i j) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register
  | 0, _ => ⟨memory, Prog.exec_rep_zero _ _, by simpa using accReg, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | k + 1, kBound => by
      obtain ⟨middle, run, acc, ram, bits, regs⟩ :=
        exec_garnerTerms mods L count table vaddr i bound memory accReg digits k (by omega)
      have liftSmall : mods i * garnerLift < 2 ^ 256 := by
        have := table.small i bound
        unfold garnerLift
        calc mods i * 2 ^ 20 < 2 ^ 11 * 2 ^ 20 := Nat.mul_lt_mul_of_pos_right this (by positivity)
          _ < 2 ^ 256 := by norm_num
      have terms := garner_terms_le mods L count table i bound (k + 1) kBound
      rw [sum_range_succ] at terms
      have digitSmall : garnerDigit mods L k < 2 ^ 128 :=
        lt_trans (garnerDigit_lt mods L k (table.pos k (by omega)))
          (lt_trans (table.small k (by omega)) (by norm_num))
      have coefSmall : garnerCoef mods i k < 2 ^ 128 :=
        lt_trans (Nat.mod_lt _ (table.pos i bound)) (lt_trans (table.small i bound) (by norm_num))
      obtain ⟨after, step, accNext, ramNext, bitsNext, regsNext⟩ :=
        exec_garnerTerm mods vaddr i k middle _ (garnerDigit mods L k) acc (by omega)
          (by rw [ram]; exact digits k (by omega)) digitSmall coefSmall (by omega)
      refine ⟨after, by rw [Prog.exec_rep_succ, run, Option.bind_some, step], ?_, ?_, ?_,
        fun register notAcc notB notC notAddr => ?_⟩
      · rw [accNext, sum_range_succ, Nat.sub_sub]
      · rw [ramNext, ram]
      · rw [bitsNext, bits]
      · rw [regsNext register notAcc notB notC notAddr, regs register notAcc notB notC notAddr]

/-- **Digit `i`**: from the earlier digits and the residue `L_i`, the machine stores
`garnerDigit mods L i` at `vaddr + i`. -/
theorem exec_garnerDigitProg (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (laddr vaddr i : Nat) (bound : i < count) (memory : Memory)
    (vaddrFits : vaddr + count < 2 ^ 256)
    (digits : ∀ j, j < i → memory.ram (word (vaddr + j)) = word (garnerDigit mods L j))
    (residue : memory.ram (word (laddr + i)) = word (L i)) (residueSmall : L i < mods i) :
    ∃ after, (garnerDigitProg mods laddr vaddr i).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (vaddr + i)) (word (garnerDigit mods L i)) ∧
      after.bits = memory.bits ∧
      ∀ register, ¬ garnerClobbers register → after.registers register = memory.registers register := by
  have mPos := table.pos i bound
  have mSmall := table.small i bound
  set m := mods i with mDef
  set S := ∑ j ∈ range i, garnerDigit mods L j * garnerCoef mods i j with SDef
  have terms : S ≤ m * garnerLift := garner_terms_le mods L count table i bound i le_rfl
  set A := m * garnerLift - S + L i with ADef
  have ASmall : A < 2 ^ 32 := by
    have : m * garnerLift + m ≤ 2 ^ 32 := by
      unfold garnerLift
      calc m * 2 ^ 20 + m = m * (2 ^ 20 + 1) := by ring
        _ ≤ 2 ^ 11 * (2 ^ 20 + 1) := Nat.mul_le_mul_right _ mSmall.le
        _ ≤ 2 ^ 32 := by norm_num
    omega
  have invLt : garnerInv mods i < m := by
    haveI : NeZero m := ⟨mPos.ne'⟩
    unfold garnerInv
    exact ZMod.val_lt _
  have prodSmall : A % m * garnerInv mods i < 2 ^ 32 := by
    have := Nat.mod_lt A mPos
    calc A % m * garnerInv mods i < m * m := Nat.mul_lt_mul'' this invLt
      _ ≤ 2 ^ 11 * 2 ^ 11 := Nat.mul_le_mul mSmall.le mSmall.le
      _ < 2 ^ 32 := by norm_num
  set m0 := setReg memory rAcc (word (m * garnerLift)) with m0Def
  obtain ⟨m1, run1, acc1, ram1, bits1, regs1⟩ :=
    exec_garnerTerms mods L count table vaddr i bound m0 (by rw [m0Def, reg_setReg, if_pos rfl])
      digits i le_rfl
  have residue1 : m1.ram (word (laddr + i)) = word (L i) := by rw [ram1]; exact residue
  set m2 := setReg (setReg m1 rAddr (word (laddr + i))) rB (word (L i)) with m2Def
  have acc2 : m2.registers rAcc = word (m * garnerLift - S) := by
    rw [m2Def, reg_setReg, if_neg (by decide), reg_setReg, if_neg (by decide), acc1]
  have addSmall : m * garnerLift - S + L i < 2 ^ 256 := lt_trans ASmall (by norm_num)
  set m3 := setReg m2 rAcc (word A) with m3Def
  obtain ⟨m4, run4, out4, ram4, bits4, regs4⟩ :=
    exec_barrett rAcc rOut m 32 A m3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [m3Def, reg_setReg, if_pos rfl]) ASmall mPos (lt_trans mSmall (by norm_num)) (by norm_num)
  set m5 := setReg m4 rC (word (garnerInv mods i)) with m5Def
  set m6 := setReg m5 rOut (word (A % m * garnerInv mods i)) with m6Def
  obtain ⟨m7, run7, out7, ram7, bits7, regs7⟩ :=
    exec_barrett rOut rOut m 32 (A % m * garnerInv mods i) m6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [m6Def, reg_setReg, if_pos rfl]) prodSmall mPos
      (lt_trans mSmall (by norm_num)) (by norm_num)
  have runAll : (garnerDigitProg mods laddr vaddr i).exec memory =
      (storeAt (vaddr + i) rOut).exec m7 := by
    unfold garnerDigitProg
    rw [exec_cst_seq, ← m0Def, Prog.exec_seq_some _ _ m0 m1 run1, exec_loadAt_seq, residue1, ← m2Def,
      exec_ar_val _ _ _ _ _ _ (word (m * garnerLift - S)) (word (L i)) acc2
        (by rw [m2Def, reg_setReg, if_pos rfl]),
      eval_add_word _ _ addSmall, ← m3Def, Prog.exec_seq_some _ _ m3 m4 run4, exec_cst_seq, ← m5Def,
      exec_ar_val _ _ _ _ _ _ (word (A % m)) (word (garnerInv mods i))
        (by rw [m5Def, reg_setReg, if_neg (by decide), out4])
        (by rw [m5Def, reg_setReg, if_pos rfl]),
      eval_mul_word _ _ (lt_trans prodSmall (by norm_num)), ← m6Def,
      Prog.exec_seq_some _ _ m6 m7 run7]
  have digitEq : A % m * garnerInv mods i % m = garnerDigit mods L i := by
    rw [garnerDigit_eq]
  rw [runAll, exec_storeAt _ _ _ (by decide), out7, digitEq]
  refine ⟨_, rfl, ?_, ?_, fun register outside => ?_⟩
  · rw [ram_storeRam, ram_setReg, ram7, m6Def, ram_setReg, m5Def, ram_setReg, ram4, m3Def, ram_setReg,
      m2Def, ram_setReg, ram_setReg, ram1, m0Def, ram_setReg]
  · rw [bits_storeRam, bits_setReg, bits7, m6Def, bits_setReg, m5Def, bits_setReg, bits4, m3Def,
      bits_setReg, m2Def, bits_setReg, bits_setReg, bits1, m0Def, bits_setReg]
  · rw [reg_storeRam, reg_setReg, if_neg (ne_of_not_garner outside rAddr (by simp)),
      regs7 register (ne_of_not_garner outside rOut (by simp)) (ne_of_not_garner outside rD (by simp))
        (ne_of_not_garner outside rE (by simp)) (ne_of_not_garner outside rF (by simp)),
      m6Def, reg_setReg, if_neg (ne_of_not_garner outside rOut (by simp)), m5Def, reg_setReg,
      if_neg (ne_of_not_garner outside rC (by simp)),
      regs4 register (ne_of_not_garner outside rOut (by simp)) (ne_of_not_garner outside rD (by simp))
        (ne_of_not_garner outside rE (by simp)) (ne_of_not_garner outside rF (by simp)),
      m3Def, reg_setReg, if_neg (ne_of_not_garner outside rAcc (by simp)), m2Def, reg_setReg,
      if_neg (ne_of_not_garner outside rB (by simp)), reg_setReg,
      if_neg (ne_of_not_garner outside rAddr (by simp)),
      regs1 register (ne_of_not_garner outside rAcc (by simp)) (ne_of_not_garner outside rB (by simp))
        (ne_of_not_garner outside rC (by simp)) (ne_of_not_garner outside rAddr (by simp)),
      m0Def, reg_setReg, if_neg (ne_of_not_garner outside rAcc (by simp))]

/-- **Block 1**: all `count` digits, digit `i` at `vaddr + i`, with the frame of the schema. -/
theorem exec_garnerDigits (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (laddr vaddr : Nat) (memory : Memory) (laddrFits : laddr + count < 2 ^ 256)
    (apart : ∀ i, i < count → ∀ j, j < count → laddr + i ≠ vaddr + j)
    (vaddrFits : vaddr + count < 2 ^ 256)
    (residues : ∀ i, i < count → memory.ram (word (laddr + i)) = word (L i))
    (residuesSmall : ∀ i, i < count → L i < mods i) :
    ∃ after, (garnerDigits mods count laddr vaddr).exec memory = some after ∧
      (∀ i, i < count → after.ram (word (vaddr + i)) = word (garnerDigit mods L i)) ∧
      Frame (Writes.region ⟨vaddr, count⟩) garnerClobbers memory after := by
  obtain ⟨after, run, done, frame, bitsSame, regs⟩ := Prog.exec_rep (garnerDigitProg mods laddr vaddr)
    (fun i current =>
      (∀ j, j < i → current.ram (word (vaddr + j)) = word (garnerDigit mods L j)) ∧
        (∀ address, (∀ j, j < count → address ≠ word (vaddr + j)) →
          current.ram address = memory.ram address) ∧
        current.bits = memory.bits ∧
        ∀ register, ¬ garnerClobbers register → current.registers register = memory.registers register)
    count (fun i bound current holds => by
      obtain ⟨done, frame, bitsSame, regs⟩ := holds
      have residueNow : current.ram (word (laddr + i)) = word (L i) := by
        rw [frame _ fun j jb => word_ne (by omega) (by omega) (apart i bound j jb)]
        exact residues i bound
      obtain ⟨next, step, ram, bits, regsNext⟩ := exec_garnerDigitProg mods L count table laddr vaddr i
        bound current vaddrFits done residueNow (residuesSmall i bound)
      refine ⟨next, step, fun j jb => ?_, fun address off => ?_, ?_, fun register outside => ?_⟩
      · rw [ram]
        by_cases last : j = i
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done j (by omega)
      · rw [ram, Function.update_of_ne (off i bound)]
        exact frame address off
      · rw [bits, bitsSame]
      · rw [regsNext register outside, regs register outside])
    memory ⟨fun j jb => absurd jb (by omega), fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  exact ⟨after, run, done, ⟨fun address outside => frame address fun j jb same =>
    outside ⟨j, jb, same⟩, bitsSame, regs⟩⟩

/-! ### Block 2 on the machine -/

/-- Zeroing the limbs. -/
theorem exec_zeroLimbs (zbase nz : Nat) (memory : Memory) (fits : zbase + nz ≤ 2 ^ 256) :
    ∃ after, (zeroLimbs zbase nz).exec memory = some after ∧
      (∀ k, k < nz → after.ram (word (zbase + k)) = word 0) ∧
      (∀ address, (∀ k, k < nz → address ≠ word (zbase + k)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set m0 := setReg memory rA (word 0) with m0Def
  obtain ⟨after, run, inv⟩ := Prog.exec_rep (fun k => storeAt (zbase + k) rA)
    (fun k current =>
      (∀ k', k' < k → current.ram (word (zbase + k')) = word 0) ∧
        current.registers rA = word 0 ∧
        (∀ address, (∀ k', k' < nz → address ≠ word (zbase + k')) →
          current.ram address = m0.ram address) ∧
        current.bits = m0.bits ∧
        ∀ register, register ≠ rAddr → current.registers register = m0.registers register)
    nz (fun k bound current holds => by
      obtain ⟨done, zero, frame, bitsSame, regs⟩ := holds
      refine ⟨_, exec_storeAt _ _ current (by decide), fun k' kb => ?_, ?_, fun address off => ?_,
        by rw [bits_storeRam, bits_setReg]; exact bitsSame, fun register notAddr => ?_⟩
      · rw [ram_storeRam, ram_setReg, zero]
        by_cases last : k' = k
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done k' (by omega)
      · rw [reg_storeRam, reg_setReg, if_neg (by decide), zero]
      · rw [ram_storeRam, ram_setReg, Function.update_of_ne (off k bound)]
        exact frame address off
      · rw [reg_storeRam, reg_setReg, if_neg notAddr, regs register notAddr])
    m0 ⟨fun k' kb => absurd kb (by omega), by rw [m0Def, reg_setReg, if_pos rfl], fun _ _ => rfl, rfl,
      fun _ _ => rfl⟩
  obtain ⟨done, _, frame, bitsSame, regs⟩ := inv
  refine ⟨after, ?_, done, fun address off => ?_, bitsSame, fun register notA notAddr => ?_⟩
  · unfold zeroLimbs
    rw [exec_cst_seq, ← m0Def, run]
  · rw [frame address off]
    rfl
  · rw [regs register notAddr, m0Def, reg_setReg, if_neg notA]

/-- **Block 2**: the limbs of `garnerValue` at `zbase`, by Horner's rule from the top digit. -/
theorem exec_garnerHorner (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (vaddr zbase nz : Nat) (memory : Memory)
    (digits : ∀ i, i < count → memory.ram (word (vaddr + i)) = word (garnerDigit mods L i))
    (vaddrFits : vaddr + count < 2 ^ 256) (zFits : zbase + nz ≤ 2 ^ 256)
    (apart : ∀ i, i < count → ∀ k, k < nz → vaddr + i ≠ zbase + k)
    (valueFits : prefixProd mods count ≤ 2 ^ (128 * nz)) :
    ∃ after, (garnerHorner mods count vaddr zbase nz).exec memory = some after ∧
      (∀ k, k < nz → after.ram (word (zbase + k)) = word (limbOf (garnerValue mods L count) k)) ∧
      Frame (Writes.region ⟨zbase, nz⟩) (Clobbers.ofList [rA, rB, rC, rAddr, rM, rMask, rK128])
        memory after := by
  set m1 := setReg (setReg memory rMask (word limbMask)) rK128 (word 128) with m1Def
  obtain ⟨m2, run2, zero2, frame2, bits2, regs2⟩ := exec_zeroLimbs zbase nz m1 zFits
  have valueLt := garnerValue_lt mods L count table.pos count le_rfl
  have hornerSmall : ∀ t, t ≤ count → hornerVal mods (garnerDigit mods L) count t < 2 ^ (128 * nz) :=
    fun t bound => lt_of_le_of_lt (hornerVal_le mods L count table.pos t bound)
      (lt_of_lt_of_le valueLt valueFits)
  have digitAway : ∀ i, i < count → ∀ k, k < nz → word (vaddr + i) ≠ word (zbase + k) :=
    fun i ib k kb => word_ne (by omega) (by omega) (apart i ib k kb)
  obtain ⟨m3, run3, limbs3, frame3, bits3, regs3⟩ :=
    Prog.exec_rep (fun t => hornerStep mods vaddr zbase nz (count - 1 - t))
    (fun t current =>
      (∀ k, k < nz → current.ram (word (zbase + k)) =
          word (limbOf (hornerVal mods (garnerDigit mods L) count t) k)) ∧
        (∀ address, (∀ k, k < nz → address ≠ word (zbase + k)) →
          current.ram address = m2.ram address) ∧
        current.bits = m2.bits ∧
        ∀ register, register ≠ rA → register ≠ rB → register ≠ rC → register ≠ rAddr →
          register ≠ rM → current.registers register = m2.registers register)
    count (fun t bound current holds => by
      obtain ⟨limbs, frame, bitsSame, regs⟩ := holds
      set i := count - 1 - t with iDef
      have iBound : i < count := by omega
      have digitNow : current.ram (word (vaddr + i)) = word (garnerDigit mods L i) := by
        rw [frame _ (digitAway i iBound), frame2 _ (digitAway i iBound), m1Def, ram_setReg, ram_setReg]
        exact digits i iBound
      set c1 := setReg (setReg (setReg current rM (word (mods i))) rAddr (word (vaddr + i))) rC
        (word (garnerDigit mods L i)) with c1Def
      have consts : LimbConsts c1 (mods i) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [c1Def, reg_setReg, if_neg (by decide), reg_setReg, if_neg (by decide), reg_setReg,
            if_pos rfl]
        · rw [c1Def, reg_setReg, if_neg (by decide), reg_setReg, if_neg (by decide), reg_setReg,
            if_neg (by decide), regs rMask (by decide) (by decide) (by decide) (by decide) (by decide),
            regs2 rMask (by decide) (by decide), m1Def, reg_setReg, if_neg (by decide), reg_setReg,
            if_pos rfl]
        · rw [c1Def, reg_setReg, if_neg (by decide), reg_setReg, if_neg (by decide), reg_setReg,
            if_neg (by decide), regs rK128 (by decide) (by decide) (by decide) (by decide) (by decide),
            regs2 rK128 (by decide) (by decide), m1Def, reg_setReg, if_pos rfl]
      have digitSmall : garnerDigit mods L i < 2 ^ 128 :=
        lt_trans (garnerDigit_lt mods L i (table.pos i iBound))
          (lt_trans (table.small i iBound) (by norm_num))
      obtain ⟨next, step, limbsNext, carry, frameNext, bitsNext, regsNext⟩ :=
        exec_mulSmallAdd zbase nz (limbOf (hornerVal mods (garnerDigit mods L) count t)) (mods i)
          (garnerDigit mods L i) c1 zFits (fun k kb => by rw [c1Def]; exact limbs k kb)
          (limbOf_lt _) consts (by rw [c1Def, reg_setReg, if_pos rfl])
          (lt_trans (table.small i iBound) (by norm_num)) digitSmall
      rw [limbValue_limbOf, Nat.mod_eq_of_lt (hornerSmall t (by omega))] at limbsNext
      refine ⟨next, ?_, fun k kb => ?_, fun address off => ?_, ?_,
        fun register notA notB notC notAddr notM => ?_⟩
      · unfold hornerStep
        rw [exec_cst_seq, exec_loadAt_seq]
        simp only [ram_setReg]
        rw [digitNow, ← c1Def]
        exact step
      · rw [limbsNext k kb]
        rfl
      · rw [frameNext address off, c1Def, ram_setReg, ram_setReg, ram_setReg]
        exact frame address off
      · rw [bitsNext, c1Def, bits_setReg, bits_setReg, bits_setReg, bitsSame]
      · rw [regsNext register notA notB notC notAddr, c1Def, reg_setReg, if_neg notC, reg_setReg,
          if_neg notAddr, reg_setReg, if_neg notM]
        exact regs register notA notB notC notAddr notM)
    m2 ⟨fun k kb => by rw [zero2 k kb]; simp [hornerVal, limbOf], fun _ _ => rfl, rfl,
      fun _ _ _ _ _ _ => rfl⟩
  rw [hornerVal_final] at limbs3
  refine ⟨m3, ?_, limbs3, ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩
  · unfold garnerHorner
    rw [exec_cst_seq, exec_cst_seq, ← m1Def, Prog.exec_seq_some _ _ m1 m2 run2]
    exact run3
  · have off : ∀ k, k < nz → address ≠ word (zbase + k) := fun k kb same => outside ⟨k, kb, same⟩
    rw [frame3 address off, frame2 address off, m1Def, ram_setReg, ram_setReg]
  · rw [bits3, bits2, m1Def, bits_setReg, bits_setReg]
  · have notIn : ∀ other : Register, other ∈ [rA, rB, rC, rAddr, rM, rMask, rK128] →
        register ≠ other := fun other inside same => outside (by rw [same]; exact inside)
    rw [regs3 register (notIn rA (by simp)) (notIn rB (by simp)) (notIn rC (by simp))
        (notIn rAddr (by simp)) (notIn rM (by simp)),
      regs2 register (notIn rA (by simp)) (notIn rAddr (by simp)), m1Def, reg_setReg,
      if_neg (notIn rK128 (by simp)), reg_setReg, if_neg (notIn rMask (by simp))]

/-! ### Block 3 on the machine -/

theorem word_xor_zero_iff {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) : word first ^^^ word second = 0 ↔ first = second := by
  constructor
  · intro zero
    have same : word first = word second := by
      have := congrArg (· ^^^ word second) zero
      simpa [BitVec.xor_assoc] using this
    exact word_inj firstSmall secondSmall same
  · intro same
    rw [same, BitVec.xor_self]
    rfl

theorem eval_less_xor_one (x y : Nat) (xSmall : x < 2 ^ 256) (ySmall : y < 2 ^ 256) :
    Arithmetic.less.eval (word x ^^^ word y) (word 1) = word (if x = y then 1 else 0) := by
  show (if (word x ^^^ word y).toNat < (word 1).toNat then 1 else 0) = _
  rw [word_toNat (by norm_num)]
  by_cases same : x = y
  · have zero : (word x ^^^ word y).toNat = 0 := by
      rw [(word_xor_zero_iff xSmall ySmall).mpr same]; rfl
    rw [if_pos (by omega), if_pos same]
    rfl
  · have nonzero : (word x ^^^ word y).toNat ≠ 0 := fun zero =>
      same ((word_xor_zero_iff xSmall ySmall).mp (BitVec.eq_of_toNat_eq (by rw [zero]; rfl)))
    rw [if_neg (by omega), if_neg same]
    rfl

theorem eval_xor_eq (first second : Word) : Arithmetic.xor.eval first second = first ^^^ second := rfl

theorem constLimb_eq (value k : Nat) : constLimb value k = limbOf value k := rfl

/-- `Z / 2 ^ (128 k)` splits into the part above limb `k` and limb `k`. -/
theorem div_limb_split (value k : Nat) :
    value / 2 ^ (128 * k) = value / 2 ^ (128 * (k + 1)) * 2 ^ 128 + limbOf value k := by
  rw [div_succ_limb]
  unfold limbOf
  exact (Nat.div_add_mod' _ _).symm

/-- The lexicographic order of two limb-split numbers. -/
theorem lex_lt (a b x y : Nat) (xSmall : x < 2 ^ 128) (ySmall : y < 2 ^ 128) :
    a * 2 ^ 128 + x < b * 2 ^ 128 + y ↔ a < b ∨ (a = b ∧ x < y) := by
  have big : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  rw [big] at xSmall ySmall ⊢
  omega

theorem lex_eq (a b x y : Nat) (xSmall : x < 2 ^ 128) (ySmall : y < 2 ^ 128) :
    a * 2 ^ 128 + x = b * 2 ^ 128 + y ↔ a = b ∧ x = y := by
  have big : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  rw [big] at xSmall ySmall ⊢
  omega

/-- The comparison invariant after the limbs at and above `h`. -/
def LessState (value bound h : Nat) (memory : Memory) : Prop :=
  memory.registers rOut =
      word (if value / 2 ^ (128 * h) < bound / 2 ^ (128 * h) then 1 else 0) ∧
    memory.registers rFlag =
      word (if value / 2 ^ (128 * h) = bound / 2 ^ (128 * h) then 1 else 0)

/-- **One limb of the comparison.** -/
theorem exec_lessStep (value bound zbase k : Nat) (memory : Memory) (zFits : zbase + k < 2 ^ 256)
    (limb : memory.ram (word (zbase + k)) = word (limbOf value k))
    (state : LessState value bound (k + 1) memory) :
    ∃ after, (lessStep bound zbase k).exec memory = some after ∧ LessState value bound k after ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rOut → register ≠ rFlag → register ≠ rA → register ≠ rB →
        register ≠ rC → register ≠ rD → register ≠ rAddr →
        after.registers register = memory.registers register := by
  obtain ⟨outReg, flagReg⟩ := state
  unfold lessStep
  rw [constLimb_eq]
  set a := value / 2 ^ (128 * (k + 1))
  set b := bound / 2 ^ (128 * (k + 1))
  set x := limbOf value k
  set y := limbOf bound k
  have xSmall : x < 2 ^ 128 := limbOf_lt _ _
  have ySmall : y < 2 ^ 128 := limbOf_lt _ _
  have x256 : x < 2 ^ 256 := lt_trans xSmall (by norm_num)
  have y256 : y < 2 ^ 256 := lt_trans ySmall (by norm_num)
  have ltBit : (if x < y then 1 else 0) * (if a = b then 1 else 0) < 2 ^ 256 := by
    split <;> split <;> norm_num
  have sumBit : (if a < b then 1 else 0) + (if x < y then 1 else 0) * (if a = b then 1 else 0) <
      2 ^ 256 := by
    split <;> split <;> split <;> norm_num
  have eqBit : (if a = b then 1 else 0) * (if x = y then 1 else 0) < 2 ^ 256 := by
    split <;> split <;> norm_num
  refine ⟨_, rfl, ⟨?_, ?_⟩, rfl, rfl, fun register n1 n2 n3 n4 n5 n6 n7 => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, limb, outReg,
      flagReg]
    rw [eval_less_word _ _ x256 y256, eval_mul_word _ _ ltBit, eval_add_word _ _ sumBit,
      div_limb_split value k, div_limb_split bound k]
    congr 1
    by_cases hab : a < b
    · have hne : a ≠ b := by omega
      rw [if_pos hab, if_neg hne, mul_zero, add_zero,
        if_pos ((lex_lt a b x y xSmall ySmall).mpr (Or.inl hab))]
    · rw [if_neg hab, zero_add]
      by_cases heq : a = b
      · rw [if_pos heq, mul_one]
        by_cases hxy : x < y
        · rw [if_pos hxy, if_pos ((lex_lt a b x y xSmall ySmall).mpr (Or.inr ⟨heq, hxy⟩))]
        · rw [if_neg hxy, if_neg (fun h => by
            rcases (lex_lt a b x y xSmall ySmall).mp h with h | h
            · exact hab h
            · exact hxy h.2)]
      · rw [if_neg heq, mul_zero, if_neg (fun h => by
          rcases (lex_lt a b x y xSmall ySmall).mp h with h | h
          · exact hab h
          · exact heq h.1)]
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, limb, flagReg]
    rw [eval_xor_eq, eval_less_xor_one _ _ x256 y256, eval_mul_word _ _ eqBit, div_limb_split value k,
      div_limb_split bound k]
    congr 1
    by_cases heq : a = b ∧ x = y
    · rw [if_pos heq.1, if_pos heq.2, if_pos ((lex_eq a b x y xSmall ySmall).mpr heq)]
    · rw [if_neg (fun h => heq ((lex_eq a b x y xSmall ySmall).mp h))]
      by_cases hab : a = b
      · rw [if_pos hab, if_neg (fun h => heq ⟨hab, h⟩)]
      · rw [if_neg hab, zero_mul]
  · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
      if_neg n7]

/-- **Block 3**: `rOut := [Z < bound]`. -/
theorem exec_limbLess (value bound zbase nz : Nat) (memory : Memory) (zFits : zbase + nz ≤ 2 ^ 256)
    (valueSmall : value < 2 ^ (128 * nz)) (boundSmall : bound < 2 ^ (128 * nz))
    (limbs : ∀ k, k < nz → memory.ram (word (zbase + k)) = word (limbOf value k)) :
    ∃ after, (limbLess bound zbase nz).exec memory = some after ∧
      after.registers rOut = word (if value < bound then 1 else 0) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rOut → register ≠ rFlag → register ≠ rA → register ≠ rB →
        register ≠ rC → register ≠ rD → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set m0 := setReg (setReg memory rOut (word 0)) rFlag (word 1) with m0Def
  obtain ⟨after, run, state, ram, bits, regs⟩ := Prog.exec_rep (fun t => lessStep bound zbase (nz - 1 - t))
    (fun t current => LessState value bound (nz - t) current ∧ current.ram = memory.ram ∧
      current.bits = memory.bits ∧
      ∀ register, register ≠ rOut → register ≠ rFlag → register ≠ rA → register ≠ rB →
        register ≠ rC → register ≠ rD → register ≠ rAddr →
        current.registers register = memory.registers register)
    nz (fun t bound' current holds => by
      obtain ⟨state, ram, bits, regs⟩ := holds
      have split : nz - t = (nz - 1 - t) + 1 := by omega
      rw [split] at state
      obtain ⟨next, step, stateNext, ramNext, bitsNext, regsNext⟩ :=
        exec_lessStep value bound zbase (nz - 1 - t) current (by omega)
          (by rw [ram]; exact limbs _ (by omega)) state
      refine ⟨next, step, ?_, by rw [ramNext, ram], by rw [bitsNext, bits],
        fun register n1 n2 n3 n4 n5 n6 n7 => ?_⟩
      · rw [show nz - (t + 1) = nz - 1 - t by omega]
        exact stateNext
      · rw [regsNext register n1 n2 n3 n4 n5 n6 n7, regs register n1 n2 n3 n4 n5 n6 n7])
    m0 ⟨⟨by
        rw [Nat.sub_zero, Nat.div_eq_of_lt valueSmall, Nat.div_eq_of_lt boundSmall, if_neg (by omega),
          m0Def, reg_setReg, if_neg (by decide), reg_setReg, if_pos rfl],
        by
        rw [Nat.sub_zero, Nat.div_eq_of_lt valueSmall, Nat.div_eq_of_lt boundSmall, if_pos rfl,
          m0Def, reg_setReg, if_pos rfl]⟩, rfl, rfl,
      fun register n1 n2 _ _ _ _ _ => by rw [m0Def, reg_setReg, if_neg n2, reg_setReg, if_neg n1]⟩
  refine ⟨after, ?_, ?_, ram, bits, regs⟩
  · unfold limbLess
    rw [exec_cst_seq, exec_cst_seq, ← m0Def]
    exact run
  · have := state.1
    simp only [Nat.sub_self, Nat.mul_zero, pow_zero, Nat.div_one] at this
    exact this

/-! ### Block 4 on the machine -/

section Field

variable [BN254.FieldCertificate]

theorem modPCoef_lt (k : Nat) : modPCoef k < 2 ^ 256 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by unfold BN254.baseFieldModulus; norm_num))
    (by unfold BN254.baseFieldModulus; norm_num)

theorem modPCoef_cast (k : Nat) : ((modPCoef k : Nat) : BN254.BaseField) = 2 ^ (128 * k) := by
  unfold modPCoef
  rw [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_ofNat]

/-- **Block 4**: `rAcc := Z mod p`. -/
theorem exec_limbModP (value zbase nz : Nat) (memory : Memory) (zFits : zbase + nz ≤ 2 ^ 256)
    (valueSmall : value < 2 ^ (128 * nz))
    (limbs : ∀ k, k < nz → memory.ram (word (zbase + k)) = word (limbOf value k)) :
    ∃ after, (limbModP zbase nz).exec memory = some after ∧
      after.registers rAcc = fieldWord (value : BN254.BaseField) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set m0 := setReg memory rAcc (word 0) with m0Def
  obtain ⟨after, run, acc, ram, bits, regs⟩ := Prog.exec_rep (modPStep zbase)
    (fun t current =>
      current.registers rAcc = fieldWord ((value % 2 ^ (128 * t) : Nat) : BN254.BaseField) ∧
        current.ram = memory.ram ∧ current.bits = memory.bits ∧
        ∀ register, register ≠ rAcc → register ≠ rA → register ≠ rB → register ≠ rAddr →
          current.registers register = memory.registers register)
    nz (fun t bound current holds => by
      obtain ⟨acc, ram, bits, regs⟩ := holds
      refine ⟨_, rfl, ?_, by rw [← ram]; rfl, by rw [← bits]; rfl,
        fun register n1 n2 n3 n4 => ?_⟩
      · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, acc]
        rw [ram, limbs t bound, eval_fieldMul, eval_fieldAdd]
        simp only [fieldWord_cast]
        rw [word_toNat (lt_trans (limbOf_lt _ _) (by norm_num)), word_toNat (modPCoef_lt t),
          modPCoef_cast]
        congr 1
        rw [← limbValue_limbOf value (t + 1), limbValue_succ, limbValue_limbOf, Nat.cast_add,
          Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      · simp only [reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4]
        exact regs register n1 n2 n3 n4)
    m0 ⟨by
        rw [m0Def, reg_setReg, if_pos rfl, Nat.mul_zero, pow_zero, Nat.mod_one, Nat.cast_zero]
        rfl, rfl, rfl,
      fun register n1 _ _ _ => by rw [m0Def, reg_setReg, if_neg n1]⟩
  refine ⟨after, ?_, ?_, ram, bits, regs⟩
  · unfold limbModP
    rw [exec_cst_seq, ← m0Def]
    exact run
  · rw [acc, Nat.mod_eq_of_lt valueSmall]

/-! ### Block 5 and the whole reconstruction -/

/-- The decoded value in the field: `Z + [h] · [Z < B] · M`. -/
theorem wrapDecode_cast (modulus wrapB value : Nat) (hint : Bool) :
    ((Kriterion.CRT.wrapDecode modulus wrapB hint value : Nat) : BN254.BaseField) =
      (value : BN254.BaseField) +
        (((if hint then 1 else 0) * (if value < wrapB then 1 else 0) : Nat) : BN254.BaseField) *
          ((modulus % BN254.baseFieldModulus : Nat) : BN254.BaseField) := by
  unfold Kriterion.CRT.wrapDecode
  rw [ZMod.natCast_mod]
  cases hint <;> by_cases below : value < wrapB <;> simp [below]

/-- **Block 5**: the combination and the store. -/
theorem exec_wrapCombine (modulusModP hintCell outCell : Nat) (memory : Memory) (acc : BN254.BaseField)
    (hintBit lt : Nat) (hintSmall : hintBit ≤ 1) (ltSmall : lt ≤ 1)
    (modSmall : modulusModP < 2 ^ 256)
    (accReg : memory.registers rAcc = fieldWord acc) (outReg : memory.registers rOut = word lt)
    (hintVal : memory.ram (word hintCell) = word hintBit) :
    ∃ after, (wrapCombine modulusModP hintCell outCell).exec memory = some after ∧
      after.ram = Function.update memory.ram (word outCell)
        (fieldWord (acc + ((hintBit * lt : Nat) : BN254.BaseField) *
          ((modulusModP : Nat) : BN254.BaseField))) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rAcc → register ≠ rB → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have prodSmall : hintBit * lt < 2 ^ 256 := by
    have : hintBit * lt ≤ 1 := by
      calc hintBit * lt ≤ 1 * 1 := Nat.mul_le_mul hintSmall ltSmall
        _ = 1 := rfl
    omega
  refine ⟨_, rfl, ?_, rfl, fun register n1 n2 n3 n4 => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reduceIte,
      hintVal, outReg, accReg]
    rw [eval_mul_word _ _ prodSmall, eval_fieldMul, eval_fieldAdd]
    simp only [fieldWord_cast]
    rw [word_toNat prodSmall, word_toNat modSmall]
  · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2, if_neg n3, if_neg n4]

/-- The layout facts the reconstruction of one encoding needs. -/
structure ReconLayout (count laddr vaddr zbase nz hintCell outCell : Nat) : Prop where
  laddrFits : laddr + count < 2 ^ 256
  vaddrFits : vaddr + count < 2 ^ 256
  zFits : zbase + nz ≤ 2 ^ 256
  residuesApart : ∀ i, i < count → ∀ j, j < count → laddr + i ≠ vaddr + j
  digitsApart : ∀ i, i < count → ∀ k, k < nz → vaddr + i ≠ zbase + k
  hintSmall : hintCell < 2 ^ 256
  hintOffDigits : ∀ j, j < count → hintCell ≠ vaddr + j
  hintOffLimbs : ∀ k, k < nz → hintCell ≠ zbase + k
  outSmall : outCell < 2 ^ 256

/-- The reconstruction writes the digit and limb scratch and its output cell. -/
def reconstructWrites (count vaddr zbase nz outCell : Nat) : Writes :=
  ((Writes.region ⟨vaddr, count⟩).union (Writes.region ⟨zbase, nz⟩)).union (Writes.cell outCell)

/-- The reconstruction's registers. -/
def reconstructClobbers : Clobbers :=
  Clobbers.ofList [rAcc, rOut, rFlag, rA, rB, rC, rD, rE, rF, rAddr, rM, rMask, rK128]

/-- **The reconstruction of one encoding**: the machine stores `wrapDecode M B h Z mod p` at
`outCell`, where `Z = garnerValue` is the CRT integer of the residues (`garnerValue_mod`,
`garnerValue_lt`) and `M = m_0 ⋯ m_(count-1)`; its frame is composed from the blocks' frames by
`Frame.trans` and `Frame.mono`. -/
theorem exec_reconstruct (mods L : Nat → Nat) (count : Nat) (table : GarnerTable mods count)
    (wrapB laddr vaddr zbase nz hintCell outCell : Nat) (hint : Bool) (memory : Memory)
    (layout : ReconLayout count laddr vaddr zbase nz hintCell outCell)
    (residues : ∀ i, i < count → memory.ram (word (laddr + i)) = word (L i))
    (residuesSmall : ∀ i, i < count → L i < mods i)
    (hintVal : memory.ram (word hintCell) = word (if hint then 1 else 0))
    (valueFits : prefixProd mods count ≤ 2 ^ (128 * nz)) (boundFits : wrapB < 2 ^ (128 * nz)) :
    ∃ after, (reconstruct mods count (prefixProd mods count) wrapB laddr vaddr zbase nz hintCell
        outCell).exec memory = some after ∧
      after.ram (word outCell) =
        fieldWord ((Kriterion.CRT.wrapDecode (prefixProd mods count) wrapB hint
          (garnerValue mods L count) : Nat) : BN254.BaseField) ∧
      Frame (reconstructWrites count vaddr zbase nz outCell) reconstructClobbers memory after := by
  have valueSmall : garnerValue mods L count < 2 ^ (128 * nz) :=
    lt_of_lt_of_le (garnerValue_lt mods L count table.pos count le_rfl) valueFits
  -- block 1
  obtain ⟨m1, run1, digits1, frame1⟩ := exec_garnerDigits mods L count table laddr vaddr memory
    layout.laddrFits layout.residuesApart layout.vaddrFits residues residuesSmall
  -- block 2
  obtain ⟨m2, run2, limbs2, frame2⟩ := exec_garnerHorner mods L count table vaddr zbase nz m1 digits1
    layout.vaddrFits layout.zFits layout.digitsApart valueFits
  -- block 3
  obtain ⟨m3, run3, out3, ram3, bits3, regs3⟩ := exec_limbLess (garnerValue mods L count) wrapB zbase
    nz m2 layout.zFits valueSmall boundFits limbs2
  have frame3 : Frame Writes.none (Clobbers.ofList [rOut, rFlag, rA, rB, rC, rD, rAddr]) m2 m3 :=
    ⟨fun address _ => by rw [ram3], bits3, fun register outside => regs3 register
      (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))
      (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))
      (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))
      (fun h => outside (by simp [Clobbers.ofList, h]))⟩
  -- block 4
  obtain ⟨m4, run4, acc4, ram4, bits4, regs4⟩ := exec_limbModP (garnerValue mods L count) zbase nz m3
    layout.zFits valueSmall (fun k kb => by rw [ram3]; exact limbs2 k kb)
  have frame4 : Frame Writes.none (Clobbers.ofList [rAcc, rA, rB, rAddr]) m3 m4 :=
    ⟨fun address _ => by rw [ram4], bits4, fun register outside => regs4 register
      (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))
      (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))⟩
  -- block 5
  have hintNow : m4.ram (word hintCell) = word (if hint then 1 else 0) := by
    rw [ram4, ram3, frame2.ram _ (fun ⟨k, kb, same⟩ => layout.hintOffLimbs k kb
        (word_inj layout.hintSmall (by have := layout.zFits; have kb' : k < nz := kb; omega) same)),
      frame1.ram _ (fun ⟨j, jb, same⟩ => layout.hintOffDigits j jb
        (word_inj layout.hintSmall (by have := layout.vaddrFits; have jb' : j < count := jb; omega)
          same))]
    exact hintVal
  have outNow : m4.registers rOut = word (if garnerValue mods L count < wrapB then 1 else 0) := by
    rw [regs4 rOut (by decide) (by decide) (by decide) (by decide), out3]
  obtain ⟨m5, run5, ram5, bits5, regs5⟩ := exec_wrapCombine (prefixProd mods count % BN254.baseFieldModulus)
    hintCell outCell m4 (garnerValue mods L count : BN254.BaseField) (if hint then 1 else 0)
    (if garnerValue mods L count < wrapB then 1 else 0) (by split <;> omega) (by split <;> omega)
    (lt_of_lt_of_le (Nat.mod_lt _ (by unfold BN254.baseFieldModulus; norm_num))
      (by unfold BN254.baseFieldModulus; norm_num)) acc4 outNow hintNow
  have frame5 : Frame (Writes.cell outCell) (Clobbers.ofList [rAcc, rB, rC, rAddr]) m4 m5 :=
    ⟨fun address outside => by rw [ram5, Function.update_of_ne outside], bits5,
      fun register outside => regs5 register
      (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))
      (fun h => outside (by simp [Clobbers.ofList, h])) (fun h => outside (by simp [Clobbers.ofList, h]))⟩
  refine ⟨m5, ?_, ?_, ?_⟩
  · unfold reconstruct
    rw [Prog.exec_seq_some _ _ memory m1 run1, Prog.exec_seq_some _ _ m1 m2 run2,
      Prog.exec_seq_some _ _ m2 m3 run3, Prog.exec_seq_some _ _ m3 m4 run4]
    exact run5
  · rw [ram5, Function.update_self, wrapDecode_cast]
  · refine ((((frame1.trans frame2).trans frame3).trans frame4).trans frame5).mono ?_ ?_
    · intro address inside
      rcases inside with (((inside | inside) | inside) | inside) | inside
      · exact Or.inl (Or.inl inside)
      · exact Or.inl (Or.inr inside)
      · exact inside.elim
      · exact inside.elim
      · exact Or.inr inside
    · intro register
      simp only [Clobbers.union, Clobbers.ofList, garnerClobbers, reconstructClobbers]
      revert register
      decide

end Field

/-! ### The fraction reading against the interface -/

/-- Pass `j` of `fracDigits` over the `2 q` limbs of a pad natural reads the interface's digit
`S - 1 - j` of `fractionValue m S q u`. -/
theorem frac_digit_interface (m S q u j : Nat) (below : j < S) :
    Kriterion.CRT.digit m (Kriterion.CRT.fractionValue m S q u) (S - 1 - j) =
      u * m ^ (j + 1) / 2 ^ (128 * (2 * q)) % m := by
  unfold Kriterion.CRT.digit Kriterion.CRT.fractionValue
  rw [show 256 * q = 128 * (2 * q) by ring]
  exact frac_digit_top u m S j _ below

end Kriterion.CRT.SimMachine
