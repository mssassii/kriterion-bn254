/-
**Garner's reconstruction, the wrap hint and the reduction modulo `p`** on the machine.

For one encoding with residues `L_i` modulo the table `m_0, …, m_(T-1)` (pairwise coprime), the
evaluator's decoded value is `wrapDecode M B h Z mod p`, where `Z < M` is the CRT integer of the
residues. The machine computes it in four blocks:

1. `garnerDigits`: the mixed-radix digits `v_i = ((L_i - Σ_(j<i) v_j c_ij) · inv_i) mod m_i`, with
   `c_ij = (m_0 ⋯ m_(j-1)) mod m_i` and `inv_i = (m_0 ⋯ m_(i-1))⁻¹ mod m_i` compile-time constants;
   the running sum is offset by `m_i · 2 ^ 20` so it never goes negative, and each reduction is one
   `barrett` at width 32. Digit `i` is stored at `vaddr + i`.
2. `garnerHorner`: `Z = Σ v_i · m_0 ⋯ m_(i-1)` by Horner's rule from the top digit, one
   `mulSmallAdd` pass over `nz` limbs at `zbase` per digit.
3. `limbLess`: `[Z < B]` by a constant-time lexicographic comparison of the limbs with the constant
   `B`, top limb first.
4. `limbModP`: `Z mod p` as `Σ z_k · (2 ^ (128 k) mod p)` with `fieldMul` and `fieldAdd`; then
   `w = Z + [h ∧ Z < B] · (M mod p)` in the field, which is `wrapDecode M B h Z mod p`.
-/

import Construction.Simulator.CRT.Arith
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! ### Compile-time constants -/

/-- `m_0 ⋯ m_(i-1)`. -/
def prefixProd (mods : Nat → Nat) (i : Nat) : Nat := ∏ k ∈ Finset.range i, mods k

/-- Garner's coefficient `c_ij = (m_0 ⋯ m_(j-1)) mod m_i`. -/
def garnerCoef (mods : Nat → Nat) (i j : Nat) : Nat := prefixProd mods j % mods i

/-- Garner's inverse `(m_0 ⋯ m_(i-1))⁻¹ mod m_i`. -/
def garnerInv (mods : Nat → Nat) (i : Nat) : Nat :=
  ((prefixProd mods i : ZMod (mods i))⁻¹).val

/-- The offset that keeps Garner's running sum nonnegative: `m_i · 2 ^ 20`. -/
def garnerLift : Nat := 2 ^ 20

/-! ### Block 1: the mixed-radix digits -/

/-- One term: `rAcc := rAcc - v_j · c_ij`. -/
def garnerTerm (mods : Nat → Nat) (vaddr i j : Nat) : Prog :=
  .seq (loadAt rB (vaddr + j))
    (.seq (cst rC (garnerCoef mods i j))
    (.seq (ar .mul rB rB rC) (ar .sub rAcc rAcc rB)))

/-- Digit `i`: the offset, the `i` terms, the residue, two reductions, the store. -/
def garnerDigitProg (mods : Nat → Nat) (laddr vaddr i : Nat) : Prog :=
  .seq (cst rAcc (mods i * garnerLift))
    (.seq (Prog.rep i (garnerTerm mods vaddr i))
    (.seq (loadAt rB (laddr + i))
    (.seq (ar .add rAcc rAcc rB)
    (.seq (barrett rAcc rOut (mods i) 32)
    (.seq (cst rC (garnerInv mods i))
    (.seq (ar .mul rOut rOut rC)
    (.seq (barrett rOut rOut (mods i) 32) (storeAt (vaddr + i) rOut))))))))

/-- The `count` digits of one encoding: residues at `laddr + i`, digits to `vaddr + i`. -/
def garnerDigits (mods : Nat → Nat) (count laddr vaddr : Nat) : Prog :=
  Prog.rep count (garnerDigitProg mods laddr vaddr)

/-! ### Block 2: Horner's rule -/

/-- Zero the `nz` limbs at `zbase` (`rA := 0`). -/
def zeroLimbs (zbase nz : Nat) : Prog :=
  .seq (cst rA 0) (Prog.rep nz fun k => storeAt (zbase + k) rA)

/-- One Horner step for digit `i`: `Z := Z · m_i + v_i`. -/
def hornerStep (mods : Nat → Nat) (vaddr zbase nz i : Nat) : Prog :=
  .seq (cst rM (mods i)) (.seq (loadAt rC (vaddr + i)) (mulSmallAdd zbase nz))

/-- `Z = Σ v_i · m_0 ⋯ m_(i-1)` in `nz` limbs at `zbase`, top digit first. -/
def garnerHorner (mods : Nat → Nat) (count vaddr zbase nz : Nat) : Prog :=
  .seq (cst rMask limbMask)
    (.seq (cst rK128 128)
    (.seq (zeroLimbs zbase nz)
      (Prog.rep count fun t => hornerStep mods vaddr zbase nz (count - 1 - t))))

/-! ### Block 3: the comparison with a constant -/

/-- Limb `k` of a constant (`(value / 2 ^ (128 k)) mod 2 ^ 128`). -/
def constLimb (value k : Nat) : Nat := value / 2 ^ (128 * k) % 2 ^ 128

/-- One limb of the comparison, top limb first: `rOut += rFlag · [z_k < K_k]`,
`rFlag := rFlag · [z_k = K_k]`. -/
def lessStep (bound zbase k : Nat) : Prog :=
  .seq (loadAt rA (zbase + k))
    (.seq (cst rB (constLimb bound k))
    (.seq (ar .less rC rA rB)
    (.seq (ar .mul rC rC rFlag)
    (.seq (ar .add rOut rOut rC)
    (.seq (ar .xor rC rA rB)
    (.seq (cst rD 1)
    (.seq (ar .less rC rC rD) (ar .mul rFlag rFlag rC))))))))

/-- `rOut := [Z < bound]` for the `nz`-limb integer `Z` at `zbase`. -/
def limbLess (bound zbase nz : Nat) : Prog :=
  .seq (cst rOut 0) (.seq (cst rFlag 1) (Prog.rep nz fun t => lessStep bound zbase (nz - 1 - t)))

/-! ### Block 4: the reduction modulo `p` -/

/-- `2 ^ (128 k) mod p`. -/
def modPCoef (k : Nat) : Nat := 2 ^ (128 * k) % BN254.baseFieldModulus

/-- One limb: `rAcc := rAcc + z_k · (2 ^ (128 k) mod p)` in the field. -/
def modPStep (zbase k : Nat) : Prog :=
  .seq (loadAt rA (zbase + k))
    (.seq (cst rB (modPCoef k))
    (.seq (ar .fieldMul rA rA rB) (ar .fieldAdd rAcc rAcc rA)))

/-- `rAcc := Z mod p` for the `nz`-limb integer `Z` at `zbase`. -/
def limbModP (zbase nz : Nat) : Prog :=
  .seq (cst rAcc 0) (Prog.rep nz (modPStep zbase))

/-! ### Block 5: the wrap hint -/

/-- `w := rAcc + (hint · rOut) · (M mod p)` in the field, stored at `outCell`; the hint is the
word `0` or `1` at `hintCell`, `rOut` holds `[Z < B]`. -/
def wrapCombine (modulusModP hintCell outCell : Nat) : Prog :=
  .seq (loadAt rB hintCell)
    (.seq (ar .mul rB rB rOut)
    (.seq (cst rC modulusModP)
    (.seq (ar .fieldMul rB rB rC)
    (.seq (ar .fieldAdd rAcc rAcc rB) (storeAt outCell rAcc)))))

/-- **The reconstruction of one encoding**: residues at `laddr + i` (`i < count`), the hint at
`hintCell`, the value `wrapDecode M B h Z mod p` to `outCell`; scratch digits at `vaddr`, limbs at
`zbase`. `M = m_0 ⋯ m_(count-1)` and `B` are passed as compile-time constants. -/
def reconstruct (mods : Nat → Nat) (count modulus wrapB laddr vaddr zbase nz hintCell outCell : Nat) :
    Prog :=
  .seq (garnerDigits mods count laddr vaddr)
    (.seq (garnerHorner mods count vaddr zbase nz)
    (.seq (limbLess wrapB zbase nz)
    (.seq (limbModP zbase nz)
      (wrapCombine (modulus % BN254.baseFieldModulus) hintCell outCell))))

/-! ### Sizes and costs -/

theorem cost_garnerTerm (mods : Nat → Nat) (vaddr i j : Nat) :
    (garnerTerm mods vaddr i j).cost = 5 := rfl

theorem cost_garnerDigitProg (mods : Nat → Nat) (laddr vaddr i : Nat) :
    (garnerDigitProg mods laddr vaddr i).cost = 32 + 5 * i := by
  simp only [garnerDigitProg, Prog.cost, cst, ar, cost_barrett, cost_loadAt, cost_storeAt]
  rw [Prog.cost_rep i _ 5 (fun j _ => cost_garnerTerm mods vaddr i j)]
  omega

theorem cost_hornerStep (mods : Nat → Nat) (vaddr zbase nz i : Nat) :
    (hornerStep mods vaddr zbase nz i).cost = 3 + 7 * nz := by
  simp only [hornerStep, Prog.cost, cst, cost_loadAt, cost_mulSmallAdd]
  omega

end Kriterion.CRT.SimMachine
