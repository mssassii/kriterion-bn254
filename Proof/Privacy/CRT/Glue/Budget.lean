/-
**The error terms of the CRT chain and the closing inequality**.

| hop | term | value |
|---|---|---|
| `G0 → G0T` | `tCollisionError = 1,759,967 / p` (`t` equal to a labelled garbler input) | `2^-232.85` |
| `G0T → G0U` | `padSwapError`: the pad-reading biases `Σ_κ Σ_{m odd} m · m^S / 2^(256 q)` and `637 δ₃` | `2^-113.5` |
| `G0U → G1U` | `hiddenPointError (q₁ + q₂) = (q₁ + q₂) (4/2^104 + 1/(p − 1))` | linear |
| `G0U → G1U` | `hiddenWindowError = smudgeError` (the curve encodings' wrap window) | `2^-100.65` |
| `G1U → HW` | `stageOneTouchError q₁ + smudgeError + exceptionalError + coincidenceError + padSwapError` | linear + `2^-100.65` + ... |
| `HW → H` | `outputKernelError = 455/(r − 1)` | `2^-244.8` |
| `H → I` | `padSwapError` (untouched sites only, no per-query term; F4) | `2^-113.51` |
| `I → M` | `machineCutoffError = 2^-128` | `2^-128` |

Every term is a fraction of two naturals (`frac`), so its share of the unit reduces to one closed `Nat.ble` of
the generated `BudgetData` (decided by `decide +kernel`, no axiom), and the readable forms
(`crtHiddenCharge_eq`, ...) are separate lemmas. `chainError_budget` closes with every constant below a thousandth
of its unit except the smudge term and the hidden window (seven tenths each), and every per-query coefficient below a
third. The constant part is closed against **two** units: the challenge's allowance is
`steps + 1 = size + 2 + firstFuel + secondFuel ≥ q₁ + q₂ + 2` (`BoundedMachine.Adversary.steps`).
-/

import Proof.Privacy.CRT.Glue.BudgetFacts
import Construction.CRT.Interface
import Mathlib.Tactic

namespace Kriterion.CRT.Privacy

open Kriterion.CRT

noncomputable section

/-! ### Fractions of naturals and their share of the unit -/

/-- A fraction of two naturals, as a real. -/
def frac (a b : ℕ) : ℝ := (a : ℝ) / (b : ℝ)

theorem frac_nonneg (a b : ℕ) : 0 ≤ frac a b := by
  unfold frac
  positivity

/-- **One closed inequality of naturals gives the share.** `a / b` is at most `1 / c` of the unit `2^-100` when
`a · 2^100 · c ≤ b`. The inequalities are the ones of `BudgetData`, restated here and decided by the
kernel (`decide +kernel`): passing `BudgetData`'s own theorems through the elaborator makes it compare core's and
Mathlib's `2 ^ n` on the 4,000-bit numerals, which exceeds the recursion depth (verified, `Scratch/BudgetProbe*.lean`). -/
theorem frac_share {a b c : ℕ} (le : a * 2 ^ 100 * c ≤ b) (hb : 0 < b) (hc : 0 < c) :
    frac a b * 2 ^ 100 ≤ 1 / (c : ℝ) := by
  have leR : (a : ℝ) * 2 ^ 100 * c ≤ b := by exact_mod_cast le
  have bpos : (0 : ℝ) < b := by exact_mod_cast hb
  have cpos : (0 : ℝ) < c := by exact_mod_cast hc
  unfold frac
  rw [div_mul_eq_mul_div, div_le_iff₀ bpos, one_div, inv_mul_eq_div, le_div_iff₀ cpos]
  exact leR

/-- **A share `c / d` of the unit** from one closed inequality of naturals: `a · 2^100 · d ≤ c · b`. -/
theorem frac_share_le {a b c d : ℕ} (le : a * 2 ^ 100 * d ≤ c * b) (hb : 0 < b) (hd : 0 < d) :
    frac a b * 2 ^ 100 ≤ (c : ℝ) / d := by
  have leR : (a : ℝ) * 2 ^ 100 * d ≤ c * b := by exact_mod_cast le
  have bpos : (0 : ℝ) < b := by exact_mod_cast hb
  have dpos : (0 : ℝ) < d := by exact_mod_cast hd
  unfold frac
  rw [div_mul_eq_mul_div, div_le_div_iff₀ bpos dpos]
  linarith

/-! ### The moduli agree with the challenge's -/

theorem baseFieldModulus_eq : BN254.baseFieldModulus = BudgetData.p := rfl

theorem scalarFieldModulus_eq : BN254.scalarFieldModulus = BudgetData.r := rfl

theorem p_pos : 0 < BudgetData.p := by decide +kernel

theorem one_lt_p : 1 < BudgetData.p := by decide +kernel

theorem one_lt_r : 1 < BudgetData.r := by decide +kernel

theorem M_pos : 0 < BudgetData.M := by decide +kernel

/-! ### The terms -/

/-- `G0 → G0T`: the garbler-input collision term, conservatively charged at the fixed G gate
1,759,967 (D11), independent of the concrete schedule's smaller query count. -/
def tCollisionError : ℝ := frac 1759967 BudgetData.p

/-- One pad-and-mask swap: `padSwapNum / 2^4352` (the pad-reading biases of both coordinates at slack 120) plus `637 δ₃`, `δ₃ = (2^384 mod p)/2^384`, over the common denominator `2^4352`. -/
def padSwapError : ℝ :=
  frac BudgetData.padSwapNumer BudgetData.padSwapDenom

/-- The CRT smudge-and-hint term `(1284 (p − 1)^2 + 273 p) / M` (kept with its
`273 p / M` part as an upper bound). The main term is doubled, `2 · 642 (B − 1)/M`,
because route M's middle game flags the two-sided window `[0, B − 1) ∪ (M − B, M)` of the CRT values (it cannot see
`a_e v`, so a real offset with the hint set may land at either end; `Core/H8.lean`, `replayWraps`). -/
def smudgeError : ℝ := frac (1284 * (BudgetData.p - 1) ^ 2 + 273 * BudgetData.p) BudgetData.M

/-- The window term of the hidden hop: the tapes on which a curve encoding's offset lies near
the wrap window, where its hint could pin the curve mask; charged once, outside the per-query charge. Bounded by the
smudge term (five encodings against its 642-encoding union bound). -/
def hiddenWindowError : ℝ := smudgeError

/-- The per-query charge of the hidden hop, `4/2^104 + 1/(p − 1)`. -/
def crtHiddenCharge : ℝ := frac (4 * (BudgetData.p - 1) + 2 ^ 104) (2 ^ 104 * (BudgetData.p - 1))

/-- `G0U → G1U`: `q · (4/2^104 + 1/(p − 1))`. -/
def hiddenPointError (queries : ℕ) : ℝ := (queries : ℝ) * crtHiddenCharge

/-- The per-query charge of a stage-1 touch of a designed-visible garbler point: the hidden hop's charge
`4/2^104 + 1/(p − 1)` (`M'`'s touch is bounded through the core by the real touch of a garbler
entry, `CrtStageOneGuess E crtHiddenCharge`). -/
def stageOneTouchCharge : ℝ := crtHiddenCharge

/-- The stage-1 touch flag of `G1U → HW`: `q₁ · (4/2^104 + 1/(p − 1))`. -/
def stageOneTouchError (first : ℕ) : ℝ := (first : ℝ) * stageOneTouchCharge

/-- The digit doublings, `364/(r − 1)` (route M's doubling flag covers `T = K`, `T = −K` and the sign row's
zero `T = 2K` for each of the 91 digits, and the certificates give only `#Point ≥ r`). -/
def doublingError : ℝ := frac 364 (BudgetData.r - 1)

/-- The row normalization's flag, `182/p`: one of the stage-1 source's two hidden cells of a digit is zero
(`H8.normBadSrc`; it pays for the construction's zero collector offsets). -/
def normError : ℝ := frac 182 BudgetData.p

/-- The exceptional event, `546/(r − 1)`: the digit doublings and the row normalization's flag. -/
def exceptionalError : ℝ := frac 546 (BudgetData.r - 1)

/-- Coincidences, `185/2^128` (182 digest keys, one per exceptional kind of each digit, the off-curve mask key, two
`Δ = 0` events). -/
def coincidenceError : ℝ := frac 185 (2 ^ 128)

/-- `HW → H`: the output kernel, `455/(r − 1)`. -/
def outputKernelError : ℝ := frac 455 (BudgetData.r - 1)

/-- `I → M`: the machine's sampler cutoff, `2^-128`. -/
def machineCutoffError : ℝ := frac 1 (2 ^ 128)

/-- **The whole chain** `G0 → G0T → G0U → G1U → HW → H → I → M`, in hop order. -/
def chainError (first second : ℕ) : ℝ :=
  tCollisionError + padSwapError + (hiddenPointError (first + second) + hiddenWindowError) +
    (stageOneTouchError first + smudgeError + exceptionalError + coincidenceError + padSwapError) +
    outputKernelError + padSwapError + machineCutoffError

/-! ### Readable forms -/

theorem crtHiddenCharge_eq :
    crtHiddenCharge = 4 / 2 ^ 104 + 1 / ((BN254.baseFieldModulus : ℝ) - 1) := by
  have hp : (1 : ℝ) < (BudgetData.p : ℝ) := by exact_mod_cast one_lt_p
  have cast : ((BudgetData.p - 1 : ℕ) : ℝ) = (BudgetData.p : ℝ) - 1 := by
    rw [Nat.cast_sub one_lt_p.le, Nat.cast_one]
  have ne : (BudgetData.p : ℝ) - 1 ≠ 0 := by linarith
  unfold crtHiddenCharge frac
  rw [baseFieldModulus_eq]
  push_cast [cast]
  field_simp
  ring

theorem exceptionalError_eq : exceptionalError = 546 / ((BN254.scalarFieldModulus : ℝ) - 1) := by
  unfold exceptionalError frac
  rw [scalarFieldModulus_eq, Nat.cast_sub one_lt_r.le, Nat.cast_one]
  norm_num

theorem outputKernelError_eq : outputKernelError = 455 / ((BN254.scalarFieldModulus : ℝ) - 1) := by
  unfold outputKernelError frac
  rw [scalarFieldModulus_eq, Nat.cast_sub one_lt_r.le, Nat.cast_one]
  norm_num

theorem machineCutoffError_eq : machineCutoffError = 1 / 2 ^ 128 := by
  unfold machineCutoffError frac
  norm_num

theorem stageOneTouchCharge_eq :
    stageOneTouchCharge = 4 / 2 ^ 104 + 1 / ((BN254.baseFieldModulus : ℝ) - 1) :=
  crtHiddenCharge_eq

/-! ### The shares, decided by the kernel (the inequalities of `BudgetData`, section "Each term") -/

theorem collision_share : 1759967 * 2 ^ 100 * 1000 ≤ BudgetData.p := by decide +kernel

theorem padSwap_share : BudgetData.padSwapNumer * 2 ^ 100 * 1000 ≤ BudgetData.padSwapDenom := by decide +kernel

theorem smudge_share : (1284 * (BudgetData.p - 1) ^ 2 + 273 * BudgetData.p) * 2 ^ 100 * 10 ≤ 7 * BudgetData.M := by
  decide +kernel

theorem exceptional_share : 546 * 2 ^ 100 * 1000 ≤ BudgetData.r - 1 := by decide +kernel

theorem r_sub_one_le_p : BudgetData.r - 1 ≤ BudgetData.p := by decide +kernel

theorem doublingError_nonneg : 0 ≤ doublingError := frac_nonneg _ _

theorem normError_nonneg : 0 ≤ normError := frac_nonneg _ _

/-- **The digit doublings and the normalization flag fit the exceptional term**: `364/(r − 1) + 182/p ≤ 546/(r − 1)`. -/
theorem doubling_add_norm_le : doublingError + normError ≤ exceptionalError := by
  have rpos : (0 : ℝ) < ((BudgetData.r - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt one_lt_r
  have le : ((BudgetData.r - 1 : ℕ) : ℝ) ≤ (BudgetData.p : ℝ) := by exact_mod_cast r_sub_one_le_p
  have normLe : normError ≤ frac 182 (BudgetData.r - 1) := by
    unfold normError frac
    exact div_le_div_of_nonneg_left (by norm_num) rpos le
  unfold doublingError exceptionalError
  refine le_trans (add_le_add_right normLe _) (le_of_eq ?_)
  unfold frac
  rw [← add_div]
  norm_num

theorem outputKernel_share : 455 * 2 ^ 100 * 1000 ≤ BudgetData.r - 1 := by decide +kernel

theorem coincidence_share : 185 * 2 ^ 100 * 1000 ≤ 2 ^ 128 := by decide +kernel

theorem machineCutoff_share : 1 * 2 ^ 100 * 1000 ≤ 2 ^ 128 := by decide +kernel

theorem hiddenCharge_share : (4 * (BudgetData.p - 1) + 2 ^ 104) * 2 ^ 100 * 3 ≤ 2 ^ 104 * (BudgetData.p - 1) := by decide +kernel

theorem stageOneTouch_share : 4 * 2 ^ 100 * 3 ≤ 2 ^ 104 := by decide +kernel

/-! ### Each term against its share of the unit -/

theorem tCollisionError_le : tCollisionError * 2 ^ 100 ≤ 1 / 1000 := by
  have := frac_share (c := 1000) collision_share p_pos (by norm_num)
  unfold tCollisionError
  exact this

theorem padSwapError_le : padSwapError * 2 ^ 100 ≤ 1 / 1000 := by
  have := frac_share (c := 1000) padSwap_share BudgetData.padSwapDenom_pos (by norm_num)
  unfold padSwapError
  exact this

theorem smudgeError_le : smudgeError * 2 ^ 100 ≤ 7 / 10 := by
  have share := frac_share_le (c := 7) (d := 10) smudge_share M_pos (by norm_num)
  unfold smudgeError
  calc _ ≤ ((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ) := share
    _ = 7 / 10 := by norm_num

theorem exceptionalError_le : exceptionalError * 2 ^ 100 ≤ 1 / 1000 := by
  have := frac_share (c := 1000) exceptional_share (Nat.sub_pos_of_lt one_lt_r) (by norm_num)
  unfold exceptionalError
  exact this

theorem outputKernelError_le : outputKernelError * 2 ^ 100 ≤ 1 / 1000 := by
  have := frac_share (c := 1000) outputKernel_share (Nat.sub_pos_of_lt one_lt_r) (by norm_num)
  unfold outputKernelError
  exact this

theorem coincidenceError_le : coincidenceError * 2 ^ 100 ≤ 1 / 1000 := by
  have := frac_share (c := 1000) coincidence_share (Nat.two_pow_pos 128) (by norm_num)
  unfold coincidenceError
  exact this

theorem machineCutoffError_le : machineCutoffError * 2 ^ 100 ≤ 1 / 1000 := by
  have := frac_share (c := 1000) machineCutoff_share (Nat.two_pow_pos 128) (by norm_num)
  unfold machineCutoffError
  exact this

theorem hiddenWindowError_le : hiddenWindowError * 2 ^ 100 ≤ 7 / 10 := smudgeError_le

theorem hiddenWindowError_nonneg : 0 ≤ hiddenWindowError := by
  unfold hiddenWindowError smudgeError
  exact frac_nonneg _ _

theorem crtHiddenCharge_le : crtHiddenCharge * 2 ^ 100 ≤ 1 / 3 := by
  have pos : 0 < 2 ^ 104 * (BudgetData.p - 1) :=
    Nat.mul_pos (Nat.two_pow_pos 104) (Nat.sub_pos_of_lt one_lt_p)
  have := frac_share (c := 3) hiddenCharge_share pos (by norm_num)
  unfold crtHiddenCharge
  exact this

theorem stageOneTouchCharge_le : stageOneTouchCharge * 2 ^ 100 ≤ 1 / 3 :=
  crtHiddenCharge_le

/-! ### The closing inequality -/

/-- **The closing inequality.** Below `2^100` queries the whole chain costs at most `(q₁ + q₂ + 2) / 2^100`: the
constant part (three swaps, the smudge term, the hidden hop's window term, the collision, the doubling, the kernel,
the coincidences, the cutoff) is below `1408/1000` of one unit and the linear part below `2/3` of a unit per query.
The second unit is the challenge's: `steps + 1 = size + 2 + firstFuel + secondFuel` (`Shapes.lean`). -/
theorem chainError_budget (first second : ℕ) (_small : first + second < 2 ^ 100) :
    chainError first second * 2 ^ 100 ≤ (first : ℝ) + (second : ℝ) + 2 := by
  have c0 := tCollisionError_le
  have c1 := padSwapError_le
  have c2 := smudgeError_le
  have c3 := exceptionalError_le
  have c4 := outputKernelError_le
  have c5 := coincidenceError_le
  have c6 := machineCutoffError_le
  have c7 := hiddenWindowError_le
  have l1 := crtHiddenCharge_le
  have l2 := stageOneTouchCharge_le
  have firstNonneg : (0 : ℝ) ≤ first := Nat.cast_nonneg _
  have secondNonneg : (0 : ℝ) ≤ second := Nat.cast_nonneg _
  have hidden : hiddenPointError (first + second) * 2 ^ 100 ≤ ((first : ℝ) + second) / 3 := by
    unfold hiddenPointError
    push_cast
    rw [mul_assoc, div_eq_mul_one_div ((first : ℝ) + second) 3]
    exact mul_le_mul_of_nonneg_left l1 (by positivity)
  have touch : stageOneTouchError first * 2 ^ 100 ≤ (first : ℝ) / 3 := by
    unfold stageOneTouchError
    rw [mul_assoc, div_eq_mul_one_div (first : ℝ) 3]
    exact mul_le_mul_of_nonneg_left l2 firstNonneg
  unfold chainError
  nlinarith

end

end Kriterion.CRT.Privacy
