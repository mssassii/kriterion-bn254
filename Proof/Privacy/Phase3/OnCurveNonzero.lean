/-
**Both coordinates of a BN254 curve point are non-zero.**

The four-element `Y` row reads its randomiser `r4` off the cubic element by a division by `x`, and
its collector is the mixed element, whose clear multiplier is `y`; the per-digit bijection and the
collector solve therefore divide by `x` and by `y` at the input. On the curve `y² = x³ + 3`:

* `x ≠ 0`, because `x = 0` would make `3` a square, and `3 ^ ((p − 1) / 2) = −1` (Euler's criterion;
  the kernel reduces the power with `reduce_mod_char`, as in Lazar's entry `d9a8327`,
  `BiquadraticDistribution.lean`);
* `y ≠ 0`, because `y = 0` would make `−3` a cube, and `(−3) ^ ((p − 1) / 3) ≠ 1` (it is a
  primitive cube root of unity; `p ≡ 1 mod 3`).

Neither fact uses the group order.
-/

import Mathlib.Tactic.ReduceModChar
import Mathlib.FieldTheory.Finite.Basic
import ScalarMultiplication

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254

private theorem three_pow_half_literal :
    (3 : ZMod 21888242871839275222246405745257275088696311157297823662689037894645226208583) ^
      10944121435919637611123202872628637544348155578648911831344518947322613104291 = -1 := by
  reduce_mod_char

/-- Euler's criterion value: three is a quadratic non-residue in the base field. -/
theorem three_pow_half [FieldCertificate] : (3 : BaseField) ^ (baseFieldModulus / 2) = -1 := by
  have half : baseFieldModulus / 2 =
      10944121435919637611123202872628637544348155578648911831344518947322613104291 := by
    unfold baseFieldModulus; norm_num
  rw [half]
  exact three_pow_half_literal

/-- Three is not a square in the base field. -/
theorem three_not_square [FieldCertificate] : ¬ IsSquare (3 : BaseField) := by
  intro square
  have three : (3 : BaseField) ≠ 0 := by
    intro zero
    have power : (3 : BaseField) ^ (baseFieldModulus / 2) = -1 := three_pow_half
    rw [zero, zero_pow (by unfold baseFieldModulus; norm_num)] at power
    have one : (1 : BaseField) = 0 := by linear_combination power
    exact one_ne_zero one
  have euler := (ZMod.euler_criterion baseFieldModulus three).mp square
  rw [three_pow_half] at euler
  have two : (2 : BaseField) = 0 := by linear_combination -euler
  have value : (2 : BaseField).val = 2 := by
    change ((2 : ℕ) : BaseField).val = 2
    exact ZMod.val_natCast_of_lt (by unfold baseFieldModulus; norm_num)
  rw [two, ZMod.val_zero] at value
  exact absurd value (by decide)

/-- **Every curve point has a non-zero `x` coordinate.** -/
theorem onCurve_x_ne_zero [FieldCertificate] (input : AffineInput) (onCurve : OnCurve input) :
    input.x ≠ 0 := by
  intro zero
  unfold OnCurve at onCurve
  rw [zero] at onCurve
  exact three_not_square ⟨input.y, by linear_combination -onCurve⟩

private theorem minus_three_pow_third_literal :
    (-3 : ZMod 21888242871839275222246405745257275088696311157297823662689037894645226208583) ^
      7296080957279758407415468581752425029565437052432607887563012631548408736194 =
      21888242871839275220042445260109153167277707414472061641714758635765020556616 := by
  reduce_mod_char

/-- `(−3) ^ ((p − 1) / 3)` is not one: `−3` is not a cube in the base field. -/
theorem minus_three_pow_third_ne_one [FieldCertificate] :
    (-3 : BaseField) ^ ((baseFieldModulus - 1) / 3) ≠ 1 := by
  have third : (baseFieldModulus - 1) / 3 =
      7296080957279758407415468581752425029565437052432607887563012631548408736194 := by
    unfold baseFieldModulus; norm_num
  rw [third]
  intro one
  have value : (21888242871839275220042445260109153167277707414472061641714758635765020556616 :
      BaseField) = 1 := by
    rw [← one]
    exact minus_three_pow_third_literal.symm
  have vals := congrArg ZMod.val value
  rw [ZMod.val_one] at vals
  change ((21888242871839275220042445260109153167277707414472061641714758635765020556616 : ℕ) :
    BaseField).val = 1 at vals
  rw [ZMod.val_natCast_of_lt (by unfold baseFieldModulus; norm_num)] at vals
  exact absurd vals (by norm_num)

/-- **Every curve point has a non-zero `y` coordinate.** -/
theorem onCurve_y_ne_zero [FieldCertificate] (input : AffineInput) (onCurve : OnCurve input) :
    input.y ≠ 0 := by
  intro zero
  unfold OnCurve at onCurve
  rw [zero] at onCurve
  have cube : input.x ^ 3 = -3 := by linear_combination -onCurve
  have xNe : input.x ≠ 0 := by
    intro xZero
    rw [xZero] at cube
    have three : (3 : BaseField) = 0 := by linear_combination cube
    have value : (3 : BaseField).val = 3 := by
      change ((3 : ℕ) : BaseField).val = 3
      exact ZMod.val_natCast_of_lt (by unfold baseFieldModulus; norm_num)
    rw [three, ZMod.val_zero] at value
    exact absurd value (by decide)
  have fermat : input.x ^ (baseFieldModulus - 1) = 1 := ZMod.pow_card_sub_one_eq_one xNe
  have split : baseFieldModulus - 1 = 3 * ((baseFieldModulus - 1) / 3) := by
    unfold baseFieldModulus; norm_num
  rw [split, pow_mul, cube] at fermat
  exact minus_three_pow_third_ne_one fermat

end Kriterion.ArgoMAC.Security.Phase3
