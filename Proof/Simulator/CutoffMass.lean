/-
**The cutoff masses of the tail samplers** that the CRT machine's rows cutoff uses (`Proof/Simulator/CRT/Cutoff.lean`):
the curve-`x` sampler aborts with probability below `2^-170` (`curveXAbort_le`) and one over the number of affine
offsets is below `2^-131` (`affineCount_inv_le`). Every numeric step is exponent arithmetic on powers of two
(`CutoffNat`, `CutoffPow`): the curve-`x` rejection ratio is bounded by `5/8` (`5^3 ≤ 2^7`), so no large numeral is
formed.
-/

import Proof.Simulator.CutoffTail
import Proof.Simulator.CutoffNat
import Proof.Simulator.CutoffPow

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

theorem scalar_large : 3 * 2 ^ 252 + 1 ≤ scalarFieldModulus := Nat.le_of_ble_eq_true rfl

section Numbers

variable [FieldCertificate] [GroupCertificate]

/-- `#A ≥ 3 · 2^252`. -/
theorem affineCount_large : 3 * 2 ^ 252 ≤ affineCount :=
  Nat.le_of_add_le_add_right (Nat.le_trans scalar_large scalar_le_affineCount)

/-- The accepted and the rejected draws partition the draws. -/
theorem acceptedSet_add_rejectedCount (width : Nat) (accept : Nat → Bool) :
    (acceptedSet width accept).card + rejectedCount width accept = 2 ^ width := by
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 ^ width))))
    (fun value : Fin (2 ^ width) => accept value.val = true)
  rw [Finset.card_univ, Fintype.card_fin] at split
  unfold rejectedCount acceptedSet
  simp only [Bool.not_eq_true] at split
  exact split

/-- The curve-`x` sampler rejects at most `5 · 2^251` draws: `#A ≥ r − 1` and each accepted `x`
carries at most two offsets. -/
theorem rejectedCount_curveX : rejectedCount fieldWidth curveXAccept ≤ 5 * 2 ^ 251 := by
  have split := acceptedSet_add_rejectedCount fieldWidth curveXAccept
  have lower := affineCount_le
  rw [show acceptedX = acceptedSet fieldWidth curveXAccept from rfl] at lower
  have large := affineCount_large
  have first : (2 : Nat) ^ fieldWidth = 8 * 2 ^ 251 := by
    show (2 : Nat) ^ (3 + 251) = 8 * 2 ^ 251
    rewrite [Nat.pow_add]
    rfl
  have second : (2 : Nat) ^ 252 = 2 * 2 ^ 251 := by
    rewrite [show 252 = 1 + 251 from rfl, Nat.pow_add]
    rfl
  omega

/-- **The curve-`x` sampler aborts with probability below `2^-170`.** -/
theorem curveXAbort_le :
    rejectLaw fieldWidth curveXAccept attempts none ≤ ((2 : ENNReal) ^ 170)⁻¹ :=
  (rejectLaw_none_le fieldWidth _ attempts _ rejectedCount_curveX).trans
    (ratio_pow_le _ fieldWidth attempts 170 fiveEighths_nat)

/-- One over the number of affine offsets is below `2^-131`. -/
theorem affineCount_inv_le : (affineCount : ENNReal)⁻¹ ≤ ((2 : ENNReal) ^ 131)⁻¹ := by
  refine inv_le_of_pow_le _ _ (Nat.le_trans ?_ affineCount_large)
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide : 131 ≤ 252))
    (Nat.le_mul_of_pos_left _ (by decide))

end Numbers

end

end Kriterion.ArgoMAC.PlanB.SimMachine
