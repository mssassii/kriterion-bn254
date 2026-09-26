/-
C7: the real table satisfies the delivery conditions (`CorrectTable`), row by row,
by kernel evaluation (`decide +kernel`; the 623-bit `M` and the pairwise gcds of the 85 moduli are
computed by the kernel's GMP-backed `Nat` operations, never by the elaborator).
-/

import Proof.Correctness.CRT.Delivery

namespace Kriterion.CRT.SliceC

open scoped Function
open Kriterion.CRT

set_option maxRecDepth 100000

theorem bn254_modulus_pos : ∀ i, 0 < bn254Table.modulus i := by decide +kernel

theorem bn254_coprime : Pairwise (Nat.Coprime on bn254Table.modulus) := by
  unfold Pairwise Function.onFun
  decide +kernel

theorem bn254_wrap : 2 * bn254Table.wrapBound ≤ bn254Table.product + 1 := by decide +kernel

theorem bn254_chunkZero : ∀ i, bn254Table.kind i = .chunkZero →
    bn254Table.modulus i = 2 ^ bn254Table.chunkWidth 0 := by decide +kernel

/-- The closed-form T9 facts of every odd modulus. -/
theorem bn254_t9Facts : ∀ i : Fin bn254Table.count, bn254Table.modulus i ≠ 256 →
    1 ≤ (t9Row 32 (bn254Table.modulus i)).width0 ∧ 1 ≤ (t9Row 32 (bn254Table.modulus i)).width1 ∧
      (t9Row 32 (bn254Table.modulus i)).width0 + (t9Row 32 (bn254Table.modulus i)).width1 + 1 =
        (t9Row 32 (bn254Table.modulus i)).ell ∧
      (t9Row 32 (bn254Table.modulus i)).width0 ≤ (t9Row 32 (bn254Table.modulus i)).keep ∧
      (t9Row 32 (bn254Table.modulus i)).keep ≤ (t9Row 32 (bn254Table.modulus i)).ell ∧
      (t9Row 32 (bn254Table.modulus i)).ell ≤ bn254Table.castWidth ∧
      bn254Table.chunkCount * (bn254Table.modulus i - 1) < 2 ^ (t9Row 32 (bn254Table.modulus i)).ell := by
  decide +kernel

theorem bn254_odd : ∀ i row, bn254Table.kind i = .odd row →
    1 ≤ row.width0 ∧ 1 ≤ row.width1 ∧ row.width0 + row.width1 + 1 = row.ell ∧
      row.width0 ≤ row.keep ∧ row.keep ≤ row.ell ∧ row.ell ≤ bn254Table.castWidth ∧
      bn254Table.chunkCount * (bn254Table.modulus i - 1) < 2 ^ row.ell := by
  intro i row kind
  have facts := bn254_t9Facts i
  change t9Kind (bn254Table.modulus i) = .odd row at kind
  unfold t9Kind at kind
  split at kind
  · cases kind
  · rename_i notPow
    cases kind
    exact facts notPow

/-- **The real table delivers** (the hypothesis of `coord_delivery`). -/
theorem bn254_correctTable : CorrectTable bn254Table where
  chunkBits_pos := by decide
  inputBits_pos := by decide
  castWidth_pos := by decide
  modulus_pos := bn254_modulus_pos
  coprime := bn254_coprime
  wrap := bn254_wrap
  chunkZero := bn254_chunkZero
  odd := bn254_odd

end Kriterion.CRT.SliceC
