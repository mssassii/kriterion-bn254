/-
C7: the real table satisfies the delivery conditions (`CorrectTable`), row by row,
by kernel evaluation (`decide +kernel`; the 619-bit `M` and the pairwise gcds of the 84 moduli are
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

/-- The original T9 facts on the real moduli, retained independently of the chosen schedule. -/
theorem bn254_t9Facts : ∀ i : Fin bn254Table.count, bn254Table.modulus i ≠ 256 →
    1 ≤ (t9Row 32 (bn254Table.modulus i)).width0 ∧ 1 ≤ (t9Row 32 (bn254Table.modulus i)).width1 ∧
      (t9Row 32 (bn254Table.modulus i)).width0 + (t9Row 32 (bn254Table.modulus i)).width1 + 1 =
        (t9Row 32 (bn254Table.modulus i)).ell ∧
      (t9Row 32 (bn254Table.modulus i)).width0 ≤ (t9Row 32 (bn254Table.modulus i)).keep ∧
      (t9Row 32 (bn254Table.modulus i)).keep ≤ (t9Row 32 (bn254Table.modulus i)).ell ∧
      (t9Row 32 (bn254Table.modulus i)).ell ≤ bn254Table.castWidth ∧
      bn254Table.chunkCount * (bn254Table.modulus i - 1) < 2 ^ (t9Row 32 (bn254Table.modulus i)).ell := by
  decide +kernel

/-- The fallback facts of every real odd modulus. Only small row data is evaluated here. -/
theorem bn254_fallbackFacts : ∀ i : Fin bn254Table.count, bn254Table.modulus i ≠ 256 →
    1 ≤ (fallbackRow 32 (bn254Table.modulus i)).width0 ∧
      1 ≤ (fallbackRow 32 (bn254Table.modulus i)).width1 ∧
      (fallbackRow 32 (bn254Table.modulus i)).width0 +
        (fallbackRow 32 (bn254Table.modulus i)).width1 + 1 = (fallbackRow 32 (bn254Table.modulus i)).ell ∧
      (fallbackRow 32 (bn254Table.modulus i)).width0 ≤ (fallbackRow 32 (bn254Table.modulus i)).keep ∧
      (fallbackRow 32 (bn254Table.modulus i)).keep ≤ (fallbackRow 32 (bn254Table.modulus i)).ell ∧
      (fallbackRow 32 (bn254Table.modulus i)).ell ≤ bn254Table.castWidth ∧
      bn254Table.chunkCount * (bn254Table.modulus i - 1) <
        2 ^ (fallbackRow 32 (bn254Table.modulus i)).ell := by
  decide +kernel

/-- The width-8 facts of every real odd modulus. Only small row data is evaluated here. -/
theorem bn254_width8Facts : ∀ i : Fin bn254Table.count, bn254Table.modulus i ≠ 256 →
    1 ≤ (width8Row 32 (bn254Table.modulus i)).width0 ∧
      1 ≤ (width8Row 32 (bn254Table.modulus i)).width1 ∧
      (width8Row 32 (bn254Table.modulus i)).width0 +
        (width8Row 32 (bn254Table.modulus i)).width1 + 1 = (width8Row 32 (bn254Table.modulus i)).ell ∧
      (width8Row 32 (bn254Table.modulus i)).width0 ≤ (width8Row 32 (bn254Table.modulus i)).keep ∧
      (width8Row 32 (bn254Table.modulus i)).keep ≤ (width8Row 32 (bn254Table.modulus i)).ell ∧
      (width8Row 32 (bn254Table.modulus i)).ell ≤ bn254Table.castWidth ∧
      bn254Table.chunkCount * (bn254Table.modulus i - 1) <
        2 ^ (width8Row 32 (bn254Table.modulus i)).ell := by
  decide +kernel

/-- The selected width-8/9 facts of every real odd modulus. Only small row data is evaluated here. -/
theorem bn254_selectiveFacts : ∀ i : Fin bn254Table.count, bn254Table.modulus i ≠ 256 →
    1 ≤ (selectiveRow 32 (bn254Table.modulus i)).width0 ∧
      1 ≤ (selectiveRow 32 (bn254Table.modulus i)).width1 ∧
      (selectiveRow 32 (bn254Table.modulus i)).width0 +
        (selectiveRow 32 (bn254Table.modulus i)).width1 + 1 = (selectiveRow 32 (bn254Table.modulus i)).ell ∧
      (selectiveRow 32 (bn254Table.modulus i)).width0 ≤ (selectiveRow 32 (bn254Table.modulus i)).keep ∧
      (selectiveRow 32 (bn254Table.modulus i)).keep ≤ (selectiveRow 32 (bn254Table.modulus i)).ell ∧
      (selectiveRow 32 (bn254Table.modulus i)).ell ≤ bn254Table.castWidth ∧
      bn254Table.chunkCount * (bn254Table.modulus i - 1) <
        2 ^ (selectiveRow 32 (bn254Table.modulus i)).ell := by
  decide +kernel

theorem bn254_odd : ∀ i row, bn254Table.kind i = .odd row →
    1 ≤ row.width0 ∧ 1 ≤ row.width1 ∧ row.width0 + row.width1 + 1 = row.ell ∧
      row.width0 ≤ row.keep ∧ row.keep ≤ row.ell ∧ row.ell ≤ bn254Table.castWidth ∧
      bn254Table.chunkCount * (bn254Table.modulus i - 1) < 2 ^ row.ell := by
  intro i row kind
  have facts := bn254_selectiveFacts i
  change selectiveKind (bn254Table.modulus i) = .odd row at kind
  unfold selectiveKind at kind
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
