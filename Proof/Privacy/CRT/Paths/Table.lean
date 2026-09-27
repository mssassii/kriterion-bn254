/-
**The real table's fields fit `tagCode`**: `TableRanges bn254Table S` for every `S ≤ 1000` (the
coordinates have `S = 367` and `275`). Big numbers are never evaluated: the pad counts are bounded symbolically
(`m < 2 ^ 9`, so `bitLength (m ^ S) ≤ 9 S`), the moduli and the rows by `decide +kernel` on the 85 small moduli
(`bn254_odd`).
-/

import Proof.Privacy.CRT.Paths.Garbler
import Proof.Correctness.CRT.RealTable

namespace Kriterion.CRT.Paths

open Kriterion.CRT

set_option maxRecDepth 100000

/-- A cast reads at most `64` answers, whatever its width. -/
theorem castAnswers_le (width : Nat) : castAnswers width ≤ 64 := by
  unfold castAnswers castBlocks
  generalize lanesPerBlock width = per
  rcases Nat.eq_zero_or_pos per with zero | positive
  · subst zero
    simp
  · have blocks : (128 + per - 1) / per ≤ 128 := Nat.div_le_of_le_mul (by omega)
    omega

theorem bn254_modulus_le : ∀ i, bn254Table.modulus i ≤ 439 := by decide +kernel

theorem bn254_count : bn254Table.count = 85 := by decide +kernel

theorem bn254_chunkCount : bn254Table.chunkCount = 32 := by decide +kernel

theorem bn254_chunkWidth (c : Nat) : bn254Table.chunkWidth c ≤ 8 := by
  unfold CrtTable.chunkWidth
  exact Nat.min_le_left _ _

theorem bitLength_pow_le (m S : Nat) (mPos : 0 < m) (mLt : m < 2 ^ 9) : bitLength (m ^ S) ≤ 9 * S + 1 := by
  unfold bitLength
  rcases Nat.eq_zero_or_pos S with zero | positive
  · subst zero
    simp only [pow_zero]
    decide
  · have power : m ^ S < 2 ^ (9 * S) := by
      rw [pow_mul]
      exact Nat.pow_lt_pow_left mLt (by omega)
    have logLt : (m ^ S).log2 < 9 * S :=
      (Nat.log2_lt (Nat.pos_iff_ne_zero.mp (Nat.pow_pos mPos))).mpr power
    omega

/-- **The real table fits `tagCode`** for up to `1000` encodings. -/
theorem bn254_ranges (S : Nat) (small : S ≤ 1000) : TableRanges bn254Table S where
  chunkCount := by rw [bn254_chunkCount]; norm_num
  chunkWidth c _ := le_trans (bn254_chunkWidth c) (by norm_num)
  castAnswers := castAnswers_le _
  count := by rw [bn254_count]; norm_num
  modulus i := le_trans (bn254_modulus_le i) (by norm_num)
  pads i := by
    unfold CrtTable.padAnswers
    split
    · unfold padAnswersPow2
      have width := bn254_chunkWidth 0
      have bound : S * bn254Table.chunkWidth 0 ≤ S * 8 := Nat.mul_le_mul_left _ width
      omega
    · unfold padAnswersOdd
      have lengthLe := bitLength_pow_le (bn254Table.modulus i) S (SliceC.bn254_modulus_pos i)
        (lt_of_le_of_lt (bn254_modulus_le i) (by norm_num))
      have slack : bn254Table.slack = 120 := rfl
      omega
  rows i row kind := by
    obtain ⟨w0, w1, sum, keepLow, keepHigh, ellHigh, _⟩ := SliceC.bn254_odd i row kind
    have cast : bn254Table.castWidth = 14 := rfl
    exact ⟨by omega, by omega, by omega, by omega, castAnswers_le _, castAnswers_le _⟩

end Kriterion.CRT.Paths
