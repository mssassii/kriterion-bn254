/-
**The real table's numeric facts the machine replay needs** (M5b): chunk shape, widths, moduli
bounds, pad answer counts, the size of the CRT integer, Garner's side conditions, the stage rows.
Every fact is proved from the table's closed form or from `bn254_correctTable`,
never by computing the product of the moduli.
-/

import Proof.Correctness.CRT.RealTable
import Proof.Simulator.CRT.ReplayCoord
import Construction.CRT.Entry

namespace Kriterion.CRT.SimMachine

open Kriterion.CRT Finset

namespace TableFacts

theorem inputBits : Entry.table.inputBits = 254 := rfl
theorem chunkBits : Entry.table.chunkBits = 8 := rfl
theorem castWidth : Entry.table.castWidth = 14 := rfl
theorem count : Entry.table.count = 84 := rfl
theorem chunkCount : Entry.table.chunkCount = 32 := rfl

theorem chunkOffset (c : Nat) : Entry.table.chunkOffset c = 8 * c := rfl

theorem chunkWidth (c : Nat) : Entry.table.chunkWidth c = min 8 (254 - 8 * c) := rfl

theorem shape : ChunkShape Entry.table.chunkOffset Entry.table.chunkWidth Entry.table.chunkCount
    Entry.table.inputBits where
  widthPos c cb := by rw [chunkWidth]; rw [chunkCount] at cb; omega
  widthSmall c cb := by rw [chunkWidth]; omega
  offsetFits c cb := by rw [chunkOffset, chunkWidth, inputBits]; rw [chunkCount] at cb; omega
  bitsLe := by rw [inputBits]; norm_num

theorem castAnswers_le : castAnswers Entry.table.castWidth ≤ 64 := by rw [castWidth]; decide

theorem moduli_le : ∀ i : Fin bn254Moduli.size, bn254Moduli[i] ≤ 439 := by decide

theorem modulus_le (i : Fin Entry.table.count) : Entry.table.modulus i ≤ 439 := moduli_le i

theorem modulus_pos (i : Fin Entry.table.count) : 0 < Entry.table.modulus i := SliceC.bn254_modulus_pos i

theorem sum_le : ∑ i : Fin Entry.table.count, Entry.table.modulus i ≤ garnerLift := by
  calc ∑ i : Fin Entry.table.count, Entry.table.modulus i ≤ ∑ _i : Fin Entry.table.count, 439 :=
        sum_le_sum fun i _ => modulus_le i
    _ ≤ garnerLift := by rw [sum_const, card_univ, Fintype.card_fin, count]; unfold garnerLift; norm_num

theorem product_le : Entry.table.product ≤ 2 ^ (128 * 6) := by
  unfold CrtTable.product
  calc ∏ i : Fin Entry.table.count, Entry.table.modulus i ≤ ∏ _i : Fin Entry.table.count, 2 ^ 9 :=
        prod_le_prod' fun i _ => (modulus_le i).trans (by norm_num)
    _ ≤ 2 ^ (128 * 6) := by
        rw [prod_const, card_univ, Fintype.card_fin, count, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem wrapBound_lt : Entry.table.wrapBound < 2 ^ (128 * 6) := by
  have wrap : 2 * Entry.table.wrapBound ≤ Entry.table.product + 1 := SliceC.bn254_wrap
  have pos : 0 < Entry.table.product := Finset.prod_pos fun i _ => modulus_pos i
  have le := product_le
  have one : 1 < (2 : Nat) ^ (128 * 6) := Nat.one_lt_two_pow (by norm_num)
  generalize (2 : Nat) ^ (128 * 6) = big at le one ⊢
  omega

theorem garnerTable : GarnerTable (modNat Entry.table) Entry.table.count :=
  garnerTable_of Entry.table modulus_pos SliceC.bn254_coprime
    (fun i => lt_of_le_of_lt (modulus_le i) (by norm_num)) sum_le

theorem bitLength_pow_le (m S : Nat) (mPos : 0 < m) (mLt : m < 2 ^ 9) : bitLength (m ^ S) ≤ 9 * S + 1 := by
  unfold bitLength
  rcases Nat.eq_zero_or_pos S with h | h
  · subst h
    have : Nat.log2 1 = 0 := by decide
    simp [this]
  · have pos : m ^ S ≠ 0 := (pow_pos mPos S).ne'
    have lt : m ^ S < 2 ^ (9 * S) := by
      rw [pow_mul]
      exact Nat.pow_lt_pow_left mLt (by omega)
    have := (Nat.log2_lt pos).mpr lt
    omega

theorem padAnswers_le (S : Nat) (sSmall : S ≤ 512) (i : Fin Entry.table.count) :
    2 * Entry.table.padAnswers S i ≤ 1024 := by
  unfold CrtTable.padAnswers
  split
  · unfold padAnswersPow2
    rw [chunkWidth]
    have : 2 * ((S * min 8 (254 - 8 * 0) + 255) / 256) ≤ 1024 := by
      have : min 8 (254 - 8 * 0) = 8 := rfl
      rw [this]; omega
    exact this
  · unfold padAnswersOdd
    have := bitLength_pow_le (Entry.table.modulus i) S (modulus_pos i)
      (lt_of_le_of_lt (modulus_le i) (by norm_num))
    have : Entry.table.slack = 120 := rfl
    omega

theorem chunkZero_facts (i : Fin Entry.table.count) (kind : Entry.table.kind i = .chunkZero) :
    Entry.table.modulus i = 2 ^ Entry.table.chunkWidth 0 ∧ 0 < Entry.table.chunkCount :=
  ⟨SliceC.bn254_chunkZero i kind, by rw [chunkCount]; norm_num⟩

theorem odd_facts (i : Fin Entry.table.count) (row : OddRow) (kind : Entry.table.kind i = .odd row) :
    1 ≤ row.width0 ∧ 1 ≤ row.width1 ∧ row.width0 + row.width1 + 1 = row.ell ∧
      row.width0 ≤ row.keep ∧ row.keep ≤ row.ell ∧ row.ell ≤ 14 ∧
      Entry.table.chunkCount * (Entry.table.modulus i - 1) < 2 ^ row.ell := by
  have := SliceC.bn254_odd i row kind
  rw [castWidth] at this
  exact this

theorem bodyTag_small (coord i ρ j : Nat) (coordLt : coord < 2) (iLt : i < 128) (ρLt : ρ < 65536)
    (jLt : j < 64) : bodyTag coord i ρ j < 2 ^ 127 := by
  unfold bodyTag tagCode Family.body
  have : (2 : Nat) ^ 60 < 2 ^ 127 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have : (2 : Nat) ^ 60 = 1152921504606846976 := by norm_num
  omega

theorem padAnswers_lt (S : Nat) (sSmall : S ≤ 512) (i : Fin Entry.table.count) :
    Entry.table.padAnswers S i < 64 := by
  unfold CrtTable.padAnswers
  split
  · unfold padAnswersPow2
    rw [chunkWidth]
    have : min 8 (254 - 8 * 0) = 8 := rfl
    rw [this]; omega
  · unfold padAnswersOdd
    have := bitLength_pow_le (Entry.table.modulus i) S (modulus_pos i)
      (lt_of_le_of_lt (modulus_le i) (by norm_num))
    have : Entry.table.slack = 120 := rfl
    omega

end TableFacts

end Kriterion.CRT.SimMachine
