/-
CRT slice, delivery part 1: the truth-table word (L4 and L5) on
the definitions (`Construction/CRT/Params.lean`: `chunkValue`, `truth`, `wordValue`;
`Construction/CRT/Chunk.lean`: `truthWord`).

* `chunk_recompose`: the chunk values recompose `v mod 2^inputBits`.
* **L5** `wordValue_modEq`, `wordValue_lt`: the word value of modulus `m` is congruent to `v`
  modulo `m` and at most `chunkCount·(m - 1)`.
* **L4** `truthWord_label`: the word of the evaluator's chunk casts (each the garbler's plus
  `[α = α_c]•Δ⃗`) is the garbler's word plus `wordValue m v • Δ⃗`.
-/

import Proof.Correctness.CRT.Conversion

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

/-! ### L5: chunk recomposition and the word value -/

theorem chunk_lt_count (T : CrtTable) (hk : 0 < T.chunkBits) {n : Nat} (hn : n < T.chunkCount) :
    T.chunkBits * n < T.inputBits := by
  unfold CrtTable.chunkCount at hn
  have h := (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt hn)
  rw [Nat.succ_mul] at h
  have := Nat.mul_comm n T.chunkBits
  omega

theorem chunk_count_cover (T : CrtTable) (hk : 0 < T.chunkBits) :
    T.inputBits ≤ T.chunkBits * T.chunkCount := by
  unfold CrtTable.chunkCount
  have h := Nat.div_add_mod (T.inputBits + T.chunkBits - 1) T.chunkBits
  have h2 := Nat.mod_lt (T.inputBits + T.chunkBits - 1) hk
  omega

/-- The partial recomposition of the chunks below `n`. -/
theorem chunk_recompose_partial (T : CrtTable) (hk : 0 < T.chunkBits) (v : Nat) :
    ∀ n ≤ T.chunkCount, ∑ c ∈ Finset.range n, T.chunkValue v c * 2 ^ T.chunkOffset c =
      v % 2 ^ (min (T.chunkBits * n) T.inputBits) := by
  intro n
  induction n with
  | zero => intro _; simp [Nat.mod_one]
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ, ih (by omega)]
    have hlt := chunk_lt_count T hk (n := n) (by omega)
    rw [Nat.min_eq_left (by omega : T.chunkBits * n ≤ T.inputBits)]
    unfold CrtTable.chunkValue CrtTable.chunkOffset CrtTable.chunkWidth
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm (v / 2 ^ (T.chunkBits * n) % _) _, ← Nat.mod_mul,
      ← pow_add]
    congr 2
    rw [Nat.mul_succ]
    omega

/-- The chunk values recompose `v mod 2^inputBits`. -/
theorem chunk_recompose (T : CrtTable) (hk : 0 < T.chunkBits) (v : Nat) :
    ∑ c : Fin T.chunkCount, T.chunkValue v c.val * 2 ^ T.chunkOffset c.val = v % 2 ^ T.inputBits := by
  rw [Fin.sum_univ_eq_sum_range (fun c => T.chunkValue v c * 2 ^ T.chunkOffset c),
    chunk_recompose_partial T hk v _ le_rfl, Nat.min_eq_right (chunk_count_cover T hk)]

/-- **L5**, congruence: the word value of modulus `m` is congruent to `v` modulo `m`. -/
theorem wordValue_modEq (T : CrtTable) (hk : 0 < T.chunkBits) (m v : Nat)
    (hv : v < 2 ^ T.inputBits) : T.wordValue m v ≡ v [MOD m] := by
  unfold CrtTable.wordValue CrtTable.truth
  unfold Nat.ModEq
  rw [← Finset.sum_nat_mod, chunk_recompose T hk v, Nat.mod_eq_of_lt hv]

/-- **L5**, range: the word value is at most `chunkCount·(m - 1)`. -/
theorem wordValue_le (T : CrtTable) (m v : Nat) (hm : 0 < m) :
    T.wordValue m v ≤ T.chunkCount * (m - 1) := by
  unfold CrtTable.wordValue CrtTable.truth
  calc ∑ c : Fin T.chunkCount, T.chunkValue v c.val * 2 ^ T.chunkOffset c.val % m
      ≤ ∑ _c : Fin T.chunkCount, (m - 1) :=
        Finset.sum_le_sum fun c _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ hm)
    _ = T.chunkCount * (m - 1) := by simp

/-- **L5**, the bound used by the conversion: `σ_m < 2^ell` when `chunkCount·(m - 1) < 2^ell`. -/
theorem wordValue_lt (T : CrtTable) (m v ell : Nat) (hm : 0 < m)
    (hell : T.chunkCount * (m - 1) < 2 ^ ell) : T.wordValue m v < 2 ^ ell :=
  Nat.lt_of_le_of_lt (wordValue_le T m v hm) hell

/-- The chunk value is below its width. -/
theorem chunkValue_lt (T : CrtTable) (v c : Nat) : T.chunkValue v c < 2 ^ T.chunkWidth c :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Bit `n` of chunk `c`'s value is bit `chunkOffset c + n` of `v` (below the chunk width). -/
theorem chunkValue_testBit (T : CrtTable) (v c n : Nat) (hn : n < T.chunkWidth c) :
    (T.chunkValue v c).testBit n = v.testBit (T.chunkOffset c + n) := by
  unfold CrtTable.chunkValue
  rw [Nat.testBit_mod_two_pow, Nat.shiftRight_eq_div_pow, Nat.testBit_div_two_pow]
  simp [hn, Nat.add_comm]

/-! ### L4: the word label -/

theorem reduceTo_add_smul {L ell : Nat} (hell : ell ≤ L) (X : Lanes L) (k : Nat) (Δ : Label) :
    reduceTo ell (X + (k : ZMod (2 ^ L)) • deltaLanes L Δ) =
      reduceTo ell X + (k : ZMod (2 ^ ell)) • deltaLanes ell Δ := by
  funext lane
  simp only [reduceTo, Pi.add_apply, Pi.smul_apply, smul_eq_mul, reduceTo_lane_eq_castHom hell,
    map_add, map_mul, map_natCast, deltaLanes]
  split_ifs <;> simp only [map_one, map_zero, mul_one, mul_zero]

/-- **L4** `truthWord_label`: if every evaluator chunk cast is the garbler's plus `Δ⃗` exactly at
the chunk value, the evaluator's word of modulus `m` is the garbler's plus `wordValue m v • Δ⃗`. -/
theorem truthWord_label (T : CrtTable) (m ell : Nat) (hell : ell ≤ T.castWidth)
    (casts castsE : Nat → Nat → Lanes T.castWidth) (Δ : Label) (v : Nat)
    (hE : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      castsE c α = casts c α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ else 0)) :
    truthWord T m ell castsE =
      truthWord T m ell casts + ((T.wordValue m v : Nat) : ZMod (2 ^ ell)) • deltaLanes ell Δ := by
  unfold truthWord
  rw [materialize_eq, materialize_eq, ← reduceTo_add_smul hell]
  congr 1
  funext lane
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : ∀ c : Fin T.chunkCount,
      ∑ leaf : Fin (2 ^ T.chunkWidth c.val),
          ((T.truth m c.val leaf.val : Nat) : ZMod (2 ^ T.castWidth)) * castsE c.val leaf.val lane =
        ∑ leaf : Fin (2 ^ T.chunkWidth c.val),
          ((T.truth m c.val leaf.val : Nat) : ZMod (2 ^ T.castWidth)) * casts c.val leaf.val lane +
          ((T.truth m c.val (T.chunkValue v c.val) : Nat) : ZMod (2 ^ T.castWidth)) *
            deltaLanes T.castWidth Δ lane := by
    intro c
    have hterm : ∀ leaf : Fin (2 ^ T.chunkWidth c.val),
        ((T.truth m c.val leaf.val : Nat) : ZMod (2 ^ T.castWidth)) * castsE c.val leaf.val lane =
          ((T.truth m c.val leaf.val : Nat) : ZMod (2 ^ T.castWidth)) * casts c.val leaf.val lane +
          (if leaf = ⟨T.chunkValue v c.val, chunkValue_lt T v c.val⟩ then
            ((T.truth m c.val (T.chunkValue v c.val) : Nat) : ZMod (2 ^ T.castWidth)) *
              deltaLanes T.castWidth Δ lane else 0) := by
      intro leaf
      rw [hE c.val c.isLt leaf.val leaf.isLt, Pi.add_apply]
      by_cases hl : leaf = ⟨T.chunkValue v c.val, chunkValue_lt T v c.val⟩
      · have hv : leaf.val = T.chunkValue v c.val := by rw [hl]
        rw [if_pos hv, if_pos hl, hv]; ring
      · have hv : leaf.val ≠ T.chunkValue v c.val := fun h => hl (Fin.ext h)
        rw [if_neg hv, if_neg hl]; simp
    rw [Finset.sum_congr rfl (fun leaf _ => hterm leaf), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl (fun c _ => hsum c), Finset.sum_add_distrib, ← Finset.sum_mul]
  unfold CrtTable.wordValue
  push_cast
  ring

end Kriterion.CRT.SliceC
