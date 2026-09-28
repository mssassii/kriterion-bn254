/-
CRT slice, conversion chain part D: L14 `conversion_final` for one odd modulus, on the
programs `conversionGarbleM` / `conversionEvalM` (`Construction/CRT/Coord.lean`) at `.eval H`, for
every `H : HashN`: stage 0 (L10), peel (L11), stage 1 (L10), the free stage-2 bit (L7 at 0), growth
(L1, L2), reindex (L12) and folds (L13) end with the evaluator's one-hot over `Z_m` equal to the
garbler's XOR `Δ` exactly at `σ mod m`, where `σ < 2^ell` is the word value.
-/

import Proof.Correctness.CRT.FoldChain

namespace Kriterion.CRT.SliceC

open scoped BigOperators
open Cryptography Kriterion.CRT Kriterion.CRT.ExtractSpec Kriterion.ArgoMAC

theorem pinOfBlocks_atNat {width : Nat} (hw : 0 < width) (P : Lanes width) :
    (pinOfBlocks width fun k => atNat (stored (pinBlocks P)) 0 k.val) = P := by
  have : (fun k : Fin width => atNat (stored (pinBlocks P)) 0 k.val) = pinBlocks P := by
    funext k
    rw [atNat_of_lt _ _ k.isLt, stored_eq]
  rw [this, pinOfBlocks_pinBlocks hw]

/-- The dense pin codec also round-trips the zero-width singleton. -/
theorem pinOfBlocks_pinBlocks_all {width : Nat} (P : Lanes width) :
    pinOfBlocks width (pinBlocks P) = P := Narrow.pinOfBlocks_pinBlocks P

/-- The total-indexed public wire round-trips at every stored width. -/
theorem pinOfBlocks_atNat_all {width : Nat} (P : Lanes width) :
    (pinOfBlocks width fun k => atNat (stored (pinBlocks P)) 0 k.val) = P := by
  have same : (fun k : Fin width => atNat (stored (pinBlocks P)) 0 k.val) = pinBlocks P := by
    funext k
    rw [atNat_of_lt _ _ k.isLt, stored_eq]
  rw [same, pinOfBlocks_pinBlocks_all]

/-- The compressed public wire restores every even internal pin. -/
theorem expand_pinOfBlocks_atNat (width : Nat) (P : Lanes width) (even : Parity.EvenLanes P) :
    Parity.pinExpand width (pinOfBlocks (width - 1) fun k =>
      atNat (stored (pinBlocks (Parity.pinHalf width P))) 0 k.val) = P := by
  rw [pinOfBlocks_atNat_all, Parity.pinExpand_pinHalf width P even]

/-- The conversion after the two fused stages: the free stage-2 bit, growth, reindex and folds,
from any stage results that satisfy the stage invariant (L10) against the garbler's. -/
theorem after_stages_correct (H : HashN) (coord i : Nat) (row : OddRow) (m : Nat) (Δ : Label)
    (σ : Nat) (h0 : 1 ≤ row.width0) (h1 : 1 ≤ row.width1)
    (hell : row.width0 + row.width1 + 1 = row.ell) (hk0 : row.width0 ≤ row.keep)
    (hk1 : row.keep ≤ row.ell) (hm : 0 < m) (hσ : σ < 2 ^ row.ell)
    {g0 : StageGarbled row.ell row.width0} {g1 : StageGarbled (row.ell - row.width0) row.width1}
    {e0 : StageEval row.ell row.width0} {e1 : StageEval (row.ell - row.width0) row.width1}
    (hl0 : ∀ α < 2 ^ row.width0,
      e0.leaves α = g0.leaves α ^^^ (if α = σ % 2 ^ row.width0 then Δ else 0))
    (hb0 : ∀ n < row.width0, e0.bits n = g0.bits n ^^^ (if σ.testBit n then Δ else 0))
    (hb1 : ∀ n < row.width1,
      e1.bits n = g1.bits n ^^^ (if (σ / 2 ^ row.width0).testBit n then Δ else 0))
    (hn1 : e1.next = g1.next + ((σ / 2 ^ row.width0 / 2 ^ row.width1 : Nat) :
      ZMod (2 ^ (row.ell - row.width0 - row.width1))) • deltaLanes (row.ell - row.width0 - row.width1) Δ) :
    let bitMask := wordBit row g0.bits g1.bits (laneBit g1.next 0)
    let grown := (growGarbleM (growTag coord i) row.width0 (stored fun leaf => g0.leaves leaf.val)
      (row.keep - row.width0)).eval H
    let folded := (foldsGarbleM m (foldTag coord i) bitMask (row.ell - row.keep) row.keep
      (reindex _ grown.1 m)).eval H
    let bitLabel := wordBit row e0.bits e1.bits (laneBit e1.next 0)
    let res := (foldsEvalM m (foldTag coord i) σ bitLabel folded.2 (row.ell - row.keep) row.keep
      (σ % 2 ^ row.keep % m)
      (reindex _ ((growEvalM (growTag coord i) σ bitLabel (fun p => grown.2 p ^^^ bitMask p)
        row.width0 (stored fun leaf => e0.leaves leaf.val) (row.keep - row.width0)).eval H) m)).eval H
    res.2 = σ % m ∧ ∀ ρ : Fin m, res.1 ρ = folded.1 ρ ^^^ (if ρ.val = σ % m then Δ else 0) := by
  intro bitMask grown folded bitLabel res
  -- the bit labels of the word, every position below `ell` (stage 0, stage 1, the free stage 2)
  have hbit : ∀ p < row.ell, bitLabel p = bitMask p ^^^ (if σ.testBit p then Δ else 0) := by
    intro p hp
    simp only [bitLabel, bitMask, wordBit]
    by_cases hp0 : p < row.width0
    · rw [if_pos hp0, if_pos hp0, hb0 p hp0]
    · rw [if_neg hp0, if_neg hp0]
      by_cases hp1 : p < row.width0 + row.width1
      · rw [if_pos hp1, if_pos hp1, hb1 (p - row.width0) (by omega), Nat.testBit_div_two_pow,
          Nat.sub_add_cancel (by omega)]
      · rw [if_neg hp1, if_neg hp1, hn1,
          laneBit_add_smul_delta_zero (by omega : 0 < row.ell - row.width0 - row.width1)]
        have hpe : p = row.width0 + row.width1 := by omega
        rw [hpe, Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul, ← pow_add]
        simp only [decide_eq_true_eq]
  -- growth (L2) from the kept leaves of stage 0
  have hgrow := growEvalM_correct H (growTag coord i) row.width0
    (stored fun leaf => g0.leaves leaf.val) (stored fun leaf => e0.leaves leaf.val) Δ σ bitMask
    bitLabel (fun p => grown.2 p ^^^ bitMask p) (row.keep - row.width0)
    (by intro x; simp only [stored_eq]; exact hl0 x.val x.isLt)
    (fun j hj => hbit j (by omega)) (fun j => rfl) (row.keep - row.width0) le_rfl
  -- reindex (L12)
  have hkeep : row.width0 + (row.keep - row.width0) = row.keep := by omega
  have hhot : σ % 2 ^ (row.width0 + (row.keep - row.width0)) % m = σ % 2 ^ row.keep % m := by
    rw [hkeep]
  have hre := fun ρ => reindex_invariant (row.width0 + (row.keep - row.width0)) m grown.1
    ((growEvalM (growTag coord i) σ bitLabel (fun p => grown.2 p ^^^ bitMask p) row.width0
      (stored fun leaf => e0.leaves leaf.val) (row.keep - row.width0)).eval H) Δ
    (σ % 2 ^ (row.width0 + (row.keep - row.width0))) (Nat.mod_lt _ (Nat.two_pow_pos _)) hgrow ρ
  -- folds (L13)
  have hfold := foldsEvalM_correct H m (foldTag coord i) σ Δ bitMask bitLabel folded.2
    (row.ell - row.keep) row.keep (σ % 2 ^ row.keep % m) (reindex _ grown.1 m)
    (reindex _ ((growEvalM (growTag coord i) σ bitLabel (fun p => grown.2 p ^^^ bitMask p) row.width0
      (stored fun leaf => e0.leaves leaf.val) (row.keep - row.width0)).eval H) m) (Nat.mod_lt _ hm)
    (by intro ρ; rw [hre ρ, hhot])
    (fun j _ h2 => hbit j (by omega)) (fun j _ _ => rfl)
  have hfh : foldHot m σ (row.ell - row.keep) row.keep (σ % 2 ^ row.keep % m) = σ % m := by
    rw [foldHot_eq m σ hm _ _ _ rfl, show row.keep + (row.ell - row.keep) = row.ell by omega,
      Nat.mod_eq_of_lt hσ]
  refine ⟨hfold.1.trans hfh, fun ρ => ?_⟩
  rw [hfold.2 ρ, hfh]

/-- **L14 `conversion_final` for one odd modulus**, on the programs, for every hash `H`:
with the published material of modulus `i` taken from the garbler's conversion, the evaluator's
conversion of the word label `W + σ•Δ⃗` (`σ < 2^ell` the word value) returns the hot index
`σ mod m` and the garbler's final one-hot XOR `Δ` exactly there. With `σ ≡ v (mod m)` (L5) that is
`v mod m`. The side conditions are those of every row of T9: `1 ≤ width0`, `1 ≤ width1`,
`width0 + width1 + 1 = ell`, `width0 ≤ keep ≤ ell`, and `0 < m`. -/
theorem conversion_final (H : HashN) (coord i : Nat) (row : OddRow) (m : Nat) (Δ : Label)
    (W : Lanes row.ell) (σ : Nat) (pub : ConvPublic)
    (h0 : 1 ≤ row.width0) (h1 : 1 ≤ row.width1) (hell : row.width0 + row.width1 + 1 = row.ell)
    (hk0 : row.width0 ≤ row.keep) (hk1 : row.keep ≤ row.ell) (hm : 0 < m) (hσ : σ < 2 ^ row.ell)
    (hpJ : pub.stageJoin i = ((conversionGarbleM coord i row m Δ W).eval H).stageJoins)
    (hpP : pub.stagePin i = ((conversionGarbleM coord i row m Δ W).eval H).stagePins)
    (hpG : pub.growJoin i = ((conversionGarbleM coord i row m Δ W).eval H).growJoins)
    (hpF : pub.foldJoin i = ((conversionGarbleM coord i row m Δ W).eval H).foldJoins) :
    ((conversionEvalM coord i row m σ (W + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ)
        pub).eval H).2 = σ % m ∧
      ∀ ρ : Fin m, ((conversionEvalM coord i row m σ (W + (σ : ZMod (2 ^ row.ell)) •
          deltaLanes row.ell Δ) pub).eval H).1 ρ =
        ((conversionGarbleM coord i row m Δ W).eval H).final ρ ^^^
          (if ρ.val = σ % m then Δ else 0) := by
  have hw0 : row.width0 ≤ row.ell := by omega
  have hw1' : row.width1 ≤ row.ell - row.width0 := by omega
  have hs0 := extStage_correct H row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0) h0 Δ W σ
  have hs1 := extStage_correct H row.width1 hw1' (extTreeTag coord i 1) (extCastTag coord i 1) h1 Δ
    ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).next
    (σ / 2 ^ row.width0)
  simp only at hs0 hs1
  obtain ⟨hl0, hb0, hn0⟩ := hs0
  obtain ⟨_, hb1, hn1⟩ := hs1
  simp only [conversionGarbleM, FreeQuery.eval_bind, FreeQuery.eval_pure] at hpJ hpP hpG hpF ⊢
  have hJ0 : pub.stageJoin i 0 =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).joins := by
    rw [hpJ]
    rfl
  have hJ1 : pub.stageJoin i 1 = ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).next).eval H).joins := by
    rw [hpJ]
    rfl
  have hP0 : Parity.pinExpand row.ell (pinOfBlocks (row.ell - 1) fun k => pub.stagePin i 0 k.val) =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).pin := by
    rw [hpP]
    exact expand_pinOfBlocks_atNat _ _
      (extStageGarbleM_pin_even H row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W)
  have hP1 : Parity.pinExpand (row.ell - row.width0)
      (pinOfBlocks (row.ell - row.width0 - 1) fun k => pub.stagePin i 1 k.val) =
      ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ
        ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).next).eval H).pin := by
    rw [hpP]
    exact expand_pinOfBlocks_atNat _ _
      (extStageGarbleM_pin_even H row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ _)
  simp only [conversionEvalM, FreeQuery.eval_bind]
  rw [hJ0, hP0, hn0, hJ1, hP1, hpG, hpF]
  exact after_stages_correct H coord i row m Δ σ h0 h1 hell hk0 hk1 hm hσ hl0 hb0 hb1 hn1

/-- Every row of schedule T9 for a modulus `m ≥ 17` (every odd modulus of the table) meets the side
conditions of `conversion_final`. -/
theorem t9Row_conditions (m : Nat) (hm : 17 ≤ m) :
    1 ≤ (t9Row 32 m).width0 ∧ 1 ≤ (t9Row 32 m).width1 ∧
      (t9Row 32 m).width0 + (t9Row 32 m).width1 + 1 = (t9Row 32 m).ell ∧
      (t9Row 32 m).width0 ≤ (t9Row 32 m).keep ∧ (t9Row 32 m).keep ≤ (t9Row 32 m).ell := by
  have hne : 32 * (m - 1) ≠ 0 := by omega
  have hlog : 9 ≤ (32 * (m - 1)).log2 := (Nat.le_log2 hne).mpr (by omega)
  simp only [t9Row, bitLength]
  omega

/-- The fallback's width-7/8 rows preserve the side conditions of `conversion_final`.
This proof uses only the selector bounds; it also applies after switching all rows to width 8. -/
theorem fallbackRow_conditions (m : Nat) (hm : 17 ≤ m) :
    1 ≤ (fallbackRow 32 m).width0 ∧ 1 ≤ (fallbackRow 32 m).width1 ∧
      (fallbackRow 32 m).width0 + (fallbackRow 32 m).width1 + 1 = (fallbackRow 32 m).ell ∧
      (fallbackRow 32 m).width0 ≤ (fallbackRow 32 m).keep ∧
      (fallbackRow 32 m).keep ≤ (fallbackRow 32 m).ell := by
  have hne : 32 * (m - 1) ≠ 0 := by omega
  have hlog : 9 ≤ (32 * (m - 1)).log2 := (Nat.le_log2 hne).mpr (by omega)
  have lower := fallbackWidth0_lower m
  have upper := fallbackWidth0_upper m
  -- CHECK: confirm omega closes max and truncated subtraction after these explicit unfoldings.
  simp only [fallbackRow, bitLength]
  omega

/-- Width-8 rows meet the side conditions of `conversion_final` for every modulus at least 17. -/
theorem width8Row_conditions (m : Nat) (hm : 17 ≤ m) :
    1 ≤ (width8Row 32 m).width0 ∧ 1 ≤ (width8Row 32 m).width1 ∧
      (width8Row 32 m).width0 + (width8Row 32 m).width1 + 1 = (width8Row 32 m).ell ∧
      (width8Row 32 m).width0 ≤ (width8Row 32 m).keep ∧
      (width8Row 32 m).keep ≤ (width8Row 32 m).ell := by
  have hne : 32 * (m - 1) ≠ 0 := by omega
  have hlog : 9 ≤ (32 * (m - 1)).log2 := (Nat.le_log2 hne).mpr (by omega)
  simp only [width8Row, bitLength]
  omega

/-- **L14 with L5**: when the word value is congruent to the coordinate value `v` modulo `m` (L5),
the evaluator's final one-hot is the garbler's XOR `Δ` exactly at `v mod m`. -/
theorem conversion_final_value (H : HashN) (coord i : Nat) (row : OddRow) (m : Nat) (Δ : Label)
    (W : Lanes row.ell) (σ v : Nat) (pub : ConvPublic)
    (h0 : 1 ≤ row.width0) (h1 : 1 ≤ row.width1) (hell : row.width0 + row.width1 + 1 = row.ell)
    (hk0 : row.width0 ≤ row.keep) (hk1 : row.keep ≤ row.ell) (hm : 0 < m) (hσ : σ < 2 ^ row.ell)
    (hv : σ % m = v % m)
    (hpJ : pub.stageJoin i = ((conversionGarbleM coord i row m Δ W).eval H).stageJoins)
    (hpP : pub.stagePin i = ((conversionGarbleM coord i row m Δ W).eval H).stagePins)
    (hpG : pub.growJoin i = ((conversionGarbleM coord i row m Δ W).eval H).growJoins)
    (hpF : pub.foldJoin i = ((conversionGarbleM coord i row m Δ W).eval H).foldJoins) :
    ((conversionEvalM coord i row m σ (W + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ)
        pub).eval H).2 = v % m ∧
      ∀ ρ : Fin m, ((conversionEvalM coord i row m σ (W + (σ : ZMod (2 ^ row.ell)) •
          deltaLanes row.ell Δ) pub).eval H).1 ρ =
        ((conversionGarbleM coord i row m Δ W).eval H).final ρ ^^^
          (if ρ.val = v % m then Δ else 0) := by
  rw [← hv]
  exact conversion_final H coord i row m Δ W σ pub h0 h1 hell hk0 hk1 hm hσ hpJ hpP hpG hpF

end Kriterion.CRT.SliceC
