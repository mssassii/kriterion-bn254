/-
**The size of the conversion replay**: `conversionReplay` has at most `2 ^ 36` code slots when the stage widths are at most 12, `keep` and
`ell` at most 16 and `m ≤ 2 ^ 11` (the rows of the real table are far inside: widths 7 and 2 to 6, `keep ≤ 9`,
`ell ≤ 14`, `m ≤ 439`). The cost is at most the size, so this bounds both.

Block by block: every straight-line block has a constant size (`rfl`), a loop of `count` bodies of size at most `c`
has size at most `count · c` (`size_rep_le`), and the powers of two are bounded by the widths.
-/

import Construction.Simulator.CRT.ReplayConversion

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! The helpers live in the file-specific namespace `ConvSize` (`ReplayCost.lean` has its own
`size_rep_le` and `size_treeStep`). -/

namespace ConvSize

/-! ### Loops -/

theorem size_rep_le (count : Nat) (body : Nat → Prog) (width : Nat)
    (each : ∀ index, index < count → (body index).size ≤ width) :
    (Prog.rep count body).size ≤ count * width := by
  induction count with
  | zero => rw [Prog.rep]; simp [Prog.size]
  | succ count ih =>
      rw [Prog.rep, Prog.size_seq, Nat.succ_mul]
      have h1 := ih fun index bound => each index (by omega)
      have h2 := each count (by omega)
      omega

theorem pow_le_4096 {n : Nat} (h : n ≤ 12) : 2 ^ n ≤ 4096 :=
  le_trans (Nat.pow_le_pow_right (by norm_num) h) (by norm_num)

theorem pow_le_65536 {n : Nat} (h : n ≤ 16) : 2 ^ n ≤ 65536 :=
  le_trans (Nat.pow_le_pow_right (by norm_num) h) (by norm_num)

theorem castAnswers_le_128' (l : Nat) (h1 : 1 ≤ l) (h2 : l ≤ 128) : Kriterion.CRT.castAnswers l ≤ 128 := by
  unfold Kriterion.CRT.castAnswers Kriterion.CRT.castBlocks Kriterion.CRT.lanesPerBlock
  have p1 : 1 ≤ 128 / l := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have : (128 + 128 / l - 1) / (128 / l) ≤ 128 := Nat.div_le_of_le_mul (by omega)
  omega

/-! ### One stage -/

section Stage

variable (cells : StageCells)

theorem size_subtreeLevel (start d base stride : Nat) :
    (subtreeLevel cells start d base stride).size = 2 ^ d * 20 + 2 ^ d * 14 := by
  unfold subtreeLevel
  rw [Prog.size_seq, Prog.size_rep _ _ 20 fun _ _ => rfl, Prog.size_rep _ _ 14 fun _ _ => rfl]

theorem size_subtreeReplay_le (start depth : Nat) (treeBase : Nat → Nat) (stride : Nat) (small : depth ≤ 12) :
    (subtreeReplay cells start depth treeBase stride).size ≤ 12 * (4096 * 34) := by
  unfold subtreeReplay
  refine le_trans (size_rep_le _ _ (4096 * 34) fun d bound => ?_) (Nat.mul_le_mul_right _ small)
  rw [size_subtreeLevel]
  have := pow_le_4096 (n := d) (by omega)
  omega

theorem size_castDyn_le (rb start t base stride : Nat) (rbPos : 1 ≤ rb) (rbLe : rb ≤ 128) :
    (castDyn cells rb start t base stride).size ≤ 12 + 128 * 7 + 128 * 8 := by
  unfold castDyn castLanesProg
  rw [Prog.size_seq, Prog.size_seq, Prog.size_rep _ _ 7 fun _ _ => rfl,
    Prog.size_rep _ _ 8 fun _ _ => rfl]
  have := castAnswers_le_128' rb rbPos rbLe
  have e : (castInputBase cells start t base stride).size = 12 := rfl
  have lc : Kriterion.CRT.laneCount = 128 := rfl
  omega

theorem size_accLevel (rb start t j : Nat) : (accLevel cells rb start t j).size = 6 + 128 * 19 := by
  unfold accLevel
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_rep _ _ 19 fun _ _ => rfl]
  have e1 : (absSlot cells start t).size = 4 := rfl
  have e2 : (cst rB (2 ^ j - 1)).size = 1 := rfl
  have e3 : (ar .and rF rF rB).size = 1 := rfl
  rw [e1, e2, e3]
  decide

theorem size_leafEntry_le (w rb start base stride t : Nat) (rbPos : 1 ≤ rb) (rbLe : rb ≤ 128)
    (small : w - start ≤ 12) :
    (leafEntry cells w rb start base stride t).size ≤ (12 + 128 * 7 + 128 * 8) + 13 * (6 + 128 * 19) := by
  unfold leafEntry
  rw [Prog.size_seq, Prog.size_rep _ _ (6 + 128 * 19) fun k _ => size_accLevel cells rb start t (start + k)]
  have := size_castDyn_le cells rb start t base stride rbPos rbLe
  have : (w - start + 1) * (6 + 128 * 19) ≤ 13 * (6 + 128 * 19) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The bound of one expansion. -/
abbrev expandBound : Nat := 12 * (4096 * 34) + 4096 * ((12 + 128 * 7 + 128 * 8) + 13 * (6 + 128 * 19))

theorem size_expandReplay_le (w rb start : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) (rbPos : 1 ≤ rb)
    (rbLe : rb ≤ 128) (wLe : w ≤ 12) :
    (expandReplay cells w rb start treeBase castBase stride).size ≤ expandBound := by
  unfold expandReplay
  rw [Prog.size_seq]
  have h1 := size_subtreeReplay_le cells start (w - start) treeBase stride (by omega)
  have h2 := size_rep_le (2 ^ (w - start)) (leafEntry cells w rb start castBase stride)
    ((12 + 128 * 7 + 128 * 8) + 13 * (6 + 128 * 19))
    fun t _ => size_leafEntry_le cells w rb start castBase stride t rbPos rbLe (by omega)
  have h3 : 2 ^ (w - start) * ((12 + 128 * 7 + 128 * 8) + 13 * (6 + 128 * 19)) ≤
      4096 * ((12 + 128 * 7 + 128 * 8) + 13 * (6 + 128 * 19)) :=
    Nat.mul_le_mul_right _ (pow_le_4096 (by omega))
  unfold expandBound
  omega

theorem size_roundPrefix (w rb n : Nat) : (roundPrefix cells w rb n).size = 7 + 128 * 29 + 9 + 6 + 19 := by
  unfold roundPrefix roundBit
  simp only [Prog.size_seq]
  rw [Prog.size_rep _ _ 29 fun _ _ => rfl]
  have e1 : (loadAt rF cells.value).size = 2 := rfl
  have e2 : (cst rB (2 ^ n - 1)).size = 1 := rfl
  have e3 : (ar .and rF rF rB).size = 1 := rfl
  have e4 : (cst rD 0).size = 1 := rfl
  have e5 : (storeAt (cells.bitBase + n) rD).size = 2 := rfl
  have e6 : (roundHot cells n).size = 9 := rfl
  have e7 : (roundTest cells n).size = 6 := rfl
  have e8 : (Prog.ite rA (roundSet cells) (roundClear cells n)).size = 19 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  decide

theorem size_roundReplay_le (w rb n : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) (rbPos : 1 ≤ rb)
    (rbLe : rb ≤ 128) (wLe : w ≤ 12) :
    (roundReplay cells w rb n treeBase castBase stride).size ≤ (7 + 128 * 29 + 9 + 6 + 19) + expandBound := by
  unfold roundReplay
  rw [Prog.size_seq, size_roundPrefix]
  have := size_expandReplay_le cells w rb (n + 1) treeBase castBase stride rbPos rbLe wLe
  omega

theorem size_zeroCells (base count : Nat) : (zeroCells base count).size = 1 + count * 2 := by
  unfold zeroCells
  rw [Prog.size_seq, Prog.size_rep _ _ 2 fun _ _ => rfl]
  have e : (cst rB 0).size = 1 := rfl
  omega

theorem size_stagePrefix_le (w : Nat) (wLe : w ≤ 12) :
    (stagePrefix cells w).size ≤ 128 * 6 + (1 + 128 * 9) + 4 + 3 * (1 + 128 * 13 * 2) + 10 := by
  unfold stagePrefix lanePack
  simp only [Prog.size_seq]
  rw [Prog.size_rep _ _ 6 fun _ _ => rfl, Prog.size_rep _ _ 9 fun _ _ => rfl, size_zeroCells,
    size_zeroCells, size_zeroCells]
  have e1 : (prefixSlot cells).size = 10 := rfl
  have e2 : (storeAt cells.active rD).size = 2 := rfl
  have e3 : (storeAt cells.bitBase rD).size = 2 := rfl
  have e4 : (cst rD 0).size = 1 := rfl
  rw [e1, e2, e3, e4]
  simp only [Kriterion.CRT.laneCount]
  omega

theorem size_stageFinal (w rb : Nat) : (stageFinal cells w rb).size = 2 + 128 * 24 + 5 := by
  unfold stageFinal
  simp only [Prog.size_seq]
  rw [Prog.size_rep _ _ 24 fun _ _ => rfl]
  have e1 : (loadAt rF cells.value).size = 2 := rfl
  have e2 : (loadAt rE cells.active).size = 2 := rfl
  have e3 : (cst rB cells.nodeBase).size = 1 := rfl
  have e4 : (ar .add rAddr rF rB).size = 1 := rfl
  have e5 : (Prog.op (.store rAddr rE)).size = 1 := rfl
  rw [e1, e2, e3, e4, e5]
  decide

/-- The bound of one stage. -/
abbrev stageBound : Nat :=
  (128 * 6 + (1 + 128 * 9) + 4 + 3 * (1 + 128 * 13 * 2) + 10) + expandBound +
    12 * ((7 + 128 * 29 + 9 + 6 + 19) + expandBound) + (2 + 128 * 24 + 5)

theorem size_stageReplay_le (w rb : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) (rbPos : 1 ≤ rb)
    (rbLe : rb ≤ 128) (wLe : w ≤ 12) :
    (stageReplay cells w rb treeBase castBase stride).size ≤ stageBound := by
  unfold stageReplay
  simp only [Prog.size_seq]
  have h1 := size_stagePrefix_le cells w wLe
  have h2 := size_expandReplay_le cells w rb 1 treeBase castBase stride rbPos rbLe wLe
  have h3 := size_rep_le (w - 1) (fun k => roundReplay cells w rb (k + 1) treeBase castBase stride)
    ((7 + 128 * 29 + 9 + 6 + 19) + expandBound)
    fun k _ => size_roundReplay_le cells w rb (k + 1) treeBase castBase stride rbPos rbLe wLe
  have h4 : (w - 1) * ((7 + 128 * 29 + 9 + 6 + 19) + expandBound) ≤
      12 * ((7 + 128 * 29 + 9 + 6 + 19) + expandBound) := Nat.mul_le_mul_right _ (by omega)
  have h5 := size_stageFinal cells w rb
  unfold stageBound
  omega

end Stage

/-! ### The growth, the reindex and the folds -/

theorem size_treeStep (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) :
    (treeStep cells tagOf n).size = 14 + 34 * 2 ^ n := by
  unfold treeStep treeLevel
  simp only [Prog.size_seq]
  rw [Prog.size_rep _ _ 25 fun _ _ => rfl, Prog.size_rep _ _ 9 fun _ _ => rfl]
  have e1 : (treeRecover cells n).size = 13 := rfl
  have e2 : (cst rD 0).size = 1 := rfl
  omega

theorem size_growEval_le (cells : TreeCells) (tagOf : Nat → Nat → Nat) (start count : Nat)
    (small : start + count ≤ 16) :
    (growEval cells tagOf start count).size ≤ 16 * (14 + 34 * 65536) := by
  unfold growEval
  refine le_trans (size_rep_le _ _ (14 + 34 * 65536) fun k bound => ?_) (Nat.mul_le_mul_right _ (by omega))
  rw [size_treeStep]
  have := pow_le_65536 (n := start + k) (by omega)
  omega

theorem size_reindexStep_le (levelBase m ρ leaf : Nat) : (reindexStep levelBase m ρ leaf).size ≤ 3 := by
  unfold reindexStep
  split
  · exact le_refl 3
  · exact Nat.zero_le 3

theorem size_reindexBlock_le (levelBase vecBase n m : Nat) (nLe : n ≤ 16) (mLe : m ≤ 2 ^ 11) :
    (reindexBlock levelBase vecBase n m).size ≤ 2 ^ 11 * (3 + 65536 * 3) := by
  unfold reindexBlock
  refine le_trans (size_rep_le _ _ (3 + 65536 * 3) fun ρ _ => ?_) (Nat.mul_le_mul_right _ mLe)
  unfold reindexResidue
  simp only [Prog.size_seq]
  have h1 := size_rep_le (2 ^ n) (reindexStep levelBase m ρ) 3 fun leaf _ => size_reindexStep_le _ _ _ _
  have h2 : 2 ^ n * 3 ≤ 65536 * 3 := Nat.mul_le_mul_right _ (pow_le_65536 nLe)
  have e1 : (cst rD 0).size = 1 := rfl
  have e2 : (storeAt (vecBase + ρ) rD).size = 2 := rfl
  omega

theorem size_foldsLoop_le (cells : FoldCells) (m start count : Nat) (tagOf : Nat → Nat → Nat)
    (countLe : count ≤ 16) (mLe : m ≤ 2 ^ 11) :
    (foldsLoop cells m start count tagOf).size ≤ 16 * (31 + 33 * 2 ^ 11) := by
  unfold foldsLoop
  refine le_trans (size_rep_le _ _ (31 + 33 * 2 ^ 11) fun k _ => ?_) (Nat.mul_le_mul_right _ countLe)
  unfold foldStep
  simp only [Prog.size_seq]
  rw [Prog.size_rep _ _ 23 fun _ _ => rfl, Prog.size_rep _ _ 10 fun _ _ => rfl]
  have e1 : (foldRecover cells (start + k)).size = 11 := rfl
  have e2 : (hotUpdate cells m (2 ^ (start + k) % m) (start + k)).size = 19 := rfl
  have e3 : (cst rD 0).size = 1 := rfl
  omega

end ConvSize

/-! ### The conversion -/

open ConvSize in

/-- **The size of the conversion replay of one odd modulus** is at most `2 ^ 36`. -/
theorem size_conversionReplay_le (coord i : Nat) (row : Kriterion.CRT.OddRow) (m W : Nat)
    (joinBase pinBase : Nat → Nat) (growJoin foldJoin : Nat → Nat) (w0Pos : 1 ≤ row.width0)
    (w0Le : row.width0 ≤ 12) (w1Le : row.width1 ≤ 12) (keepGe : row.width0 ≤ row.keep)
    (keepLe : row.keep ≤ 16) (ellLe : row.ell ≤ 16) (ellGt : row.width0 < row.ell) (mLe : m ≤ 2 ^ 11) :
    (conversionReplay coord i row m W joinBase pinBase growJoin foldJoin).size ≤ 2 ^ 36 := by
  unfold conversionReplay
  simp only [Prog.size_seq]
  have h0 : (stageValue0 W row.width0).size = 6 := rfl
  have h1 : (stageValue1 W row.width0 row.width1).size = 8 := rfl
  have h2 := size_stageReplay_le (convStage0 row W (joinBase 0) (pinBase 0)) row.width0 row.ell
    (fun level => Kriterion.CRT.extTreeTag coord i 0 level 0) (Kriterion.CRT.extCastTag coord i 0 0 0) 64
    (by omega) (by omega) w0Le
  have h3 := size_stageReplay_le (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1))
    row.width1 (row.ell - row.width0) (fun level => Kriterion.CRT.extTreeTag coord i 1 level 0)
    (Kriterion.CRT.extCastTag coord i 1 0 0) 64 (by omega) (by omega) w1Le
  have h4 : (lastBitProg W (convStage1 row W (joinBase 0) (pinBase 0) (joinBase 1) (pinBase 1)).nextBase).size =
      1 + 128 * 9 + 2 := by
    unfold lastBitProg lanePack
    simp only [Prog.size_seq]
    rw [Prog.size_rep _ _ 9 fun _ _ => rfl]
    have e1 : (cst rD 0).size = 1 := rfl
    have e2 : (storeAt (W + 258) rD).size = 2 := rfl
    have lc : Kriterion.CRT.laneCount = 128 := rfl
    omega
  have h5 : (saveLeaves (convStage0 row W (joinBase 0) (pinBase 0)).nodeBase (W + 2 ^ 16) row.width0 0).size ≤
      4096 * 4 := by
    unfold saveLeaves
    rw [Prog.size_rep _ _ 4 fun _ _ => rfl]
    exact Nat.mul_le_mul_right _ (pow_le_4096 w0Le)
  have h6 := size_growEval_le (convGrowCells row W joinBase pinBase growJoin) (Kriterion.CRT.growTag coord i)
    row.width0 (row.keep - row.width0) (by omega)
  have h7 := size_reindexBlock_le (W + 2 ^ 16) (W + 2 ^ 12) (row.width0 + (row.keep - row.width0)) m
    (by omega) mLe
  have h8 : (hotInit (convFoldCells row W joinBase pinBase foldJoin) row.keep m).size = 18 := rfl
  have h9 := size_foldsLoop_le (convFoldCells row W joinBase pinBase foldJoin) m row.keep (row.ell - row.keep)
    (Kriterion.CRT.foldTag coord i) (by omega) mLe
  unfold stageBound expandBound at h2 h3
  omega

end Kriterion.CRT.SimMachine
