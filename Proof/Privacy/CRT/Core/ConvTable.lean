/-
The parity conversion garbler on an answer table.

Raw hashes depend only on tags on this table reading. Tree materials therefore
ignore their control labels, but arithmetic casts keep their leaf label in the
low plane. Their independent upper planes use the original full-width hash
reading with its old low random plane discarded.

The material-tree bridge reconstructs every actual leaf before its parity cast
is evaluated. Published pins serialize only their upper planes. Extraction
stages use the same label-aware cast rule through `tableStage`.
-/

import Proof.Correctness.CRT.ChunkStep
import Proof.Privacy.CRT.Core.ExtractStageHash
import Proof.Privacy.CRT.Core.ExtractStageSpec
import Proof.Privacy.CRT.Core.ParityExtractStage
import Proof.Correctness.CRT.ParityCast

namespace Kriterion.CRT.Privacy.Conv

open Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.ExtractSpec (StageParams gJoin gPin gBit gNext gCast gLeaf gRes gNode gBit0 gLevelSum)

/-! ### Readings of a table -/

/-- The cast reading of a table: `castAnswers l` answers at `tagOf 0, 1, …`, read block-aligned (D11). -/
def castRd (A : ℕ → Block × Block) (l : ℕ) (tagOf : ℕ → ℕ) : Lanes l :=
  castLanes l (packAnswers (castAnswers l) fun j => A (tagOf j.val))

/-- The independent upper planes retain the original hash readings. -/
def upperRd (A : ℕ → Block × Block) (l : ℕ) (tagOf : ℕ → ℕ) : Lanes (l - 1) :=
  Parity.pinHalf l (castRd A l tagOf)

theorem upperRd_congr (A A' : ℕ → Block × Block) (l : ℕ) (tagOf : ℕ → ℕ)
    (same : ∀ j : Fin (castAnswers l), A (tagOf j.val) = A' (tagOf j.val)) :
    upperRd A l tagOf = upperRd A' l tagOf := by
  unfold upperRd castRd
  congr 3
  exact funext same

/-- The cast on a tag table still derives its low plane from its leaf label. -/
def parityRd (A : ℕ → Block × Block) (l : ℕ) (tagOf : ℕ → ℕ) (G : Label) : Lanes l :=
  Parity.liftUpper l (upperRd A l tagOf) G

@[simp] theorem parityRd_low (A : ℕ → Block × Block) (l : ℕ) (tagOf : ℕ → ℕ)
    (G : Label) (hl : 1 ≤ l) : laneBit (parityRd A l tagOf G) 0 = G :=
  Parity.laneBit_liftUpper_zero l _ G hl

theorem hLabel_table (A : ℕ → Block × Block) (G : Label) (tag : ℕ) : hLabel (tableHash A) G tag = (clip (A tag).1) :=
  ExtractStage.hLabel_tableHash A G tag

theorem castM_table (A : ℕ → Block × Block) (l : ℕ) (G : Label) (tagOf : ℕ → ℕ) :
    (castM l G tagOf).eval (tableHash A) = parityRd A l tagOf G := by
  rw [SliceC.eval_castM, ExtractStage.hlong_tableHash]
  cases l <;> rfl

/-! ### Trees, growth and folds -/

/-- **A tree join on a table**: the level XOR is the XOR of the table's materials of the level. -/
theorem treeGarbleM_levelSum_table (A : ℕ → Block × Block) (tagOf : ℕ → ℕ → ℕ) (Δ b0 : Label) (total n : ℕ)
    (h1 : 1 ≤ n) (h2 : n < total) :
    ((treeGarbleM tagOf Δ b0 total).eval (tableHash A)).2 n =
      xorFold (fun slot : Fin (2 ^ n) => (clip (A (tagOf n slot.val)).1)) := by
  rw [SliceC.treeGarbleM_levelSum _ _ _ _ total n h1 h2]
  simp only [hLabel_table]

/-- **A growth join on a table.** -/
theorem growGarbleM_levelSum_table (A : ℕ → Block × Block) (tagOf : ℕ → ℕ → ℕ) (start : ℕ)
    (labels : Fin (2 ^ start) → Label) (count j : ℕ) (hj : j < count) :
    ((growGarbleM tagOf start labels count).eval (tableHash A)).2 (start + j) =
      xorFold (fun slot : Fin (2 ^ (start + j)) => (clip (A (tagOf (start + j) slot.val)).1)) := by
  rw [SliceC.growGarbleM_levelSum _ _ _ _ count j hj]
  simp only [hLabel_table]

/-- **A fold join on a table**: the XOR of the table's materials of the position, XOR the bit mask. -/
theorem foldsGarbleM_join_table (A : ℕ → Block × Block) (m : ℕ) (tagOf : ℕ → ℕ → ℕ) (bitMask : ℕ → Label) :
    ∀ (count start : ℕ) (labels : Fin m → Label) (position : ℕ), start ≤ position → position < start + count →
      ((foldsGarbleM m tagOf bitMask count start labels).eval (tableHash A)).2 position =
        xorFold (fun ρ : Fin m => (clip (A (tagOf position ρ.val)).1)) ^^^ bitMask position
  | 0, start, _, position, h1, h2 => absurd h2 (by omega)
  | count + 1, start, labels, position, h1, h2 => by
      rw [SliceC.eval_foldsGarbleM_succ]
      simp only
      by_cases hp : position = start
      · subst hp
        rw [if_pos rfl, SliceC.eval_foldGarbleM]
        simp only [hLabel_table]
      · rw [if_neg hp]
        exact foldsGarbleM_join_table A m tagOf bitMask count (start + 1) _ position (by omega) (by omega)

/-! ### A chunk -/

/-- A tree evaluated with fixed materials indexed by level and slot. -/
def materialTree (mat : ℕ → ℕ → Label) (Δ b0 : Label) : (n : ℕ) → Fin (2 ^ n) → Label
  | 0 => fun _ => Δ
  | n + 1 => extendLevel n (materialTree mat Δ b0 n)
      (fun slot => if n = 0 then b0 else mat n slot.val)

/-- Fixed-material tree evaluation is the tag-table reading of the garbler. -/
theorem treeGarbleM_table_leaves (A : ℕ → Block × Block) (tagOf : ℕ → ℕ → ℕ)
    (Δ b0 : Label) : ∀ n,
    ((treeGarbleM tagOf Δ b0 n).eval (tableHash A)).1 =
      materialTree (fun level slot => clip (A (tagOf level slot)).1) Δ b0 n
  | 0 => rfl
  | n + 1 => by
      simp only [treeGarbleM, FreeQuery.eval_bind]
      by_cases hn : n = 0
      · simp only [if_pos hn, FreeQuery.eval_pure, stored_eq, materialTree,
          if_pos hn, treeGarbleM_table_leaves A tagOf Δ b0 n]
      · simp only [if_neg hn, SliceC.eval_garbleStepM, FreeQuery.eval_pure,
          hLabel_table, materialTree, if_neg hn, treeGarbleM_table_leaves A tagOf Δ b0 n]

/-- Only the materials of the in-range hashed levels influence a material tree. -/
theorem materialTree_congr (mat mat' : ℕ → ℕ → Label) (Δ b0 : Label) :
    ∀ n, (∀ k, 1 ≤ k → k < n → ∀ slot, slot < 2 ^ k → mat k slot = mat' k slot) →
      materialTree mat Δ b0 n = materialTree mat' Δ b0 n
  | 0, _ => rfl
  | n + 1, same => by
      rw [materialTree, materialTree, materialTree_congr mat mat' Δ b0 n
        (fun k h1 h2 slot hs => same k h1 (by omega) slot hs)]
      congr 1
      funext slot
      by_cases hn : n = 0
      · simp only [if_pos hn]
      · simp only [if_neg hn]
        exact same n (by omega) (by omega) slot.val slot.isLt

/-- Every material tree preserves the XOR of its root. -/
theorem materialTree_xor (mat : ℕ → ℕ → Label) (Δ b0 : Label) :
    ∀ n, xorFold (materialTree mat Δ b0 n) = Δ
  | 0 => by simp [materialTree, xorFold, Fin.foldl_succ_last]
  | n + 1 => by rw [materialTree, SliceC.xorFold_extendLevel, materialTree_xor mat Δ b0 n]

/-- **A chunk on a table**: casts keep the actual leaf parity. -/
theorem chunk_table (A : ℕ → Block × Block) (tbl : CrtTable) (coord : ℕ) (Δ : Label) (Z : ℕ → Label) (c : ℕ) :
    let g := (chunkGarbleM tbl coord Δ Z c).eval (tableHash A)
    let leaves := materialTree (fun n slot => clip (A (chunkTreeTag coord c n slot)).1)
      Δ (Z (tbl.chunkOffset c)) (tbl.chunkWidth c)
    (∀ n, 1 ≤ n → n < tbl.chunkWidth c →
        g.joins n = xorFold (fun slot : Fin (2 ^ n) => (clip (A (chunkTreeTag coord c n slot.val)).1)) ^^^
          Z (tbl.chunkOffset c + n)) ∧
    (∀ leaf, leaf < 2 ^ tbl.chunkWidth c → g.casts leaf =
      parityRd A tbl.castWidth (chunkCastTag coord c leaf) (atNat leaves 0 leaf)) ∧
    g.pin = (∑ leaf : Fin (2 ^ tbl.chunkWidth c),
      parityRd A tbl.castWidth (chunkCastTag coord c leaf.val) (leaves leaf)) + deltaLanes tbl.castWidth Δ := by
  intro g leaves
  simp only [g, chunkGarbleM, FreeQuery.eval_bind, eval_tableM, castM_table, FreeQuery.eval_pure,
    materialize_eq, SliceC.sumLanes_eq, treeGarbleM_table_leaves]
  refine ⟨fun n h1 h2 => ?_, fun leaf hl => ?_, trivial⟩
  · rw [treeGarbleM_levelSum_table A _ _ _ _ n h1 h2]
  · rw [SliceC.atNat_of_lt _ _ hl, SliceC.atNat_of_lt _ _ hl]

/-! ### An extraction stage -/

/-- **A stage on a table**: `ExtractSpec`'s stage whose materials and casts are the table's readings, labels
ignored. -/
def tableStage (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb) (treeTag castTag : ℕ → ℕ → ℕ) :
    StageParams rb :=
  ExtractStage.stageOf w hw (fun n x _ => (clip (A (treeTag n x)).1)) (fun α G => parityRd A rb (castTag α) G)

@[simp] theorem tableStage_low (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb)
    (treeTag castTag : ℕ → ℕ → ℕ) (positive : 1 ≤ rb) (α : ℕ) (G : Label) :
    laneBit ((tableStage A w hw treeTag castTag).castF α G) 0 = G :=
  parityRd_low A rb (castTag α) G positive

/-- Hot tree materials and hot upper casts on a tag table do not depend on the current labels. -/
@[simp] theorem upperHidden_table (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb)
    (treeTag castTag : ℕ → ℕ → ℕ) (R : Lanes rb) (Δ : Label) (s : ℕ) :
    ExtractStage.upperHiddenOfSpec (tableStage A w hw treeTag castTag) R Δ s =
      ((fun k => clip (A (treeTag (k.val + 1) (s % 2 ^ (k.val + 1)))).1),
        upperRd A rb (castTag s)) := by
  simp only [ExtractStage.upperHiddenOfSpec, ExtractStage.hiddenOfSpec, tableStage,
    ExtractStage.stageOf, gCast, parityRd, Parity.pinHalf_liftUpper]

theorem gNext_upper_table_self (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb)
    (treeTag castTag : ℕ → ℕ → ℕ) (positive : 1 ≤ rb) (R : Lanes rb) (Δ : Label) (s : ℕ) :
    (gNext (ExtractStage.upperOverrideHot (tableStage A w hw treeTag castTag) s
      ((fun k => clip (A (treeTag (k.val + 1) (s % 2 ^ (k.val + 1)))).1),
        upperRd A rb (castTag s))) R Δ : Lanes (rb - w)) =
      gNext (tableStage A w hw treeTag castTag) R Δ := by
  simpa only [upperHidden_table] using ExtractStage.gNext_upper_override_self
    (tableStage A w hw treeTag castTag) (tableStage_low A w hw treeTag castTag positive) R Δ s

theorem gBit_upper_table_self (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb)
    (treeTag castTag : ℕ → ℕ → ℕ) (positive : 1 ≤ rb) (R : Lanes rb) (Δ : Label) (s n : ℕ) :
    gBit (ExtractStage.upperOverrideHot (tableStage A w hw treeTag castTag) s
      ((fun k => clip (A (treeTag (k.val + 1) (s % 2 ^ (k.val + 1)))).1),
        upperRd A rb (castTag s))) R Δ n = gBit (tableStage A w hw treeTag castTag) R Δ n := by
  simpa only [upperHidden_table] using ExtractStage.gBit_upper_override_self
    (tableStage A w hw treeTag castTag) (tableStage_low A w hw treeTag castTag positive) R Δ s n

theorem upperSpecPublish_table_self (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb)
    (treeTag castTag : ℕ → ℕ → ℕ) (positive : 1 ≤ w) (R : Lanes rb) (Δ : Label) (s : ℕ)
    (hs : s < 2 ^ w) :
    ExtractStage.upperSpecPublish (tableStage A w hw treeTag castTag) R Δ s
      ((fun k => clip (A (treeTag (k.val + 1) (s % 2 ^ (k.val + 1)))).1),
        upperRd A rb (castTag s)) =
      ((fun k => gJoin (tableStage A w hw treeTag castTag) R Δ (k.val + 1)),
        Parity.pinHalf rb (gPin (tableStage A w hw treeTag castTag) R Δ)) := by
  simpa only [upperHidden_table] using ExtractStage.upperSpecPublish_self
    (tableStage A w hw treeTag castTag) positive (tableStage_low A w hw treeTag castTag (by omega))
      R Δ s hs

theorem hashStage_table (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb) (treeTag castTag : ℕ → ℕ → ℕ) :
    SliceC.hashStage (tableHash A) w hw treeTag castTag = tableStage A w hw treeTag castTag := by
  unfold SliceC.hashStage tableStage ExtractStage.stageOf
  congr 1
  · funext n x lab
    exact hLabel_table A lab (treeTag n x)
  · funext α lab
    simp only [parityRd, upperRd, castRd, ExtractStage.hlong_tableHash]
    cases rb <;> rfl

/-- `gNext` of the hashed stage on a table (the stage appears in its type, so `hashStage_table` does not rewrite
it directly). -/
theorem gNext_table (A : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb) (treeTag castTag : ℕ → ℕ → ℕ)
    (R : Lanes rb) (Δ : Label) :
    (gNext (SliceC.hashStage (tableHash A) w hw treeTag castTag) R Δ : Lanes (rb - w)) =
      gNext (tableStage A w hw treeTag castTag) R Δ := by
  show peelDiv R (gRes (SliceC.hashStage (tableHash A) w hw treeTag castTag) R Δ w) w =
    peelDiv R (gRes (tableStage A w hw treeTag castTag) R Δ w) w
  rw [hashStage_table]

/-- The bit masks of a conversion above stage 0 read only stage 1's bits and remainder. -/
theorem wordBit_high (row : OddRow) (b0 b1 : ℕ → Label) (last : Label) (p : ℕ) (hp : row.width0 ≤ p) :
    wordBit row b0 b1 last p = if p < row.width0 + row.width1 then b1 (p - row.width0) else last := by
  simp only [wordBit, if_neg (show ¬ p < row.width0 by omega)]

/-! ### One odd modulus -/

/-- The conversion program of one odd modulus, evaluated, with its intermediate results named. -/
theorem conversionGarbleM_eval (H : HashN) (coord i : ℕ) (row : OddRow) (m : ℕ) (Δ : Label) (W : Lanes row.ell)
    (g0 : StageGarbled row.ell row.width0) (g1 : StageGarbled (row.ell - row.width0) row.width1)
    (grown : (Fin (2 ^ (row.width0 + (row.keep - row.width0))) → Label) × (ℕ → Label))
    (folded : (Fin m → Label) × (ℕ → Label))
    (hg0 : (extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H = g0)
    (hg1 : (extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ g0.next).eval H = g1)
    (hgrown : (growGarbleM (growTag coord i) row.width0 (stored fun leaf => g0.leaves leaf.val)
      (row.keep - row.width0)).eval H = grown)
    (hfolded : (foldsGarbleM m (foldTag coord i) (wordBit row g0.bits g1.bits (laneBit g1.next 0))
      (row.ell - row.keep) row.keep (reindex _ grown.1 m)).eval H = folded) :
    (conversionGarbleM coord i row m Δ W).eval H =
      { stageJoins := fun stage n => if stage = 0 then g0.joins n else g1.joins n
        stagePins := fun stage k =>
          if stage = 0 then atNat (stored (pinBlocks (Parity.pinHalf row.ell g0.pin))) 0 k else atNat (stored (pinBlocks (Parity.pinHalf (row.ell - row.width0) g1.pin))) 0 k
        growJoins := fun position => grown.2 position ^^^ wordBit row g0.bits g1.bits (laneBit g1.next 0) position
        foldJoins := folded.2
        final := folded.1 } := by
  subst hg0 hg1 hgrown hfolded
  simp only [conversionGarbleM, FreeQuery.eval_bind, FreeQuery.eval_pure]

/-- **The conversion of one odd modulus on a table**: the stage joins and pins are `ExtractSpec`'s at the table's
stages (stage 1 on stage 0's peeled remainder), and the growth and fold joins are the XOR of the table's materials of
their level, XOR the bit mask of the word's bit there. -/
theorem conversion_table (A : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m : ℕ) (Δ : Label)
    (W : Lanes row.ell) (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0)
    (hk : row.width0 ≤ row.keep) :
    let sp0 := tableStage A row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)
    let sp1 := tableStage A row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1)
    let R1 : Lanes (row.ell - row.width0) := gNext sp0 W Δ
    let bitMask := fun p => if p < row.width0 + row.width1 then gBit sp1 R1 Δ (p - row.width0)
      else laneBit (gNext sp1 R1 Δ) 0
    let g := (conversionGarbleM coord i row m Δ W).eval (tableHash A)
    (∀ n, 1 ≤ n → n < row.width0 → g.stageJoins 0 n = gJoin sp0 W Δ n) ∧
    (∀ k, g.stagePins 0 k = atNat (stored (pinBlocks (Parity.pinHalf row.ell (gPin sp0 W Δ)))) 0 k) ∧
    (∀ n, 1 ≤ n → n < row.width1 → g.stageJoins 1 n = gJoin sp1 R1 Δ n) ∧
    (∀ k, g.stagePins 1 k = atNat (stored (pinBlocks (Parity.pinHalf (row.ell - row.width0) (gPin sp1 R1 Δ)))) 0 k) ∧
    (∀ j, j < row.keep - row.width0 → g.growJoins (row.width0 + j) =
        xorFold (fun slot : Fin (2 ^ (row.width0 + j)) => (clip (A (growTag coord i (row.width0 + j) slot.val)).1)) ^^^
          bitMask (row.width0 + j)) ∧
    (∀ j, j < row.ell - row.keep → g.foldJoins (row.keep + j) =
        xorFold (fun ρ : Fin m => (clip (A (foldTag coord i (row.keep + j) ρ.val)).1)) ^^^ bitMask (row.keep + j)) := by
  intro sp0 sp1 R1 bitMask g
  obtain ⟨g0, hg0⟩ : ∃ g0, (extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval
      (tableHash A) = g0 := ⟨_, rfl⟩
  have e0 := SliceC.extStageGarbleM_eval (tableHash A) row.width0 hw0 (extTreeTag coord i 0)
    (extCastTag coord i 0) Δ W
  simp only [hashStage_table, hg0] at e0
  obtain ⟨-, -, j0, p0, n0⟩ := e0
  have n0' : g0.next = R1 := n0.trans (gNext_table A row.width0 hw0 _ _ W Δ)
  obtain ⟨g1, hg1⟩ : ∃ g1, (extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ R1).eval
      (tableHash A) = g1 := ⟨_, rfl⟩
  have hg1' : (extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ g0.next).eval
      (tableHash A) = g1 := by
    rw [n0']
    exact hg1
  have e1 := SliceC.extStageGarbleM_eval (tableHash A) row.width1 hw1 (extTreeTag coord i 1)
    (extCastTag coord i 1) Δ R1
  simp only [hashStage_table, hg1] at e1
  obtain ⟨-, b1, j1, p1, n1⟩ := e1
  have n1' : g1.next = gNext sp1 R1 Δ := n1.trans (gNext_table A row.width1 hw1 _ _ R1 Δ)
  obtain ⟨grown, hgrown⟩ : ∃ grown, (growGarbleM (growTag coord i) row.width0 (stored fun leaf => g0.leaves leaf.val)
      (row.keep - row.width0)).eval (tableHash A) = grown := ⟨_, rfl⟩
  obtain ⟨folded, hfolded⟩ : ∃ folded, (foldsGarbleM m (foldTag coord i) (wordBit row g0.bits g1.bits
      (laneBit g1.next 0)) (row.ell - row.keep) row.keep (reindex _ grown.1 m)).eval (tableHash A) = folded :=
    ⟨_, rfl⟩
  have hgEq : g = _ := conversionGarbleM_eval (tableHash A) coord i row m Δ W g0 g1 grown folded hg0 hg1' hgrown
    hfolded
  have high : ∀ p, row.width0 ≤ p → wordBit row g0.bits g1.bits (laneBit g1.next 0) p = bitMask p := by
    intro p hp
    rw [wordBit_high row _ _ _ p hp, n1']
    show _ = if p < row.width0 + row.width1 then gBit sp1 R1 Δ (p - row.width0) else laneBit (gNext sp1 R1 Δ) 0
    split_ifs with h2
    · exact b1 _ (by omega)
    · rfl
  rw [hgEq]
  refine ⟨fun n h1 h2 => ?_, fun k => ?_, fun n h1 h2 => ?_, fun k => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · show (if (0 : ℕ) = 0 then g0.joins n else g1.joins n) = _
    rw [if_pos rfl]
    exact j0 n h1 h2
  · show (if (0 : ℕ) = 0 then atNat (stored (pinBlocks (Parity.pinHalf row.ell g0.pin))) 0 k
      else atNat (stored (pinBlocks (Parity.pinHalf (row.ell - row.width0) g1.pin))) 0 k) = _
    rw [if_pos rfl, p0]
  · show (if (1 : ℕ) = 0 then g0.joins n else g1.joins n) = _
    rw [if_neg one_ne_zero]
    exact j1 n h1 h2
  · show (if (1 : ℕ) = 0 then atNat (stored (pinBlocks (Parity.pinHalf row.ell g0.pin))) 0 k
      else atNat (stored (pinBlocks (Parity.pinHalf (row.ell - row.width0) g1.pin))) 0 k) = _
    rw [if_neg one_ne_zero, p1]
  · show grown.2 (row.width0 + j) ^^^ _ = _
    rw [← hgrown, growGarbleM_levelSum_table A (growTag coord i) row.width0 _ _ j hj, high _ (by omega)]
  · show folded.2 (row.keep + j) = _
    rw [← hfolded, foldsGarbleM_join_table A m (foldTag coord i) _ (row.ell - row.keep) row.keep _ (row.keep + j)
      (by omega) (by omega), high _ (by omega)]

/-! ### A modulus and a coordinate -/

/-- **An odd modulus**: its published conversion material is its conversion's, on the word of the chunks' casts. -/
theorem modGarbleM_odd (H : HashN) (tbl : CrtTable) (S coord : ℕ) (Δ : Label)
    (chunks : ℕ → ChunkGarbled tbl.castWidth) (i : Fin tbl.count) (row : OddRow) (hk : tbl.kind i = .odd row) :
    let conv := (conversionGarbleM coord i.val row (tbl.modulus i) Δ
      (truthWord tbl (tbl.modulus i) row.ell fun c leaf => (chunks c).casts leaf)).eval H
    let g := (modGarbleM tbl S coord Δ chunks i).eval H
    g.stageJoins = conv.stageJoins ∧ g.stagePins = conv.stagePins ∧ g.growJoins = conv.growJoins ∧
      g.foldJoins = conv.foldJoins := by
  intro conv g
  simp only [g, conv, modGarbleM, hk, FreeQuery.eval_bind, eval_materializeM, FreeQuery.eval_pure]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- **A coordinate's published conversion material** is its chunks' and its moduli's. -/
theorem coord_pub (H : HashN) (tbl : CrtTable) (S coord : ℕ) (Δ : Label) (Z : ℕ → Label) :
    let chunks : ℕ → ChunkGarbled tbl.castWidth :=
      atNat (fun c : Fin tbl.chunkCount => (chunkGarbleM tbl coord Δ Z c.val).eval H) (ChunkGarbled.empty _)
    let pub := ((coordGarbleM tbl S coord Δ Z).eval H).pub
    (∀ c, c < tbl.chunkCount → ∀ n, pub.chunkJoin c n = ((chunkGarbleM tbl coord Δ Z c).eval H).joins n) ∧
    (∀ c, c < tbl.chunkCount → ∀ k,
      pub.chunkPin c k = atNat (stored (pinBlocks (Parity.pinHalf tbl.castWidth ((chunkGarbleM tbl coord Δ Z c).eval H).pin))) 0 k) ∧
    (∀ i (hi : i < tbl.count) stage n,
      pub.stageJoin i stage n = ((modGarbleM tbl S coord Δ chunks ⟨i, hi⟩).eval H).stageJoins stage n) ∧
    (∀ i (hi : i < tbl.count) stage k,
      pub.stagePin i stage k = ((modGarbleM tbl S coord Δ chunks ⟨i, hi⟩).eval H).stagePins stage k) ∧
    (∀ i (hi : i < tbl.count) j,
      pub.growJoin i j = ((modGarbleM tbl S coord Δ chunks ⟨i, hi⟩).eval H).growJoins j) ∧
    (∀ i (hi : i < tbl.count) j,
      pub.foldJoin i j = ((modGarbleM tbl S coord Δ chunks ⟨i, hi⟩).eval H).foldJoins j) := by
  intro chunks pub
  simp only [pub, chunks, coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]
  refine ⟨fun c hc n => ?_, fun c hc k => ?_, fun i hi stage n => ?_, fun i hi stage k => ?_, fun i hi j => ?_,
    fun i hi j => ?_⟩
  · rw [SliceC.atNat_of_lt _ _ hc]
  · rw [dif_pos hc]
    simp only [stored_eq]
  · simp only [dif_pos hi]
  · simp only [dif_pos hi]
  · simp only [dif_pos hi]
  · simp only [dif_pos hi]

end Kriterion.CRT.Privacy.Conv
