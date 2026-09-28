/-
**No chunk joins, privacy groundwork (3/4): the hot tree answers and the cold table.**

Imports the tag decoders and `hotTag` (`Sites.lean`) and the tag table type (`Hybrids.lean`), both of which
build on this branch; nothing of the H8 chain.

At an input `u`, the evaluator's active slot of level `n` of chunk `c` of coordinate `κ` is
`hotSlot u κ j` for the coordinate bit `j = 8c + n` (`n ≥ 1`); its tag is hot (`hotTag`, family `0`), the
other slots of the level are cold (visible). `withHotTree t u y` is the table `t` with the answer at the hot
tree tag of every non-first bit `(κ, j)` replaced by `y κ j` (and nothing else changed:
`withHotTree_other`). Then:

* `levelSum_withHotTree`: the level sum is `clip (y κ j).1 ⊕ coldSum t u κ j`, where `coldSum` reads the
  cold slots of `t` only (`coldSum_withHotTree`);
* **`actualZeros_withHotTree`**: the actual zero labels of the real garbling on `withHotTree t u y` with
  coins' zero labels `Z` are the first component of `keysEquiv firstFlag (coldSum t u) (Z, y)`: a bijection
  of `(Z, y)` that depends on the cold table and `u` only (not on `Δ`, nor on `Z` or `y`).

With `NoJoins.Key.keyOf_tagOnly`, the real returned key on `withHotTree t u y` is `keyOfZeros Z' Δ` with
`(Z', r) = keysEquiv … (Z, y)` (`keyOf_withHotTree`).
-/

import Proof.Privacy.CRT.NoJoins.Key
import Proof.Privacy.CRT.Sites
import Proof.Privacy.CRT.Hybrids

namespace Kriterion.CRT.Privacy.NoJoins

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy

/-! ### The hot slot of a bit -/

/-- The evaluator's active slot of level `j % 8` of chunk `j / 8` of coordinate `κ` at `u`. -/
def hotSlot (u : AffineInput) (κ : Fin 2) (j : Bits) : Nat :=
  Entry.table.chunkValue (coordValue u κ.val) (j.val / 8) % 2 ^ (j.val % 8)

theorem hotSlot_lt (u : AffineInput) (κ : Fin 2) (j : Bits) : hotSlot u κ j < 2 ^ (j.val % 8) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A chunk-tree tag of the real table is below `2 ^ 36` (family `0`), so it indexes the tag table as is. -/
theorem chunkTreeTag_lt (κ : Fin 2) (j : Bits) (s : Nat) (hs : s < 2 ^ (j.val % 8)) :
    chunkTreeTag κ.val (j.val / 8) (j.val % 8) s < 2 ^ 40 := by
  have hj := j.isLt
  have hκ := κ.isLt
  have small : 2 ^ (j.val % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  unfold chunkTreeTag tagCode Family.chunkTree
  have : s < 128 := lt_of_lt_of_le hs (by simpa using small)
  omega

theorem chunkTreeTag_inRange (κ : Fin 2) (j : Bits) (s : Nat) (hs : s < 2 ^ (j.val % 8)) :
    TagInRange κ.val (j.val / 8) 0 (j.val % 8) s 0 := by
  have hj := j.isLt
  have hκ := κ.isLt
  have small : 2 ^ (j.val % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have : s < 128 := lt_of_lt_of_le hs (by simpa using small)
  exact ⟨hκ, by omega, by decide, by omega, by omega, by decide⟩

/-! ### Overriding the hot tree answers -/

/-- The non-first bit whose hot chunk-tree tag `tag` is at `u` (`none` for every other tag). -/
def hotTreeBit (u : AffineInput) (tag : Nat) : Option (Fin 2 × Bits) :=
  if h : tagFamily tag = 0 ∧ tagStage tag = 0 ∧ tagPart tag = 0 ∧ 1 ≤ tagLevel tag ∧ tagLevel tag < 8 ∧
      8 * tagIdx tag + tagLevel tag < 254 ∧ hotTag Entry.table u tag = true then
    some (⟨tagCoord tag, Nat.mod_lt _ (by decide)⟩, ⟨8 * tagIdx tag + tagLevel tag, h.2.2.2.2.2.1⟩)
  else none

/-- **The table with the hot tree answers replaced**: at the hot chunk-tree tag of every non-first bit
`(κ, j)` at `u` the answer is `y κ j`; every other tag keeps `t`'s answer. -/
def withHotTree (t : TagTable) (u : AffineInput) (y : HotAnswers) : TagTable :=
  fun tag => match hotTreeBit u tag.val with
    | some (κ, j) => y κ j
    | none => t tag

/-- Off the hot tree tags nothing changes. -/
theorem withHotTree_other (t : TagTable) (u : AffineInput) (y : HotAnswers) (tag : Fin (2 ^ 40))
    (other : hotTreeBit u tag.val = none) : withHotTree t u y tag = t tag := by
  unfold withHotTree
  rw [other]

/-- A tag that is not a family-`0` hot tag is never overridden. -/
theorem hotTreeBit_eq_none (u : AffineInput) (tag : Nat)
    (away : ¬ (tagFamily tag = 0 ∧ hotTag Entry.table u tag = true)) : hotTreeBit u tag = none := by
  unfold hotTreeBit
  rw [dif_neg]
  rintro ⟨fam, -, -, -, -, -, hot⟩
  exact away ⟨fam, hot⟩

/-- The decoding of a chunk-tree tag of a non-first bit: hot exactly at the hot slot. -/
theorem hotTreeBit_chunkTreeTag (u : AffineInput) (κ : Fin 2) (j : Bits) (first : ¬ j.val % 8 = 0) (s : Nat)
    (hs : s < 2 ^ (j.val % 8)) :
    hotTreeBit u (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) =
      if s = hotSlot u κ j then some (κ, j) else none := by
  have range := chunkTreeTag_inRange κ j s hs
  have fam : tagFamily (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = 0 := tagFamily_tagCode range
  have coord : tagCoord (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = κ.val := tagCoord_tagCode range
  have idx : tagIdx (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = j.val / 8 := tagIdx_tagCode range
  have stage : tagStage (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = 0 := tagStage_tagCode range
  have level : tagLevel (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = j.val % 8 := tagLevel_tagCode range
  have slot : tagSlot (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = s := tagSlot_tagCode range
  have part : tagPart (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = 0 := tagPart_tagCode range
  have hot : hotTag Entry.table u (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = true ↔ s = hotSlot u κ j := by
    unfold hotTag
    simp only [fam, coord, idx, level, slot, hotSlot, beq_iff_eq]
  have hj := j.isLt
  unfold hotTreeBit
  by_cases same : s = hotSlot u κ j
  · rw [if_pos same, dif_pos ⟨fam, stage, part, by omega, by omega, by omega, hot.mpr same⟩]
    congr 1
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · exact coord
    · show 8 * tagIdx _ + tagLevel _ = j.val
      rw [idx, level]
      omega
  · rw [if_neg same, dif_neg]
    rintro ⟨-, -, -, -, -, -, isHot⟩
    exact same (hot.mp isHot)

/-- The tag-table answer at a chunk-tree tag of a non-first bit on the overridden table. -/
theorem material_withHotTree (t : TagTable) (u : AffineInput) (y : HotAnswers) (κ : Fin 2) (j : Bits)
    (first : ¬ j.val % 8 = 0) (s : Nat) (hs : s < 2 ^ (j.val % 8)) :
    material (tableAnswers (withHotTree t u y)) κ.val (j.val / 8) (j.val % 8) s =
      if s = hotSlot u κ j then clip (y κ j).1 else material (tableAnswers t) κ.val (j.val / 8) (j.val % 8) s := by
  have small := chunkTreeTag_lt κ j s hs
  unfold material tableAnswers withHotTree
  simp only [Nat.mod_eq_of_lt small]
  rw [hotTreeBit_chunkTreeTag u κ j first s hs]
  by_cases same : s = hotSlot u κ j
  · rw [if_pos same, if_pos same]
  · rw [if_neg same, if_neg same]

/-! ### The level sum: hot material XOR the cold XOR -/

/-- **The cold XOR** of non-first bit `j` of coordinate `κ`: the XOR of the level's materials off the hot
slot, read from the cold (visible) tags of `t`. -/
def coldSum (t : TagTable) (u : AffineInput) (κ : Fin 2) (j : Bits) : Label :=
  xorFoldExcept (⟨hotSlot u κ j, hotSlot_lt u κ j⟩ : Fin (2 ^ (j.val % 8)))
    fun s => material (tableAnswers t) κ.val (j.val / 8) (j.val % 8) s.val

/-- The cold XOR does not read the hot tree answers. -/
theorem coldSum_withHotTree (t : TagTable) (u : AffineInput) (y : HotAnswers) (κ : Fin 2) (j : Bits)
    (first : ¬ j.val % 8 = 0) : coldSum (withHotTree t u y) u κ j = coldSum t u κ j := by
  unfold coldSum
  refine SliceC.xorFoldExcept_congr _ _ _ fun s off => ?_
  rw [material_withHotTree t u y κ j first s.val s.isLt, if_neg]
  intro same
  exact off (Fin.ext same)

/-- **The level sum of a non-first bit on the overridden table**: the hot answer's material XOR the cold XOR. -/
theorem levelSum_withHotTree (t : TagTable) (u : AffineInput) (y : HotAnswers) (κ : Fin 2) (j : Bits)
    (first : ¬ j.val % 8 = 0) :
    levelSum (tableAnswers (withHotTree t u y)) κ.val (j.val / 8) (j.val % 8) = clip (y κ j).1 ^^^ coldSum t u κ j := by
  let hot : Fin (2 ^ (j.val % 8)) := ⟨hotSlot u κ j, hotSlot_lt u κ j⟩
  unfold levelSum
  rw [← SliceC.xorFoldExcept_xor hot]
  have atHot : material (tableAnswers (withHotTree t u y)) κ.val (j.val / 8) (j.val % 8) hot.val = clip (y κ j).1 := by
    rw [material_withHotTree t u y κ j first hot.val hot.isLt, if_pos rfl]
  have cold : xorFoldExcept hot (fun s : Fin (2 ^ (j.val % 8)) =>
      material (tableAnswers (withHotTree t u y)) κ.val (j.val / 8) (j.val % 8) s.val) = coldSum t u κ j := by
    unfold coldSum
    refine SliceC.xorFoldExcept_congr _ _ _ fun s off => ?_
    rw [material_withHotTree t u y κ j first s.val s.isLt, if_neg]
    intro same
    exact off (Fin.ext same)
  rw [atHot, cold]
  exact BitVec.xor_comm _ _

/-! ### The actual zero labels are the first component of the key relabelling -/

/-- The first-bit flags of the coordinate bits (`j % 8 = 0`). -/
def firstFlag (_κ : Fin 2) (j : Bits) : Bool := decide (j.val % 8 = 0)

/-- **The actual zero labels on the overridden table** are the first component of `keysEquiv`, a
bijection of (coins' zero labels, hot answers) that reads the cold table and `u` only. -/
theorem actualZeros_withHotTree (t : TagTable) (u : AffineInput) (Z : KeyZeros) (y : HotAnswers) :
    actualZeros (tableAnswers (withHotTree t u y)) Z = (keysEquiv firstFlag (coldSum t u) (Z, y)).1 := by
  funext κ j
  rw [keysEquiv_fst]
  unfold actualZeros actualZero firstFlag
  by_cases first : j.val % 8 = 0
  · rw [if_pos first, if_pos (decide_eq_true first)]
  · rw [if_neg first, if_neg (by simpa using first), levelSum_withHotTree t u y κ j first]

/-- **The real returned key on the overridden table**, at a tag-only hash of it. -/
theorem keyOf_withHotTree (t : TagTable) (u : AffineInput) (y : HotAnswers) (coins : Coins) :
    EntryCorrect.keyOf (tableHash (withHotTree t u y)) coins =
      keyOfZeros (keysEquiv firstFlag (coldSum t u) (zeroOf coins, y)).1 (deltaOf coins) := by
  rw [keyOf_tagOnly (tagOnly_tableHash _), actualZeros_withHotTree]

/-- **The real selected labels on the overridden table**: source-form labels of the relabelled zeros. -/
theorem labelsFor_withHotTree (t : TagTable) (u : AffineInput) (y : HotAnswers) (coins : Coins) :
    EntryCorrect.labelsFor (tableHash (withHotTree t u y)) coins u =
      sourceLabels (keysEquiv firstFlag (coldSum t u) (zeroOf coins, y)).1 (deltaOf coins) u := by
  rw [labelsFor_tagOnly (tagOnly_tableHash _), actualZeros_withHotTree]

end Kriterion.CRT.Privacy.NoJoins
