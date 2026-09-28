/-
**No chunk joins, privacy groundwork (2/4): the actual key at a tag-only hash, in closed form.**

Standalone: imports the correctness proof of the entry (for `EntryCorrect.keyOf`, the garbler's returned
key) and `Algebra.lean`; no privacy-chain module.

The tag-table hybrids answer every labelled input `hashInput label tag` by its tag alone (`TagOnly`; the
chain's `H8.tagHash table` is `tableHash table`, and `CurveWindow.gxOf_tableOracle` moves the scheme's
hash of the table oracle there). Under such a hash the chunk-tree materials do not depend on the tree
labels, so the coordinate garbler's chunk join of level `n` of chunk `c` is
`levelSum A coord c n ⊕ clip Z_{8c+n}` (`chunkJoin_tagOnly`), and the actual zero label of bit `j` is

* `Z_j` at a chunk's first bit (`j % 8 = 0`),
* `setLow Z_j (levelSum A coord (j / 8) (j % 8))` otherwise (`actualZero`, `keyZero_tagOnly`):

its low part is the XOR of the level's tree materials, its high part the coins'. The garbler's returned
key is the pairs `(Z'_j, Z'_j ⊕ Δ)` of these actual zero labels (`keyOf_tagOnly`), and the selected
labels of an input `u` are the source-form labels `Z'_j ⊕ u_j Δ` (`labelsFor_tagOnly`, via
`selectedLabels_keyOfZeros` for every key of that form).
-/

import Proof.Correctness.CRT.EntryCorrect
import Construction.CRT.Layout
import Proof.Privacy.CRT.NoJoins.Algebra

namespace Kriterion.CRT.Privacy.NoJoins

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry

/-! ### Tag-only hashes -/

/-- A hash that answers every labelled input with a tag below `2 ^ 40` by its tag alone (the chain's tag tables:
`H8.tagHash` everywhere, the scheme's hash of `tableOracle` below `p`). -/
def TagOnly (H : HashN) (A : Nat → Block × Block) : Prop :=
  ∀ (label : Block) (tag : Nat), tag < 2 ^ 40 → H (hashInput label tag) = A tag

/-- The tag-table hash (definitionally the chain's `H8.tagHash`). -/
def tableHash (table : Fin (2 ^ 40) → Block × Block) : HashN :=
  fun n => table ⟨n / 2 ^ 128 % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- The answers of a tag table by tag. -/
def tableAnswers (table : Fin (2 ^ 40) → Block × Block) (tag : Nat) : Block × Block :=
  table ⟨tag % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

theorem hashInput_div (label : Block) (tag : Nat) : hashInput label tag / 2 ^ 128 = tag := by
  unfold hashInput
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.div_eq_of_lt label.isLt, Nat.zero_add]

theorem tagOnly_tableHash (table : Fin (2 ^ 40) → Block × Block) :
    TagOnly (tableHash table) (tableAnswers table) := by
  intro label tag _
  unfold tableHash tableAnswers
  congr 1
  exact Fin.ext (by show hashInput label tag / 2 ^ 128 % 2 ^ 40 = tag % 2 ^ 40; rw [hashInput_div])

theorem hLabel_tagOnly {H : HashN} {A : Nat → Block × Block} (hH : TagOnly H A) (label : Label) (tag : Nat)
    (small : tag < 2 ^ 40) : hLabel H label tag = clip (A tag).1 := by
  unfold hLabel h128
  rw [hH _ _ small]

/-! ### The chunk joins -/

/-- The chunk-tree material of slot `s` of level `n` of chunk `c` of coordinate `coord`, at a tag-only hash. -/
def material (A : Nat → Block × Block) (coord c n s : Nat) : Label := clip (A (chunkTreeTag coord c n s)).1

/-- The XOR of the tree materials of level `n` of chunk `c`. -/
def levelSum (A : Nat → Block × Block) (coord c n : Nat) : Label :=
  xorFold fun s : Fin (2 ^ n) => material A coord c n s.val

/-- **The chunk joins at a tag-only hash**: `J_{c,n} = levelSum ⊕ clip Z_{8c+n}`. -/
theorem chunkJoin_tagOnly {H : HashN} {A : Nat → Block × Block} (hH : TagOnly H A) (T : CrtTable)
    (S coord : Nat) (Δ : Label) (Z : Nat → Label) (c n : Nat) (hc : c < T.chunkCount) (lower : 1 ≤ n)
    (upper : n < T.chunkWidth c) (small : ∀ s, s < 2 ^ n → chunkTreeTag coord c n s < 2 ^ 40) :
    ((coordGarbleM T S coord Δ Z).eval H).pub.chunkJoin c n = levelSum A coord c n ^^^ Z (T.chunkOffset c + n) := by
  obtain ⟨fJ, -⟩ := SliceC.coordGarbleM_fields H T S coord Δ Z
  rw [fJ c, SliceC.atNat_of_lt _ _ hc]
  simp only [chunkGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]
  rw [SliceC.treeGarbleM_levelSum H _ Δ _ _ n lower upper]
  unfold levelSum material
  congr 1
  congr 1
  funext s
  exact hLabel_tagOnly hH _ _ (small s.val s.isLt)

/-! ### The actual zero labels -/

/-- **The actual zero label** of bit `j` of coordinate `coord` at a tag-only hash, from the coins' zero label
`Z`: `Z` at a chunk's first bit, else `Z` with its low part replaced by the level sum. -/
def actualZero (A : Nat → Block × Block) (coord : Nat) (Z : Block) (j : Nat) : Block :=
  if j % 8 = 0 then Z else setLow Z (levelSum A coord (j / 8) (j % 8))

/-- The actual zero labels of both coordinates. -/
def actualZeros (A : Nat → Block × Block) (Z : KeyZeros) : KeyZeros :=
  fun κ j => actualZero A κ.val (Z κ j) j.val

theorem table_chunkBits : Entry.table.chunkBits = 8 := rfl

theorem table_chunkCount : Entry.table.chunkCount = 32 := by decide

theorem table_chunkWidth (c : Nat) : Entry.table.chunkWidth c = min 8 (254 - 8 * c) := rfl

/-- Bit `j < 254` is bit `j % 8` of chunk `j / 8`, which is in range. -/
theorem bit_in_chunk (j : Nat) (low : j < 254) :
    j / 8 < Entry.table.chunkCount ∧ j % 8 < Entry.table.chunkWidth (j / 8) ∧
      Entry.table.chunkOffset (j / 8) + j % 8 = j := by
  rw [table_chunkCount, table_chunkWidth]
  refine ⟨by omega, by omega, ?_⟩
  show 8 * (j / 8) + j % 8 = j
  omega

/-- The real table's chunk-tree tags are below `2 ^ 40`. -/
theorem chunkTreeTag_small (coord : Nat) (hc : coord < 2) (j : Nat) (low : j < 254) (s : Nat)
    (hs : s < 2 ^ (j % 8)) : chunkTreeTag coord (j / 8) (j % 8) s < 2 ^ 40 := by
  have small : 2 ^ (j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have : s < 128 := lt_of_lt_of_le hs (by simpa using small)
  unfold chunkTreeTag tagCode Family.chunkTree
  omega

theorem zeroOf_x (coins : Coins) : zeroOf coins 0 = coins.inputZero .x := rfl

theorem zeroOf_y (coins : Coins) : zeroOf coins 1 = coins.inputZero .y := rfl

/-- The `x` coordinate's chunk join at a non-first bit, at a tag-only hash. (Stated through an explicit
unfolding of `gxOf`: letting the elaborator unfold it inside the projection evaluates the garbler.) -/
theorem gxOf_chunkJoin {H : HashN} {A : Nat → Block × Block} (hH : TagOnly H A) (coins : Coins)
    (j : Fin coordinateBitCount) (first : ¬ j.val % 8 = 0) :
    (EntryCorrect.gxOf H coins).pub.chunkJoin (j.val / 8) (j.val % 8) =
      levelSum A 0 (j.val / 8) (j.val % 8) ^^^ clip (coins.inputZero .x j) := by
  obtain ⟨hc, upper, offset⟩ := bit_in_chunk j.val j.isLt
  have lower : 1 ≤ j.val % 8 := by omega
  have key := chunkJoin_tagOnly hH Entry.table xCount 0 (clip (coins.inputDelta .x))
    (fun j => clip (atNat (coins.inputZero .x) 0 j)) _ _ hc lower upper
    (chunkTreeTag_small 0 (by decide) j.val j.isLt)
  have unfoldG : EntryCorrect.gxOf H coins = (coordGarbleM Entry.table xCount 0 (clip (coins.inputDelta .x))
    (fun j => clip (atNat (coins.inputZero .x) 0 j))).eval H := rfl
  rw [unfoldG, key, offset, SliceC.atNat_of_lt _ _ j.isLt]

/-- The `y` coordinate's chunk join at a non-first bit, at a tag-only hash. -/
theorem gyOf_chunkJoin {H : HashN} {A : Nat → Block × Block} (hH : TagOnly H A) (coins : Coins)
    (j : Fin coordinateBitCount) (first : ¬ j.val % 8 = 0) :
    (EntryCorrect.gyOf H coins).pub.chunkJoin (j.val / 8) (j.val % 8) =
      levelSum A 1 (j.val / 8) (j.val % 8) ^^^ clip (coins.inputZero .y j) := by
  obtain ⟨hc, upper, offset⟩ := bit_in_chunk j.val j.isLt
  have lower : 1 ≤ j.val % 8 := by omega
  have key := chunkJoin_tagOnly hH Entry.table yCount 1 (clip (coins.inputDelta .y))
    (fun j => clip (atNat (coins.inputZero .y) 0 j)) _ _ hc lower upper
    (chunkTreeTag_small 1 (by decide) j.val j.isLt)
  have unfoldG : EntryCorrect.gyOf H coins = (coordGarbleM Entry.table yCount 1 (clip (coins.inputDelta .y))
    (fun j => clip (atNat (coins.inputZero .y) 0 j))).eval H := rfl
  rw [unfoldG, key, offset, SliceC.atNat_of_lt _ _ j.isLt]

/-- **The garbler's actual zero labels at a tag-only hash are `actualZeros`.** -/
theorem keyZero_tagOnly {H : HashN} {A : Nat → Block × Block} (hH : TagOnly H A) (coins : Coins) :
    EntryCorrect.keyZero H coins = actualZeros A (zeroOf coins) := by
  funext κ j
  unfold EntryCorrect.keyZero keyZeroOf absorbedOf actualZeros actualZero CrtTable.chunkShift
  rw [table_chunkBits]
  by_cases first : j.val % 8 = 0
  · rw [if_pos first, if_pos first, show embed (0 : Label) = 0 from Narrow.embed_zero, raw_xor_zero]
  · rw [if_neg first, if_neg first]
    by_cases hκ : κ = 0
    · subst hκ
      rw [if_pos rfl, gxOf_chunkJoin hH coins j first, zeroOf_x]
      exact xor_embed_eq_setLow _ _
    · have one : κ = 1 := by omega
      subst one
      rw [if_neg hκ, gyOf_chunkJoin hH coins j first, zeroOf_y]
      exact xor_embed_eq_setLow _ _

/-- **The garbler's returned key at a tag-only hash**: the pairs of the actual zero labels. -/
theorem keyOf_tagOnly {H : HashN} {A : Nat → Block × Block} (hH : TagOnly H A) (coins : Coins) :
    EntryCorrect.keyOf H coins = keyOfZeros (actualZeros A (zeroOf coins)) (deltaOf coins) := by
  unfold EntryCorrect.keyOf
  rw [keyZero_tagOnly hH]

/-! ### Selected labels -/

/-- The selected labels of zero labels `Z` and offsets `Δ` at `u`: `Z_j ⊕ u_j Δ`, `x` then `y` (the form of
`Entry.labels` on a source, and of the chain's `LabelsSplitProof.labelsFrom`). -/
def sourceLabels (Z : KeyZeros) (Δ : Fin 2 → Block) (input : AffineInput) : GarbledCircuit.LamportSignature :=
  Vector.ofFn fun index =>
    if inRange : index.val < coordinateBitCount then
      let position : Fin coordinateBitCount := ⟨index.val, inRange⟩
      if input.x.val.testBit index.val then Z 0 position ^^^ Δ 0 else Z 0 position
    else
      let position : Fin coordinateBitCount := ⟨index.val - coordinateBitCount, by
        have := index.isLt; simp only [coordinateBitCount] at *; omega⟩
      if input.y.val.testBit position.val then Z 1 position ^^^ Δ 1 else Z 1 position

/-- The source's labels are the source-form labels of its zeros and deltas. -/
theorem labels_source (source : Source) (input : AffineInput) :
    Entry.labels source input = sourceLabels source.zeros source.deltas input := rfl

theorem getElem_eq_getD (labels : GarbledCircuit.LamportSignature) (i : Nat) (hi : i < 508) :
    labels[i] = labels.toArray.getD i 0 := by
  simp [Array.getD, hi]

/-- **The selected labels of every key of the form `keyOfZeros Z Δ` are the source-form labels.** -/
theorem selectedLabels_keyOfZeros (Z : KeyZeros) (Δ : Fin 2 → Block) (input : AffineInput) :
    Lamport.selectedLabels ((keyOfZeros Z Δ).encode (BitInput.ofAffine input)) = sourceLabels Z Δ input := by
  apply Vector.ext
  intro i hi
  rw [getElem_eq_getD _ i hi]
  simp only [sourceLabels, Vector.getElem_ofFn]
  by_cases low : i < coordinateBitCount
  · rw [dif_pos low]
    have hx := EntryDelivery.labelX_honest (keyOfZeros Z Δ) (Z 0) (Δ 0) (EntryDelivery.keyOfZeros_x Z Δ)
      input i low
    unfold Entry.labelX at hx
    rw [hx]
    simp only [atNat, dif_pos low]
    split <;> simp
  · rw [dif_neg low]
    have bound : i - coordinateBitCount < 254 := by
      change i < 508 at hi
      simp only [coordinateBitCount] at low ⊢
      omega
    have hy := EntryDelivery.labelY_honest (keyOfZeros Z Δ) (Z 1) (Δ 1) (EntryDelivery.keyOfZeros_y Z Δ)
      input (i - coordinateBitCount) bound
    unfold Entry.labelY at hy
    rw [show coordinateBitCount + (i - coordinateBitCount) = i by simp only [coordinateBitCount] at low ⊢; omega]
      at hy
    rw [hy]
    simp only [atNat, dif_pos bound]
    split <;> simp

/-- **The selected labels of the real garbling at a tag-only hash**: the source-form labels of the actual
zero labels and the coins' offsets. -/
theorem labelsFor_tagOnly {H : HashN} {A : Nat → Block × Block} (hH : TagOnly H A) (coins : Coins)
    (input : AffineInput) :
    EntryCorrect.labelsFor H coins input = sourceLabels (actualZeros A (zeroOf coins)) (deltaOf coins) input := by
  unfold EntryCorrect.labelsFor
  rw [keyOf_tagOnly hH]
  exact selectedLabels_keyOfZeros _ _ input

/-- The scheme's key selection at a tag-only hash (the chain's `tapeLabels`, before the table reduction). -/
theorem scheme_encode_tagOnly [FieldCertificate] [GroupCertificate] {H : HashN} {A : Nat → Block × Block}
    (hH : TagOnly H A) (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput) :
    (Entry.scheme).encode ((garbleCM scalar coins).eval H).2 input =
      sourceLabels (actualZeros A (zeroOf coins)) (deltaOf coins) input := by
  rw [EntryCorrect.garbleCM_eval]
  exact labelsFor_tagOnly hH coins input

end Kriterion.CRT.Privacy.NoJoins
