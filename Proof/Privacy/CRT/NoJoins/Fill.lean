/-
**No chunk joins in the chain: the hot chunk-tree positions of the tag table.**

At an input `u`, `hotPos u (κ, j)` is the hot chunk-tree tag of coordinate bit `j`: level `j % 8` of chunk `j / 8` at
the evaluator's active slot (`hotSlot`); for a chunk's first bit it is the level-`0` tag at slot `0`, which no
program asks. These 508 positions are distinct (`hotPos_injective`), hot family-`0` tags (`hotPos_family`,
`hotPos_hot`), and away from every pad and mask site (`hotPos_away`), so the swapped table law refills them
uniformly (`HiddenGuess.swappedTableLaw_fill`).

On a table whose hot chunk-tree positions are filled with `f` (`fillAt (hotPos u) f A`), the level sum of a non-first
bit is `clip (f (κ, j)).1 ⊕ coldSum A u κ j` (`levelSum_fillAt`), so the actual zero labels are the first component
of `keysEquiv firstFlag (coldSum A u)` at `(Z, f)` (`actualZeros_fillAt`), and so are the real selected labels of the
scheme on the table oracle (`encode_fillAt`).
-/

import Proof.Privacy.CRT.NoJoins.Law
import Proof.Privacy.CRT.Hidden.GuessCore
import Proof.Privacy.CRT.Core.ConvAsks
import Proof.Privacy.CRT.Core.ConvSplit

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.NoJoins

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.HiddenGuess (fillAt fillAt_comp fillAt_apply_of_not_mem)

/-! ### The hot chunk-tree positions -/

/-- The hot chunk-tree tag of bit `j` of coordinate `κ` at `u` (level `0`, slot `0` for a chunk's first bit). -/
def hotTagOf (u : AffineInput) (κ : Fin 2) (j : Bits) : Nat :=
  chunkTreeTag κ.val (j.val / 8) (j.val % 8) (hotSlot u κ j)

theorem hotTagOf_lt (u : AffineInput) (κ : Fin 2) (j : Bits) : hotTagOf u κ j < 2 ^ 40 :=
  chunkTreeTag_lt κ j _ (hotSlot_lt u κ j)

/-- The hot chunk-tree positions at `u`. -/
def hotPos (u : AffineInput) (p : Fin 2 × Bits) : Fin (2 ^ 40) := ⟨hotTagOf u p.1 p.2, hotTagOf_lt u p.1 p.2⟩

theorem hotTagOf_inRange (u : AffineInput) (κ : Fin 2) (j : Bits) :
    TagInRange κ.val (j.val / 8) 0 (j.val % 8) (hotSlot u κ j) 0 :=
  chunkTreeTag_inRange κ j _ (hotSlot_lt u κ j)

/-- A chunk-tree tag of the real table at `(κ, j)` and a slot below `2 ^ (j % 8)` determines `(κ, j)` and the slot. -/
theorem chunkTreeTag_inj {κ κ' : Fin 2} {j j' : Bits} {s s' : Nat} (hs : s < 2 ^ (j.val % 8))
    (hs' : s' < 2 ^ (j'.val % 8))
    (same : chunkTreeTag κ.val (j.val / 8) (j.val % 8) s = chunkTreeTag κ'.val (j'.val / 8) (j'.val % 8) s') :
    κ = κ' ∧ j = j' ∧ s = s' := by
  obtain ⟨-, hc, hi, -, hl, hsl, -⟩ := tagCode_injective (chunkTreeTag_inRange κ j s hs)
    (chunkTreeTag_inRange κ' j' s' hs') same
  refine ⟨Fin.ext hc, Fin.ext ?_, hsl⟩
  omega

theorem hotPos_injective (u : AffineInput) : Function.Injective (hotPos u) := by
  rintro ⟨κ, j⟩ ⟨κ', j'⟩ same
  have e : hotTagOf u κ j = hotTagOf u κ' j' := congrArg Fin.val same
  obtain ⟨hκ, hj, -⟩ := chunkTreeTag_inj (hotSlot_lt u κ j) (hotSlot_lt u κ' j') e
  rw [hκ, hj]

theorem hotPos_family (u : AffineInput) (p : Fin 2 × Bits) : tagFamily (hotPos u p).val = 0 :=
  tagFamily_tagCode (hotTagOf_inRange u p.1 p.2)

theorem hotPos_hot (u : AffineInput) (p : Fin 2 × Bits) : hotTag Entry.table u (hotPos u p).val = true := by
  have range := hotTagOf_inRange u p.1 p.2
  have fam : tagFamily (chunkTreeTag p.1.val (p.2.val / 8) (p.2.val % 8) (hotSlot u p.1 p.2)) = 0 :=
    tagFamily_tagCode range
  have coord : tagCoord (chunkTreeTag p.1.val (p.2.val / 8) (p.2.val % 8) (hotSlot u p.1 p.2)) = p.1.val :=
    tagCoord_tagCode range
  have idx : tagIdx (chunkTreeTag p.1.val (p.2.val / 8) (p.2.val % 8) (hotSlot u p.1 p.2)) = p.2.val / 8 :=
    tagIdx_tagCode range
  have level : tagLevel (chunkTreeTag p.1.val (p.2.val / 8) (p.2.val % 8) (hotSlot u p.1 p.2)) = p.2.val % 8 :=
    tagLevel_tagCode range
  have slot : tagSlot (chunkTreeTag p.1.val (p.2.val / 8) (p.2.val % 8) (hotSlot u p.1 p.2)) = hotSlot u p.1 p.2 :=
    tagSlot_tagCode range
  show hotTag Entry.table u (chunkTreeTag p.1.val (p.2.val / 8) (p.2.val % 8) (hotSlot u p.1 p.2)) = true
  unfold hotTag
  simp only [fam, coord, idx, level, slot]
  unfold hotSlot
  exact beq_self_eq_true _

/-- A site tag is not a hot chunk-tree position (sites have families `6` and `7`). -/
theorem site_ne_hotPos (u : AffineInput) (p : Fin 2 × Bits) {fam coord idx stage level slot part : ℕ}
    (hf : 5 < fam) (hf16 : fam < 16) (hin : TagInRange coord idx stage level slot part) :
    tagPos (tagCode fam coord idx stage level slot part) ≠ hotPos u p := by
  intro heq
  have h1 := Asks.tagCode_lt hf16 hin
  have e := congrArg Fin.val heq
  simp only [tagPos] at e
  rw [Nat.mod_eq_of_lt h1] at e
  have f1 := tagFamily_tagCode (fam := fam) hin
  rw [e, hotPos_family u p] at f1
  omega

/-- **The hot chunk-tree positions lie away from every pad and mask site.** -/
theorem hotPos_away (u : AffineInput) :
    ∀ site ∈ crtLayout.sites, ∀ p : Fin 2 × Bits, hotPos u p ∉ (siteTags crtLayout site).map tagPos := by
  intro site mem p hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  rcases List.mem_append.mp mem with pad | mask
  · obtain ⟨κ', i, ρ, rfl, hκ', hi, hρ⟩ := Layout.mem_padSites pad
    obtain ⟨-, -, -, -, hm, hq⟩ := Layout.tableFacts κ' hκ' i hi
    simp only [siteTags, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have hj' : j < Layout.padCount κ' i := hj
    exact site_ne_hotPos u p (by decide) (by decide) ⟨hκ', by omega, by omega, by omega, by omega, by omega⟩ heq
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 2 := hj
      exact site_ne_hotPos u p (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        heq
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 3 := hj
      exact site_ne_hotPos u p (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        heq

/-! ### The level sums on a filled table -/

/-- The answer at a chunk-tree tag of a non-first bit on a table filled at the hot positions. -/
theorem material_fillAt (u : AffineInput) (f : Fin 2 × Bits → Block × Block) (A : TagTable) (κ : Fin 2) (j : Bits)
    (first : ¬ j.val % 8 = 0) (s : Nat) (hs : s < 2 ^ (j.val % 8)) :
    material (tableAnswers (fillAt (hotPos u) f A)) κ.val (j.val / 8) (j.val % 8) s =
      if s = hotSlot u κ j then clip (f (κ, j)).1 else material (tableAnswers A) κ.val (j.val / 8) (j.val % 8) s := by
  have small := chunkTreeTag_lt κ j s hs
  unfold material tableAnswers
  simp only [Nat.mod_eq_of_lt small]
  by_cases hot : s = hotSlot u κ j
  · rw [if_pos hot]
    subst hot
    have at_ : (⟨chunkTreeTag κ.val (j.val / 8) (j.val % 8) (hotSlot u κ j), small⟩ : Fin (2 ^ 40)) = hotPos u (κ, j) :=
      rfl
    rw [at_]
    exact congrArg (fun a => clip a.1) (congrFun (fillAt_comp (hotPos u) (hotPos_injective u) f A) (κ, j))
  · rw [if_neg hot, fillAt_apply_of_not_mem]
    rintro ⟨⟨κ', j'⟩, e⟩
    have ev : hotTagOf u κ' j' = chunkTreeTag κ.val (j.val / 8) (j.val % 8) s := congrArg Fin.val e
    obtain ⟨hκ, hj, hsl⟩ := chunkTreeTag_inj (hotSlot_lt u κ' j') hs ev
    subst hκ hj
    exact hot hsl.symm

/-- **The level sum of a non-first bit on a filled table**: the filled answer's material XOR the cold XOR. -/
theorem levelSum_fillAt (u : AffineInput) (f : Fin 2 × Bits → Block × Block) (A : TagTable) (κ : Fin 2) (j : Bits)
    (first : ¬ j.val % 8 = 0) :
    levelSum (tableAnswers (fillAt (hotPos u) f A)) κ.val (j.val / 8) (j.val % 8) =
      clip (f (κ, j)).1 ^^^ coldSum A u κ j := by
  let hot : Fin (2 ^ (j.val % 8)) := ⟨hotSlot u κ j, hotSlot_lt u κ j⟩
  unfold levelSum
  rw [← SliceC.xorFoldExcept_xor hot]
  have atHot : material (tableAnswers (fillAt (hotPos u) f A)) κ.val (j.val / 8) (j.val % 8) hot.val =
      clip (f (κ, j)).1 := by
    rw [material_fillAt u f A κ j first hot.val hot.isLt, if_pos rfl]
  have cold : xorFoldExcept hot (fun s : Fin (2 ^ (j.val % 8)) =>
      material (tableAnswers (fillAt (hotPos u) f A)) κ.val (j.val / 8) (j.val % 8) s.val) = coldSum A u κ j := by
    unfold coldSum
    refine SliceC.xorFoldExcept_congr _ _ _ fun s off => ?_
    rw [material_fillAt u f A κ j first s.val s.isLt, if_neg]
    intro same
    exact off (Fin.ext same)
  rw [atHot, cold]
  exact BitVec.xor_comm _ _

/-- The cold XOR does not read the hot positions. -/
theorem coldSum_fillAt (u : AffineInput) (f : Fin 2 × Bits → Block × Block) (A : TagTable) (κ : Fin 2) (j : Bits)
    (first : ¬ j.val % 8 = 0) : coldSum (fillAt (hotPos u) f A) u κ j = coldSum A u κ j := by
  unfold coldSum
  refine SliceC.xorFoldExcept_congr _ _ _ fun s off => ?_
  rw [material_fillAt u f A κ j first s.val s.isLt, if_neg]
  intro same
  exact off (Fin.ext same)

/-- **The actual zero labels on a filled table** are the first component of `keysEquiv` at `(Z, f)`. -/
theorem actualZeros_fillAt (u : AffineInput) (f : Fin 2 × Bits → Block × Block) (A : TagTable) (Z : KeyZeros) :
    actualZeros (tableAnswers (fillAt (hotPos u) f A)) Z =
      (keysEquiv firstFlag (coldSum A u) (Z, fun κ j => f (κ, j))).1 := by
  funext κ j
  rw [keysEquiv_fst]
  unfold actualZeros actualZero firstFlag
  by_cases first : j.val % 8 = 0
  · rw [if_pos first, if_pos (decide_eq_true first)]
  · rw [if_neg first, if_neg (by simpa using first), levelSum_fillAt u f A κ j first]

/-! ### The actual zero labels read the chunk-tree answers only -/

/-- The actual zero labels read the table only at the chunk-tree tags of the coordinates' bits. -/
theorem actualZeros_congr {A A' : Nat → Block × Block}
    (agree : ∀ (κ : Fin 2) (j : Bits) (s : Nat), s < 2 ^ (j.val % 8) →
      A (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s) = A' (chunkTreeTag κ.val (j.val / 8) (j.val % 8) s))
    (Z : KeyZeros) : actualZeros A Z = actualZeros A' Z := by
  funext κ j
  unfold actualZeros actualZero
  split
  · rfl
  · have sums : levelSum A κ.val (j.val / 8) (j.val % 8) = levelSum A' κ.val (j.val / 8) (j.val % 8) := by
      unfold levelSum material
      congr 1
      funext s
      rw [agree κ j s.val s.isLt]
    rw [sums]

/-- Two tag tables that agree at every family-`0` tag give the same actual zero labels. -/
theorem actualZeros_family0 {t t' : TagTable} (agree : ∀ p : Fin (2 ^ 40), tagFamily p.val = 0 → t p = t' p)
    (Z : KeyZeros) : actualZeros (tableAnswers t) Z = actualZeros (tableAnswers t') Z := by
  refine actualZeros_congr (fun κ j s hs => ?_) Z
  have small := chunkTreeTag_lt κ j s hs
  unfold tableAnswers
  simp only [Nat.mod_eq_of_lt small]
  exact agree _ (tagFamily_tagCode (chunkTreeTag_inRange κ j s hs))

/-! ### The scheme on the table oracle -/

/-- The scheme's hash of the table oracle answers small labelled inputs by tag. -/
theorem tagOnly_schemeHash (A : TagTable) :
    TagOnly (schemeHash (tableOracle (FI := Empty) (EI := Empty) A)) (tableAnswers A) := by
  intro label tag small
  rw [Asks.schemeHash_small A _ (Asks.hashInput_small label tag small)]
  show A ⟨hashInput label tag / 2 ^ 128 % 2 ^ 40, _⟩ = A ⟨tag % 2 ^ 40, _⟩
  congr 1
  exact Fin.ext (by show hashInput label tag / 2 ^ 128 % 2 ^ 40 = tag % 2 ^ 40; rw [hashInput_div])

section Real

variable [FieldCertificate] [GroupCertificate]

/-- **The real selected labels** of the scheme on the table oracle of a table filled at the hot positions. -/
theorem encode_fillAt (scalar : NonZeroScalar) (coins : Coins) (u : AffineInput)
    (f : Fin 2 × Bits → Block × Block) (A : TagTable) :
    (Entry.scheme).encode ((garbleCM scalar coins).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) (fillAt (hotPos u) f A)))).2 u =
      sourceLabels (keysEquiv firstFlag (coldSum A u) (zeroOf coins, fun κ j => f (κ, j))).1 (deltaOf coins) u := by
  rw [scheme_encode_tagOnly (tagOnly_schemeHash _), actualZeros_fillAt]

/-- The real selected labels of the scheme on the table oracle of any table. -/
theorem encode_table (scalar : NonZeroScalar) (coins : Coins) (u : AffineInput) (A : TagTable) :
    (Entry.scheme).encode ((garbleCM scalar coins).eval
        (schemeHash (tableOracle (FI := Empty) (EI := Empty) A))).2 u =
      sourceLabels (actualZeros (tableAnswers A) (zeroOf coins)) (deltaOf coins) u :=
  scheme_encode_tagOnly (tagOnly_schemeHash _) scalar coins u

end Real

end Kriterion.CRT.Privacy.NoJoins
