/-
**No chunk joins, the labels of the `Δ` fine view** (for `Hidden/DeltaView.lean`).

* `selZ Z Δ u`: the selected label `Z ⊕ u_j Δ` of every coordinate bit. The source-form labels determine it and are
  determined by it (`selZ_of_labels`, `labels_of_selZ`).
* **One coordinate's hot chunk-tree positions** `hotPosOf u κ` (injective, away from the sites): filling them
  changes the actual zero labels of `κ` at the non-first bits only, to `setLow Z (clip f ⊕ cold)`
  (`actualZeros_fillOne`).
* **The relabelling of `Δ_κ`** (`selZ_fillOne_shift`): two coins with the same selected coin labels of `κ` at `u` and
  the same keys off `κ` give, on a filled table, the same selected actual labels once the hot answers are shifted by
  `u_j · clip (Δ_κ ⊕ Δ'_κ)` (`shiftEquiv`, an involution). So the law of the selected actual labels given the coin
  labels of `u` and the cold table does not depend on `Δ_κ`.
* **The chunk joins through the labels** (`clip_selZ_actual`): at a non-first bit the low part of the selected actual
  label XOR the low part of the selected coin label is `levelSum ⊕ clip Z`, the chunk join.
-/

import Proof.Privacy.CRT.NoJoins.Fill

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.NoJoins

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy Kriterion.CRT.Narrow
open Kriterion.CRT.Privacy.HiddenGuess (fillAt fillAt_comp fillAt_apply_of_not_mem fillAt_self)

/-! ### Selected labels per coordinate bit -/

/-- The selected labels of zero labels `Z` and offsets `Δ` at `u`, per coordinate bit: `Z ⊕ u_j Δ`. -/
def selZ (Z : KeyZeros) (Δ : Fin 2 → Block) (u : AffineInput) : KeyZeros := fun κ j => Z κ j ^^^ deltaMask Δ u κ j

theorem selZ_apply (Z : KeyZeros) (Δ : Fin 2 → Block) (u : AffineInput) (κ : Fin 2) (j : Bits) :
    selZ Z Δ u κ j = if bitOf u κ j then Z κ j ^^^ Δ κ else Z κ j := by
  unfold selZ deltaMask
  split
  · rfl
  · exact BitVec.xor_zero

theorem sourceLabels_eq_selZ (Z : KeyZeros) (Δ : Fin 2 → Block) (u : AffineInput) :
    sourceLabels Z Δ u = sourceLabels (selZ Z Δ u) 0 u :=
  sourceLabels_shift Z Δ u

/-- The source-form labels with zero offsets are injective in the zero labels. -/
theorem sourceLabels_zero_injective (u : AffineInput) {Z Z' : KeyZeros}
    (same : sourceLabels Z 0 u = sourceLabels Z' 0 u) : Z = Z' := by
  funext κ j
  have hx : ∀ W : KeyZeros, (sourceLabels W 0 u)[j.val]'(by omega) = W 0 j := by
    intro W
    simp only [sourceLabels, Vector.getElem_ofFn]
    rw [dif_pos j.isLt]
    split
    · exact BitVec.xor_zero
    · rfl
  have hy : ∀ W : KeyZeros, (sourceLabels W 0 u)[coordinateBitCount + j.val]'(by
      have := j.isLt; simp only [coordinateBitCount] at *; omega) = W 1 j := by
    intro W
    simp only [sourceLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    have pos : (⟨coordinateBitCount + j.val - coordinateBitCount, by
        have := j.isLt; simp only [coordinateBitCount] at *; omega⟩ : Fin coordinateBitCount) = j :=
      Fin.ext (by simp only [coordinateBitCount]; omega)
    simp only [pos]
    split
    · exact BitVec.xor_zero
    · rfl
  by_cases zero : κ = 0
  · subst zero
    rw [← hx Z, ← hx Z', same]
  · have one : κ = 1 := by omega
    subst one
    rw [← hy Z, ← hy Z', same]

theorem selZ_of_labels {Z Z' : KeyZeros} {Δ Δ' : Fin 2 → Block} {u : AffineInput}
    (same : sourceLabels Z Δ u = sourceLabels Z' Δ' u) : selZ Z Δ u = selZ Z' Δ' u := by
  rw [sourceLabels_eq_selZ, sourceLabels_eq_selZ Z'] at same
  exact sourceLabels_zero_injective u same

theorem labels_of_selZ {Z Z' : KeyZeros} {Δ Δ' : Fin 2 → Block} {u : AffineInput}
    (same : selZ Z Δ u = selZ Z' Δ' u) : sourceLabels Z Δ u = sourceLabels Z' Δ' u := by
  rw [sourceLabels_eq_selZ, sourceLabels_eq_selZ Z', same]

/-- Equal selected labels and equal offsets give equal zero labels. -/
theorem zero_of_selZ {Z Z' : KeyZeros} {Δ Δ' : Fin 2 → Block} {u : AffineInput} {κ : Fin 2} {j : Bits}
    (same : selZ Z Δ u κ j = selZ Z' Δ' u κ j) (delta : Δ κ = Δ' κ) : Z κ j = Z' κ j := by
  unfold selZ deltaMask at same
  rw [delta] at same
  have cancel := congrArg (· ^^^ (if bitOf u κ j then Δ' κ else 0)) same
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using cancel

/-! ### Low parts -/

theorem setLow_xor (x y : RawBlock) (l : Label) : setLow x l ^^^ y = setLow (x ^^^ y) (l ^^^ clip y) := by
  unfold setLow
  rw [clip_xor, embed_xor, embed_xor]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases (embed (clip x)).getLsbD i <;>
    cases (embed (clip y)).getLsbD i <;> cases (embed l).getLsbD i <;> rfl

/-- **The chunk join through the labels**: at a non-first bit, the low part of the selected actual label XOR the low
part of the selected coin label is the level sum XOR the low part of the zero label. -/
theorem clip_selZ_actual (Z Δ : RawBlock) (sum : Label) (b : Bool) :
    clip (setLow Z sum ^^^ (if b then Δ else 0)) ^^^ clip (Z ^^^ (if b then Δ else 0)) = sum ^^^ clip Z := by
  rw [clip_xor, clip_xor, clip_setLow]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases (clip Z).getLsbD i <;> cases (clip (if b then Δ else 0)).getLsbD i <;> cases sum.getLsbD i <;> rfl

/-! ### One coordinate's hot chunk-tree positions -/

/-- The hot chunk-tree positions of coordinate `κ` at `u`. -/
def hotPosOf (u : AffineInput) (κ : Fin 2) (j : Bits) : Fin (2 ^ 40) := hotPos u (κ, j)

theorem hotPosOf_injective (u : AffineInput) (κ : Fin 2) : Function.Injective (hotPosOf u κ) := fun j j' same =>
  congrArg Prod.snd (hotPos_injective u same)

theorem hotPosOf_away (u : AffineInput) (κ : Fin 2) :
    ∀ site ∈ crtLayout.sites, ∀ j, hotPosOf u κ j ∉ (siteTags crtLayout site).map tagPos :=
  fun site mem j => hotPos_away u site mem (κ, j)

theorem hotPos_coord (u : AffineInput) (p : Fin 2 × Bits) : tagCoord (hotPos u p).val = p.1.val :=
  tagCoord_tagCode (hotTagOf_inRange u p.1 p.2)

/-- Filling one coordinate's hot positions is filling all of them, the other coordinate's with the table's own
answers. -/
theorem fillAt_hotPosOf (u : AffineInput) (κ : Fin 2) (f : Bits → Block × Block) (A : TagTable) :
    fillAt (hotPosOf u κ) f A = fillAt (hotPos u) (fun p => if p.1 = κ then f p.2 else A (hotPos u p)) A := by
  funext i
  by_cases hit : ∃ p, hotPos u p = i
  · obtain ⟨⟨κ', j⟩, rfl⟩ := hit
    have right : fillAt (hotPos u) (fun p => if p.1 = κ then f p.2 else A (hotPos u p)) A (hotPos u (κ', j)) =
        if κ' = κ then f j else A (hotPos u (κ', j)) :=
      congrFun (fillAt_comp (hotPos u) (hotPos_injective u) _ A) (κ', j)
    rw [right]
    by_cases same : κ' = κ
    · subst same
      rw [if_pos rfl]
      exact congrFun (fillAt_comp (hotPosOf u κ') (hotPosOf_injective u κ') f A) j
    · rw [if_neg same]
      apply fillAt_apply_of_not_mem
      rintro ⟨j', e⟩
      exact same (congrArg Prod.fst (hotPos_injective u e)).symm
  · have off : i ∉ Set.range (hotPos u) := fun ⟨p, e⟩ => hit ⟨p, e⟩
    have off' : i ∉ Set.range (hotPosOf u κ) := fun ⟨j, e⟩ => hit ⟨(κ, j), e⟩
    rw [fillAt_apply_of_not_mem _ _ _ _ off, fillAt_apply_of_not_mem _ _ _ _ off']

/-- The actual zero labels of any table, through the key relabelling at the table's own hot answers. -/
theorem actualZeros_self (u : AffineInput) (A : TagTable) (Z : KeyZeros) :
    actualZeros (tableAnswers A) Z = (keysEquiv firstFlag (coldSum A u) (Z, fun κ j => A (hotPos u (κ, j)))).1 := by
  have filled := actualZeros_fillAt u (A ∘ hotPos u) A Z
  rwa [fillAt_self] at filled

/-- **The actual zero labels on a table with coordinate `κ`'s hot positions filled.** -/
theorem actualZeros_fillOne (u : AffineInput) (κ : Fin 2) (f : Bits → Block × Block) (A : TagTable) (Z : KeyZeros)
    (κ' : Fin 2) (j : Bits) :
    actualZeros (tableAnswers (fillAt (hotPosOf u κ) f A)) Z κ' j =
      if κ' = κ ∧ ¬ j.val % 8 = 0 then setLow (Z κ' j) (clip (f j).1 ^^^ coldSum A u κ' j)
      else actualZeros (tableAnswers A) Z κ' j := by
  rw [fillAt_hotPosOf, actualZeros_fillAt, keysEquiv_fst, actualZeros_self u A Z, keysEquiv_fst]
  unfold firstFlag
  by_cases first : j.val % 8 = 0
  · simp only [first, decide_true, if_true, not_true_eq_false, and_false, if_false]
  · by_cases same : κ' = κ
    · subst same
      simp only [first, decide_false, Bool.false_eq_true, if_false, if_true, not_false_eq_true, and_self]
    · simp only [first, same, decide_false, Bool.false_eq_true, if_false, false_and]

/-- The selected actual labels on a table with coordinate `κ`'s hot positions filled. -/
theorem selZ_fillOne (u : AffineInput) (κ : Fin 2) (f : Bits → Block × Block) (A : TagTable) (Z : KeyZeros)
    (Δ : Fin 2 → Block) (κ' : Fin 2) (j : Bits) :
    selZ (actualZeros (tableAnswers (fillAt (hotPosOf u κ) f A)) Z) Δ u κ' j =
      if κ' = κ ∧ ¬ j.val % 8 = 0 then setLow (Z κ' j) (clip (f j).1 ^^^ coldSum A u κ' j) ^^^ deltaMask Δ u κ' j
      else selZ (actualZeros (tableAnswers A) Z) Δ u κ' j := by
  unfold selZ
  rw [actualZeros_fillOne]
  split <;> rfl

/-! ### The relabelling of `Δ_κ` -/

/-- Shift the hot answers of coordinate `κ` by `u_j · δ` in the low part of their first block. -/
def shiftAns (u : AffineInput) (κ : Fin 2) (δ : Label) (f : Bits → Block × Block) : Bits → Block × Block :=
  fun j => ((f j).1 ^^^ embed (if bitOf u κ j then δ else 0), (f j).2)

theorem shiftAns_shiftAns (u : AffineInput) (κ : Fin 2) (δ : Label) (f : Bits → Block × Block) :
    shiftAns u κ δ (shiftAns u κ δ f) = f := by
  funext j
  unfold shiftAns
  refine Prod.ext ?_ rfl
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The shift, an involution. -/
def shiftEquiv (u : AffineInput) (κ : Fin 2) (δ : Label) : (Bits → Block × Block) ≃ (Bits → Block × Block) where
  toFun := shiftAns u κ δ
  invFun := shiftAns u κ δ
  left_inv := shiftAns_shiftAns u κ δ
  right_inv := shiftAns_shiftAns u κ δ

/-- **The relabelling of `Δ_κ`**: coins with the same selected coin labels of `κ` at `u` and the same keys off `κ`
give the same selected actual labels once the hot answers of `κ` are shifted by `u_j · clip (Δ_κ ⊕ Δ'_κ)`. -/
theorem selZ_fillOne_shift (u : AffineInput) (κ : Fin 2) (A : TagTable) (Z Z' : KeyZeros) (Δ Δ' : Fin 2 → Block)
    (sameE : ∀ j, selZ Z Δ u κ j = selZ Z' Δ' u κ j) (otherZ : ∀ κ', κ' ≠ κ → Z κ' = Z' κ')
    (otherΔ : ∀ κ', κ' ≠ κ → Δ κ' = Δ' κ') (f : Bits → Block × Block) :
    selZ (actualZeros (tableAnswers (fillAt (hotPosOf u κ) f A)) Z') Δ' u =
      selZ (actualZeros (tableAnswers (fillAt (hotPosOf u κ) (shiftAns u κ (clip (Δ κ ^^^ Δ' κ)) f) A)) Z) Δ u := by
  funext κ' j
  rw [selZ_fillOne, selZ_fillOne]
  by_cases hot : κ' = κ ∧ ¬ j.val % 8 = 0
  · rw [if_pos hot, if_pos hot]
    obtain ⟨rfl, _⟩ := hot
    rw [setLow_xor, setLow_xor]
    have first : Z' κ' j ^^^ deltaMask Δ' u κ' j = Z κ' j ^^^ deltaMask Δ u κ' j := (sameE j).symm
    rw [first]
    congr 1
    unfold shiftAns deltaMask
    cases bitOf u κ' j
    · simp only [Bool.false_eq_true, if_false, embed_zero, clip_zero, raw_xor_zero, label_xor_zero]
    · simp only [if_true, clip_xor, clip_embed]
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_xor]
      cases (clip (f j).1).getLsbD i <;> cases (clip (Δ κ')).getLsbD i <;> cases (clip (Δ' κ')).getLsbD i <;>
        cases (coldSum A u κ' j).getLsbD i <;> rfl
  · rw [if_neg hot, if_neg hot]
    by_cases same : κ' = κ
    · subst same
      have first : j.val % 8 = 0 := by
        by_contra h
        exact hot ⟨rfl, h⟩
      unfold selZ actualZeros actualZero
      rw [if_pos first, if_pos first]
      exact (sameE j).symm
    · unfold selZ actualZeros deltaMask
      rw [otherZ κ' same, otherΔ κ' same]

end Kriterion.CRT.Privacy.NoJoins
