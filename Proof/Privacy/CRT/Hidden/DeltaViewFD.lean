/-
**H7's `Δ` residual, part 2: the stage-2 view is a function of the fine view**.

Two tapes with the same fine view (`DeltaView.fine`: coordinate `κ`'s published conversion material, the coins through
`u`'s labels, the table off the hot conversion tags of `κ`) have

* related garbler question lists (`gAsked_rel`): position by position the same tag, the same input off the `Shifted`
  tags, labels shifted by the tag-dependent `queryShift (Δ_κ ⊕ Δ'_κ)` on them (coordinate `κ` from `coord_relational`, the other
  coordinate by congruence, the tail from `TailRel`);
* the same stage-2 view (`view_fd`): the same published value, the same labels, the same designed entries (a designed
  tag is never `Shifted`, so its input is the same, and it is not a hot conversion tag, so its answer is the same).

With `DeltaView.fine_split` this gives `delta_guess_le`: an event that forces `Δ_κ` to a value fixed by the fine view
has conditional mass at most `2^-128` given the stage-2 view.

`coord_relational` and `TailRel` enter as hypotheses until their files merge.
-/

import Proof.Privacy.CRT.Hidden.DeltaView
import Proof.Privacy.CRT.Paths.SameVisible
import Proof.Privacy.CRT.Core.LabelUniform

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Kriterion.CRT.Privacy.DeltaView

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.Laws.LabelsSplitProof (LabelKeys coinKeys withKeys coinKeys_withKeys labelsFrom
  coordOf)
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_of_tagged tagInRange_of_key tagFamily_key)
open Kriterion.ArgoMAC.PlanB (digitCount)
open Kriterion.CRT.Privacy.Align (designTag)
open Kriterion.CRT.Privacy.HiddenGuess (outer_fine_le)
open scoped ENNReal

noncomputable section

/-! ### 1. `coord_relational`, as a hypothesis -/

/-- **`coord_relational`** (`Core/CoordRelational.lean`): two garblers of one
coordinate whose labels of `u` agree, whose published material agrees and whose hashes agree off the hot conversion
tags ask related lists and agree on everything but the material. -/
def CoordRelational : Prop :=
  ∀ (H₁ H₂ : HashN) (S coord : ℕ), S ≤ 1000 → coord < 2 → ∀ (u : AffineInput) (Δ₁ Δ₂ : Label) (Z₁ Z₂ : ℕ → Label),
    (∀ j < 254, Z₁ j ^^^ (if (coordValue u coord).testBit j then Δ₁ else 0) =
      Z₂ j ^^^ (if (coordValue u coord).testBit j then Δ₂ else 0)) →
    FlatLayout.ConvAgree Entry.table ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).pub
      ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).pub →
    (∀ (label₁ label₂ : Block) (τ : ℕ), τ < 2 ^ 40 →
      ¬ (tagFamily τ ≤ 5 ∧ tagCoord τ = coord ∧ hotTag Entry.table u τ = true) →
      H₁ (hashInput label₁ τ) = H₂ (hashInput label₂ τ)) →
    RelAskedConst (fun τ => hotTag Entry.table u τ = true) (embed (Δ₁ ^^^ Δ₂))
        (asked H₁ (coordGarbleM Entry.table S coord Δ₁ Z₁)) (asked H₂ (coordGarbleM Entry.table S coord Δ₂ Z₂)) ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).residue =
        ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).residue ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).padSum =
        ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).padSum ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).offset =
        ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).offset ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).hint =
        ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).hint

/-! ### 2. The garbler, cut into its coordinates and its tail -/

/-- Coordinate `x`'s garbler on the coins. -/
abbrev cxM (coins : Entry.Coins) : CM (CoordGarbled Entry.table Entry.xCount) :=
  coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))

/-- Coordinate `y`'s garbler on the coins. -/
abbrev cyM (coins : Entry.Coins) : CM (CoordGarbled Entry.table Entry.yCount) :=
  coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))

theorem garbleCM_asked (H : HashN) (scalar : NonZeroScalar) (coins : Entry.Coins) :
    asked H (Entry.garbleCM scalar coins) = asked H (cxM coins) ++ (asked H (cyM coins) ++ asked H (tailM scalar coins)) := by
  unfold Entry.garbleCM tailM
  simp only [asked_bind, asked_pure]

theorem garbleCM_eval (H : HashN) (scalar : NonZeroScalar) (coins : Entry.Coins) :
    (Entry.garbleCM scalar coins).eval H =
      (Entry.assemble scalar coins ((cxM coins).eval H) ((cyM coins).eval H) ((tailM scalar coins).eval H).1
        ((tailM scalar coins).eval H).2, coins.inputMacKey) := by
  unfold Entry.garbleCM tailM
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]

/-! ### 3. The two coordinates -/

/-- **A coordinate's garbler reads the table only at its own coordinate's tags.** -/
theorem coord_congr (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label) (t t' : TagTable)
    (agree : ∀ tag : Fin (2 ^ 40), tagCoord tag.val = coord → t tag = t' tag) :
    asked (hashOf t') (coordGarbleM Entry.table S coord Δ Z) = asked (hashOf t) (coordGarbleM Entry.table S coord Δ Z) ∧
      (coordGarbleM Entry.table S coord Δ Z).eval (hashOf t') =
        (coordGarbleM Entry.table S coord Δ Z).eval (hashOf t) := by
  refine Paths.SameVisible.asked_congr (hashOf t) (hashOf t') _ fun n inside => ?_
  obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
    (Paths.coordGarbleM_tagged Entry.table S coord (Paths.bn254_ranges S hS) hc Δ Z) (hashOf t) n inside
  rw [hashOf_hashInput t label k.code (Paths.TagKey.code_lt range),
    hashOf_hashInput t' label k.code (Paths.TagKey.code_lt range)]
  refine agree _ ?_
  show tagCoord k.code = coord
  rw [Paths.TagKey.code, tagCoord_tagCode (tagInRange_of_key range)]
  exact member.2

/-- The tags of a coordinate's garbler: coordinate `coord`, family at most 6, in range. -/
theorem coord_tags (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label) (H : HashN) :
    ∀ n ∈ asked H (coordGarbleM Entry.table S coord Δ Z),
      tagCoord (n / 2 ^ 128) = coord ∧ tagFamily (n / 2 ^ 128) ≤ 6 := by
  intro n inside
  obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
    (Paths.coordGarbleM_tagged Entry.table S coord (Paths.bn254_ranges S hS) hc Δ Z) H n inside
  rw [hashInput_tag]
  refine ⟨?_, ?_⟩
  · rw [Paths.TagKey.code, tagCoord_tagCode (tagInRange_of_key range)]
    exact member.2
  · rw [tagFamily_key range]
    exact member.1

/-- On a coordinate's tags, `Shifted` is `hotTag` at the coordinate `κ`, and false at the other coordinate. -/
theorem shifted_iff_hot {u : AffineInput} {κ : Fin 2} {τ : ℕ} (coord : tagCoord τ = κ.val) (fam : tagFamily τ ≤ 6) :
    Shifted u κ τ ↔ hotTag Entry.table u τ = true := by
  unfold Shifted
  constructor
  · rintro ⟨_, ⟨_, hot⟩ | ⟨eight, _⟩⟩
    · exact hot
    · omega
  · intro hot
    exact ⟨coord, Or.inl ⟨fam, hot⟩⟩

theorem not_shifted_of_coord {u : AffineInput} {κ : Fin 2} {τ : ℕ} (coord : tagCoord τ ≠ κ.val) : ¬ Shifted u κ τ :=
  fun shifted => coord shifted.1

/-- The label-selection identity of `coord_relational`'s first hypothesis. -/
theorem xor_ite (b : Bool) (Z Δ : Block) : Z ^^^ (if b then Δ else 0) = if b then Z ^^^ Δ else Z := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact BitVec.xor_zero
  · simp only [if_true]

theorem uBit_eq (u : AffineInput) (κ : Fin 2) (p : ℕ) : uBit u κ p = (coordValue u κ.val).testBit p := by
  unfold uBit coordValue
  by_cases h : κ.val = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- Two materials with the same flat vector agree on every index the evaluator reads. -/
theorem convAgree_of_convVector_eq {p q : ConvPublic} (same : Entry.convVector p = Entry.convVector q) :
    FlatLayout.ConvAgree Entry.table p q := by
  have hp := EntryDelivery.convAgree_convOf p
  have hq := EntryDelivery.convAgree_convOf q
  rw [same] at hp
  obtain ⟨p1, p2, p3⟩ := hp
  obtain ⟨q1, q2, q3⟩ := hq
  refine ⟨fun c hc n h1 h2 => (p1 c hc n h1 h2).symm.trans (q1 c hc n h1 h2),
    fun c hc k hk => (p2 c hc k hk).symm.trans (q2 c hc k hk), fun i row kind => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := p3 i row kind
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := q3 i row kind
  exact ⟨fun n h1 h2 => (a1 n h1 h2).symm.trans (b1 n h1 h2), fun n h1 h2 => (a2 n h1 h2).symm.trans (b2 n h1 h2),
    fun k hk => (a3 k hk).symm.trans (b3 k hk), fun k hk => (a4 k hk).symm.trans (b4 k hk),
    fun j h1 h2 => (a5 j h1 h2).symm.trans (b5 j h1 h2), fun j h1 h2 => (a6 j h1 h2).symm.trans (b6 j h1 h2)⟩

/-- Coordinate `i`'s garbler on the coins. -/
abbrev progM (S : ℕ) (i : Fin 2) (coins : Entry.Coins) : CM (CoordGarbled Entry.table S) :=
  coordGarbleM Entry.table S i.val (clip (coins.inputDelta (coordOf i))) (fun j => clip (atNat (coins.inputZero (coordOf i)) 0 j))

theorem cxM_eq (coins : Entry.Coins) : cxM coins = progM Entry.xCount 0 coins := rfl

theorem cyM_eq (coins : Entry.Coins) : cyM coins = progM Entry.yCount 1 coins := rfl

/-- Two coordinate garblings that the rest of the garbler cannot tell apart. -/
def GAgree {S : ℕ} (g g' : CoordGarbled Entry.table S) : Prop :=
  Entry.convVector g.pub = Entry.convVector g'.pub ∧ g.offset = g'.offset ∧ g.padSum = g'.padSum ∧ g.hint = g'.hint

/-- **One coordinate of two tapes with the same fine view.** -/
theorem coord_part (rel : CoordRelational) (u : AffineInput) (κ : Fin 2) {c c' : Entry.Coins} {t t' : TagTable}
    (sameC : eCoins u κ c = eCoins u κ c') (sameT : maskTable u κ t = maskTable u κ t') (S : ℕ) (hS : S ≤ 1000)
    (i : Fin 2)
    (hvec : i = κ → Entry.convVector ((progM S i c).eval (hashOf t)).pub =
      Entry.convVector ((progM S i c').eval (hashOf t')).pub) :
    RelAsked (Shifted u κ) (deltaAt κ c ^^^ deltaAt κ c') (asked (hashOf t) (progM S i c))
        (asked (hashOf t') (progM S i c')) ∧
      GAgree ((progM S i c).eval (hashOf t)) ((progM S i c').eval (hashOf t')) := by
  by_cases hi : i = κ
  · subst hi
    have vec := hvec rfl
    have hE : ∀ j < 254, atNat (c.inputZero (coordOf i)) 0 j ^^^
        (if (coordValue u i.val).testBit j then c.inputDelta (coordOf i) else 0) =
        atNat (c'.inputZero (coordOf i)) 0 j ^^^
          (if (coordValue u i.val).testBit j then c'.inputDelta (coordOf i) else 0) := by
      intro j hj
      have labels := congrFun (eLabel_eq sameC) ⟨j, hj⟩
      unfold eLabel at labels
      rw [uBit_eq] at labels
      unfold atNat
      rw [dif_pos hj, dif_pos hj, xor_ite, xor_ite]
      exact labels
    have hagree : ∀ (label₁ label₂ : Block) (τ : ℕ), τ < 2 ^ 40 →
        ¬ (tagFamily τ ≤ 5 ∧ tagCoord τ = i.val ∧ hotTag Entry.table u τ = true) →
        hashOf t (hashInput label₁ τ) = hashOf t' (hashInput label₂ τ) :=
      fun label₁ label₂ τ small cold => hash_agree sameT label₁ label₂ τ small cold
    have hEclip : ∀ j < 254, clip (atNat (c.inputZero (coordOf i)) 0 j) ^^^
        (if (coordValue u i.val).testBit j then clip (c.inputDelta (coordOf i)) else 0) =
        clip (atNat (c'.inputZero (coordOf i)) 0 j) ^^^
          (if (coordValue u i.val).testBit j then clip (c'.inputDelta (coordOf i)) else 0) := by
      intro j hj
      have h := congrArg clip (hE j hj)
      simpa only [Narrow.clip_xor, apply_ite clip, show clip (0 : Block) = 0 from Narrow.clip_zero] using h
    obtain ⟨relHot, _, hpad, hoff, hhint⟩ := rel (hashOf t) (hashOf t') S i.val hS i.isLt u _ _ _ _ hEclip
      (convAgree_of_convVector_eq vec) hagree
    have mixed : RelAsked (fun τ => hotTag Entry.table u τ = true)
        (deltaAt i c ^^^ deltaAt i c') (asked (hashOf t) (progM S i c))
        (asked (hashOf t') (progM S i c')) := by
      refine RelAsked.of_constant relHot fun n inside => ?_
      obtain ⟨_, fam⟩ := coord_tags S i.val hS i.isLt _ _ (hashOf t) n inside
      simp only [queryShift, if_pos fam, Narrow.clip_xor]
      rfl
    refine ⟨RelAsked.congr (fun n inside => ?_) mixed, vec, hoff, hpad, hhint⟩
    obtain ⟨coord, fam⟩ := coord_tags S i.val hS i.isLt _ _ (hashOf t) n inside
    exact (shifted_iff_hot coord fam).symm
  · have keys := keys_other sameC i hi
    have hZ : c.inputZero (coordOf i) = c'.inputZero (coordOf i) := keys.1
    have hΔ : c.inputDelta (coordOf i) = c'.inputDelta (coordOf i) := keys.2
    have prog : progM S i c = progM S i c' := by
      unfold progM
      rw [hZ, hΔ]
    rw [← prog]
    obtain ⟨askedSame, evalSame⟩ := coord_congr S i.val hS i.isLt (clip (c.inputDelta (coordOf i)))
      (fun j => clip (atNat (c.inputZero (coordOf i)) 0 j)) t t' fun tag coord =>
        table_agree sameT tag fun hot => hi (Fin.ext (coord.symm.trans hot.2.1))
    refine ⟨RelAsked.of_eq askedSame.symm fun n inside => ?_, ?_⟩
    · obtain ⟨coord, _⟩ := coord_tags S i.val hS i.isLt _ _ (hashOf t) n inside
      exact not_shifted_of_coord fun same => hi (Fin.ext (coord.symm.trans same))
    · rw [evalSame]
      exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### 4. The published value and the labels -/

theorem records_congr {S : ℕ} {g g' : CoordGarbled Entry.table S} (hpad : g.padSum = g'.padSum)
    (hhint : g.hint = g'.hint) : g.records = g'.records := by
  funext slopes
  unfold CoordGarbled.records CoordGarbled.join
  rw [hpad, hhint]

/-- **The assembly reads the coordinates only through what `GAgree` compares**, and the coins only off their label
keys. -/
theorem assemble_congr (scalar : NonZeroScalar) {c c' : Entry.Coins} (h1 : c.offsets = c'.offsets)
    (h2 : c.pointRandomness = c'.pointRandomness) (h3 : c.bridgeKey = c'.bridgeKey) (h4 : c.curveMask = c'.curveMask)
    (h5 : c.curveR1 = c'.curveR1) (h6 : c.curveR2 = c'.curveR2)
    {gx gx' : CoordGarbled Entry.table Entry.xCount} {gy gy' : CoordGarbled Entry.table Entry.yCount}
    (hx : GAgree gx gx') (hy : GAgree gy gy') (masks : MaskValues digitCount)
    (entries : Fin digitCount → Exception.Entry) :
    Entry.assemble scalar c gx gy masks entries = Entry.assemble scalar c' gx' gy' masks entries := by
  obtain ⟨vx, ox, px, tx⟩ := hx
  obtain ⟨vy, oy, py, ty⟩ := hy
  have rx := records_congr px tx
  have ry := records_congr py ty
  unfold Entry.assemble Entry.outputKeysOf
  rw [h1, h2, h3, h4, h5, h6, vx, vy, ox, oy, rx, ry]

/-- **The labels of `u` read the coordinate `κ`'s keys only through `u`'s labels.** -/
theorem labelsFrom_congr {u : AffineInput} {κ : Fin 2} {k k' : LabelKeys} (h1 : eLabel u κ k = eLabel u κ k')
    (h2 : ∀ i, i ≠ κ → k.1 i = k'.1 i ∧ k.2 i = k'.2 i) : labelsFrom k u = labelsFrom k' u := by
  unfold labelsFrom
  congr 1
  funext index
  by_cases low : index.val < coordinateBitCount
  · rw [dif_pos low, dif_pos low]
    by_cases hκ : κ = 0
    · subst hκ
      have same := congrFun h1 ⟨index.val, low⟩
      unfold eLabel uBit at same
      simpa using same
    · rw [(h2 0 (Ne.symm hκ)).1, (h2 0 (Ne.symm hκ)).2]
  · rw [dif_neg low, dif_neg low]
    by_cases hκ : κ = 1
    · subst hκ
      have bound : index.val - coordinateBitCount < coordinateBitCount := by
        have := index.isLt; simp only [coordinateBitCount] at *; omega
      have same := congrFun h1 ⟨index.val - coordinateBitCount, bound⟩
      unfold eLabel uBit at same
      simpa using same
    · rw [(h2 1 (Ne.symm hκ)).1, (h2 1 (Ne.symm hκ)).2]

/-! ### 5. The designed entries -/

/-- A designed tag is never shifted. -/
theorem designed_not_shifted (exc : ℕ → Option AffineInput) (u : AffineInput) (κ : Fin 2) (τ : ℕ)
    (designed : designTag Entry.table exc u τ = true) : ¬ Shifted u κ τ := by
  rintro ⟨coord, ⟨fam, hot⟩ | ⟨eight, part⟩⟩
  · rw [Align.designTag_conv _ _ _ fam, hot] at designed
    exact absurd designed (by decide)
  · rw [Align.designTag_label _ _ _ eight, coord] at designed
    exact part (by simpa using designed)

/-- A designed tag is not a hot conversion tag. -/
theorem designed_cold (exc : ℕ → Option AffineInput) (u : AffineInput) (κ : Fin 2) (τ : ℕ) (small : τ < 2 ^ 40)
    (designed : designTag Entry.table exc u τ = true) : ¬ H8.hotConvTag Entry.table u κ.val ⟨τ, small⟩ := by
  rintro ⟨fam, _, hot⟩
  have fam' : tagFamily τ ≤ 5 := fam
  rw [Align.designTag_conv _ _ _ (by omega), hot] at designed
  exact absurd designed (by decide)

/-- Filtering related lists by a tag predicate that never holds on shifted tags gives equal lists. -/
theorem filter_rel {hot : ℕ → Prop} {δ : Block} {A B : List ℕ} (rel : RelAsked hot δ A B) (D : ℕ → Bool)
    (never : ∀ τ, D τ = true → ¬ hot τ) :
    A.filter (fun n => D (n / 2 ^ 128)) = B.filter (fun n => D (n / 2 ^ 128)) := by
  induction rel with
  | nil => rfl
  | @cons a b rest rest' head _ ih =>
    obtain ⟨tag, off, _⟩ := head
    by_cases d : D (a / 2 ^ 128) = true
    · have eq : a = b := off (never _ d)
      rw [List.filter_cons_of_pos (p := fun n => D (n / 2 ^ 128)) d,
        List.filter_cons_of_pos (p := fun n => D (n / 2 ^ 128)) (show D (b / 2 ^ 128) = true by rw [← tag]; exact d),
        eq, ih]
    · rw [List.filter_cons_of_neg (p := fun n => D (n / 2 ^ 128)) d,
        List.filter_cons_of_neg (p := fun n => D (n / 2 ^ 128)) (show ¬ D (b / 2 ^ 128) = true by rw [← tag]; exact d),
        ih]

section Designed

variable [FieldCertificate] [GroupCertificate]

/-- The designed rule at a garbler input, read from its tag. -/
theorem designed_pred (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape crtEntry) (n : ℕ)
    (a : Block × Block) (small : n < baseFieldModulus) :
    crtDesigned (FI := Empty) (EI := Empty) Entry.table ⟨fun scalar tape => crtEntry.exceptional scalar tape.1⟩ scalar
        (tape.1, tapeOracle crtEntry tape) u ⟨.hash (n : BaseField), a⟩ =
      designTag Entry.table (Entry.exceptional scalar tape.1) u (n / 2 ^ 128) := by
  rw [Align.crtDesigned_hash, Align.val_natCast_of_lt small]
  dsimp only [Instance.crtEntry]

/-- The designed entries of a tape, read off the garbler's inputs by tag. -/
theorem designedEntries_eq (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape crtEntry) :
    designedEntries crtEntry Entry.table parameter scalar tape u =
      ((StageTwo.gAsked scalar tape).filter fun n =>
          designTag Entry.table (Entry.exceptional scalar tape.1) u (n / 2 ^ 128)).map fun n : ℕ =>
        (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) tape.2).2.2 (n : BaseField)⟩ :
          Kriterion.CRT.Privacy.Entry Empty Empty) := by
  unfold designedEntries
  rw [StageTwo.garblerEntries_eq, List.filter_map]
  refine congrArg (List.map _) (List.filter_congr fun n inside => ?_)
  have small := Align.garbler_input_lt (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) scalar tape.1 n
    inside
  simp only [Function.comp]
  exact designed_pred scalar u tape n ((tableOracle (FI := Empty) (EI := Empty) tape.2).2.2 (n : BaseField)) small

end Designed

/-- At a designed labelled input the two tables give the same entry. -/
theorem entry_agree (t t' : TagTable) (u : AffineInput) (κ : Fin 2) (sameT : maskTable u κ t = maskTable u κ t')
    (exc : ℕ → Option AffineInput) (label : Block) (k : Paths.TagKey) (range : k.InRange)
    (d : designTag Entry.table exc u k.code = true) :
    (⟨.hash ((hashInput label k.code : ℕ) : BaseField),
        (tableOracle (FI := Empty) (EI := Empty) t).2.2 ((hashInput label k.code : ℕ) : BaseField)⟩ :
        Kriterion.CRT.Privacy.Entry Empty Empty) =
      ⟨.hash ((hashInput label k.code : ℕ) : BaseField),
        (tableOracle (FI := Empty) (EI := Empty) t').2.2 ((hashInput label k.code : ℕ) : BaseField)⟩ := by
  have small := Paths.TagKey.code_lt range
  have answer := hash_agree sameT label label k.code small (designed_cold exc u κ k.code small d)
  unfold hashOf schemeHash at answer
  rw [answer]

section View

variable [FieldCertificate] [GroupCertificate]

theorem crtPart_x (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape crtEntry) :
    crtPart parameter scalar 0 tape = Entry.convVector ((cxM tape.1).eval (hashOf tape.2)).pub := by
  unfold crtPart
  rw [if_pos rfl]
  exact ConvSplit.realGarbled_crtX parameter scalar tape

theorem crtPart_y (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape crtEntry) :
    crtPart parameter scalar 1 tape = Entry.convVector ((cyM tape.1).eval (hashOf tape.2)).pub := by
  unfold crtPart
  rw [if_neg (by decide)]
  exact ConvSplit.realGarbled_crtY parameter scalar tape

variable (rel : CoordRelational) (tail : TailRel) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
  (κ : Fin 2) {ω ω' : TableTape crtEntry} (same : fine parameter scalar u κ ω = fine parameter scalar u κ ω')

include same

theorem same_crt : crtPart parameter scalar κ ω = crtPart parameter scalar κ ω' := congrArg Prod.fst same

theorem same_coins : eCoins u κ ω.1 = eCoins u κ ω'.1 := congrArg (fun w : WType => w.2.1) same

theorem same_table : maskTable u κ ω.2 = maskTable u κ ω'.2 := congrArg (fun w : WType => w.2.2) same

include rel tail

/-- **The garbler's question lists of two tapes with the same fine view are related**, and so are the pieces the
published value reads. -/
theorem garbler_rel :
    RelAsked (Shifted u κ) (res κ ω ^^^ res κ ω') (asked (hashOf ω.2) (Entry.garbleCM scalar ω.1))
        (asked (hashOf ω'.2) (Entry.garbleCM scalar ω'.1)) ∧
      GAgree ((cxM ω.1).eval (hashOf ω.2)) ((cxM ω'.1).eval (hashOf ω'.2)) ∧
      GAgree ((cyM ω.1).eval (hashOf ω.2)) ((cyM ω'.1).eval (hashOf ω'.2)) ∧
      (tailM scalar ω.1).eval (hashOf ω.2) = (tailM scalar ω'.1).eval (hashOf ω'.2) := by
  have sameC := same_coins parameter scalar u κ same
  have sameT := same_table parameter scalar u κ same
  have crt := same_crt parameter scalar u κ same
  obtain ⟨relX, agreeX⟩ := coord_part rel u κ sameC sameT Entry.xCount (by decide) 0 fun h => by
    subst h
    exact (crtPart_x parameter scalar ω).symm.trans (crt.trans (crtPart_x parameter scalar ω'))
  obtain ⟨relY, agreeY⟩ := coord_part rel u κ sameC sameT Entry.yCount (by decide) 1 fun h => by
    subst h
    exact (crtPart_y parameter scalar ω).symm.trans (crt.trans (crtPart_y parameter scalar ω'))
  obtain ⟨relTail, evalTail⟩ := tail scalar u κ ω.1 ω'.1 ω.2 ω'.2 sameC sameT
  refine ⟨?_, agreeX, agreeY, evalTail⟩
  rw [garbleCM_asked (hashOf ω.2) scalar ω.1, garbleCM_asked (hashOf ω'.2) scalar ω'.1]
  exact relX.append (relY.append relTail)

/-- **The published values agree.** -/
theorem published_eq :
    (H8.realGarbled crtEntry parameter scalar ω).1 = (H8.realGarbled crtEntry parameter scalar ω').1 := by
  obtain ⟨_, agreeX, agreeY, evalTail⟩ := garbler_rel rel tail parameter scalar u κ same
  have sameC := same_coins parameter scalar u κ same
  rw [ConvSplit.realGarbled_eq, ConvSplit.realGarbled_eq, garbleCM_eval (hashOf ω.2) scalar ω.1,
    garbleCM_eval (hashOf ω'.2) scalar ω'.1, evalTail]
  exact assemble_congr scalar (offsets_eq sameC) (pointRandomness_eq sameC) (bridgeKey_eq sameC)
    (curveMask_eq sameC) (curveR1_eq sameC) (curveR2_eq sameC) agreeX agreeY _ _

omit rel tail in
/-- **The labels agree.** -/
theorem labels_eq :
    Laws.tapeLabels parameter scalar u ω = Laws.tapeLabels parameter scalar u ω' := by
  have sameC := same_coins parameter scalar u κ same
  obtain ⟨c, t⟩ := ω
  obtain ⟨c', t'⟩ := ω'
  rw [Laws.LabelsSplitProof.tapeLabels_eq, Laws.LabelsSplitProof.tapeLabels_eq]
  exact labelsFrom_congr (eLabel_eq sameC) fun i hi => keys_other sameC i hi

/-- The designed inputs agree. -/
theorem designed_filter_eq :
    (StageTwo.gAsked scalar ω).filter (fun n => designTag Entry.table (Entry.exceptional scalar ω.1) u (n / 2 ^ 128)) =
      (StageTwo.gAsked scalar ω').filter
        (fun n => designTag Entry.table (Entry.exceptional scalar ω'.1) u (n / 2 ^ 128)) := by
  have rel' : RelAsked (Shifted u κ) (res κ ω ^^^ res κ ω') (StageTwo.gAsked scalar ω) (StageTwo.gAsked scalar ω') :=
    (garbler_rel rel tail parameter scalar u κ same).1
  have sameC := same_coins parameter scalar u κ same
  have exc : Entry.exceptional scalar ω.1 = Entry.exceptional scalar ω'.1 := exceptional_eq sameC scalar
  rw [exc]
  exact filter_rel rel' (fun τ => designTag Entry.table (Entry.exceptional scalar ω'.1) u τ)
    (fun τ d => designed_not_shifted _ u κ τ d)

/-- **The designed entries agree.** -/
theorem designed_eq :
    designedEntries crtEntry Entry.table parameter scalar ω u = designedEntries crtEntry Entry.table parameter scalar ω' u := by
  have sameT := same_table parameter scalar u κ same
  rw [designedEntries_eq, designedEntries_eq, designed_filter_eq rel tail parameter scalar u κ same]
  refine List.map_congr_left fun n inside => ?_
  obtain ⟨inG, d⟩ := List.mem_filter.mp inside
  have tagged := asked_of_tagged (Paths.garbleCM_tagged scalar ω'.1) (hashOf ω'.2) n inG
  obtain ⟨k, _, range, label, hn⟩ := tagged
  subst hn
  have d' : designTag Entry.table (Entry.exceptional scalar ω'.1) u k.code = true := by
    rw [← hashInput_tag label k.code]
    exact d
  exact entry_agree ω.2 ω'.2 u κ sameT _ label k range d'

/-- **The functional dependence: two tapes with the same fine view have the same stage-2 view.** -/
theorem view_fd :
    stageTwoView crtEntry Entry.table parameter scalar u ω = stageTwoView crtEntry Entry.table parameter scalar u ω' := by
  have hp := published_eq rel tail parameter scalar u κ same
  have hl := labels_eq parameter scalar u κ same
  have hd := designed_eq rel tail parameter scalar u κ same
  unfold H8.realGarbled at hp
  unfold Laws.tapeLabels H8.realGarbled at hl
  unfold stageTwoView tapeOracle
  dsimp only
  rw [hp, hl, hd]

end View

/-! ### 6. The guess bound -/

section Guess

variable [FieldCertificate] [GroupCertificate]

open Classical in
/-- **A guess of `Δ_κ` given the stage-2 view.** An event that forces `Δ_κ` to `X(fine) ⊕ ℓ`, for a function `X`
of the fine view, has conditional mass at most `2^-128` given the stage-2 view. -/
theorem delta_guess_le (rel : CoordRelational) (tail : TailRel) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (κ : Fin 2) (view : crtEntry.Public × LamportSignature × List (Kriterion.CRT.Privacy.Entry Empty Empty))
    (S : Set (TableTape crtEntry)) (X : WType → Block) (ℓ : Block)
    (hS : ∀ tape ∈ S, res κ tape = X (fine parameter scalar u κ tape) ^^^ ℓ) :
    (swappedTableTape crtEntry).toOuterMeasure
        {tape | stageTwoView crtEntry Entry.table parameter scalar u tape = view ∧ tape ∈ S} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ * (swappedTableTape crtEntry).toOuterMeasure
        {tape | stageTwoView crtEntry Entry.table parameter scalar u tape = view} := by
  have nonempty : Nonempty (TableTape crtEntry) := ⟨(crtEntry.coinWitness, fun _ => (0, 0))⟩
  let coarse : WType → crtEntry.Public × LamportSignature × List (Kriterion.CRT.Privacy.Entry Empty Empty) :=
    fun w => stageTwoView crtEntry Entry.table parameter scalar u
      (Classical.epsilon fun tape => fine parameter scalar u κ tape = w)
  have hview : ∀ tape, stageTwoView crtEntry Entry.table parameter scalar u tape =
      coarse (fine parameter scalar u κ tape) := fun tape =>
    view_fd rel tail parameter scalar u κ (Classical.epsilon_spec (p := fun tape' =>
      fine parameter scalar u κ tape' = fine parameter scalar u κ tape) ⟨tape, rfl⟩).symm
  have bound := HiddenGuess.outer_fine_le (swappedTableTape crtEntry)
    (stageTwoView crtEntry Entry.table parameter scalar u) (fine parameter scalar u κ) coarse hview (res κ)
    (fine_split parameter scalar u κ) (fun tape => tape ∈ S) (fun w r => r = X w ^^^ ℓ) 1
    (fun w => Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rw [ha, hb])
    (fun tape inside => hS tape inside) view
  refine le_trans bound (le_of_eq ?_)
  rw [Kriterion.ArgoMAC.Security.PGS.card_block, Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat]

set_option maxRecDepth 4096 in
open Classical in
/-- A projected delta guess retains exactly `2^24` raw preimages; no high bits of the raw residual are exposed. -/
theorem delta_guess_clip_le (rel : CoordRelational) (tail : TailRel) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (κ : Fin 2) (view : crtEntry.Public × LamportSignature × List (Kriterion.CRT.Privacy.Entry Empty Empty))
    (S : Set (TableTape crtEntry)) (X : WType → Label) (ℓ : Label)
    (hS : ∀ tape ∈ S, clip (res κ tape) = X (fine parameter scalar u κ tape) ^^^ ℓ) :
    (swappedTableTape crtEntry).toOuterMeasure
        {tape | stageTwoView crtEntry Entry.table parameter scalar u tape = view ∧ tape ∈ S} ≤
      ((2 : ℝ≥0∞) ^ labelBits)⁻¹ * (swappedTableTape crtEntry).toOuterMeasure
        {tape | stageTwoView crtEntry Entry.table parameter scalar u tape = view} := by
  have nonempty : Nonempty (TableTape crtEntry) := ⟨(crtEntry.coinWitness, fun _ => (0, 0))⟩
  let coarse : WType → crtEntry.Public × LamportSignature × List (Kriterion.CRT.Privacy.Entry Empty Empty) :=
    fun w => stageTwoView crtEntry Entry.table parameter scalar u
      (Classical.epsilon fun tape => fine parameter scalar u κ tape = w)
  have hview : ∀ tape, stageTwoView crtEntry Entry.table parameter scalar u tape =
      coarse (fine parameter scalar u κ tape) := fun tape =>
    view_fd rel tail parameter scalar u κ (Classical.epsilon_spec (p := fun tape' =>
      fine parameter scalar u κ tape' = fine parameter scalar u κ tape) ⟨tape, rfl⟩).symm
  have bound := HiddenGuess.outer_fine_le (swappedTableTape crtEntry)
    (stageTwoView crtEntry Entry.table parameter scalar u) (fine parameter scalar u κ) coarse hview (res κ)
    (fine_split parameter scalar u κ) (fun tape => tape ∈ S) (fun w r => clip r = X w ^^^ ℓ) (2 ^ (128 - labelBits))
    (fun w => by
      have card := Narrow.card_clip_fibre (X w ^^^ ℓ)
      rw [← Nat.card_eq_fintype_card] at card
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact le_of_eq card)
    (fun tape inside => hS tape inside) view
  refine le_trans bound (le_of_eq ?_)
  have ratio : ((2 ^ (128 - labelBits) : ℕ) : ℝ≥0∞) / (Fintype.card Block : ℝ≥0∞) =
      ((2 : ℝ≥0∞) ^ labelBits)⁻¹ := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact Narrow.clip_fibre_ratio
  rw [ratio]

end Guess

/-- **`Δ_κ` given the stage-2 view** (the named fact of `CaseDigest.DeltaGivenView`, stated verbatim):
each coordinate's `Δ` takes any value with conditional mass at most `2^-128` given the stage-2 view. -/
theorem deltaGivenView (rel : CoordRelational) (tail : TailRel) :
    ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
      (view : Instance.crtEntry.Public × LamportSignature × List (Kriterion.CRT.Privacy.Entry Empty Empty)) (κ : Fin 2)
      (d : Block),
      (swappedTableTape Instance.crtEntry).toOuterMeasure
          {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
            Entry.deltaOf tape.1 κ = d} ≤
        ((2 : ℝ≥0∞) ^ 128)⁻¹ * (swappedTableTape Instance.crtEntry).toOuterMeasure
          {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view} := by
  intro field group parameter scalar u view κ d
  exact delta_guess_le rel tail parameter scalar u κ view {tape | Entry.deltaOf tape.1 κ = d} (fun _ => 0) d
    fun tape inside => by
      have zx : (0 : Block) ^^^ d = d := BitVec.zero_xor
      rw [zx]
      exact (deltaAt_eq_deltaOf tape.1 κ).trans inside

end

end Kriterion.CRT.Privacy.DeltaView
