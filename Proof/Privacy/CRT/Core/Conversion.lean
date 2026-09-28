/-
The parity conversion layer is a bijection of its independent hidden data.

Each hashed tree, growth, or fold level contributes one hidden 104-bit material.
Each cast contributes only its independent upper `l - 1` planes; its low plane is
computed from the actual leaf label. The public tuple has the same shape: joins
and half-pins whose omitted low plane is proved zero.

For chunks, published joins first determine the hidden tree materials. Those
materials determine every leaf label, after which the half-pin determines the
hot cast's upper planes. Each fused extraction stage uses restricted publication
injectivity, with hidden data equal to its hot tree materials and hot cast upper
planes. The old full-width stage injection is used only as an algebraic kernel;
full-width uniformity is never asserted for the parity cast.

Malformed rows retain the empty-row singleton convention. The actual-garbler
link reads independent upper data from the original full-width raw hash packing.
-/

import Proof.Privacy.CRT.Core.ConvTable
import Proof.Privacy.CRT.Core.Inversion

namespace Kriterion.CRT.Privacy.Conv

open Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.ExtractSpec (StageParams gJoin gPin gBit gNext gCast gLeaf gRes gNode gBit0 gLevelSum)
open Kriterion.CRT.Privacy.ExtractStage (Hidden overrideHot specPublish spec_publish_injective UpperHidden upperOverrideHot upperSpecPublish upper_spec_publish_injective)

noncomputable section

/-! ### Rows -/

/-- A well-formed schedule row (the common T9/fallback side conditions). -/
def RowWF (row : OddRow) : Prop :=
  1 ≤ row.width0 ∧ 1 ≤ row.width1 ∧ row.width0 + row.width1 + 1 = row.ell ∧ row.width0 ≤ row.keep ∧
    row.keep ≤ row.ell

instance (row : OddRow) : Decidable (RowWF row) := by
  unfold RowWF
  infer_instance

/-- The empty row: no stage, growth or fold. -/
def emptyRow : OddRow := ⟨0, 0, 0, 0⟩

/-- **The row of a modulus**: its schedule row if well formed with a positive modulus, the empty row otherwise
(the modulus `2 ^ 8` read from chunk 0 has no conversion). -/
def rowOf (k : Kind) (m : ℕ) : OddRow :=
  match k with
  | .chunkZero => emptyRow
  | .odd row => if RowWF row ∧ 0 < m then row else emptyRow

theorem rowOf_cases (k : Kind) (m : ℕ) : rowOf k m = emptyRow ∨ (RowWF (rowOf k m) ∧ 0 < m) := by
  cases k with
  | chunkZero => exact Or.inl rfl
  | odd row =>
      by_cases h : RowWF row ∧ 0 < m
      · right
        simp only [rowOf, if_pos h]
        exact h
      · left
        simp only [rowOf, if_neg h]

theorem rowOf_odd (row : OddRow) (m : ℕ) (wf : RowWF row) (hm : 0 < m) : rowOf (.odd row) m = row := by
  simp only [rowOf, if_pos (And.intro wf hm)]

theorem rowOf_hw0 (k : Kind) (m : ℕ) : (rowOf k m).width0 ≤ (rowOf k m).ell := by
  rcases rowOf_cases k m with e | ⟨⟨_, _, h3, _, _⟩, _⟩
  · rw [e]
    exact Nat.le_refl 0
  · omega

theorem rowOf_hw1 (k : Kind) (m : ℕ) : (rowOf k m).width1 ≤ (rowOf k m).ell - (rowOf k m).width0 := by
  rcases rowOf_cases k m with e | ⟨⟨_, _, h3, _, _⟩, _⟩
  · rw [e]
    exact Nat.le_refl 0
  · omega

/-! ### Hidden and published values -/

/-- The values of one modulus: stage 0's and stage 1's tuples (joins of the hashed levels and the pin), the growth
joins and the fold joins. -/
abbrev StageVals (row : OddRow) : Type :=
  UpperHidden row.width0 row.ell × UpperHidden row.width1 (row.ell - row.width0) ×
    (Fin (row.keep - row.width0) → Label) × (Fin (row.ell - row.keep) → Label)

/-- The values of the chunks: the (upper-plane) pins. No chunk joins: the tree joins are absorbed into the Lamport
labels and are not published, so the tree materials are not part of the conversion payload (the chunk trees are read
from the table). -/
abbrev ChunkVals (tbl : CrtTable) : Type := Fin tbl.chunkCount → Lanes (tbl.castWidth - 1)

/-- **The conversion values of one coordinate**: the hidden values at the hot slots, and equally the published
conversion material (one pin per chunk; per odd modulus one join per hashed level and one pin per cast family). -/
abbrev ConvVals (tbl : CrtTable) : Type :=
  ChunkVals tbl × ((i : Fin tbl.count) → StageVals (rowOf (tbl.kind i) (tbl.modulus i)))

instance stageValsFintype (row : OddRow) : Fintype (StageVals row) := by
  unfold StageVals UpperHidden Hidden
  infer_instance

instance stageValsNonempty (row : OddRow) : Nonempty (StageVals row) :=
  ⟨((fun _ => 0, fun _ => 0), (fun _ => 0, fun _ => 0), fun _ => 0, fun _ => 0)⟩

instance convValsFintype (tbl : CrtTable) : Fintype (ConvVals tbl) := by
  unfold ConvVals ChunkVals
  infer_instance

instance convValsNonempty (tbl : CrtTable) : Nonempty (ConvVals tbl) :=
  ⟨(fun _ _ => 0, fun _ => Classical.arbitrary _)⟩

/-- Everything of one coordinate's conversion that is not hidden: the answer table (read at the cold slots), the zero
labels and `Δ`. -/
structure ConvRest where
  table : ℕ → Block × Block
  zero : ℕ → Label
  delta : Label

/-! ### The published material from the rest and the hidden values -/

section Publish

variable (tbl : CrtTable) (coord v : ℕ) (r : ConvRest)

/-- The material at a tree slot, read from the table (no chunk joins: the tree materials are not hidden values of
the conversion payload). -/
def chunkMatH (c : Fin tbl.chunkCount) (n slot : ℕ) : Label := clip (r.table (chunkTreeTag coord c.val n slot)).1

/-- Leaf labels of the chunk tree, from the table. -/
def chunkTreeH (c : Fin tbl.chunkCount) : Fin (2 ^ tbl.chunkWidth c.val) → Label :=
  materialTree (chunkMatH tbl coord r c) r.delta (r.zero (tbl.chunkOffset c.val)) (tbl.chunkWidth c.val)

/-- Each cast retains the tree's leaf label in its low plane. -/
def chunkCastH (h : ChunkVals tbl) (c : Fin tbl.chunkCount) (leaf : ℕ) : Lanes tbl.castWidth :=
  let label := atNat (chunkTreeH tbl coord r c) 0 leaf
  if leaf = tbl.chunkValue v c.val then Parity.liftUpper tbl.castWidth (h c) label
  else parityRd r.table tbl.castWidth (chunkCastTag coord c.val leaf) label

/-- The full even pin, before its zero low plane is omitted. -/
def chunkFullPinH (h : ChunkVals tbl) (c : Fin tbl.chunkCount) : Lanes tbl.castWidth :=
  (∑ leaf : Fin (2 ^ tbl.chunkWidth c.val), chunkCastH tbl coord v r h c leaf.val) +
    deltaLanes tbl.castWidth r.delta

/-- The actual public chunk pin stores only its upper planes. -/
def chunkPinH (h : ChunkVals tbl) (c : Fin tbl.chunkCount) : Lanes (tbl.castWidth - 1) :=
  Parity.pinHalf tbl.castWidth (chunkFullPinH tbl coord v r h c)

/-- The word depends on the reconstructed labels as well as the independent upper casts. -/
def wordH (h : ChunkVals tbl) (m ell : ℕ) : Lanes ell :=
  reduceTo ell fun lane => ∑ c : Fin tbl.chunkCount, ∑ leaf : Fin (2 ^ tbl.chunkWidth c.val),
    ((tbl.truth m c.val leaf.val : ℕ) : ZMod (2 ^ tbl.castWidth)) * chunkCastH tbl coord v r h c leaf.val lane

end Publish

/-- **The published material of one modulus** of row `row` and word value `σ`, from the word mask `W` and the
modulus's hidden values `h`: the two stages (`specPublish`, the stage with its hot answers overridden), then the
growth and fold joins with the word's bit masks. -/
def modPublish (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Label)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell)
    (h : StageVals row) : StageVals row :=
  let st0 := tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)
  let st1 := tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1)
  let s0 := σ % 2 ^ row.width0
  let s1 := σ / 2 ^ row.width0 % 2 ^ row.width1
  let R1 : Lanes (row.ell - row.width0) := gNext (upperOverrideHot st0 s0 h.1) W Δ
  let bitMask : ℕ → Label := fun p =>
    if p < row.width0 + row.width1 then gBit (upperOverrideHot st1 s1 h.2.1) R1 Δ (p - row.width0)
    else laneBit (gNext (upperOverrideHot st1 s1 h.2.1) R1 Δ) 0
  (upperSpecPublish st0 W Δ s0 h.1, upperSpecPublish st1 R1 Δ s1 h.2.1,
    fun k => xorFold (fun slot : Fin (2 ^ (row.width0 + k.val)) =>
        if slot.val = σ % 2 ^ (row.width0 + k.val) then h.2.2.1 k
        else (clip (T (growTag coord i (row.width0 + k.val) slot.val)).1)) ^^^ bitMask (row.width0 + k.val),
    fun k => xorFold (fun ρ : Fin m =>
        if ρ.val = σ % 2 ^ (row.keep + k.val) % m then h.2.2.2 k
        else (clip (T (foldTag coord i (row.keep + k.val) ρ.val)).1)) ^^^ bitMask (row.keep + k.val))

/-- **The published conversion material of one coordinate** from the rest and the hidden values. -/
def convPublish (tbl : CrtTable) (coord v : ℕ) (r : ConvRest) (h : ConvVals tbl) : ConvVals tbl :=
  (fun c => chunkPinH tbl coord v r h.1 c,
    fun i => modPublish r.table coord i.val (rowOf (tbl.kind i) (tbl.modulus i)) (tbl.modulus i)
      (tbl.wordValue (tbl.modulus i) v) r.delta (rowOf_hw0 _ _) (rowOf_hw1 _ _)
      (wordH tbl coord v r h.1 (tbl.modulus i) (rowOf (tbl.kind i) (tbl.modulus i)).ell) (h.2 i))

/-! ### Injectivity -/

/-- A XOR fold with one hidden slot is the XOR of the others and the hidden value. -/
theorem xorFold_hot {n : ℕ} (hot : ℕ) (hh : hot < n) (y : Label) (Y : Fin n → Label) :
    xorFold (fun slot : Fin n => if slot.val = hot then y else Y slot) = xorFoldExcept ⟨hot, hh⟩ Y ^^^ y := by
  rw [← SliceC.xorFoldExcept_xor ⟨hot, hh⟩ (fun slot : Fin n => if slot.val = hot then y else Y slot), if_pos rfl]
  congr 1
  refine SliceC.xorFoldExcept_congr _ _ _ fun slot hs => ?_
  rw [if_neg fun h => hs (Fin.ext h)]

theorem xor_cancel_mid (K y y' z : Label) (h : K ^^^ y ^^^ z = K ^^^ y' ^^^ z) : y = y' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have e := congrArg (fun t : Label => t.getLsbD i) h
  simp only [BitVec.getLsbD_xor] at e
  revert e
  cases K.getLsbD i <;> cases y.getLsbD i <;> cases y'.getLsbD i <;> cases z.getLsbD i <;> simp

/-- A sum with one hidden term determines the term. -/
theorem sum_hot_cancel {n : ℕ} {M : Type*} [AddCommGroup M] (hot : ℕ) (hh : hot < n) (x x' : M) (Y : ℕ → M)
    (h : ∑ leaf : Fin n, (if leaf.val = hot then x else Y leaf.val) =
      ∑ leaf : Fin n, (if leaf.val = hot then x' else Y leaf.val)) : x = x' := by
  have point : ∀ leaf : Fin n, ((if leaf.val = hot then x else Y leaf.val) -
      (if leaf.val = hot then x' else Y leaf.val)) = if leaf = ⟨hot, hh⟩ then x - x' else 0 := by
    intro leaf
    by_cases e : leaf = ⟨hot, hh⟩
    · subst e
      simp
    · have ne : leaf.val ≠ hot := fun h' => e (Fin.ext h')
      rw [if_neg ne, if_neg ne, if_neg e, sub_self]
  have diff : ∑ leaf : Fin n, ((if leaf.val = hot then x else Y leaf.val) -
      (if leaf.val = hot then x' else Y leaf.val)) = x - x' := by
    rw [Finset.sum_congr rfl (fun leaf _ => point leaf), Finset.sum_ite_eq' Finset.univ,
      if_pos (Finset.mem_univ _)]
  rw [Finset.sum_sub_distrib, h, sub_self] at diff
  exact sub_eq_zero.mp diff.symm

theorem lanes_zero_eq (a b : Lanes 0) : a = b := by
  funext lane
  apply ZMod.val_injective
  have ha := ZMod.val_lt (a lane)
  have hb := ZMod.val_lt (b lane)
  simp only [pow_zero] at ha hb
  omega

theorem stageVals_empty_eq (a b : StageVals emptyRow) : a = b := by
  obtain ⟨⟨a0, a0'⟩, ⟨a1, a1'⟩, a2, a3⟩ := a
  obtain ⟨⟨b0, b0'⟩, ⟨b1, b1'⟩, b2, b3⟩ := b
  have f0 : a0 = b0 := funext fun k => absurd k.isLt (by simp [emptyRow])
  have f1 : a1 = b1 := funext fun k => absurd k.isLt (by simp [emptyRow])
  have f2 : a2 = b2 := funext fun k => absurd k.isLt (by simp [emptyRow])
  have f3 : a3 = b3 := funext fun k => absurd k.isLt (by simp [emptyRow])
  rw [f0, f1, f2, f3, lanes_zero_eq a0' b0', lanes_zero_eq a1' b1']

/-- The reconstructed tree supplies every cast's low plane, so the full pin is even. -/
theorem chunkFullPinH_even (tbl : CrtTable) (coord v : ℕ) (r : ConvRest)
    (h : ChunkVals tbl) (c : Fin tbl.chunkCount) :
    Parity.EvenLanes (chunkFullPinH tbl coord v r h c) := by
  apply SliceC.pin_even_of_leaf_xor_total _ (chunkTreeH tbl coord r c) r.delta
  · intro positive leaf
    unfold chunkCastH
    rw [SliceC.atNat_of_lt _ _ leaf.isLt]
    split_ifs
    · exact Parity.laneBit_liftUpper_zero _ _ _ positive
    · exact parityRd_low _ _ _ _ positive
  · exact materialTree_xor _ _ _ _

/-- **One modulus is injective in its hidden values.** -/
theorem modPublish_injective (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Label)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell)
    (hrow : row = emptyRow ∨ (RowWF row ∧ 0 < m)) :
    Function.Injective (modPublish T coord i row m σ Δ hw0 hw1 W) := by
  intro a b e
  rcases hrow with rfl | ⟨⟨w0pos, w1pos, _, _, _⟩, hm⟩
  · exact stageVals_empty_eq a b
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  have e0 : upperSpecPublish (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ
      (σ % 2 ^ row.width0) a0 =
      upperSpecPublish (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ
      (σ % 2 ^ row.width0) b0 := congrArg (fun x => x.1) e
  have h0 : a0 = b0 := upper_spec_publish_injective _ w0pos
    (tableStage_low T _ hw0 _ _ (by omega)) W Δ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) e0
  subst h0
  have e1 : upperSpecPublish (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (gNext (upperOverrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) a0) W Δ) Δ (σ / 2 ^ row.width0 % 2 ^ row.width1) a1 =
      upperSpecPublish (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (gNext (upperOverrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) a0) W Δ) Δ (σ / 2 ^ row.width0 % 2 ^ row.width1) b1 :=
    congrArg (fun x => x.2.1) e
  have h1 : a1 = b1 := upper_spec_publish_injective _ w1pos
    (tableStage_low T _ hw1 _ _ (by omega)) _ Δ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) e1
  subst h1
  have h2 : a2 = b2 := funext fun k => by
    have ek := congrFun (congrArg (fun x => x.2.2.1) e) k
    simp only [modPublish] at ek
    rw [xorFold_hot _ (Nat.mod_lt _ (Nat.two_pow_pos _)), xorFold_hot _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
      at ek
    exact xor_cancel_mid _ _ _ _ ek
  have h3 : a3 = b3 := funext fun k => by
    have ek := congrFun (congrArg (fun x => x.2.2.2) e) k
    simp only [modPublish] at ek
    rw [xorFold_hot _ (Nat.mod_lt _ hm), xorFold_hot _ (Nat.mod_lt _ hm)] at ek
    exact xor_cancel_mid _ _ _ _ ek
  rw [h2, h3]

/-- **P3, the set statement: the conversion layer of one coordinate is injective in its hidden values** (hence a
bijection of `ConvVals tbl`), for every table, coordinate, value and rest. -/
theorem convPublish_injective (tbl : CrtTable) (coord v : ℕ) (r : ConvRest) :
    Function.Injective (convPublish tbl coord v r) := by
  rintro ⟨hP, hM⟩ ⟨hP', hM'⟩ same
  have pins : hP = hP' := funext fun c => by
    have halves := congrArg (fun x => x.1 c) same
    change Parity.pinHalf tbl.castWidth (chunkFullPinH tbl coord v r hP c) =
      Parity.pinHalf tbl.castWidth (chunkFullPinH tbl coord v r hP' c) at halves
    have full := Parity.pinHalf_injective_on_even tbl.castWidth
      (chunkFullPinH_even tbl coord v r hP c)
      (chunkFullPinH_even tbl coord v r hP' c) halves
    have sums := add_right_cancel full
    change ∑ leaf : Fin (2 ^ tbl.chunkWidth c.val), chunkCastH tbl coord v r hP c leaf.val =
      ∑ leaf : Fin (2 ^ tbl.chunkWidth c.val), chunkCastH tbl coord v r hP' c leaf.val at sums
    have hot : tbl.chunkValue v c.val < 2 ^ tbl.chunkWidth c.val := Nat.mod_lt _ (Nat.two_pow_pos _)
    have fixed : ∀ (pins : Fin tbl.chunkCount → Lanes (tbl.castWidth - 1))
        (leaf : Fin (2 ^ tbl.chunkWidth c.val)),
        chunkCastH tbl coord v r pins c leaf.val =
          if leaf.val = tbl.chunkValue v c.val then
            Parity.liftUpper tbl.castWidth (pins c)
              (atNat (chunkTreeH tbl coord r c) 0 (tbl.chunkValue v c.val))
          else parityRd r.table tbl.castWidth (chunkCastTag coord c.val leaf.val)
            (atNat (chunkTreeH tbl coord r c) 0 leaf.val) := by
      intro pins leaf
      unfold chunkCastH
      split_ifs with hit
      · rw [hit]
      · rfl
    simp only [fixed] at sums
    apply Parity.liftUpper_injective tbl.castWidth
      (atNat (chunkTreeH tbl coord r c) 0 (tbl.chunkValue v c.val))
    exact sum_hot_cancel _ hot _ _
      (fun leaf => parityRd r.table tbl.castWidth (chunkCastTag coord c.val leaf)
        (atNat (chunkTreeH tbl coord r c) 0 leaf)) sums
  subst pins
  have mods : hM = hM' := funext fun i =>
    modPublish_injective _ _ _ _ _ _ _ _ _ _ (rowOf_cases _ _) (congrArg (fun x => x.2 i) same)
  rw [mods]

/-- **P3, the law statement: the published conversion material of uniform hidden values is uniform and independent of
the rest**, whatever the law of the rest (`Core/Inversion.lean`'s form). -/
theorem conversion_uniform (tbl : CrtTable) (coord v : ℕ) {Rest : Type*} (rest : PMF Rest)
    (restOf : Rest → ConvRest) :
    (rest.bind fun r => (PMF.uniformOfFintype (ConvVals tbl)).map fun h => (r, convPublish tbl coord v (restOf r) h))
      = rest.bind fun r => (PMF.uniformOfFintype (ConvVals tbl)).map fun b => (r, b) :=
  bind_map_uniform_of_injective rest _ (fun r => convPublish_injective tbl coord v (restOf r)) rfl

/-! ### The real garbler: `convPublish` at its own hot readings -/

section Link

variable {rb : ℕ}

/-- The hidden tuple a stage's own answers give: overriding with it changes no cast (`spec_garbler_eq_publish`, restated for the casts). -/
theorem gCast_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Label) (s α : ℕ) :
    gCast (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ α = gCast sp R Δ α := by
  unfold gCast gLeaf
  show (if α = s then _ else sp.castF α _) = _
  rw [show (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)).w = sp.w from rfl,
    show gBit0 (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R = gBit0 sp R from rfl,
    ExtractStage.gNode_override_self sp R Δ s sp.w le_rfl α]
  split_ifs with hα
  · rw [hα]
    rfl
  · rfl

theorem gRes_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Label) (s n : ℕ) :
    gRes (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ n = gRes sp R Δ n :=
  Finset.sum_congr rfl fun α _ => by rw [gCast_override_self]

theorem gNext_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Label) (s : ℕ) :
    (gNext (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ : Lanes (rb - sp.w)) = gNext sp R Δ := by
  show peelDiv R (gRes (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ sp.w) sp.w =
    peelDiv R (gRes sp R Δ sp.w) sp.w
  rw [gRes_override_self]

theorem gBit_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Label) (s n : ℕ) :
    gBit (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ n = gBit sp R Δ n := by
  unfold gBit
  rw [gRes_override_self]
  rfl

/-- At its own hot answers the overridden stage publishes what the stage publishes. -/
theorem specPublish_self (sp : StageParams rb) (R : Lanes rb) (Δ : Label) (s : ℕ) (hw1 : 1 ≤ sp.w) :
    specPublish sp R Δ s (ExtractStage.hiddenOfSpec sp R Δ s) =
      ((fun k : Fin (sp.w - 1) => gJoin sp R Δ (k.val + 1)), gPin sp R Δ) := by
  unfold specPublish
  rw [ExtractStage.spec_publish_eq sp R Δ s _ hw1, ← ExtractStage.spec_garbler_eq_publish sp R Δ s hw1]

end Link

/-- The in-range published material of one modulus of row `row`. -/
def readMod (pub : ConvPublic) (i : ℕ) (row : OddRow) : StageVals row :=
  ((fun k => pub.stageJoin i 0 (k.val + 1), pinOfBlocks (row.ell - 1) fun j => pub.stagePin i 0 j.val),
    (fun k => pub.stageJoin i 1 (k.val + 1), pinOfBlocks (row.ell - row.width0 - 1) fun j => pub.stagePin i 1 j.val),
    fun k => pub.growJoin i (row.width0 + k.val), fun k => pub.foldJoin i (row.keep + k.val))

/-- **The published conversion material read in range** (pins through the dense codec; no chunk joins). -/
def readPub (tbl : CrtTable) (pub : ConvPublic) : ConvVals tbl :=
  (fun c => pinOfBlocks (tbl.castWidth - 1) fun j => pub.chunkPin c.val j.val,
    fun i => readMod pub i.val (rowOf (tbl.kind i) (tbl.modulus i)))

/-- A table's readings at the hot slots of one modulus of row `row` and word value `σ`. -/
def readHotMod (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) : StageVals row :=
  ((fun k => (clip (T (extTreeTag coord i 0 (k.val + 1) (σ % 2 ^ row.width0 % 2 ^ (k.val + 1)))).1),
      upperRd T row.ell (extCastTag coord i 0 (σ % 2 ^ row.width0))),
    (fun k => (clip (T (extTreeTag coord i 1 (k.val + 1) (σ / 2 ^ row.width0 % 2 ^ row.width1 % 2 ^ (k.val + 1)))).1),
      upperRd T (row.ell - row.width0) (extCastTag coord i 1 (σ / 2 ^ row.width0 % 2 ^ row.width1))),
    fun k => (clip (T (growTag coord i (row.width0 + k.val) (σ % 2 ^ (row.width0 + k.val)))).1),
    fun k => (clip (T (foldTag coord i (row.keep + k.val) (σ % 2 ^ (row.keep + k.val) % m))).1))

/-- **A table's readings at the hot slots of the coordinate value `v`**: the hidden values the garbler's own table
gives. -/
def readHot (tbl : CrtTable) (coord v : ℕ) (T : ℕ → Block × Block) : ConvVals tbl :=
  (fun c => upperRd T tbl.castWidth (chunkCastTag coord c.val (tbl.chunkValue v c.val)),
    fun i => readHotMod T coord i.val (rowOf (tbl.kind i) (tbl.modulus i)) (tbl.modulus i)
      (tbl.wordValue (tbl.modulus i) v))

/-- The chunk tree is the table's complete tree. -/
theorem chunkTreeH_self (tbl : CrtTable) (coord : ℕ) (T : ℕ → Block × Block)
    (Z : ℕ → Label) (Δ : Label) (c : Fin tbl.chunkCount) :
    chunkTreeH tbl coord ⟨T, Z, Δ⟩ c =
      materialTree (fun n slot => clip (T (chunkTreeTag coord c.val n slot)).1)
        Δ (Z (tbl.chunkOffset c.val)) (tbl.chunkWidth c.val) := rfl

/-- At its own hot data every chunk cast is its actual label-dependent table reading. -/
theorem chunkCastH_self (tbl : CrtTable) (coord v : ℕ) (T : ℕ → Block × Block)
    (Z : ℕ → Label) (Δ : Label) (c : Fin tbl.chunkCount) (leaf : ℕ) :
    chunkCastH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 c leaf =
      parityRd T tbl.castWidth (chunkCastTag coord c.val leaf)
        (atNat (materialTree (fun n slot => clip (T (chunkTreeTag coord c.val n slot)).1)
          Δ (Z (tbl.chunkOffset c.val)) (tbl.chunkWidth c.val)) 0 leaf) := by
  unfold chunkCastH
  rw [chunkTreeH_self]
  split_ifs with hit
  · rw [hit]
    rfl
  · rfl

/-- A table the conversion's link needs: a positive cast width and well-formed odd rows with positive moduli. -/
structure ConvTableWF (tbl : CrtTable) : Prop where
  cast : 0 < tbl.castWidth
  rows : ∀ i row, tbl.kind i = .odd row → RowWF row ∧ 0 < tbl.modulus i

/-- The program's word (from the chunks' casts on the table) is `wordH` at the table's own hot readings. -/
theorem word_eq (tbl : CrtTable) (coord v : ℕ) (T : ℕ → Block × Block) (Z : ℕ → Label) (Δ : Label) (m ell : ℕ) :
    truthWord tbl m ell (fun c leaf =>
        (atNat (fun c : Fin tbl.chunkCount => (chunkGarbleM tbl coord Δ Z c.val).eval (tableHash T))
          (ChunkGarbled.empty _) c).casts leaf) =
      wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 m ell := by
  unfold truthWord wordH
  rw [materialize_eq]
  congr 1
  funext lane
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun leaf _ => ?_
  congr 1
  beta_reduce
  rw [SliceC.atNat_of_lt _ _ c.isLt, (chunk_table T tbl coord Δ Z c.val).2.1 leaf.val leaf.isLt]
  rw [chunkCastH_self]

/-- The published material of one odd modulus as the garbler computes it on a table (`conversion_table`). -/
def modGarbled (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m : ℕ) (Δ : Label)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell) : StageVals row :=
  let sp0 := tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)
  let sp1 := tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1)
  let R1 : Lanes (row.ell - row.width0) := gNext sp0 W Δ
  let bitMask : ℕ → Label := fun p =>
    if p < row.width0 + row.width1 then gBit sp1 R1 Δ (p - row.width0) else laneBit (gNext sp1 R1 Δ) 0
  (((fun k : Fin (row.width0 - 1) => gJoin sp0 W Δ (k.val + 1)), Parity.pinHalf row.ell (gPin sp0 W Δ)),
    ((fun k : Fin (row.width1 - 1) => gJoin sp1 R1 Δ (k.val + 1)), Parity.pinHalf (row.ell - row.width0) (gPin sp1 R1 Δ)),
    fun k => xorFold (fun slot : Fin (2 ^ (row.width0 + k.val)) =>
        (clip (T (growTag coord i (row.width0 + k.val) slot.val)).1)) ^^^ bitMask (row.width0 + k.val),
    fun k => xorFold (fun ρ : Fin m => (clip (T (foldTag coord i (row.keep + k.val) ρ.val)).1)) ^^^
      bitMask (row.keep + k.val))

/-- **One modulus at its own hot readings** publishes what the garbler publishes. -/
theorem modPublish_self (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Label)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell)
    (w0pos : 1 ≤ row.width0) (w1pos : 1 ≤ row.width1) :
    modPublish T coord i row m σ Δ hw0 hw1 W (readHotMod T coord i row m σ) =
      modGarbled T coord i row m Δ hw0 hw1 W := by
  have eR : (gNext (upperOverrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
      (σ % 2 ^ row.width0) (readHotMod T coord i row m σ).1) W Δ : Lanes (row.ell - row.width0)) =
      gNext (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ :=
    gNext_upper_table_self T _ hw0 _ _ (by omega) W Δ _
  have eB : ∀ n, gBit (upperOverrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1)
      (gNext (upperOverrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) (readHotMod T coord i row m σ).1) W Δ) Δ n =
      gBit (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
        (gNext (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ) Δ n := fun n =>
    (congrArg (fun R => gBit (upperOverrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1)
      (extCastTag coord i 1)) (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1) R Δ n)
      eR).trans (gBit_upper_table_self T _ hw1 _ _ (by omega) _ Δ _ n)
  have eN : (gNext (upperOverrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1)
      (gNext (upperOverrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) (readHotMod T coord i row m σ).1) W Δ) Δ :
        Lanes (row.ell - row.width0 - row.width1)) =
      gNext (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
        (gNext (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ) Δ :=
    (congrArg (fun R => (gNext (upperOverrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1)
      (extCastTag coord i 1)) (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1) R Δ :
        Lanes (row.ell - row.width0 - row.width1))) eR).trans (gNext_upper_table_self T _ hw1 _ _ (by omega) _ Δ _)
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact upperSpecPublish_table_self T row.width0 hw0 _ _ w0pos W Δ
      (σ % 2 ^ row.width0) (Nat.mod_lt _ (Nat.two_pow_pos _))
  · exact (congrArg (fun R => upperSpecPublish (tableStage T row.width1 hw1 (extTreeTag coord i 1)
      (extCastTag coord i 1)) R Δ (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1)
      eR).trans (upperSpecPublish_table_self T row.width1 hw1 _ _ w1pos _ Δ _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
  · funext k
    show xorFold _ ^^^ (if row.width0 + k.val < row.width0 + row.width1 then _ else _) =
      xorFold _ ^^^ (if row.width0 + k.val < row.width0 + row.width1 then _ else _)
    congr 1
    · congr 1
      funext slot
      split_ifs with hs
      · rw [hs]
        rfl
      · rfl
    · split_ifs
      · exact eB _
      · exact congrArg (fun R => laneBit R 0) eN
  · funext k
    show xorFold _ ^^^ (if row.keep + k.val < row.width0 + row.width1 then _ else _) =
      xorFold _ ^^^ (if row.keep + k.val < row.width0 + row.width1 then _ else _)
    congr 1
    · congr 1
      funext ρ
      split_ifs with hs
      · rw [hs]
        rfl
      · rfl
    · split_ifs
      · exact eB _
      · exact congrArg (fun R => laneBit R 0) eN

/-- **One odd modulus of the real garbler** publishes `modGarbled` on the word of its chunks. -/
theorem mod_link (tbl : CrtTable) (S coord v : ℕ) (T : ℕ → Block × Block) (Z : ℕ → Label) (Δ : Label)
    (i : Fin tbl.count) (row : OddRow) (hk : tbl.kind i = .odd row) (wf : RowWF row)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) :
    readMod ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub i.val row =
      modGarbled T coord i.val row (tbl.modulus i) Δ hw0 hw1
        (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 (tbl.modulus i) row.ell) := by
  obtain ⟨w0pos, w1pos, hell, hk0, hk1⟩ := wf
  obtain ⟨-, -, sj, sp, gj, fj⟩ := coord_pub (tableHash T) tbl S coord Δ Z
  obtain ⟨mj, mp, mg, mf⟩ := modGarbleM_odd (tableHash T) tbl S coord Δ
    (atNat (fun c : Fin tbl.chunkCount => (chunkGarbleM tbl coord Δ Z c.val).eval (tableHash T))
      (ChunkGarbled.empty _)) i row hk
  rw [word_eq tbl coord v T Z Δ] at mj mp mg mf
  obtain ⟨cj0, cp0, cj1, cp1, cg, cf⟩ := conversion_table T coord i.val row (tbl.modulus i) Δ
    (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 (tbl.modulus i) row.ell) hw0 hw1 hk0
  refine Prod.ext (Prod.ext (funext fun k => ?_) ?_) (Prod.ext (Prod.ext (funext fun k => ?_) ?_)
    (Prod.ext (funext fun k => ?_) (funext fun k => ?_)))
  · exact (sj i.val i.isLt 0 (k.val + 1)).trans ((congrFun (congrFun mj 0) (k.val + 1)).trans
      (cj0 (k.val + 1) (by omega) (by omega)))
  · have e : (fun j : Fin (row.ell - 1) => ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub.stagePin i.val 0
        j.val) = fun j => atNat (stored (pinBlocks (Parity.pinHalf row.ell (gPin (tableStage T row.width0 hw0 (extTreeTag coord i.val 0)
          (extCastTag coord i.val 0)) (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 (tbl.modulus i)
            row.ell) Δ)))) 0 j.val :=
      funext fun j => (sp i.val i.isLt 0 j.val).trans ((congrFun (congrFun mp 0) j.val).trans (cp0 j.val))
    show pinOfBlocks (row.ell - 1) _ = _
    rw [e, SliceC.pinOfBlocks_atNat_all]
    rfl
  · exact (sj i.val i.isLt 1 (k.val + 1)).trans ((congrFun (congrFun mj 1) (k.val + 1)).trans
      (cj1 (k.val + 1) (by omega) (by omega)))
  · have e : (fun j : Fin (row.ell - row.width0 - 1) =>
        ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub.stagePin i.val 1 j.val) =
        fun j => atNat (stored (pinBlocks (Parity.pinHalf (row.ell - row.width0) (gPin (tableStage T row.width1 hw1 (extTreeTag coord i.val 1)
          (extCastTag coord i.val 1)) (gNext (tableStage T row.width0 hw0 (extTreeTag coord i.val 0)
            (extCastTag coord i.val 0)) (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 (tbl.modulus i)
              row.ell) Δ) Δ)))) 0 j.val :=
      funext fun j => (sp i.val i.isLt 1 j.val).trans ((congrFun (congrFun mp 1) j.val).trans (cp1 j.val))
    show pinOfBlocks (row.ell - row.width0 - 1) _ = _
    rw [e, SliceC.pinOfBlocks_atNat_all]
    rfl
  · exact (gj i.val i.isLt (row.width0 + k.val)).trans ((congrFun mg (row.width0 + k.val)).trans
      (cg k.val k.isLt))
  · exact (fj i.val i.isLt (row.keep + k.val)).trans ((congrFun mf (row.keep + k.val)).trans
      (cf k.val k.isLt))

theorem stageVals_eq_of_empty (r : OddRow) (hr : r = emptyRow) (a b : StageVals r) : a = b := by
  subst hr
  exact stageVals_empty_eq a b

theorem mod_eq_gen (tbl : CrtTable) (S coord v : ℕ) (T : ℕ → Block × Block) (Z : ℕ → Label) (Δ : Label)
    (i : Fin tbl.count) (r row : OddRow) (hr : r = row) (hk : tbl.kind i = .odd row) (wf : RowWF row)
    (hw0 : r.width0 ≤ r.ell) (hw1 : r.width1 ≤ r.ell - r.width0) :
    readMod ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub i.val r =
      modPublish T coord i.val r (tbl.modulus i) (tbl.wordValue (tbl.modulus i) v) Δ hw0 hw1
        (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 (tbl.modulus i) r.ell)
        (readHotMod T coord i.val r (tbl.modulus i) (tbl.wordValue (tbl.modulus i) v)) := by
  subst hr
  rw [modPublish_self _ _ _ _ _ _ _ _ _ _ wf.1 wf.2.1]
  exact mod_link tbl S coord v T Z Δ i r hk wf hw0 hw1

/-- A well-formed row of a modulus comes from its odd kind. -/
theorem rowOf_wf_odd (k : Kind) (m : ℕ) (wf : RowWF (rowOf k m)) :
    ∃ row, k = .odd row ∧ rowOf k m = row ∧ RowWF row := by
  cases k with
  | chunkZero => exact absurd wf.1 (by simp [rowOf, emptyRow])
  | odd row =>
      by_cases h : RowWF row ∧ 0 < m
      · exact ⟨row, rfl, by simp only [rowOf, if_pos h], h.1⟩
      · exfalso
        have e : rowOf (.odd row) m = emptyRow := by simp only [rowOf, if_neg h]
        rw [e] at wf
        exact absurd wf.1 (by simp [emptyRow])

/-- **The real garbler publishes `convPublish` at its own hot readings**: for a well-formed table, the
frozen `coordGarbleM` run on the answer table `T` publishes, read in range, exactly `convPublish` of the rest
`(T, Z, Δ)` at the hidden values `readHot tbl coord v T` (the table's readings at the hot slots of `v`). With
`conversion_uniform` this is the law of the real garbler's conversion material. -/
theorem garbler_conv_eq (tbl : CrtTable) (wf : ConvTableWF tbl) (S coord v : ℕ) (T : ℕ → Block × Block)
    (Z : ℕ → Label) (Δ : Label) :
    readPub tbl ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub =
      convPublish tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T) := by
  obtain ⟨-, jp, -, -, -, -⟩ := coord_pub (tableHash T) tbl S coord Δ Z
  refine Prod.ext (funext fun c => ?_) (funext fun i => ?_)
  · obtain ⟨-, -, cpin⟩ := chunk_table T tbl coord Δ Z c.val
    have e : (fun j : Fin (tbl.castWidth - 1) => ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub.chunkPin c.val
        j.val) = fun j => atNat (stored (pinBlocks (Parity.pinHalf tbl.castWidth ((chunkGarbleM tbl coord Δ Z c.val).eval (tableHash T)).pin)))
          0 j.val :=
      funext fun j => jp c.val c.isLt j.val
    show pinOfBlocks (tbl.castWidth - 1) _ = _
    rw [e, SliceC.pinOfBlocks_atNat_all, cpin]
    show _ = chunkPinH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1 c
    unfold chunkPinH chunkFullPinH
    congr 2
    refine Finset.sum_congr rfl fun leaf _ => ?_
    rw [chunkCastH_self, SliceC.atNat_of_lt _ _ leaf.isLt]
  · rcases rowOf_cases (tbl.kind i) (tbl.modulus i) with e | ⟨rwf, _⟩
    · exact stageVals_eq_of_empty _ e _ _
    · obtain ⟨row, hk, hrow, rowWF⟩ := rowOf_wf_odd _ _ rwf
      exact mod_eq_gen tbl S coord v T Z Δ i _ row hrow hk rowWF (rowOf_hw0 _ _) (rowOf_hw1 _ _)

/-! ### The real table -/

theorem bn254Moduli_ge : ∀ i : Fin bn254Table.count, 17 ≤ bn254Table.modulus i := by
  decide +kernel

/-- **The real table is well formed** (`width8Row_conditions` at every odd modulus, all `≥ 17`). -/
theorem bn254Table_wf : ConvTableWF bn254Table where
  cast := by decide
  rows := by
    intro i row hk
    have hm := bn254Moduli_ge i
    refine ⟨?_, by omega⟩
    have hkind : bn254Table.kind i = width8Kind (bn254Table.modulus i) := rfl
    rw [hkind] at hk
    unfold width8Kind at hk
    split_ifs at hk
    cases hk
    exact SliceC.width8Row_conditions _ hm

end

end Kriterion.CRT.Privacy.Conv
