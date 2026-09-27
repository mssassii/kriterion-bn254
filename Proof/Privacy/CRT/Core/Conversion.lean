/-
**CRT privacy core: the conversion layer of one coordinate is a bijection of its hidden values.**

At input `u` with coordinate value `v`, every gadget of the conversion layer (the chunk trees and casts, the two fused
extraction stages, the growth and the folds of every odd modulus) has one hidden value at its hot slot: a material
(one block, the `.1` of the hot answer) per hashed tree, growth or fold level, and a cast (`Lanes l`) per pin. The
published conversion material has exactly the same shape: one join per hashed level, one pin per cast family. Both
are `ConvVals tbl`.

On the answer-table reading (`ConvTable.lean`) the published material is an explicit function `convPublish` of the rest
(the table's readings at the cold slots, the zero labels, `Δ`) and of the hidden values, which enter by slot
comparison (as `overrideHot` for the stages). It is triangular in two phases:

* every **pin** is its own hidden cast plus a function of the rest;
* every **join** is its own hidden material XOR a function of the rest and of the hidden casts only (the word, the
  class sums, the peeled remainder).

So `convPublish` is injective (`convPublish_injective`), hence a bijection of `ConvVals tbl`, and uniform hidden values
publish uniform material independent of the rest (`conversion_uniform`, the form of `Core/Inversion.lean`'s
`bind_map_uniform_of_injective`). The extraction stages use `spec_publish_injective`.

Malformed schedule rows are normalised away by `rowOf` (a row that fails `RowWF` or has modulus `0` reads
as the empty row), so the statements hold for every table; the link to the real garbler (`garbler_conv_eq`) assumes
the table well formed.
-/

import Proof.Privacy.CRT.Core.ConvTable
import Proof.Privacy.CRT.Core.Inversion

namespace Kriterion.CRT.Privacy.Conv

open Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.ExtractSpec (StageParams gJoin gPin gBit gNext gCast gLeaf gRes gNode gBit0 gLevelSum)
open Kriterion.CRT.Privacy.ExtractStage (Hidden overrideHot specPublish spec_publish_injective)

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
  Hidden 128 row.width0 row.ell × Hidden 128 row.width1 (row.ell - row.width0) ×
    (Fin (row.keep - row.width0) → Block) × (Fin (row.ell - row.keep) → Block)

/-- The values of the chunks: the joins of the hashed tree levels `1 .. w_c − 1` and the pins. -/
abbrev ChunkVals (tbl : CrtTable) : Type :=
  ((c : Fin tbl.chunkCount) → Fin (tbl.chunkWidth c.val - 1) → Block) × (Fin tbl.chunkCount → Lanes tbl.castWidth)

/-- **The conversion values of one coordinate**: the hidden values at the hot slots, and equally the published
conversion material (one join per hashed level, one pin per cast family). -/
abbrev ConvVals (tbl : CrtTable) : Type :=
  ChunkVals tbl × ((i : Fin tbl.count) → StageVals (rowOf (tbl.kind i) (tbl.modulus i)))

instance stageValsFintype (row : OddRow) : Fintype (StageVals row) := by
  unfold StageVals Hidden
  infer_instance

instance stageValsNonempty (row : OddRow) : Nonempty (StageVals row) :=
  ⟨((fun _ => 0, fun _ => 0), (fun _ => 0, fun _ => 0), fun _ => 0, fun _ => 0)⟩

instance convValsFintype (tbl : CrtTable) : Fintype (ConvVals tbl) := by
  unfold ConvVals ChunkVals
  infer_instance

instance convValsNonempty (tbl : CrtTable) : Nonempty (ConvVals tbl) :=
  ⟨((fun _ _ => 0, fun _ _ => 0), fun _ => Classical.arbitrary _)⟩

/-- Everything of one coordinate's conversion that is not hidden: the answer table (read at the cold slots), the zero
labels and `Δ`. -/
structure ConvRest where
  table : ℕ → Block × Block
  zero : ℕ → Block
  delta : Block

/-! ### The published material from the rest and the hidden values -/

section Publish

variable (tbl : CrtTable) (coord v : ℕ) (r : ConvRest)

/-- The cast of leaf `leaf` of chunk `c`: the hidden cast at the hot leaf, the table's reading elsewhere. -/
def chunkCastH (pins : Fin tbl.chunkCount → Lanes tbl.castWidth) (c : Fin tbl.chunkCount) (leaf : ℕ) :
    Lanes tbl.castWidth :=
  if leaf = tbl.chunkValue v c.val then pins c else castRd r.table tbl.castWidth (chunkCastTag coord c.val leaf)

/-- The join of hashed level `k + 1` of chunk `c`. -/
def chunkJoinH (joins : (c : Fin tbl.chunkCount) → Fin (tbl.chunkWidth c.val - 1) → Block) (c : Fin tbl.chunkCount)
    (k : Fin (tbl.chunkWidth c.val - 1)) : Block :=
  xorFold (fun slot : Fin (2 ^ (k.val + 1)) =>
      if slot.val = tbl.chunkValue v c.val % 2 ^ (k.val + 1) then joins c k
      else (r.table (chunkTreeTag coord c.val (k.val + 1) slot.val)).1) ^^^
    r.zero (tbl.chunkOffset c.val + (k.val + 1))

/-- The pin of chunk `c`. -/
def chunkPinH (pins : Fin tbl.chunkCount → Lanes tbl.castWidth) (c : Fin tbl.chunkCount) : Lanes tbl.castWidth :=
  (∑ leaf : Fin (2 ^ tbl.chunkWidth c.val), chunkCastH tbl coord v r pins c leaf.val) +
    deltaLanes tbl.castWidth r.delta

/-- The word of modulus `m` of width `ell` from the chunks' casts (`truthWord`). -/
def wordH (pins : Fin tbl.chunkCount → Lanes tbl.castWidth) (m ell : ℕ) : Lanes ell :=
  reduceTo ell fun lane => ∑ c : Fin tbl.chunkCount, ∑ leaf : Fin (2 ^ tbl.chunkWidth c.val),
    ((tbl.truth m c.val leaf.val : ℕ) : ZMod (2 ^ tbl.castWidth)) * chunkCastH tbl coord v r pins c leaf.val lane

end Publish

/-- **The published material of one modulus** of row `row` and word value `σ`, from the word mask `W` and the
modulus's hidden values `h`: the two stages (`specPublish`, the stage with its hot answers overridden), then the
growth and fold joins with the word's bit masks. -/
def modPublish (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Block)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell)
    (h : StageVals row) : StageVals row :=
  let st0 := tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)
  let st1 := tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1)
  let s0 := σ % 2 ^ row.width0
  let s1 := σ / 2 ^ row.width0 % 2 ^ row.width1
  let R1 : Lanes (row.ell - row.width0) := gNext (overrideHot st0 s0 h.1) W Δ
  let bitMask : ℕ → Block := fun p =>
    if p < row.width0 + row.width1 then gBit (overrideHot st1 s1 h.2.1) R1 Δ (p - row.width0)
    else laneBit (gNext (overrideHot st1 s1 h.2.1) R1 Δ) 0
  (specPublish st0 W Δ s0 h.1, specPublish st1 R1 Δ s1 h.2.1,
    fun k => xorFold (fun slot : Fin (2 ^ (row.width0 + k.val)) =>
        if slot.val = σ % 2 ^ (row.width0 + k.val) then h.2.2.1 k
        else (T (growTag coord i (row.width0 + k.val) slot.val)).1) ^^^ bitMask (row.width0 + k.val),
    fun k => xorFold (fun ρ : Fin m =>
        if ρ.val = σ % 2 ^ (row.keep + k.val) % m then h.2.2.2 k
        else (T (foldTag coord i (row.keep + k.val) ρ.val)).1) ^^^ bitMask (row.keep + k.val))

/-- **The published conversion material of one coordinate** from the rest and the hidden values. -/
def convPublish (tbl : CrtTable) (coord v : ℕ) (r : ConvRest) (h : ConvVals tbl) : ConvVals tbl :=
  ((fun c k => chunkJoinH tbl coord v r h.1.1 c k, fun c => chunkPinH tbl coord v r h.1.2 c),
    fun i => modPublish r.table coord i.val (rowOf (tbl.kind i) (tbl.modulus i)) (tbl.modulus i)
      (tbl.wordValue (tbl.modulus i) v) r.delta (rowOf_hw0 _ _) (rowOf_hw1 _ _)
      (wordH tbl coord v r h.1.2 (tbl.modulus i) (rowOf (tbl.kind i) (tbl.modulus i)).ell) (h.2 i))

/-! ### Injectivity -/

/-- A XOR fold with one hidden slot is the XOR of the others and the hidden value. -/
theorem xorFold_hot {n : ℕ} (hot : ℕ) (hh : hot < n) (y : Block) (Y : Fin n → Block) :
    xorFold (fun slot : Fin n => if slot.val = hot then y else Y slot) = xorFoldExcept ⟨hot, hh⟩ Y ^^^ y := by
  rw [← SliceC.xorFoldExcept_xor ⟨hot, hh⟩ (fun slot : Fin n => if slot.val = hot then y else Y slot), if_pos rfl]
  congr 1
  refine SliceC.xorFoldExcept_congr _ _ _ fun slot hs => ?_
  rw [if_neg fun h => hs (Fin.ext h)]

theorem xor_cancel_mid (K y y' z : Block) (h : K ^^^ y ^^^ z = K ^^^ y' ^^^ z) : y = y' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have e := congrArg (fun t : Block => t.getLsbD i) h
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

/-- **One modulus is injective in its hidden values.** -/
theorem modPublish_injective (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Block)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell)
    (hrow : row = emptyRow ∨ (RowWF row ∧ 0 < m)) :
    Function.Injective (modPublish T coord i row m σ Δ hw0 hw1 W) := by
  intro a b e
  rcases hrow with rfl | ⟨⟨w0pos, w1pos, _, _, _⟩, hm⟩
  · exact stageVals_empty_eq a b
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  have e0 : specPublish (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ
      (σ % 2 ^ row.width0) a0 =
      specPublish (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ
      (σ % 2 ^ row.width0) b0 := congrArg (fun x => x.1) e
  have h0 : a0 = b0 := spec_publish_injective _ w0pos W Δ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) e0
  subst h0
  have e1 : specPublish (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (gNext (overrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) a0) W Δ) Δ (σ / 2 ^ row.width0 % 2 ^ row.width1) a1 =
      specPublish (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (gNext (overrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) a0) W Δ) Δ (σ / 2 ^ row.width0 % 2 ^ row.width1) b1 :=
    congrArg (fun x => x.2.1) e
  have h1 : a1 = b1 := spec_publish_injective _ w1pos _ Δ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) e1
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
  rintro ⟨⟨hJ, hP⟩, hM⟩ ⟨⟨hJ', hP'⟩, hM'⟩ same
  have pins : hP = hP' := funext fun c => by
    have e := congrArg (fun x => x.1.2 c) same
    simp only [convPublish, chunkPinH, chunkCastH] at e
    have e' := add_right_cancel e
    have hot : tbl.chunkValue v c.val < 2 ^ tbl.chunkWidth c.val := Nat.mod_lt _ (Nat.two_pow_pos _)
    exact sum_hot_cancel _ hot (hP c) (hP' c)
      (fun leaf => castRd r.table tbl.castWidth (chunkCastTag coord c.val leaf)) e'
  subst pins
  have joins : hJ = hJ' := funext fun c => funext fun k => by
    have e := congrArg (fun x => x.1.1 c k) same
    simp only [convPublish, chunkJoinH] at e
    rw [xorFold_hot _ (Nat.mod_lt _ (Nat.two_pow_pos _)), xorFold_hot _ (Nat.mod_lt _ (Nat.two_pow_pos _))] at e
    exact xor_cancel_mid _ _ _ _ e
  subst joins
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
theorem gCast_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (s α : ℕ) :
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

theorem gRes_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (s n : ℕ) :
    gRes (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ n = gRes sp R Δ n :=
  Finset.sum_congr rfl fun α _ => by rw [gCast_override_self]

theorem gNext_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (s : ℕ) :
    (gNext (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ : Lanes (rb - sp.w)) = gNext sp R Δ := by
  show peelDiv R (gRes (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ sp.w) sp.w =
    peelDiv R (gRes sp R Δ sp.w) sp.w
  rw [gRes_override_self]

theorem gBit_override_self (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (s n : ℕ) :
    gBit (overrideHot sp s (ExtractStage.hiddenOfSpec sp R Δ s)) R Δ n = gBit sp R Δ n := by
  unfold gBit
  rw [gRes_override_self]
  rfl

/-- At its own hot answers the overridden stage publishes what the stage publishes. -/
theorem specPublish_self (sp : StageParams rb) (R : Lanes rb) (Δ : Block) (s : ℕ) (hw1 : 1 ≤ sp.w) :
    specPublish sp R Δ s (ExtractStage.hiddenOfSpec sp R Δ s) =
      ((fun k : Fin (sp.w - 1) => gJoin sp R Δ (k.val + 1)), gPin sp R Δ) := by
  unfold specPublish
  rw [ExtractStage.spec_publish_eq sp R Δ s _ hw1, ← ExtractStage.spec_garbler_eq_publish sp R Δ s hw1]

end Link

/-- The in-range published material of one modulus of row `row`. -/
def readMod (pub : ConvPublic) (i : ℕ) (row : OddRow) : StageVals row :=
  ((fun k => pub.stageJoin i 0 (k.val + 1), pinOfBlocks row.ell fun j => pub.stagePin i 0 j.val),
    (fun k => pub.stageJoin i 1 (k.val + 1), pinOfBlocks (row.ell - row.width0) fun j => pub.stagePin i 1 j.val),
    fun k => pub.growJoin i (row.width0 + k.val), fun k => pub.foldJoin i (row.keep + k.val))

/-- **The published conversion material read in range** (pins through the dense codec). -/
def readPub (tbl : CrtTable) (pub : ConvPublic) : ConvVals tbl :=
  ((fun c k => pub.chunkJoin c.val (k.val + 1), fun c => pinOfBlocks tbl.castWidth fun j => pub.chunkPin c.val j.val),
    fun i => readMod pub i.val (rowOf (tbl.kind i) (tbl.modulus i)))

/-- A table's readings at the hot slots of one modulus of row `row` and word value `σ`. -/
def readHotMod (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) : StageVals row :=
  ((fun k => (T (extTreeTag coord i 0 (k.val + 1) (σ % 2 ^ row.width0 % 2 ^ (k.val + 1)))).1,
      castRd T row.ell (extCastTag coord i 0 (σ % 2 ^ row.width0))),
    (fun k => (T (extTreeTag coord i 1 (k.val + 1) (σ / 2 ^ row.width0 % 2 ^ row.width1 % 2 ^ (k.val + 1)))).1,
      castRd T (row.ell - row.width0) (extCastTag coord i 1 (σ / 2 ^ row.width0 % 2 ^ row.width1))),
    fun k => (T (growTag coord i (row.width0 + k.val) (σ % 2 ^ (row.width0 + k.val)))).1,
    fun k => (T (foldTag coord i (row.keep + k.val) (σ % 2 ^ (row.keep + k.val) % m))).1)

/-- **A table's readings at the hot slots of the coordinate value `v`**: the hidden values the garbler's own table
gives. -/
def readHot (tbl : CrtTable) (coord v : ℕ) (T : ℕ → Block × Block) : ConvVals tbl :=
  ((fun c k => (T (chunkTreeTag coord c.val (k.val + 1) (tbl.chunkValue v c.val % 2 ^ (k.val + 1)))).1,
      fun c => castRd T tbl.castWidth (chunkCastTag coord c.val (tbl.chunkValue v c.val))),
    fun i => readHotMod T coord i.val (rowOf (tbl.kind i) (tbl.modulus i)) (tbl.modulus i)
      (tbl.wordValue (tbl.modulus i) v))

/-- A table the conversion's link needs: a positive cast width and well-formed odd rows with positive moduli. -/
structure ConvTableWF (tbl : CrtTable) : Prop where
  cast : 0 < tbl.castWidth
  rows : ∀ i row, tbl.kind i = .odd row → RowWF row ∧ 0 < tbl.modulus i

/-- The program's word (from the chunks' casts on the table) is `wordH` at the table's own hot readings. -/
theorem word_eq (tbl : CrtTable) (coord v : ℕ) (T : ℕ → Block × Block) (Z : ℕ → Block) (Δ : Block) (m ell : ℕ) :
    truthWord tbl m ell (fun c leaf =>
        (atNat (fun c : Fin tbl.chunkCount => (chunkGarbleM tbl coord Δ Z c.val).eval (tableHash T))
          (ChunkGarbled.empty _) c).casts leaf) =
      wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.2 m ell := by
  unfold truthWord wordH
  rw [materialize_eq]
  congr 1
  funext lane
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun leaf _ => ?_
  congr 1
  beta_reduce
  rw [SliceC.atNat_of_lt _ _ c.isLt, (chunk_table T tbl coord Δ Z c.val).2.1 leaf.val leaf.isLt]
  unfold chunkCastH
  split_ifs with h
  · rw [h]
    rfl
  · rfl

/-- The published material of one odd modulus as the garbler computes it on a table (`conversion_table`). -/
def modGarbled (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m : ℕ) (Δ : Block)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell) : StageVals row :=
  let sp0 := tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)
  let sp1 := tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1)
  let R1 : Lanes (row.ell - row.width0) := gNext sp0 W Δ
  let bitMask : ℕ → Block := fun p =>
    if p < row.width0 + row.width1 then gBit sp1 R1 Δ (p - row.width0) else laneBit (gNext sp1 R1 Δ) 0
  (((fun k : Fin (row.width0 - 1) => gJoin sp0 W Δ (k.val + 1)), gPin sp0 W Δ),
    ((fun k : Fin (row.width1 - 1) => gJoin sp1 R1 Δ (k.val + 1)), gPin sp1 R1 Δ),
    fun k => xorFold (fun slot : Fin (2 ^ (row.width0 + k.val)) =>
        (T (growTag coord i (row.width0 + k.val) slot.val)).1) ^^^ bitMask (row.width0 + k.val),
    fun k => xorFold (fun ρ : Fin m => (T (foldTag coord i (row.keep + k.val) ρ.val)).1) ^^^
      bitMask (row.keep + k.val))

/-- **One modulus at its own hot readings** publishes what the garbler publishes. -/
theorem modPublish_self (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Block)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell)
    (w0pos : 1 ≤ row.width0) (w1pos : 1 ≤ row.width1) :
    modPublish T coord i row m σ Δ hw0 hw1 W (readHotMod T coord i row m σ) =
      modGarbled T coord i row m Δ hw0 hw1 W := by
  have eR : (gNext (overrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
      (σ % 2 ^ row.width0) (readHotMod T coord i row m σ).1) W Δ : Lanes (row.ell - row.width0)) =
      gNext (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ :=
    gNext_override_self _ W Δ _
  have eB : ∀ n, gBit (overrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1)
      (gNext (overrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) (readHotMod T coord i row m σ).1) W Δ) Δ n =
      gBit (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
        (gNext (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ) Δ n := fun n =>
    (congrArg (fun R => gBit (overrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1)
      (extCastTag coord i 1)) (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1) R Δ n)
      eR).trans (gBit_override_self _ _ Δ _ n)
  have eN : (gNext (overrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1)
      (gNext (overrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
        (σ % 2 ^ row.width0) (readHotMod T coord i row m σ).1) W Δ) Δ :
        Lanes (row.ell - row.width0 - row.width1)) =
      gNext (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
        (gNext (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ) Δ :=
    (congrArg (fun R => (gNext (overrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1)
      (extCastTag coord i 1)) (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1) R Δ :
        Lanes (row.ell - row.width0 - row.width1))) eR).trans (gNext_override_self _ _ Δ _)
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact specPublish_self (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ
      (σ % 2 ^ row.width0) w0pos
  · exact (congrArg (fun R => specPublish (tableStage T row.width1 hw1 (extTreeTag coord i 1)
      (extCastTag coord i 1)) R Δ (σ / 2 ^ row.width0 % 2 ^ row.width1) (readHotMod T coord i row m σ).2.1)
      eR).trans (specPublish_self _ _ Δ _ w1pos)
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
theorem mod_link (tbl : CrtTable) (S coord v : ℕ) (T : ℕ → Block × Block) (Z : ℕ → Block) (Δ : Block)
    (i : Fin tbl.count) (row : OddRow) (hk : tbl.kind i = .odd row) (wf : RowWF row)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) :
    readMod ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub i.val row =
      modGarbled T coord i.val row (tbl.modulus i) Δ hw0 hw1
        (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.2 (tbl.modulus i) row.ell) := by
  obtain ⟨w0pos, w1pos, hell, hk0, hk1⟩ := wf
  obtain ⟨-, -, sj, sp, gj, fj⟩ := coord_pub (tableHash T) tbl S coord Δ Z
  obtain ⟨mj, mp, mg, mf⟩ := modGarbleM_odd (tableHash T) tbl S coord Δ
    (atNat (fun c : Fin tbl.chunkCount => (chunkGarbleM tbl coord Δ Z c.val).eval (tableHash T))
      (ChunkGarbled.empty _)) i row hk
  rw [word_eq tbl coord v T Z Δ] at mj mp mg mf
  obtain ⟨cj0, cp0, cj1, cp1, cg, cf⟩ := conversion_table T coord i.val row (tbl.modulus i) Δ
    (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.2 (tbl.modulus i) row.ell) hw0 hw1 hk0
  refine Prod.ext (Prod.ext (funext fun k => ?_) ?_) (Prod.ext (Prod.ext (funext fun k => ?_) ?_)
    (Prod.ext (funext fun k => ?_) (funext fun k => ?_)))
  · exact (sj i.val i.isLt 0 (k.val + 1)).trans ((congrFun (congrFun mj 0) (k.val + 1)).trans
      (cj0 (k.val + 1) (by omega) (by omega)))
  · have e : (fun j : Fin row.ell => ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub.stagePin i.val 0
        j.val) = fun j => atNat (stored (pinBlocks (gPin (tableStage T row.width0 hw0 (extTreeTag coord i.val 0)
          (extCastTag coord i.val 0)) (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.2 (tbl.modulus i)
            row.ell) Δ))) 0 j.val :=
      funext fun j => (sp i.val i.isLt 0 j.val).trans ((congrFun (congrFun mp 0) j.val).trans (cp0 j.val))
    show pinOfBlocks row.ell _ = _
    rw [e, SliceC.pinOfBlocks_atNat (by omega)]
    rfl
  · exact (sj i.val i.isLt 1 (k.val + 1)).trans ((congrFun (congrFun mj 1) (k.val + 1)).trans
      (cj1 (k.val + 1) (by omega) (by omega)))
  · have e : (fun j : Fin (row.ell - row.width0) =>
        ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub.stagePin i.val 1 j.val) =
        fun j => atNat (stored (pinBlocks (gPin (tableStage T row.width1 hw1 (extTreeTag coord i.val 1)
          (extCastTag coord i.val 1)) (gNext (tableStage T row.width0 hw0 (extTreeTag coord i.val 0)
            (extCastTag coord i.val 0)) (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.2 (tbl.modulus i)
              row.ell) Δ) Δ))) 0 j.val :=
      funext fun j => (sp i.val i.isLt 1 j.val).trans ((congrFun (congrFun mp 1) j.val).trans (cp1 j.val))
    show pinOfBlocks (row.ell - row.width0) _ = _
    rw [e, SliceC.pinOfBlocks_atNat (by omega)]
    rfl
  · exact (gj i.val i.isLt (row.width0 + k.val)).trans ((congrFun mg (row.width0 + k.val)).trans
      (cg k.val k.isLt))
  · exact (fj i.val i.isLt (row.keep + k.val)).trans ((congrFun mf (row.keep + k.val)).trans
      (cf k.val k.isLt))

theorem stageVals_eq_of_empty (r : OddRow) (hr : r = emptyRow) (a b : StageVals r) : a = b := by
  subst hr
  exact stageVals_empty_eq a b

theorem mod_eq_gen (tbl : CrtTable) (S coord v : ℕ) (T : ℕ → Block × Block) (Z : ℕ → Block) (Δ : Block)
    (i : Fin tbl.count) (r row : OddRow) (hr : r = row) (hk : tbl.kind i = .odd row) (wf : RowWF row)
    (hw0 : r.width0 ≤ r.ell) (hw1 : r.width1 ≤ r.ell - r.width0) :
    readMod ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub i.val r =
      modPublish T coord i.val r (tbl.modulus i) (tbl.wordValue (tbl.modulus i) v) Δ hw0 hw1
        (wordH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.2 (tbl.modulus i) r.ell)
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
    (Z : ℕ → Block) (Δ : Block) :
    readPub tbl ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub =
      convPublish tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T) := by
  obtain ⟨cp, jp, -, -, -, -⟩ := coord_pub (tableHash T) tbl S coord Δ Z
  refine Prod.ext (Prod.ext (funext fun c => funext fun k => ?_) (funext fun c => ?_)) (funext fun i => ?_)
  · obtain ⟨cj, -, -⟩ := chunk_table T tbl coord Δ Z c.val
    refine (cp c.val c.isLt (k.val + 1)).trans ((cj (k.val + 1) (by omega) (by omega)).trans ?_)
    show _ = chunkJoinH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.1 c k
    unfold chunkJoinH
    congr 1
    congr 1
    funext slot
    split_ifs with hs
    · rw [hs]
      rfl
    · rfl
  · obtain ⟨-, -, cpin⟩ := chunk_table T tbl coord Δ Z c.val
    have e : (fun j : Fin tbl.castWidth => ((coordGarbleM tbl S coord Δ Z).eval (tableHash T)).pub.chunkPin c.val
        j.val) = fun j => atNat (stored (pinBlocks ((chunkGarbleM tbl coord Δ Z c.val).eval (tableHash T)).pin))
          0 j.val :=
      funext fun j => jp c.val c.isLt j.val
    show pinOfBlocks tbl.castWidth _ = _
    rw [e, SliceC.pinOfBlocks_atNat wf.cast, cpin]
    show _ = chunkPinH tbl coord v ⟨T, Z, Δ⟩ (readHot tbl coord v T).1.2 c
    unfold chunkPinH chunkCastH
    congr 1
    refine Finset.sum_congr rfl fun leaf _ => ?_
    split_ifs with h
    · rw [h]
      rfl
    · rfl
  · rcases rowOf_cases (tbl.kind i) (tbl.modulus i) with e | ⟨rwf, _⟩
    · exact stageVals_eq_of_empty _ e _ _
    · obtain ⟨row, hk, hrow, rowWF⟩ := rowOf_wf_odd _ _ rwf
      exact mod_eq_gen tbl S coord v T Z Δ i _ row hrow hk rowWF (rowOf_hw0 _ _) (rowOf_hw1 _ _)

/-! ### The real table -/

theorem bn254Moduli_ge : ∀ i : Fin bn254Table.count, 17 ≤ bn254Table.modulus i := by
  decide +kernel

/-- **The real table is well formed** (`fallbackRow_conditions` at every odd modulus, all `≥ 17`). -/
theorem bn254Table_wf : ConvTableWF bn254Table where
  cast := by decide
  rows := by
    intro i row hk
    have hm := bn254Moduli_ge i
    refine ⟨?_, by omega⟩
    have hkind : bn254Table.kind i = fallbackKind (bn254Table.modulus i) := rfl
    rw [hkind] at hk
    unfold fallbackKind at hk
    split_ifs at hk
    cases hk
    exact SliceC.fallbackRow_conditions _ hm

end

end Kriterion.CRT.Privacy.Conv
