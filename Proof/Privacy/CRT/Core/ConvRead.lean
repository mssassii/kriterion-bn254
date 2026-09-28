/-
**CRT privacy core, part (a): the hot readings of a uniform tag table are uniform.**

`Conversion.lean` states the conversion core on the hidden values `ConvVals tbl`. On the chain's tag table
(`TagTable := Fin (2 ^ 40) → Block × Block`, read by tag, `tagRead`) the garbler's own hidden values are the readings
of the table at the hot tags (`readHot tbl coord v (tagRead A)`): `clip` of `.1` of one answer per hashed tree, growth or fold
level, the upper planes of the cast reading of `castAnswers l` answers per pin. This file names every such read (`HotRead tbl`, one index
per answer read) and its tag (`readTag`), shows that the hot readings are a fixed function `rho` of the table read at
those tags (`readHot_eq`, by `rfl`), and that `rho` pushes the uniform law to the uniform law (`rho_uniform`, from the
clipped first-block projection and `upperRead_uniform`). The index types are built from sums and sigmas in the shape of
`ConvVals`, so the law is the composition of `TableSplit`'s combinators.
-/

import Proof.Privacy.CRT.Core.LabelUniform
import Proof.Privacy.CRT.Core.ParityRead
import Proof.Privacy.CRT.Core.Conversion
import Proof.Privacy.CRT.Core.TableSplit
import Proof.Privacy.CRT.Swap.Reading
import Proof.Privacy.CRT.Sites

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Conv

open Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.ExtractStage (Hidden UpperHidden)
open Kriterion.CRT.ExtractSpec (StageParams gJoin gPin gBit gNext gCast gLeaf gRes gNode gBit0 gLevelSum)
open Kriterion.CRT.Privacy.Split (pi_map_uniform prod_map_uniform)

noncomputable section

/-! ### Uniform-preserving combinators -/

section Combinators

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

/-- Reading the two halves of a table indexed by a sum. -/
theorem sum_map_uniform {α β C D : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype C]
    [Nonempty C] [Fintype D] [Nonempty D] [DecidableEq C] [DecidableEq D] (F : (α → X) → C) (G : (β → X) → D)
    (uF : (PMF.uniformOfFintype (α → X)).map F = PMF.uniformOfFintype C)
    (uG : (PMF.uniformOfFintype (β → X)).map G = PMF.uniformOfFintype D) :
    (PMF.uniformOfFintype ((α ⊕ β) → X)).map (fun g => (F fun a => g (.inl a), G fun b => g (.inr b))) =
      PMF.uniformOfFintype (C × D) := by
  have factor : (fun g : (α ⊕ β) → X => (F fun a => g (.inl a), G fun b => g (.inr b))) =
      (fun p : (α → X) × (β → X) => (F p.1, G p.2)) ∘ Equiv.sumArrowEquivProdArrow α β X := by
    funext g
    rfl
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]
  exact prod_map_uniform F G uF uG

/-- Reading every fibre of a table indexed by a sigma. -/
theorem sigma_map_uniform {I : Type} [Fintype I] [DecidableEq I] {β C : I → Type} [∀ i, Fintype (β i)]
    [∀ i, DecidableEq (β i)] [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)] [∀ i, DecidableEq (C i)]
    (F : ∀ i, (β i → X) → C i) (uF : ∀ i, (PMF.uniformOfFintype (β i → X)).map (F i) = PMF.uniformOfFintype (C i)) :
    (PMF.uniformOfFintype ((Σ i, β i) → X)).map (fun g i => F i fun b => g ⟨i, b⟩) =
      PMF.uniformOfFintype (∀ i, C i) := by
  have factor : (fun g : (Σ i, β i) → X => fun i => F i fun b => g ⟨i, b⟩) =
      (fun p : ∀ i, β i → X => fun i => F i (p i)) ∘ Equiv.piCurry (fun i (_ : β i) => X) := by
    funext g
    rfl
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]
  exact pi_map_uniform F uF

end Combinators

/-- The first block of a uniform answer remains a full raw block (digest consumers). -/
theorem fst_uniform : (PMF.uniformOfFintype (Block × Block)).map Prod.fst = PMF.uniformOfFintype Block := by
  classical
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun b b' => ?_
  exact {
    toFun := fun p => ⟨(b', p.1.2), rfl⟩
    invFun := fun p => ⟨(b, p.1.2), rfl⟩
    left_inv := fun p => Subtype.ext (Prod.ext p.2.symm rfl)
    right_inv := fun p => Subtype.ext (Prod.ext p.2.symm rfl) }

/-- The clipped first block of a uniform answer is uniform. -/
theorem clip_fst_uniform : (PMF.uniformOfFintype (Block × Block)).map (fun a => clip a.1) =
    PMF.uniformOfFintype Label := Narrow.uniform_answer_clip

set_option maxRecDepth 4096 in
/-- The clipped first blocks of uniform answers are uniform active labels. -/
theorem fsts_uniform (n : ℕ) :
    (PMF.uniformOfFintype (Fin n → Block × Block)).map (fun g k => (clip (g k).1)) = PMF.uniformOfFintype (Fin n → Label) :=
  pi_map_uniform (fun (_ : Fin n) (a : Block × Block) => clip a.1) fun _ => clip_fst_uniform

theorem lanes_subsingleton_zero (a b : Lanes 0) : a = b := lanes_zero_eq a b

/-- **A cast reading of uniform answers is uniform** (width at most `128`; the width `0` of the empty row is a single
point). -/
theorem castRead_uniform (l : ℕ) (hl : l ≤ 128) :
    (PMF.uniformOfFintype (Fin (castAnswers l) → Block × Block)).map
        (fun answers => castLanes l (packAnswers (castAnswers l) answers)) = PMF.uniformOfFintype (Lanes l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · refine PMF.ext fun a => ?_
    have one : ∀ b : Lanes 0, b = a := fun b => lanes_zero_eq b a
    rw [PMF.map_apply, PMF.uniformOfFintype_apply]
    have card : Fintype.card (Lanes 0) = 1 := Fintype.card_eq_one_iff.mpr ⟨a, fun b => one b⟩
    rw [card, Nat.cast_one, inv_one]
    simp only [one _, if_true]
    exact PMF.tsum_coe _
  · exact Privacy.castLanes_uniform l hpos hl

/-- Only the upper cast planes are independent hidden randomness. The old full
cast reading is used solely before its low plane is discarded. -/
theorem upperRead_uniform (l : ℕ) (hl : l ≤ 128) :
    (PMF.uniformOfFintype (Fin (castAnswers l) → Block × Block)).map
        (fun answers => Parity.pinHalf l (castLanes l (packAnswers (castAnswers l) answers))) =
      PMF.uniformOfFintype (Lanes (l - 1)) := by
  change (PMF.uniformOfFintype _).map
    ((Parity.pinHalf l) ∘ fun answers => castLanes l (packAnswers (castAnswers l) answers)) = _
  rw [← PMF.map_comp, castRead_uniform l hl, ParityRead.pinHalf_uniform]

/-! ### The hot reads -/

/-- The hot reads of one fused stage: the hashed levels' materials and the hot cast's answers. -/
abbrev PairRead (w l : ℕ) : Type := Fin (w - 1) ⊕ Fin (castAnswers l)

/-- The hot reads of one modulus: stage 0, stage 1, growth, folds (the shape of `StageVals`). -/
abbrev StageRead (row : OddRow) : Type :=
  PairRead row.width0 row.ell ⊕ (PairRead row.width1 (row.ell - row.width0) ⊕
    (Fin (row.keep - row.width0) ⊕ Fin (row.ell - row.keep)))

/-- The hot reads of the chunks: the hashed levels' materials and the hot casts' answers. -/
abbrev ChunkRead (tbl : CrtTable) : Type :=
  (Σ c : Fin tbl.chunkCount, Fin (tbl.chunkWidth c.val - 1)) ⊕ (Σ c : Fin tbl.chunkCount, Fin (castAnswers tbl.castWidth))

/-- **Every hot read of one coordinate**: one index per answer the garbler's hidden values read. -/
abbrev HotRead (tbl : CrtTable) : Type :=
  ChunkRead tbl ⊕ (Σ i : Fin tbl.count, StageRead (rowOf (tbl.kind i) (tbl.modulus i)))

/-- The clipped first blocks of a family of raw answers. -/
def fstRho (n : ℕ) (g : Fin n → Block × Block) : Fin n → Label := fun k => (clip (g k).1)

/-- A stage's hidden tuple from its reads. -/
def pairRho (w l : ℕ) (g : PairRead w l → Block × Block) : UpperHidden w l :=
  (fstRho _ fun k => g (.inl k), Parity.pinHalf l (castLanes l (packAnswers (castAnswers l) fun j => g (.inr j))))

/-- The growth and fold materials of a modulus from their reads. -/
def gfRho (row : OddRow) (g : (Fin (row.keep - row.width0) ⊕ Fin (row.ell - row.keep)) → Block × Block) :
    (Fin (row.keep - row.width0) → Label) × (Fin (row.ell - row.keep) → Label) :=
  (fstRho _ fun k => g (.inl k), fstRho _ fun k => g (.inr k))

/-- Stage 1, growth and folds of a modulus from their reads. -/
def tailRho (row : OddRow) (g : (PairRead row.width1 (row.ell - row.width0) ⊕
    (Fin (row.keep - row.width0) ⊕ Fin (row.ell - row.keep))) → Block × Block) :
    UpperHidden row.width1 (row.ell - row.width0) ×
      ((Fin (row.keep - row.width0) → Label) × (Fin (row.ell - row.keep) → Label)) :=
  (pairRho row.width1 (row.ell - row.width0) fun r => g (.inl r), gfRho row fun r => g (.inr r))

/-- A modulus's hidden values from its reads. -/
def stageRho (row : OddRow) (g : StageRead row → Block × Block) : StageVals row :=
  (pairRho row.width0 row.ell fun r => g (.inl r), tailRho row fun r => g (.inr r))

/-- The chunks' tree materials from their reads. -/
def chunkJoinRho (tbl : CrtTable) (g : (Σ c : Fin tbl.chunkCount, Fin (tbl.chunkWidth c.val - 1)) → Block × Block) :
    (c : Fin tbl.chunkCount) → Fin (tbl.chunkWidth c.val - 1) → Label :=
  fun c => fstRho _ fun k => g ⟨c, k⟩

/-- The chunks' hot casts from their reads. -/
def chunkPinRho (tbl : CrtTable) (g : (Σ c : Fin tbl.chunkCount, Fin (castAnswers tbl.castWidth)) → Block × Block) :
    Fin tbl.chunkCount → Lanes (tbl.castWidth - 1) :=
  fun c => Parity.pinHalf tbl.castWidth (castLanes tbl.castWidth (packAnswers (castAnswers tbl.castWidth) fun j => g ⟨c, j⟩))

/-- The chunks' hidden values from their reads. -/
def chunkRho (tbl : CrtTable) (g : ChunkRead tbl → Block × Block) : ChunkVals tbl :=
  (chunkJoinRho tbl fun r => g (.inl r), chunkPinRho tbl fun r => g (.inr r))

/-- The moduli's hidden values from their reads. -/
def modsRho (tbl : CrtTable) (g : (Σ i : Fin tbl.count, StageRead (rowOf (tbl.kind i) (tbl.modulus i))) → Block × Block) :
    (i : Fin tbl.count) → StageVals (rowOf (tbl.kind i) (tbl.modulus i)) :=
  fun i => stageRho _ fun s => g ⟨i, s⟩

/-- **The hidden values from the hot reads.** -/
def rho (tbl : CrtTable) (g : HotRead tbl → Block × Block) : ConvVals tbl :=
  (chunkRho tbl fun r => g (.inl r), modsRho tbl fun r => g (.inr r))

theorem fstRho_uniform (n : ℕ) :
    (PMF.uniformOfFintype (Fin n → Block × Block)).map (fstRho n) = PMF.uniformOfFintype (Fin n → Label) :=
  fsts_uniform n

theorem pairRho_uniform (w l : ℕ) (hl : l ≤ 128) :
    (PMF.uniformOfFintype (PairRead w l → Block × Block)).map (pairRho w l) =
      PMF.uniformOfFintype (UpperHidden w l) :=
  sum_map_uniform (fstRho _) (fun g => Parity.pinHalf l (castLanes l (packAnswers (castAnswers l) g))) (fstRho_uniform _)
    (upperRead_uniform l hl)

theorem gfRho_uniform (row : OddRow) :
    (PMF.uniformOfFintype ((Fin (row.keep - row.width0) ⊕ Fin (row.ell - row.keep)) → Block × Block)).map
      (gfRho row) = PMF.uniformOfFintype ((Fin (row.keep - row.width0) → Label) × (Fin (row.ell - row.keep) → Label)) :=
  sum_map_uniform (fstRho _) (fstRho _) (fstRho_uniform _) (fstRho_uniform _)

theorem tailRho_uniform (row : OddRow) (hl : row.ell ≤ 128) :
    (PMF.uniformOfFintype ((PairRead row.width1 (row.ell - row.width0) ⊕
      (Fin (row.keep - row.width0) ⊕ Fin (row.ell - row.keep))) → Block × Block)).map (tailRho row) =
      PMF.uniformOfFintype (UpperHidden row.width1 (row.ell - row.width0) ×
        ((Fin (row.keep - row.width0) → Label) × (Fin (row.ell - row.keep) → Label))) :=
  sum_map_uniform (pairRho _ _) (gfRho row) (pairRho_uniform _ _ (le_trans (Nat.sub_le _ _) hl)) (gfRho_uniform row)

theorem stageRho_uniform (row : OddRow) (hl : row.ell ≤ 128) :
    (PMF.uniformOfFintype (StageRead row → Block × Block)).map (stageRho row) =
      PMF.uniformOfFintype (StageVals row) :=
  sum_map_uniform (pairRho _ _) (tailRho row) (pairRho_uniform _ _ hl) (tailRho_uniform row hl)

theorem chunkRho_uniform (tbl : CrtTable) (hL : tbl.castWidth ≤ 128) :
    (PMF.uniformOfFintype (ChunkRead tbl → Block × Block)).map (chunkRho tbl) =
      PMF.uniformOfFintype (ChunkVals tbl) :=
  sum_map_uniform (chunkJoinRho tbl) (chunkPinRho tbl)
    (sigma_map_uniform (β := fun c : Fin tbl.chunkCount => Fin (tbl.chunkWidth c.val - 1))
      (fun _ => fstRho _) fun _ => fstRho_uniform _)
    (sigma_map_uniform (β := fun _ : Fin tbl.chunkCount => Fin (castAnswers tbl.castWidth))
      (fun _ g => Parity.pinHalf tbl.castWidth (castLanes tbl.castWidth (packAnswers (castAnswers tbl.castWidth) g))) fun _ => upperRead_uniform _ hL)

/-- **The hidden values of uniform hot reads are uniform** (cast widths at most `128`). -/
theorem rho_uniform (tbl : CrtTable) (hL : tbl.castWidth ≤ 128)
    (hl : ∀ i, (rowOf (tbl.kind i) (tbl.modulus i)).ell ≤ 128) :
    (PMF.uniformOfFintype (HotRead tbl → Block × Block)).map (rho tbl) = PMF.uniformOfFintype (ConvVals tbl) :=
  sum_map_uniform (chunkRho tbl) (modsRho tbl) (chunkRho_uniform tbl hL)
    (sigma_map_uniform (β := fun i : Fin tbl.count => StageRead (rowOf (tbl.kind i) (tbl.modulus i)))
      (fun i => stageRho (rowOf (tbl.kind i) (tbl.modulus i))) fun i => stageRho_uniform _ (hl i))

/-! ### The tags of the hot reads -/

/-- A tag table read as a table of naturals (tags below `2 ^ 40`, D10). -/
def tagRead (A : Fin (2 ^ 40) → Block × Block) : ℕ → Block × Block := fun n =>
  A ⟨n % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- The tag of a natural. -/
def tag40 (n : ℕ) : Fin (2 ^ 40) := ⟨n % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- The tags of one modulus's hot reads (row `row`, modulus `m`, word value `σ`). -/
def stageReadTag (coord i : ℕ) (row : OddRow) (m σ : ℕ) : StageRead row → ℕ
  | .inl (.inl k) => extTreeTag coord i 0 (k.val + 1) (σ % 2 ^ row.width0 % 2 ^ (k.val + 1))
  | .inl (.inr j) => extCastTag coord i 0 (σ % 2 ^ row.width0) j.val
  | .inr (.inl (.inl k)) =>
      extTreeTag coord i 1 (k.val + 1) (σ / 2 ^ row.width0 % 2 ^ row.width1 % 2 ^ (k.val + 1))
  | .inr (.inl (.inr j)) => extCastTag coord i 1 (σ / 2 ^ row.width0 % 2 ^ row.width1) j.val
  | .inr (.inr (.inl k)) => growTag coord i (row.width0 + k.val) (σ % 2 ^ (row.width0 + k.val))
  | .inr (.inr (.inr k)) => foldTag coord i (row.keep + k.val) (σ % 2 ^ (row.keep + k.val) % m)

/-- **The tag of every hot read of coordinate `coord` at value `v`.** -/
def readTag (tbl : CrtTable) (coord v : ℕ) : HotRead tbl → ℕ
  | .inl (.inl ⟨c, k⟩) => chunkTreeTag coord c.val (k.val + 1) (tbl.chunkValue v c.val % 2 ^ (k.val + 1))
  | .inl (.inr ⟨c, j⟩) => chunkCastTag coord c.val (tbl.chunkValue v c.val) j.val
  | .inr ⟨i, s⟩ => stageReadTag coord i.val (rowOf (tbl.kind i) (tbl.modulus i)) (tbl.modulus i)
      (tbl.wordValue (tbl.modulus i) v) s

/-- **The hot readings are `rho` of the table at the hot tags.** -/
theorem readHot_eq (tbl : CrtTable) (coord v : ℕ) (A : Fin (2 ^ 40) → Block × Block) :
    readHot tbl coord v (tagRead A) = rho tbl fun r => A (tag40 (readTag tbl coord v r)) :=
  rfl


/-! ### The hot tags are distinct -/

/-- A cast reads at most `64` answers (no lane straddles a block, D11). -/
theorem castAnswers_le (l : ℕ) : castAnswers l ≤ 64 := by
  unfold castAnswers castBlocks
  rcases Nat.eq_zero_or_pos (lanesPerBlock l) with h | h
  · rw [h, Nat.div_zero]
    norm_num
  · have : (labelBits + lanesPerBlock l - 1) / lanesPerBlock l ≤ 128 :=
      Nat.div_le_of_le_mul (by unfold labelBits; omega)
    omega

/-- The fields of the tags the conversion core reads stay in range (tags below `2 ^ 40`). -/
structure ConvTagRange (tbl : CrtTable) : Prop where
  castWidth : tbl.castWidth ≤ 128
  chunkCount : tbl.chunkCount ≤ 128
  chunkWidth : ∀ c, c < tbl.chunkCount → tbl.chunkWidth c ≤ 15
  count : tbl.count ≤ 128
  ell : ∀ i, (rowOf (tbl.kind i) (tbl.modulus i)).ell ≤ 15
  modulus : ∀ i, tbl.modulus i ≤ 65536

/-- The fields `(family, idx, stage, level, slot, part)` of a hot read's tag. -/
def hotField (tbl : CrtTable) (v : ℕ) : HotRead tbl → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | .inl (.inl ⟨c, k⟩) => (0, c.val, 0, k.val + 1, tbl.chunkValue v c.val % 2 ^ (k.val + 1), 0)
  | .inl (.inr ⟨c, j⟩) => (1, c.val, 0, 0, tbl.chunkValue v c.val, j.val)
  | .inr ⟨i, .inl (.inl k)⟩ => (2, i.val, 0, k.val + 1,
      tbl.wordValue (tbl.modulus i) v % 2 ^ (rowOf (tbl.kind i) (tbl.modulus i)).width0 % 2 ^ (k.val + 1), 0)
  | .inr ⟨i, .inl (.inr j)⟩ => (3, i.val, 0, 0,
      tbl.wordValue (tbl.modulus i) v % 2 ^ (rowOf (tbl.kind i) (tbl.modulus i)).width0, j.val)
  | .inr ⟨i, .inr (.inl (.inl k))⟩ => (2, i.val, 1, k.val + 1,
      tbl.wordValue (tbl.modulus i) v / 2 ^ (rowOf (tbl.kind i) (tbl.modulus i)).width0 %
        2 ^ (rowOf (tbl.kind i) (tbl.modulus i)).width1 % 2 ^ (k.val + 1), 0)
  | .inr ⟨i, .inr (.inl (.inr j))⟩ => (3, i.val, 1, 0,
      tbl.wordValue (tbl.modulus i) v / 2 ^ (rowOf (tbl.kind i) (tbl.modulus i)).width0 %
        2 ^ (rowOf (tbl.kind i) (tbl.modulus i)).width1, j.val)
  | .inr ⟨i, .inr (.inr (.inl k))⟩ => (4, i.val, 0, (rowOf (tbl.kind i) (tbl.modulus i)).width0 + k.val,
      tbl.wordValue (tbl.modulus i) v % 2 ^ ((rowOf (tbl.kind i) (tbl.modulus i)).width0 + k.val), 0)
  | .inr ⟨i, .inr (.inr (.inr k))⟩ => (5, i.val, 0, (rowOf (tbl.kind i) (tbl.modulus i)).keep + k.val,
      tbl.wordValue (tbl.modulus i) v % 2 ^ ((rowOf (tbl.kind i) (tbl.modulus i)).keep + k.val) % tbl.modulus i, 0)

theorem readTag_eq_field (tbl : CrtTable) (coord v : ℕ) (r : HotRead tbl) :
    readTag tbl coord v r = tagCode (hotField tbl v r).1 coord (hotField tbl v r).2.1 (hotField tbl v r).2.2.1
      (hotField tbl v r).2.2.2.1 (hotField tbl v r).2.2.2.2.1 (hotField tbl v r).2.2.2.2.2 := by
  rcases r with (⟨c, k⟩ | ⟨c, j⟩) | ⟨i, ((k | j) | ((k | j) | (k | k)))⟩ <;> rfl

theorem pow_le_pow15 {a : ℕ} (h : a ≤ 15) : 2 ^ a ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) h

/-- **Every hot read's tag has its fields in range.** -/
theorem hotField_range (tbl : CrtTable) (range : ConvTagRange tbl) (coord v : ℕ) (hc : coord < 2)
    (r : HotRead tbl) :
    TagInRange coord (hotField tbl v r).2.1 (hotField tbl v r).2.2.1 (hotField tbl v r).2.2.2.1
      (hotField tbl v r).2.2.2.2.1 (hotField tbl v r).2.2.2.2.2 ∧ (hotField tbl v r).1 < 16 := by
  have e15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
  rcases r with (⟨c, k⟩ | ⟨c, j⟩) | ⟨i, ((k | j) | ((k | j) | (k | k)))⟩
  · have hw := range.chunkWidth c.val c.isLt
    have hk := k.isLt
    have hs := Nat.mod_lt (tbl.chunkValue v c.val) (Nat.two_pow_pos (k.val + 1))
    have hp := pow_le_pow15 (show k.val + 1 ≤ 15 by omega)
    exact ⟨⟨hc, by have := c.isLt; have := range.chunkCount; simp only [hotField]; omega, by simp [hotField],
      by simp only [hotField]; omega, by simp only [hotField]; omega, by simp [hotField]⟩, by simp [hotField]⟩
  · have hw := range.chunkWidth c.val c.isLt
    have hs : tbl.chunkValue v c.val < 2 ^ tbl.chunkWidth c.val := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hp := pow_le_pow15 hw
    have hj := j.isLt
    have ha := castAnswers_le tbl.castWidth
    exact ⟨⟨hc, by have := c.isLt; have := range.chunkCount; simp only [hotField]; omega, by simp [hotField],
      by simp [hotField], by simp only [hotField]; omega, by simp only [hotField]; omega⟩, by simp [hotField]⟩
  all_goals
    have hl := range.ell i
    have hi := i.isLt
    have hcount := range.count
    have hm := range.modulus i
    rcases rowOf_cases (tbl.kind i) (tbl.modulus i) with hr | ⟨⟨w0, w1, hell, hk0, hk1⟩, hmpos⟩
    · -- the empty row has no reads
      first
        | exact absurd k.isLt (by simp [hr, emptyRow])
        | exact absurd j.isLt (by simp [hr, emptyRow, castAnswers, castBlocks, lanesPerBlock])
    · first
        | (have hk := k.isLt
           refine ⟨⟨hc, by simp only [hotField]; omega, by simp only [hotField]; omega, by simp only [hotField]; omega,
             ?_, by simp only [hotField]; omega⟩, by simp only [hotField]; omega⟩
           simp only [hotField]
           first
             | exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
                 (le_trans (pow_le_pow15 (by omega)) (by norm_num))
             | exact lt_of_lt_of_le (Nat.mod_lt _ hmpos) (by omega))
        | (have hj := j.isLt
           have ha := castAnswers_le (rowOf (tbl.kind i) (tbl.modulus i)).ell
           have ha' := castAnswers_le ((rowOf (tbl.kind i) (tbl.modulus i)).ell -
             (rowOf (tbl.kind i) (tbl.modulus i)).width0)
           refine ⟨⟨hc, by simp only [hotField]; omega, by simp only [hotField]; omega, by simp only [hotField]; omega,
             ?_, by simp only [hotField]; omega⟩, by simp only [hotField]; omega⟩
           simp only [hotField]
           exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
             (le_trans (pow_le_pow15 (by omega)) (by norm_num)))

/-- **The family, index, stage, level and part of a hot read's tag determine the read.** -/
theorem hotKey_injective (tbl : CrtTable) (v : ℕ) {r r' : HotRead tbl}
    (h1 : (hotField tbl v r).1 = (hotField tbl v r').1) (h2 : (hotField tbl v r).2.1 = (hotField tbl v r').2.1)
    (h3 : (hotField tbl v r).2.2.1 = (hotField tbl v r').2.2.1)
    (h4 : (hotField tbl v r).2.2.2.1 = (hotField tbl v r').2.2.2.1)
    (h6 : (hotField tbl v r).2.2.2.2.2 = (hotField tbl v r').2.2.2.2.2) : r = r' := by
  rcases r with (⟨c, k⟩ | ⟨c, j⟩) | ⟨i, ((k | j) | ((k | j) | (k | k)))⟩ <;>
    rcases r' with (⟨c', k'⟩ | ⟨c', j'⟩) | ⟨i', ((k' | j') | ((k' | j') | (k' | k')))⟩ <;>
    simp only [hotField] at h1 h2 h3 h4 h6 <;>
    (try omega)
  all_goals
    first
      | (obtain rfl : c = c' := Fin.ext h2)
      | (obtain rfl : i = i' := Fin.ext h2)
  all_goals
    first
      | (obtain rfl : k = k' := Fin.ext (by omega))
      | (obtain rfl : j = j' := Fin.ext (by omega))
  all_goals rfl

/-- **The hot reads have distinct tags**, below `2 ^ 40`. -/
theorem readTag_lt (tbl : CrtTable) (range : ConvTagRange tbl) (coord v : ℕ) (hc : coord < 2) (r : HotRead tbl) :
    readTag tbl coord v r < 2 ^ 40 := by
  obtain ⟨hr, hf⟩ := hotField_range tbl range coord v hc r
  rw [readTag_eq_field]
  have := hr.coord; have := hr.idx; have := hr.stage; have := hr.level; have := hr.slot; have := hr.part
  unfold tagCode
  omega

theorem tag40_readTag_injective (tbl : CrtTable) (range : ConvTagRange tbl) (coord v : ℕ) (hc : coord < 2) :
    Function.Injective fun r => tag40 (readTag tbl coord v r) := by
  intro r r' e
  have ev : readTag tbl coord v r = readTag tbl coord v r' := by
    have := congrArg Fin.val e
    simp only [tag40, Nat.mod_eq_of_lt (readTag_lt tbl range coord v hc r),
      Nat.mod_eq_of_lt (readTag_lt tbl range coord v hc r')] at this
    exact this
  rw [readTag_eq_field, readTag_eq_field] at ev
  obtain ⟨hr, hf⟩ := hotField_range tbl range coord v hc r
  obtain ⟨hr', hf'⟩ := hotField_range tbl range coord v hc r'
  have fam : (hotField tbl v r).1 = (hotField tbl v r').1 := by
    rw [← tagFamily_tagCode (fam := (hotField tbl v r).1) hr, ev, tagFamily_tagCode hr']
  obtain ⟨-, -, e2, e3, e4, -, e6⟩ := tagCode_injective hr hr' ev
  exact hotKey_injective tbl v fam e2 e3 e4 e6

/-- **A tag in range that shares a hot read's family, index, stage, level and part but not its slot is cold.** -/
theorem tag40_not_hot (tbl : CrtTable) (range : ConvTagRange tbl) (coord v : ℕ) (hc : coord < 2) (r0 : HotRead tbl)
    (slot : ℕ) (hslot : slot < 65536) (hne : slot ≠ (hotField tbl v r0).2.2.2.2.1) :
    ∀ r, tag40 (readTag tbl coord v r) ≠ tag40 (tagCode (hotField tbl v r0).1 coord (hotField tbl v r0).2.1
      (hotField tbl v r0).2.2.1 (hotField tbl v r0).2.2.2.1 slot (hotField tbl v r0).2.2.2.2.2) := by
  intro r e
  obtain ⟨hr0, hf0⟩ := hotField_range tbl range coord v hc r0
  obtain ⟨hr, hf⟩ := hotField_range tbl range coord v hc r
  have hin : TagInRange coord (hotField tbl v r0).2.1 (hotField tbl v r0).2.2.1 (hotField tbl v r0).2.2.2.1 slot
      (hotField tbl v r0).2.2.2.2.2 := ⟨hr0.coord, hr0.idx, hr0.stage, hr0.level, hslot, hr0.part⟩
  have lt0 : tagCode (hotField tbl v r0).1 coord (hotField tbl v r0).2.1 (hotField tbl v r0).2.2.1
      (hotField tbl v r0).2.2.2.1 slot (hotField tbl v r0).2.2.2.2.2 < 2 ^ 40 := by
    have := hin.coord; have := hin.idx; have := hin.stage; have := hin.level; have := hin.slot; have := hin.part
    unfold tagCode
    omega
  have ev : readTag tbl coord v r = tagCode (hotField tbl v r0).1 coord (hotField tbl v r0).2.1
      (hotField tbl v r0).2.2.1 (hotField tbl v r0).2.2.2.1 slot (hotField tbl v r0).2.2.2.2.2 := by
    have := congrArg Fin.val e
    simp only [tag40, Nat.mod_eq_of_lt (readTag_lt tbl range coord v hc r), Nat.mod_eq_of_lt lt0] at this
    exact this
  rw [readTag_eq_field] at ev
  have fam : (hotField tbl v r).1 = (hotField tbl v r0).1 := by
    rw [← tagFamily_tagCode (fam := (hotField tbl v r).1) hr, ev, tagFamily_tagCode hin]
  obtain ⟨-, -, e2, e3, e4, e5, e6⟩ := tagCode_injective hr hin ev
  have same := hotKey_injective tbl v fam e2 e3 e4 e6
  subst same
  exact hne e5.symm

/-! ### `convPublish` reads the table at cold tags only -/

section Congr

open Kriterion.CRT.Privacy.ExtractStage (upperOverrideHot upperSpecPublish)

/-- **A stage on two tables that agree at its cold tags** publishes the same, with the same remainder and bits. -/
theorem stage_congr (T T' : ℕ → Block × Block) {rb : ℕ} (w : ℕ) (hw : w ≤ rb) (tt ct : ℕ → ℕ → ℕ) (s : ℕ)
    (h : UpperHidden w rb) (R : Lanes rb) (Δ : Label)
    (treeEq : ∀ n x, 1 ≤ n → n < w → x < 2 ^ n → x ≠ s % 2 ^ n → (clip (T (tt n x)).1) = (clip (T' (tt n x)).1))
    (castEq : ∀ α, α < 2 ^ w → α ≠ s → upperRd T rb (ct α) = upperRd T' rb (ct α)) :
    upperSpecPublish (tableStage T w hw tt ct) R Δ s h = upperSpecPublish (tableStage T' w hw tt ct) R Δ s h ∧
      (gNext (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ : Lanes (rb - w)) =
        gNext (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ ∧
      ∀ n, gBit (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ n =
        gBit (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ n := by
  have mats : ∀ n x G G', 1 ≤ n → n < w → x < 2 ^ n →
      (upperOverrideHot (tableStage T w hw tt ct) s h).mat n x G =
      (upperOverrideHot (tableStage T' w hw tt ct) s h).mat n x G' := by
    intro n x G G' hn1 hn2 hx
    change (if x = s % 2 ^ n then _ else clip (T (tt n x)).1) =
      (if x = s % 2 ^ n then _ else clip (T' (tt n x)).1)
    split_ifs with hit
    · rfl
    · exact treeEq n x hn1 hn2 hx hit
  have nodes : ∀ n, n ≤ w → ∀ x,
      gNode (upperOverrideHot (tableStage T w hw tt ct) s h)
        (gBit0 (tableStage T w hw tt ct) R) Δ n x =
      gNode (upperOverrideHot (tableStage T' w hw tt ct) s h)
        (gBit0 (tableStage T' w hw tt ct) R) Δ n x := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro hn x
      simp only [gNode, ih (by omega)]
      cases n with
      | zero => rfl
      | succ n =>
        simp only [Kriterion.CRT.ExtractSpec.stepMat]
        rw [mats (n + 1) (x % 2 ^ (n + 1)) _ _ (by omega) (by omega)
          (Nat.mod_lt _ (Nat.two_pow_pos _))]
  have casts : ∀ α ∈ Finset.range (2 ^ w), gCast (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ α =
      gCast (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ α := by
    intro α hα
    unfold gCast gLeaf
    rw [show (upperOverrideHot (tableStage T w hw tt ct) s h).w = w from rfl,
      show gBit0 (upperOverrideHot (tableStage T w hw tt ct) s h) R =
        gBit0 (tableStage T w hw tt ct) R from rfl, nodes w le_rfl α]
    change (if α = s then _ else parityRd T rb (ct α) _) =
      (if α = s then _ else parityRd T' rb (ct α) _)
    split_ifs with hit
    · rfl
    · unfold parityRd
      rw [castEq α (Finset.mem_range.mp hα) hit]
      rfl
  have res : ∀ n, gRes (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ n =
      gRes (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ n := fun n =>
    Finset.sum_congr rfl fun α hα => by rw [casts α hα]
  have bits : ∀ n, gBit (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ n =
      gBit (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ n := by
    intro n
    unfold gBit
    rw [res]
    rfl
  have next : (gNext (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ : Lanes (rb - w)) =
      gNext (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ := by
    show peelDiv R (gRes (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ w) w =
      peelDiv R (gRes (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ w) w
    rw [res]
  have pin : gPin (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ =
      gPin (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ := by
    show (∑ α ∈ Finset.range (2 ^ w), gCast (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ α) +
        deltaLanes rb Δ =
      (∑ α ∈ Finset.range (2 ^ w), gCast (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ α) + deltaLanes rb Δ
    rw [Finset.sum_congr rfl casts]
  have levels : ∀ n, 1 ≤ n → n < w → gLevelSum (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ n =
      gLevelSum (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ n := by
    intro n h1 h2
    unfold gLevelSum
    apply SliceC.xsum_congr
    intro x hx
    show (if x = s % 2 ^ n then ExtractStage.hot h.1 (n - 1) else (clip (T (tt n x)).1)) =
      (if x = s % 2 ^ n then ExtractStage.hot h.1 (n - 1) else (clip (T' (tt n x)).1))
    split_ifs with e
    · rfl
    · exact treeEq n x h1 h2 (Finset.mem_range.mp hx) e
  refine ⟨Prod.ext (funext fun k => ?_) (congrArg (Parity.pinHalf rb) pin), next, bits⟩
  have hk : k.val < w - 1 := k.isLt
  show gLevelSum (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ (k.val + 1) ^^^
      gBit (upperOverrideHot (tableStage T w hw tt ct) s h) R Δ (k.val + 1) =
    gLevelSum (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ (k.val + 1) ^^^
      gBit (upperOverrideHot (tableStage T' w hw tt ct) s h) R Δ (k.val + 1)
  rw [levels (k.val + 1) (by omega) (by omega), bits]

/-- Stage 1's input remainder in `modPublish`. -/
def modR1 (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (σ : ℕ) (Δ : Label) (hw0 : row.width0 ≤ row.ell)
    (W : Lanes row.ell) (h : StageVals row) : Lanes (row.ell - row.width0) :=
  gNext (upperOverrideHot (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0))
    (σ % 2 ^ row.width0) h.1) W Δ

/-- The bit masks of the growth and fold joins in `modPublish`. -/
def modBit (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (σ : ℕ) (Δ : Label) (hw0 : row.width0 ≤ row.ell)
    (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell) (h : StageVals row) (p : ℕ) : Label :=
  if p < row.width0 + row.width1 then
    gBit (upperOverrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (σ / 2 ^ row.width0 % 2 ^ row.width1) h.2.1) (modR1 T coord i row σ Δ hw0 W h) Δ (p - row.width0)
  else laneBit (gNext (upperOverrideHot (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (σ / 2 ^ row.width0 % 2 ^ row.width1) h.2.1) (modR1 T coord i row σ Δ hw0 W h) Δ) 0

section Forms

variable (T : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Label) (hw0 : row.width0 ≤ row.ell)
  (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell) (h : StageVals row)

theorem modPublish_stage0 : (modPublish T coord i row m σ Δ hw0 hw1 W h).1 =
    upperSpecPublish (tableStage T row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)) W Δ
      (σ % 2 ^ row.width0) h.1 := rfl

theorem modPublish_stage1 : (modPublish T coord i row m σ Δ hw0 hw1 W h).2.1 =
    upperSpecPublish (tableStage T row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1))
      (modR1 T coord i row σ Δ hw0 W h) Δ (σ / 2 ^ row.width0 % 2 ^ row.width1) h.2.1 := rfl

theorem modPublish_grow (k : Fin (row.keep - row.width0)) : (modPublish T coord i row m σ Δ hw0 hw1 W h).2.2.1 k =
    xorFold (fun slot : Fin (2 ^ (row.width0 + k.val)) =>
        if slot.val = σ % 2 ^ (row.width0 + k.val) then h.2.2.1 k
        else (clip (T (growTag coord i (row.width0 + k.val) slot.val)).1)) ^^^
      modBit T coord i row σ Δ hw0 hw1 W h (row.width0 + k.val) := rfl

theorem modPublish_fold (k : Fin (row.ell - row.keep)) : (modPublish T coord i row m σ Δ hw0 hw1 W h).2.2.2 k =
    xorFold (fun ρ : Fin m =>
        if ρ.val = σ % 2 ^ (row.keep + k.val) % m then h.2.2.2 k
        else (clip (T (foldTag coord i (row.keep + k.val) ρ.val)).1)) ^^^
      modBit T coord i row σ Δ hw0 hw1 W h (row.keep + k.val) := rfl

end Forms

/-- **One modulus on two tables that agree at its cold tags** publishes the same. -/
theorem modPublish_congr (T T' : ℕ → Block × Block) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (Δ : Label)
    (hw0 : row.width0 ≤ row.ell) (hw1 : row.width1 ≤ row.ell - row.width0) (W : Lanes row.ell) (h : StageVals row)
    (tree0 : ∀ n x, 1 ≤ n → n < row.width0 → x < 2 ^ n → x ≠ σ % 2 ^ row.width0 % 2 ^ n →
      (clip (T (extTreeTag coord i 0 n x)).1) = (clip (T' (extTreeTag coord i 0 n x)).1))
    (cast0 : ∀ α, α < 2 ^ row.width0 → α ≠ σ % 2 ^ row.width0 →
      upperRd T row.ell (extCastTag coord i 0 α) = upperRd T' row.ell (extCastTag coord i 0 α))
    (tree1 : ∀ n x, 1 ≤ n → n < row.width1 → x < 2 ^ n → x ≠ σ / 2 ^ row.width0 % 2 ^ row.width1 % 2 ^ n →
      (clip (T (extTreeTag coord i 1 n x)).1) = (clip (T' (extTreeTag coord i 1 n x)).1))
    (cast1 : ∀ α, α < 2 ^ row.width1 → α ≠ σ / 2 ^ row.width0 % 2 ^ row.width1 →
      upperRd T (row.ell - row.width0) (extCastTag coord i 1 α) =
        upperRd T' (row.ell - row.width0) (extCastTag coord i 1 α))
    (grow : ∀ k, k < row.keep - row.width0 → ∀ x, x < 2 ^ (row.width0 + k) → x ≠ σ % 2 ^ (row.width0 + k) →
      (clip (T (growTag coord i (row.width0 + k) x)).1) = (clip (T' (growTag coord i (row.width0 + k) x)).1))
    (fold : ∀ k, k < row.ell - row.keep → ∀ ρ, ρ < m → ρ ≠ σ % 2 ^ (row.keep + k) % m →
      (clip (T (foldTag coord i (row.keep + k) ρ)).1) = (clip (T' (foldTag coord i (row.keep + k) ρ)).1)) :
    modPublish T coord i row m σ Δ hw0 hw1 W h = modPublish T' coord i row m σ Δ hw0 hw1 W h := by
  obtain ⟨p0, n0, -⟩ := stage_congr T T' row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0)
    (σ % 2 ^ row.width0) h.1 W Δ tree0 cast0
  have eR : modR1 T coord i row σ Δ hw0 W h = modR1 T' coord i row σ Δ hw0 W h := n0
  obtain ⟨p1, n1, b1⟩ := stage_congr T T' row.width1 hw1 (extTreeTag coord i 1) (extCastTag coord i 1)
    (σ / 2 ^ row.width0 % 2 ^ row.width1) h.2.1 (modR1 T' coord i row σ Δ hw0 W h) Δ tree1 cast1
  have eBit : modBit T coord i row σ Δ hw0 hw1 W h = modBit T' coord i row σ Δ hw0 hw1 W h := by
    funext p
    unfold modBit
    rw [eR]
    split_ifs
    · exact b1 _
    · exact congrArg (fun R => laneBit R 0) n1
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext (funext fun k => ?_) (funext fun k => ?_)))
  · rw [modPublish_stage0, modPublish_stage0]
    exact p0
  · rw [modPublish_stage1, modPublish_stage1, eR]
    exact p1
  · rw [modPublish_grow, modPublish_grow, eBit]
    congr 1
    congr 1
    funext slot
    split_ifs with e
    · rfl
    · exact grow k.val k.isLt slot.val slot.isLt e
  · rw [modPublish_fold, modPublish_fold, eBit]
    congr 1
    congr 1
    funext ρ
    split_ifs with e
    · rfl
    · exact fold k.val k.isLt ρ.val ρ.isLt e

/-- A tag table read at a cold tag of the same gadget as a hot read `r0` (same family, index, stage, level and part,
another slot in range). -/
theorem cold_at (tbl : CrtTable) (range : ConvTagRange tbl) (coord v : ℕ) (hc : coord < 2)
    (A A' : Fin (2 ^ 40) → Block × Block)
    (agree : ∀ x, (∀ r, tag40 (readTag tbl coord v r) ≠ x) → A x = A' x) (r0 : HotRead tbl) (slot : ℕ)
    (hslot : slot < 65536) (hne : slot ≠ (hotField tbl v r0).2.2.2.2.1) :
    tagRead A (tagCode (hotField tbl v r0).1 coord (hotField tbl v r0).2.1 (hotField tbl v r0).2.2.1
      (hotField tbl v r0).2.2.2.1 slot (hotField tbl v r0).2.2.2.2.2) =
    tagRead A' (tagCode (hotField tbl v r0).1 coord (hotField tbl v r0).2.1 (hotField tbl v r0).2.2.1
      (hotField tbl v r0).2.2.2.1 slot (hotField tbl v r0).2.2.2.2.2) :=
  agree _ (tag40_not_hot tbl range coord v hc r0 slot hslot hne)

theorem two_pow_lt_65536 {a : ℕ} (h : a ≤ 15) : 2 ^ a < 65536 :=
  lt_of_le_of_lt (pow_le_pow15 h) (by norm_num)

/-- **`convPublish` reads the table at cold tags only**: two tag tables that agree off the hot tags of `v` give the
same published conversion material for every hidden value. -/
theorem convPublish_cold (tbl : CrtTable) (range : ConvTagRange tbl) (coord v : ℕ) (hc : coord < 2) (Z : ℕ → Label)
    (Δ : Label) (A A' : Fin (2 ^ 40) → Block × Block)
    (agree : ∀ x, (∀ r, tag40 (readTag tbl coord v r) ≠ x) → A x = A' x) (h : ConvVals tbl) :
    convPublish tbl coord v ⟨tagRead A, Z, Δ⟩ h = convPublish tbl coord v ⟨tagRead A', Z, Δ⟩ h := by
  have cold := cold_at tbl range coord v hc A A' agree
  have trees : ∀ c : Fin tbl.chunkCount,
      chunkTreeH tbl coord v ⟨tagRead A, Z, Δ⟩ h.1.1 c =
        chunkTreeH tbl coord v ⟨tagRead A', Z, Δ⟩ h.1.1 c := by
    intro c
    apply materialTree_congr
    intro n hn1 hn2 slot hslot
    unfold chunkMatH
    split_ifs with hit
    · rfl
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have cw := range.chunkWidth c.val c.isLt
      exact congrArg (fun a => clip a.1) (cold (.inl (.inl ⟨c, ⟨k, by omega⟩⟩)) slot
        (lt_of_lt_of_le hslot (le_of_lt (two_pow_lt_65536 (by omega)))) hit)
  -- the chunks' casts
  have casts : ∀ (c : Fin tbl.chunkCount) (leaf : ℕ), leaf < 2 ^ tbl.chunkWidth c.val →
      chunkCastH tbl coord v ⟨tagRead A, Z, Δ⟩ h.1 c leaf = chunkCastH tbl coord v ⟨tagRead A', Z, Δ⟩ h.1 c leaf := by
    intro c leaf hleaf
    unfold chunkCastH
    rw [trees c]
    split_ifs with e
    · rfl
    · unfold parityRd
      apply congrArg (fun upper => Parity.liftUpper tbl.castWidth upper _)
      apply upperRd_congr
      intro j
      exact cold (.inl (.inr ⟨c, j⟩)) leaf
        (lt_of_lt_of_le hleaf (le_of_lt (two_pow_lt_65536 (range.chunkWidth c.val c.isLt)))) e
  have word : ∀ m ell, wordH tbl coord v ⟨tagRead A, Z, Δ⟩ h.1 m ell =
      wordH tbl coord v ⟨tagRead A', Z, Δ⟩ h.1 m ell := by
    intro m ell
    unfold wordH
    congr 1
    funext lane
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun leaf _ => ?_
    rw [casts c leaf.val leaf.isLt]
  refine Prod.ext (Prod.ext (funext fun c => funext fun k => ?_) (funext fun c => ?_)) (funext fun i => ?_)
  · show chunkJoinH tbl coord v ⟨tagRead A, Z, Δ⟩ h.1.1 c k = chunkJoinH tbl coord v ⟨tagRead A', Z, Δ⟩ h.1.1 c k
    unfold chunkJoinH
    congr 1
    congr 1
    funext slot
    split_ifs with e
    · rfl
    · have hk := k.isLt
      have hw := range.chunkWidth c.val c.isLt
      exact congrArg (fun a => clip a.1) (cold (.inl (.inl ⟨c, k⟩)) slot.val
        (lt_of_lt_of_le slot.isLt (le_of_lt (two_pow_lt_65536 (by omega)))) e)
  · show chunkPinH tbl coord v ⟨tagRead A, Z, Δ⟩ h.1 c = chunkPinH tbl coord v ⟨tagRead A', Z, Δ⟩ h.1 c
    unfold chunkPinH chunkFullPinH
    rw [Finset.sum_congr rfl fun leaf _ => casts c leaf.val leaf.isLt]
  · show modPublish (tagRead A) coord i.val _ _ _ Δ _ _ (wordH tbl coord v ⟨tagRead A, Z, Δ⟩ h.1 _ _) (h.2 i) =
      modPublish (tagRead A') coord i.val _ _ _ Δ _ _ (wordH tbl coord v ⟨tagRead A', Z, Δ⟩ h.1 _ _) (h.2 i)
    rw [← word]
    have hl := range.ell i
    have hm := range.modulus i
    have bounds : (rowOf (tbl.kind i) (tbl.modulus i)).width0 ≤ (rowOf (tbl.kind i) (tbl.modulus i)).ell ∧
        (rowOf (tbl.kind i) (tbl.modulus i)).width0 + (rowOf (tbl.kind i) (tbl.modulus i)).width1 ≤
          (rowOf (tbl.kind i) (tbl.modulus i)).ell ∧
        (rowOf (tbl.kind i) (tbl.modulus i)).keep ≤ (rowOf (tbl.kind i) (tbl.modulus i)).ell := by
      rcases rowOf_cases (tbl.kind i) (tbl.modulus i) with e | ⟨⟨_, _, h3, _, h5⟩, _⟩
      · rw [e]
        exact ⟨le_refl 0, le_refl 0, le_refl 0⟩
      · omega
    obtain ⟨b0, b1, b2⟩ := bounds
    apply modPublish_congr
    · intro n x h1 h2 hx e
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact congrArg (fun a => clip a.1) (cold (.inr ⟨i, .inl (.inl ⟨k, by omega⟩)⟩) x
        (lt_of_lt_of_le hx (le_of_lt (two_pow_lt_65536 (by omega)))) e)
    · intro α hα e
      apply upperRd_congr
      intro j
      exact cold (.inr ⟨i, .inl (.inr j)⟩) α (lt_of_lt_of_le hα (le_of_lt (two_pow_lt_65536 (by omega)))) e
    · intro n x h1 h2 hx e
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact congrArg (fun a => clip a.1) (cold (.inr ⟨i, .inr (.inl (.inl ⟨k, by omega⟩))⟩) x
        (lt_of_lt_of_le hx (le_of_lt (two_pow_lt_65536 (by omega)))) e)
    · intro α hα e
      apply upperRd_congr
      intro j
      exact cold (.inr ⟨i, .inr (.inl (.inr j))⟩) α (lt_of_lt_of_le hα (le_of_lt (two_pow_lt_65536 (by omega))))
        e
    · intro k hk x hx e
      exact congrArg (fun a => clip a.1) (cold (.inr ⟨i, .inr (.inr (.inl ⟨k, hk⟩))⟩) x
        (lt_of_lt_of_le hx (le_of_lt (two_pow_lt_65536 (by omega)))) e)
    · intro k hk ρ hρ e
      exact congrArg (fun a => clip a.1) (cold (.inr ⟨i, .inr (.inr (.inr ⟨k, hk⟩))⟩) ρ (by omega) e)

end Congr

/-! ### The law of the real garbler's conversion material -/

/-- **P3, part (a) with the core: the real garbler's published conversion material is uniform and independent of
everything else.** `rest` is any law of everything besides this coordinate's hot answers (coins, the table at every
other tag, any other data), `tableOf ρ g` the tag table built from it and the hot answers `g` (read at the hot tags,
and not depending on `g` elsewhere), `zOf ρ` and `dOf ρ` the coordinate's zero labels and `Δ`. With the hot answers
uniform, the garbler's conversion material of coordinate `coord` at value `v`, read in range, is uniform and independent
of `ρ`. -/
theorem conversion_law (tbl : CrtTable) (wf : ConvTableWF tbl) (range : ConvTagRange tbl) (coord v : ℕ)
    (hc : coord < 2) (S : ℕ) {Rest : Type*} (rest : PMF Rest)
    (tableOf : Rest → (HotRead tbl → Block × Block) → Fin (2 ^ 40) → Block × Block)
    (zOf : Rest → ℕ → Label) (dOf : Rest → Label)
    (hot : ∀ ρ g r, tableOf ρ g (tag40 (readTag tbl coord v r)) = g r)
    (cold : ∀ ρ g g' x, (∀ r, tag40 (readTag tbl coord v r) ≠ x) → tableOf ρ g x = tableOf ρ g' x) :
    (rest.bind fun ρ => (PMF.uniformOfFintype (HotRead tbl → Block × Block)).map fun g =>
        (ρ, readPub tbl ((coordGarbleM tbl S coord (dOf ρ) (zOf ρ)).eval (tableHash (tagRead (tableOf ρ g)))).pub))
      = rest.bind fun ρ => (PMF.uniformOfFintype (ConvVals tbl)).map fun b => (ρ, b) := by
  congr 1
  funext ρ
  let g0 : HotRead tbl → Block × Block := fun _ => (0, 0)
  let r0 : ConvRest := ⟨tagRead (tableOf ρ g0), zOf ρ, dOf ρ⟩
  have pointwise : ∀ g, readPub tbl ((coordGarbleM tbl S coord (dOf ρ) (zOf ρ)).eval
      (tableHash (tagRead (tableOf ρ g)))).pub = convPublish tbl coord v r0 (rho tbl g) := by
    intro g
    rw [garbler_conv_eq tbl wf S coord v, readHot_eq]
    have reads : (fun r => tableOf ρ g (tag40 (readTag tbl coord v r))) = g := funext fun r => hot ρ g r
    rw [reads]
    exact convPublish_cold tbl range coord v hc (zOf ρ) (dOf ρ) _ _ (fun x hx => cold ρ g g0 x hx) _
  have factor : (fun g => (ρ, readPub tbl ((coordGarbleM tbl S coord (dOf ρ) (zOf ρ)).eval
      (tableHash (tagRead (tableOf ρ g)))).pub)) =
      (fun b => (ρ, b)) ∘ convPublish tbl coord v r0 ∘ rho tbl := by
    funext g
    rw [pointwise]
    rfl
  have hL : tbl.castWidth ≤ 128 := range.castWidth
  have hl : ∀ i, (rowOf (tbl.kind i) (tbl.modulus i)).ell ≤ 128 := fun i => le_trans (range.ell i) (by norm_num)
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, rho_uniform tbl hL hl,
    map_uniform_of_bijective (bijective_of_injective_card (convPublish_injective tbl coord v r0) rfl)]

/-- The table filled at the hot tags with `g` (the rest unchanged). -/
def fillHot (tbl : CrtTable) (coord v : ℕ) (A : Fin (2 ^ 40) → Block × Block) (g : HotRead tbl → Block × Block) :
    Fin (2 ^ 40) → Block × Block :=
  Split.overwrite (fun r => tag40 (readTag tbl coord v r)) g A

theorem fillHot_hot (tbl : CrtTable) (range : ConvTagRange tbl) (coord v : ℕ) (hc : coord < 2)
    (A : Fin (2 ^ 40) → Block × Block) (g : HotRead tbl → Block × Block) (r : HotRead tbl) :
    fillHot tbl coord v A g (tag40 (readTag tbl coord v r)) = g r :=
  congrFun (Split.overwrite_comp _ (tag40_readTag_injective tbl range coord v hc) g A) r

theorem fillHot_cold (tbl : CrtTable) (coord v : ℕ) (A : Fin (2 ^ 40) → Block × Block)
    (g : HotRead tbl → Block × Block) (x : Fin (2 ^ 40)) (hx : ∀ r, tag40 (readTag tbl coord v r) ≠ x) :
    fillHot tbl coord v A g x = A x := by
  unfold fillHot Split.overwrite
  rw [dif_neg]
  rintro ⟨r, e⟩
  exact hx r e

/-- **The law on a table whose hot tags are refilled uniformly**: for any law of the rest `ρ` and of a tag table
`tableOf ρ`, refilling the table's hot tags of `v` with uniform answers makes the garbler's conversion material uniform
and independent of `ρ`. -/
theorem conversion_law_fill (tbl : CrtTable) (wf : ConvTableWF tbl) (range : ConvTagRange tbl) (coord v : ℕ)
    (hc : coord < 2) (S : ℕ) {Rest : Type*} (rest : PMF Rest) (tableOf : Rest → Fin (2 ^ 40) → Block × Block)
    (zOf : Rest → ℕ → Label) (dOf : Rest → Label) :
    (rest.bind fun ρ => (PMF.uniformOfFintype (HotRead tbl → Block × Block)).map fun g =>
        (ρ, readPub tbl ((coordGarbleM tbl S coord (dOf ρ) (zOf ρ)).eval
          (tableHash (tagRead (fillHot tbl coord v (tableOf ρ) g)))).pub))
      = rest.bind fun ρ => (PMF.uniformOfFintype (ConvVals tbl)).map fun b => (ρ, b) :=
  conversion_law tbl wf range coord v hc S rest (fun ρ g => fillHot tbl coord v (tableOf ρ) g) zOf dOf
    (fun ρ g r => fillHot_hot tbl range coord v hc (tableOf ρ) g r)
    (fun ρ g g' x hx => by rw [fillHot_cold tbl coord v _ g x hx, fillHot_cold tbl coord v _ g' x hx])

/-! ### The real table -/

/-- **The real table's tags are in range.** -/
theorem bn254Table_range : ConvTagRange bn254Table where
  castWidth := by decide
  chunkCount := by decide
  chunkWidth := by decide +kernel
  count := by decide
  ell := by decide +kernel
  modulus := by decide +kernel

end

end Kriterion.CRT.Privacy.Conv
