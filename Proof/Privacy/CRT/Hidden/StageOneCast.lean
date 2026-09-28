/-
**H6 for the CRT entry: the 30 never-hot casts**.

`StageOneProof.neverCase : OneCase NeverHotCast (2^104)⁻¹`. The casts `49 .. 63` of chunk 31 (width 6) are hot at no
input, so the stage-2 case `convHot` does not cover them; they are bounded directly.

* **The label** (`never_input`): a garbler input at a never-hot cast tag of coordinate `κ` and leaf `α` is labelled by
  the right child `α` of chunk 31's tree, which is the level-5 material at slot `α − 32`, a table answer: the label is
  the zero-embedded low 104 bits of the table at `P = treePos κ (α − 32)`.
* **The symmetry** (`pub_shift`): shifting the first blocks of the table at `P` and at a second level-5 slot `Q` of the
  same tree by the same `d` keeps the published value. On the tag reading the table enters the published value only
  through answers by tag; the two materials enter only the level-5 join (their XOR is unchanged), the leaf labels they
  feed are only hash labels (casts read the table by tag), and every other block reads neither position.
* **The count** (`outer_family_le`, `count_le`): under the swapped table law the answers at `P` and `Q` are uniform and
  independent of the rest (`indep_swapped_family`); the shifts pair the fibres of the clipped first block at `P` within each
  view, so each fibre carries `2^-104` of the view's mass.
-/

import Proof.Privacy.CRT.Hidden.StageOneTable
import Proof.Correctness.CRT.ChunkStep

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Kriterion.CRT.Privacy.CastNever

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Privacy.StageTwo (gAsked)
open Kriterion.CRT.Privacy.StageOneProof (OneCase NeverHotCast keyRun_congr tagHash_key label_of_hashInput pubT
  pubT_congr viewSet_eq swappedTableTape_eq stageOneView_pubT gAsked_eq entriesOf_tagHash away_of_family)
open Kriterion.CRT.Privacy.Laws (Indep Ignores)
open Kriterion.CRT.Privacy.HiddenGuess (fillAt fillAt_comp fillAt_self fillAt_apply_of_not_mem indep_swapped_family)
open scoped ENNReal

noncomputable section

theorem xz {width : ℕ} (a : BitVec width) : a ^^^ (0 : BitVec width) = a := BitVec.xor_zero

theorem zx {width : ℕ} (a : BitVec width) : (0 : BitVec width) ^^^ a = a := BitVec.zero_xor

/-! ### 1. The positions of chunk 31's level-5 materials -/

/-- The position of the level-5 material at slot `s` of chunk 31's tree of coordinate `κ`. -/
def treePos (κ s : ℕ) : Fin (2 ^ 40) := Conv.tag40 (chunkTreeTag κ 31 5 s)

theorem treeRange {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : TagInRange κ 31 0 5 s 0 :=
  ⟨hκ, by norm_num, by norm_num, by norm_num, hs, by norm_num⟩

theorem treeTag_lt {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : chunkTreeTag κ 31 5 s < 2 ^ 40 :=
  Asks.tagCode_lt (by decide) (treeRange hκ hs)

theorem treePos_val {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : (treePos κ s).val = chunkTreeTag κ 31 5 s :=
  Nat.mod_eq_of_lt (treeTag_lt hκ hs)

theorem treePos_family {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : tagFamily (treePos κ s).val = 0 := by
  rw [treePos_val hκ hs]
  exact tagFamily_tagCode (treeRange hκ hs)

theorem treePos_slot {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) : tagSlot (treePos κ s).val = s := by
  rw [treePos_val hκ hs]
  exact tagSlot_tagCode (treeRange hκ hs)

theorem treePos_inj {κ s t : ℕ} (hκ : κ < 2) (hs : s < 65536) (ht : t < 65536) (same : treePos κ s = treePos κ t) :
    s = t := by
  rw [← treePos_slot hκ hs, ← treePos_slot hκ ht, same]

/-- The fields of a key whose position is a level-5 material of chunk 31 of coordinate `κ`. -/
def Level5 (κ : ℕ) (k : Paths.TagKey) : Prop := k.fam = 0 ∧ k.coord = κ ∧ k.idx = 31 ∧ k.level = 5

theorem level5_of_pos {κ s : ℕ} (hκ : κ < 2) (hs : s < 65536) {k : Paths.TagKey} (range : k.InRange)
    (same : Conv.tag40 k.code = treePos κ s) : Level5 κ k := by
  have e := congrArg Fin.val same
  rw [treePos_val hκ hs] at e
  have e' : k.code = chunkTreeTag κ 31 5 s := by
    rw [← e]
    exact (Nat.mod_eq_of_lt (Paths.TagKey.code_lt range)).symm
  obtain ⟨f, c, i, _, l, _, _⟩ := tagCode_injective (tagInRange_of_key range) (treeRange hκ hs) e'
  exact ⟨f, c, i, l⟩

/-! ### 2. Two tables that differ by a shift at two positions -/

/-- `A'` is `A` with the first answer blocks at `P` and `Q` shifted by `d`. -/
structure Shift2 (P Q : Fin (2 ^ 40)) (d : Block) (A A' : TagTable) : Prop where
  off : ∀ i, i ≠ P → i ≠ Q → A' i = A i
  atP : (A' P).1 = (A P).1 ^^^ d
  atQ : (A' Q).1 = (A Q).1 ^^^ d

section Shifted

variable {κ s s' : ℕ} (hκ : κ < 2) (hs : s < 65536) (hs' : s' < 65536) {d : Block} {A A' : TagTable}
  (shift : Shift2 (treePos κ s) (treePos κ s') d A A')
include hκ hs hs' shift

/-- The tables agree off family 0. -/
theorem pos_agree (p : Fin (2 ^ 40)) (fam : tagFamily p.val ≠ 0) : A' p = A p := by
  refine shift.off p (fun h => fam ?_) (fun h => fam ?_)
  · rw [h]; exact treePos_family hκ hs
  · rw [h]; exact treePos_family hκ hs'

/-- **The hashes agree at every key that is not a level-5 material of chunk 31 of `κ`.** -/
theorem key_agree {k : Paths.TagKey} (range : k.InRange) (not5 : ¬ Level5 κ k) (label : Block) :
    H8.tagHash A' (hashInput label k.code) = H8.tagHash A (hashInput label k.code) := by
  rw [tagHash_key A' range, tagHash_key A range]
  exact shift.off _ (fun h => not5 (level5_of_pos hκ hs range h)) (fun h => not5 (level5_of_pos hκ hs' range h))

/-- The first blocks of the level-5 materials of chunk 31 of `κ`. -/
theorem shift_at {t : ℕ} (ht : t < 65536) :
    (A' (treePos κ t)).1 = (A (treePos κ t)).1 ^^^ (if t = s ∨ t = s' then d else 0) := by
  by_cases h1 : t = s
  · subst h1
    rw [if_pos (Or.inl rfl)]
    exact shift.atP
  · by_cases h2 : t = s'
    · subst h2
      rw [if_pos (Or.inr rfl)]
      exact shift.atQ
    · rw [if_neg (by tauto), xz,
        shift.off _ (fun h => h1 (treePos_inj hκ ht hs h)) (fun h => h2 (treePos_inj hκ ht hs' h))]

end Shifted

/-! ### 3. XOR folds -/

theorem xorFold_xor {count : ℕ} (f g : Fin count → Label) :
    xorFold (fun r => f r ^^^ g r) = xorFold f ^^^ xorFold g := by
  induction count with
  | zero =>
      unfold xorFold
      rw [Fin.foldl_zero, Fin.foldl_zero, Fin.foldl_zero]
      exact BitVec.xor_self.symm
  | succ n ih =>
      unfold xorFold at ih ⊢
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last, Fin.foldl_succ_last]
      have := ih (fun r => f r.castSucc) (fun r => g r.castSucc)
      simp only at this ⊢
      rw [this]
      ac_rfl

theorem xorFold_zero {count : ℕ} : xorFold (fun _ : Fin count => (0 : Label)) = 0 := by
  have h := xorFold_xor (fun _ : Fin count => (0 : Label)) (fun _ => 0)
  simp only [BitVec.xor_self] at h
  exact h

theorem xorFold_single {count : ℕ} (s : ℕ) (hs : s < count) (d : Label) :
    xorFold (fun t : Fin count => if t.val = s then d else 0) = d := by
  induction count with
  | zero => exact absurd hs (Nat.not_lt_zero _)
  | succ n ih =>
      unfold xorFold at ih ⊢
      rw [Fin.foldl_succ_last]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with lt | eq
      · have first := ih lt
        simp only [Fin.val_castSucc, Fin.val_last] at first ⊢
        rw [first, if_neg (by omega), xz]
      · subst eq
        have zero : (fun (acc : Label) (t : Fin s) => acc ^^^ if (Fin.castSucc t).val = s then d else 0) =
            fun acc (t : Fin s) => acc ^^^ (fun _ : Fin s => (0 : Label)) t := by
          funext acc t
          rw [if_neg (by simp only [Fin.val_castSucc]; omega)]
        simp only [Fin.val_last, if_true]
        rw [zero]
        have := @xorFold_zero s
        unfold xorFold at this
        rw [this, zx]

/-- **Shifting two entries of a XOR fold by the same block keeps it.** -/
theorem xorFold_shift2 {count : ℕ} (f : Fin count → Label) {s s' : ℕ} (hs : s < count) (hs' : s' < count)
    (ne : s ≠ s') (d : Label) :
    xorFold (fun t => f t ^^^ (if t.val = s ∨ t.val = s' then d else 0)) = xorFold f := by
  have split : (fun t : Fin count => if t.val = s ∨ t.val = s' then d else 0) =
      fun t => (if t.val = s then d else 0) ^^^ (if t.val = s' then d else 0) := by
    funext t
    by_cases h1 : t.val = s
    · rw [if_pos (Or.inl h1), if_pos h1, if_neg (by omega), xz]
    · by_cases h2 : t.val = s'
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zx]
      · rw [if_neg (by tauto), if_neg h1, if_neg h2, xz]
  rw [xorFold_xor f, split, xorFold_xor, xorFold_single s hs, xorFold_single s' hs', BitVec.xor_self,
    BitVec.xor_zero]

/-! ### 4. The garbler's pieces on two hashes -/

/-- A cast on the tag reading reads the table by tag only (its label does not matter). -/
theorem castM_tagHash (A : TagTable) (l : ℕ) (label : Label) (tagOf : ℕ → ℕ) :
    (castM l label tagOf).eval (H8.tagHash A) =
      materialize (castLanes l (packAnswers (castAnswers l) fun j => A (Conv.tag40 (tagOf j.val)))) := by
  simp only [castM, FreeQuery.eval_bind, eval_hlongM, FreeQuery.eval_pure, hlong, BmrEntry.tagHash_hashInput]
  rfl

/-- A one-block hash on the tag reading. -/
theorem hLabel_tagHash (A : TagTable) (label : Label) (tag : ℕ) :
    hLabel (H8.tagHash A) label tag = clip (A (Conv.tag40 tag)).1 := by
  unfold hLabel h128
  rw [BmrEntry.tagHash_hashInput]
  rfl

/-- The joins of a tree whose levels below `n` agree and whose level-`n` XOR agrees. -/
theorem tree_snd (H H' : HashN) (tagOf : ℕ → ℕ → ℕ) (Δ b0 : Label) (L n : ℕ) (hL : L = n + 1) (hn : n ≠ 0)
    (prev : (treeGarbleM tagOf Δ b0 n).eval H = (treeGarbleM tagOf Δ b0 n).eval H')
    (level : ∀ parent : Fin (2 ^ n) → Label, xorFold (fun slot => hLabel H (parent slot) (tagOf n slot.val)) =
      xorFold (fun slot => hLabel H' (parent slot) (tagOf n slot.val))) :
    ((treeGarbleM tagOf Δ b0 L).eval H).2 = ((treeGarbleM tagOf Δ b0 L).eval H').2 := by
  subst hL
  rw [SliceC.eval_treeGarbleM_succ H tagOf Δ b0 n hn, SliceC.eval_treeGarbleM_succ H' tagOf Δ b0 n hn]
  funext m
  simp only
  rw [prev, level]

/-- The right half of the last level of a tree is its last level's materials. -/
theorem tree_right (H : HashN) (tagOf : ℕ → ℕ → ℕ) (Δ b0 : Label) (L n : ℕ) (hL : L = n + 1) (hn : n ≠ 0)
    (leaf : Fin (2 ^ L)) (big : 2 ^ n ≤ leaf.val) :
    ∃ label, ((treeGarbleM tagOf Δ b0 L).eval H).1 leaf = hLabel H label (tagOf n (leaf.val - 2 ^ n)) := by
  subst hL
  rw [SliceC.eval_treeGarbleM_succ H tagOf Δ b0 n hn]
  simp only [extendLevel, dif_neg (not_lt.mpr big)]
  exact ⟨_, rfl⟩

/-- The fields of a chunk that the rest of the coordinate reads. -/
theorem chunk_joins (T : CrtTable) (coord : ℕ) (Δ : Label) (Z : ℕ → Label) (c : ℕ) (H : HashN) :
    ((chunkGarbleM T coord Δ Z c).eval H).joins = fun n =>
      ((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)).eval H).2 n ^^^
        Z (T.chunkOffset c + n) := by
  simp only [chunkGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]

theorem chunk_casts (T : CrtTable) (coord : ℕ) (Δ : Label) (Z : ℕ → Label) (c : ℕ) (H : HashN) :
    ((chunkGarbleM T coord Δ Z c).eval H).casts = atNat (fun leaf : Fin (2 ^ T.chunkWidth c) =>
      (castM T.castWidth (((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)).eval
        H).1 leaf) (chunkCastTag coord c leaf.val)).eval H) 0 := by
  simp only [chunkGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]

theorem chunk_pin (T : CrtTable) (coord : ℕ) (Δ : Label) (Z : ℕ → Label) (c : ℕ) (H : HashN) :
    ((chunkGarbleM T coord Δ Z c).eval H).pin = materialize ((sumLanes fun leaf : Fin (2 ^ T.chunkWidth c) =>
      (castM T.castWidth (((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)).eval
        H).1 leaf) (chunkCastTag coord c leaf.val)).eval H) + deltaLanes T.castWidth Δ) := by
  simp only [chunkGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]

/-- What the rest of a coordinate reads of a chunk: its joins, pin and casts, and the leaves of chunk 0. -/
def ChunkAgree (c : ℕ) {L : ℕ} (g g' : ChunkGarbled L) : Prop :=
  g.joins = g'.joins ∧ g.pin = g'.pin ∧ g.casts = g'.casts ∧ (c = 0 → g.leaves = g'.leaves)

/-- **A chunk whose tree agrees below level `n`, whose level-`n` XOR agrees and whose casts read the same answers.** -/
theorem chunk_agree (T : CrtTable) (coord : ℕ) (Δ : Label) (Z : ℕ → Label) (c n : ℕ) (H H' : HashN)
    (hw : T.chunkWidth c = n + 1) (hn : n ≠ 0) (c0 : c ≠ 0)
    (prev : (treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) n).eval H =
      (treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) n).eval H')
    (level : ∀ parent : Fin (2 ^ n) → Label,
      xorFold (fun slot => hLabel H (parent slot) (chunkTreeTag coord c n slot.val)) =
        xorFold (fun slot => hLabel H' (parent slot) (chunkTreeTag coord c n slot.val)))
    (casts : ∀ (label label' : Label) (leaf : ℕ), leaf < 2 ^ T.chunkWidth c →
      (castM T.castWidth label (chunkCastTag coord c leaf)).eval H =
        (castM T.castWidth label' (chunkCastTag coord c leaf)).eval H') :
    ChunkAgree c ((chunkGarbleM T coord Δ Z c).eval H) ((chunkGarbleM T coord Δ Z c).eval H') := by
  have htree := tree_snd H H' (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c) n hw hn prev level
  have hcasts : (fun leaf : Fin (2 ^ T.chunkWidth c) =>
      (castM T.castWidth (((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)).eval
        H).1 leaf) (chunkCastTag coord c leaf.val)).eval H) = fun leaf =>
      (castM T.castWidth (((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)).eval
        H').1 leaf) (chunkCastTag coord c leaf.val)).eval H' :=
    funext fun leaf => casts _ _ leaf.val leaf.isLt
  refine ⟨?_, ?_, ?_, fun h => absurd h c0⟩
  · rw [chunk_joins, chunk_joins, htree]
  · rw [chunk_pin, chunk_pin, hcasts]
  · rw [chunk_casts, chunk_casts, hcasts]

/-- A modulus's garbler reads its chunks only through their casts and the leaves of chunk 0. -/
theorem mod_congr (T : CrtTable) (S coord : ℕ) (Δ : Label) (X X' : ℕ → ChunkGarbled T.castWidth)
    (hcasts : ∀ c, (X c).casts = (X' c).casts) (hleaves : (X 0).leaves = (X' 0).leaves) (i : Fin T.count) :
    modGarbleM T S coord Δ X i = modGarbleM T S coord Δ X' i := by
  unfold modGarbleM
  cases h : T.kind i <;> simp only [hcasts, hleaves]

/-- **A coordinate on two hashes**: chunks that agree on what the rest reads, and moduli that read the same answers. -/
theorem coord_congr_of (T : CrtTable) (S coord : ℕ) (Δ : Label) (Z : ℕ → Label) (H H' : HashN)
    (chunks : ∀ c : Fin T.chunkCount,
      ChunkAgree c.val ((chunkGarbleM T coord Δ Z c.val).eval H) ((chunkGarbleM T coord Δ Z c.val).eval H'))
    (mods : ∀ (X : ℕ → ChunkGarbled T.castWidth) (i : Fin T.count),
      (modGarbleM T S coord Δ X i).eval H = (modGarbleM T S coord Δ X i).eval H') :
    (coordGarbleM T S coord Δ Z).eval H = (coordGarbleM T S coord Δ Z).eval H' := by
  set X := atNat (fun index : Fin T.chunkCount => (chunkGarbleM T coord Δ Z index.val).eval H)
    (ChunkGarbled.empty T.castWidth) with hX
  set X' := atNat (fun index : Fin T.chunkCount => (chunkGarbleM T coord Δ Z index.val).eval H')
    (ChunkGarbled.empty T.castWidth) with hX'
  have hjoins : ∀ c, (X c).joins = (X' c).joins := by
    intro c
    rw [hX, hX']
    unfold atNat
    split
    · exact (chunks ⟨c, ‹_›⟩).1
    · rfl
  have hcasts : ∀ c, (X c).casts = (X' c).casts := by
    intro c
    rw [hX, hX']
    unfold atNat
    split
    · exact (chunks ⟨c, ‹_›⟩).2.2.1
    · rfl
  have hleaves : (X 0).leaves = (X' 0).leaves := by
    rw [hX, hX']
    unfold atNat
    split
    · exact (chunks ⟨0, ‹_›⟩).2.2.2 rfl
    · rfl
  have hpin : ∀ c : Fin T.chunkCount, ((chunkGarbleM T coord Δ Z c.val).eval H).pin =
      ((chunkGarbleM T coord Δ Z c.val).eval H').pin := fun c => (chunks c).2.1
  have hmod : ∀ i, (modGarbleM T S coord Δ X i).eval H = (modGarbleM T S coord Δ X' i).eval H' := by
    intro i
    rw [mod_congr T S coord Δ X X' hcasts hleaves i]
    exact mods X' i
  simp only [coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]
  simp only [← hX, ← hX', hmod, hjoins, hpin]

/-! ### 5. The published value under the shift -/

theorem table_chunkCount' : table.chunkCount = 32 := Paths.bn254_chunkCount

/-- **The published value is invariant under the two-slot shift** at level 5 of chunk 31 of coordinate `κ`. -/
theorem pub_shift (scalar : NonZeroScalar) (coins : Entry.Coins) {κ s s' : ℕ} (hκ : κ < 2) (hs : s < 32)
    (hs' : s' < 32) (ne : s ≠ s') {d : Block} {A A' : TagTable}
    (shift : Shift2 (treePos κ s) (treePos κ s') d A A') :
    EntryCorrect.pubOf (H8.tagHash A') scalar coins = EntryCorrect.pubOf (H8.tagHash A) scalar coins := by
  have hs6 : s < 65536 := by omega
  have hs6' : s' < 65536 := by omega
  have coordEq : ∀ (S coord : ℕ), S ≤ 1000 → coord < 2 → ∀ (Δ : Label) (Z : ℕ → Label),
      (coordGarbleM table S coord Δ Z).eval (H8.tagHash A') =
        (coordGarbleM table S coord Δ Z).eval (H8.tagHash A) := by
    intro S coord hS hc Δ Z
    have ranges := Paths.bn254_ranges S hS
    refine coord_congr_of table S coord Δ Z _ _ (fun c => ?_) (fun X i => ?_)
    · have cLt : c.val < 32 := lt_of_lt_of_le c.isLt table_chunkCount'.le
      by_cases special : coord = κ ∧ c.val = 31
      · obtain ⟨hcκ, c31⟩ := special
        refine chunk_agree table coord Δ Z c.val 5 _ _ (by rw [c31]; rfl) (by norm_num) (by omega) ?_ ?_ ?_
        · exact (keyRun_congr (Paths.treeGarbleM_tagged 0 coord c.val 0
            ⟨by norm_num, hc, by omega, by norm_num, by norm_num, by norm_num⟩ Δ _ 5 (by norm_num)) _ _
            fun k member range label => key_agree hκ hs6 hs6' shift range (fun h5 => by
              simp only [Paths.treeKeys, Set.mem_ofPred_eq] at member
              exact absurd h5.2.2.2 (by omega)) label).1
        · intro parent
          simp only [hLabel_tagHash]
          have hpos : ∀ slot : Fin (2 ^ 5), Conv.tag40 (chunkTreeTag coord c.val 5 slot.val) = treePos κ slot.val := by
            intro slot
            rw [hcκ, c31]
            rfl
          simp only [hpos]
          have each : ∀ slot : Fin (2 ^ 5), clip (A' (treePos κ slot.val)).1 =
              clip (A (treePos κ slot.val)).1 ^^^ (if slot.val = s ∨ slot.val = s' then clip d else 0) := by
            intro slot
            rw [shift_at hκ hs6 hs6' shift (by have := slot.isLt; omega), Narrow.clip_xor]
            split_ifs <;> simp only [Narrow.clip_zero]
          simp only [each]
          exact xorFold_shift2 _ (by norm_num; omega) (by norm_num; omega) ne (clip d)
        · intro label label' leaf hleaf
          rw [castM_tagHash, castM_tagHash]
          have leafLt : leaf < 256 := lt_of_lt_of_le hleaf
            (le_trans (Nat.pow_le_pow_right (by norm_num) (Paths.bn254_chunkWidth c.val)) (by norm_num))
          have e : (fun j : Fin (castAnswers table.castWidth) => A' (Conv.tag40 (chunkCastTag coord c.val leaf j.val))) =
              fun j => A (Conv.tag40 (chunkCastTag coord c.val leaf j.val)) := by
            funext j
            have jLt : j.val < 64 := lt_of_lt_of_le j.isLt ranges.castAnswers
            have range : TagInRange coord c.val 0 0 leaf j.val := ⟨hc, by omega, by norm_num, by norm_num, by omega, jLt⟩
            refine pos_agree hκ hs6 hs6' shift _ ?_
            have lt40 : chunkCastTag coord c.val leaf j.val < 2 ^ 40 :=
              Asks.tagCode_lt (fam := Family.chunkCast) (by decide) range
            have hf : tagFamily (chunkCastTag coord c.val leaf j.val) = Family.chunkCast := tagFamily_tagCode range
            show tagFamily (chunkCastTag coord c.val leaf j.val % 2 ^ 40) ≠ 0
            rw [Nat.mod_eq_of_lt lt40, hf]
            decide
          rw [e]
      · have full := (keyRun_congr (Paths.chunkGarbleM_tagged table coord Δ Z c.val hc (by omega)
          (ranges.chunkWidth c.val c.isLt) ranges.castAnswers) (H8.tagHash A') (H8.tagHash A)
          fun k member range label => key_agree hκ hs6 hs6' shift range (fun h5 => special (by
            simp only [Paths.pairKeys, Set.mem_ofPred_eq] at member
            obtain ⟨_, h2, h3, _⟩ := h5
            omega)) label).1
        rw [full]
        exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
    · exact (keyRun_congr (Paths.modGarbleM_tagged table S coord ranges hc Δ X i) _ _
        fun k member range label => key_agree hκ hs6 hs6' shift range (fun h5 => by
          simp only [Paths.modKeys, Set.mem_ofPred_eq] at member
          have := h5.1
          omega) label).1
  have masks : EntryCorrect.masksOf (H8.tagHash A') coins = EntryCorrect.masksOf (H8.tagHash A) coins := by
    have maskFams : ∀ k ∈ Paths.maskKeys digitCount, ¬ Level5 κ k := by
      intro k member h5
      simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
        Set.mem_ofPred_eq] at member
      have := h5.1
      omega
    have tagged := Paths.maskAnswersM_tagged (0 : Block) digitCount (by decide) (by decide)
    have same := (keyRun_congr tagged (H8.tagHash A') (H8.tagHash A) fun k member range label =>
      key_agree hκ hs6 hs6' shift range (maskFams k member) label).1
    calc EntryCorrect.masksOf (H8.tagHash A') coins
        = maskValues (H8.tagHash A') 0 digitCount := BmrEntry.maskValues_tagHash A' _
      _ = (maskAnswersM (0 : Block) digitCount).eval (H8.tagHash A') := (eval_maskAnswersM _ _ _).symm
      _ = (maskAnswersM (0 : Block) digitCount).eval (H8.tagHash A) := same
      _ = maskValues (H8.tagHash A) 0 digitCount := eval_maskAnswersM _ _ _
      _ = EntryCorrect.masksOf (H8.tagHash A) coins := (BmrEntry.maskValues_tagHash A _).symm
  have entries : EntryCorrect.entriesOf (H8.tagHash A') scalar coins =
      EntryCorrect.entriesOf (H8.tagHash A) scalar coins := by
    funext o
    rw [entriesOf_tagHash, entriesOf_tagHash]
    have h0 : 2 * o.val < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
    have h1 : 2 * o.val + 1 < 65536 := by have := o.isLt; simp only [digitCount] at this; omega
    rw [pos_agree hκ hs6 hs6' shift _ (by rw [DigestSplit.family_final _ h0]; decide),
      pos_agree hκ hs6 hs6' shift _ (by rw [DigestSplit.family_final _ h1]; decide)]
  have gx : EntryCorrect.gxOf (H8.tagHash A') coins = EntryCorrect.gxOf (H8.tagHash A) coins :=
    coordEq xCount 0 (by decide) (by norm_num) _ _
  have gy : EntryCorrect.gyOf (H8.tagHash A') coins = EntryCorrect.gyOf (H8.tagHash A) coins :=
    coordEq yCount 1 (by decide) (by norm_num) _ _
  unfold EntryCorrect.pubOf
  rw [gx, gy, masks, entries]

/-! ### 6. The label of a never-hot cast -/

/-- What a never-hot garbler input is: a cast of chunk 31 of a coordinate at a leaf `49 ≤ α < 64`, labelled by the
first block of the table at the level-5 material `α − 32`. -/
def NeverFacts (A : TagTable) (N : ℕ) : Prop :=
  tagCoord (N / 2 ^ 128) < 2 ∧ 49 ≤ tagSlot (N / 2 ^ 128) ∧ tagSlot (N / 2 ^ 128) < 64 ∧
    BitVec.ofNat 128 N = embed (clip (A (treePos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32))).1)

/-- **One coordinate's never-hot inputs.** -/
theorem coord_never (A : TagTable) (S coord : ℕ) (hS : S ≤ 1000) (hc : coord < 2) (Δ : Label) (Z : ℕ → Label)
    (N : ℕ) (inside : N ∈ asked (H8.tagHash A) (coordGarbleM table S coord Δ Z))
    (never : NeverHotCast (N / 2 ^ 128)) : NeverFacts A N := by
  have ranges := Paths.bn254_ranges S hS
  obtain ⟨fam1, idx31, slot49⟩ := never
  simp only [coordGarbleM, asked_bind, asked_tableM, asked_pure, List.append_nil, List.mem_append,
    List.mem_flatMap, List.mem_finRange, true_and] at inside
  rcases inside with ⟨c, inC⟩ | ⟨i, inM⟩
  · have cLt : c.val < 32 := lt_of_lt_of_le c.isLt table_chunkCount'.le
    rw [asked_chunkGarbleM] at inC
    rcases List.mem_append.mp inC with inTree | inCast
    · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged (Paths.treeGarbleM_tagged 0 coord c.val 0
        ⟨by norm_num, hc, by omega, by norm_num, by norm_num, by norm_num⟩ Δ _ (table.chunkWidth c.val)
        (ranges.chunkWidth c.val c.isLt)) _ _ inTree
      rw [hashInput_tag, tagFamily_key range] at fam1
      simp only [Paths.treeKeys, Set.mem_ofPred_eq] at member
      omega
    · obtain ⟨leaf, -, inCast⟩ := List.mem_flatMap.mp inCast
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp inCast
      rw [hashInput_tag] at fam1 idx31 slot49
      have leafLt : leaf.val < 256 := lt_of_lt_of_le leaf.isLt
        (le_trans (Nat.pow_le_pow_right (by norm_num) (Paths.bn254_chunkWidth c.val)) (by norm_num))
      have jLt : j.val < 64 := lt_of_lt_of_le j.isLt ranges.castAnswers
      have range : TagInRange coord c.val 0 0 leaf.val j.val := ⟨hc, by omega, by norm_num, by norm_num, by omega, jLt⟩
      have hidx : tagIdx (chunkCastTag coord c.val leaf.val j.val) = c.val := tagIdx_tagCode range
      have hslot : tagSlot (chunkCastTag coord c.val leaf.val j.val) = leaf.val := tagSlot_tagCode range
      have hcoord : tagCoord (chunkCastTag coord c.val leaf.val j.val) = coord := tagCoord_tagCode range
      rw [hidx] at idx31
      rw [hslot] at slot49
      have hw : table.chunkWidth c.val = 5 + 1 := by rw [idx31]; rfl
      have e64 : (2 : ℕ) ^ table.chunkWidth c.val = 64 := by rw [hw]; norm_num
      have leaf64 : leaf.val < 64 := lt_of_lt_of_eq leaf.isLt e64
      obtain ⟨label, hlabel⟩ := tree_right (H8.tagHash A) (chunkTreeTag coord c.val) Δ
        (Z (table.chunkOffset c.val + 0)) (table.chunkWidth c.val) 5 hw (by norm_num) leaf (by norm_num; omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hashInput_tag, hcoord]; exact hc
      · rw [hashInput_tag, hslot]; exact slot49
      · rw [hashInput_tag, hslot]; exact leaf64
      · rw [label_of_hashInput, hlabel, hLabel_tagHash, hashInput_tag, hcoord, hslot]
        have same : ∀ x, chunkTreeTag coord c.val 5 x = chunkTreeTag coord 31 5 x := fun x => by rw [idx31]
        show embed (clip (A (Conv.tag40 (chunkTreeTag coord c.val 5 (leaf.val - 2 ^ 5)))).1) =
          embed (clip (A (Conv.tag40 (chunkTreeTag coord 31 5 (leaf.val - 32)))).1)
        rw [same, show (2 : ℕ) ^ 5 = 32 by norm_num]
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.modGarbleM_tagged table S coord ranges hc Δ _ i) _ _ inM
    rw [hashInput_tag, tagFamily_key range] at fam1
    simp only [Paths.modKeys, Set.mem_ofPred_eq] at member
    omega

/-- **A garbler input at a never-hot cast tag is labelled by the level-5 material at slot `α − 32`.** -/
theorem never_input (scalar : NonZeroScalar) (coins : Entry.Coins) (A : TagTable) (N : ℕ)
    (inside : N ∈ asked (H8.tagHash A) (garbleCM scalar coins)) (never : NeverHotCast (N / 2 ^ 128)) :
    NeverFacts A N := by
  unfold garbleCM at inside
  simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at inside
  rcases inside with inX | inY | inKey | inMask | inDigest
  · exact coord_never A xCount 0 (by decide) (by norm_num) _ _ N inX never
  · exact coord_never A yCount 1 (by decide) (by norm_num) _ _ N inY never
  · simp only [keyM, asked_bind, asked_askN, asked_pure, List.append_nil, List.mem_singleton] at inKey
    subst inKey
    have fam := never.1
    unfold maskKeyInput at fam
    rw [hashInput_div, maskKeyTag_family] at fam
    exact absurd fam (by decide)
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.maskAnswersM_tagged _ digitCount (by decide) (by decide)) _ _ inMask
    have fam := never.1
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.maskKeys, Paths.nonCollectorKeys, Paths.maskStageKeys, Paths.maskSiteKeys, Set.mem_union,
      Set.mem_ofPred_eq] at member
    omega
  · obtain ⟨k, member, range, label, rfl⟩ := asked_of_tagged
      (Paths.digestGarbleM_tagged coordinateBitCount digitCount (by decide) (by decide) _ _ _ _ _) _ _ inDigest
    have fam := never.1
    rw [hashInput_div, tagFamily_key range] at fam
    simp only [Paths.digestLabelKeys, Paths.digestFinalKeys, Set.mem_union, Set.mem_ofPred_eq] at member
    omega

/-! ### 7. The count -/

open Classical in
/-- The mass of a table event, through the refill of the table at an independent uniform family. -/
theorem mass_eq {ι : Type} [Fintype ι] [DecidableEq ι] (μT : PMF TagTable) (pos : ι → Fin (2 ^ 40))
    (indep : Indep μT (Set.range pos) (PMF.uniformOfFintype (ι → Block × Block)) (fun T => T ∘ pos) (fun _ => True))
    (R : TagTable → Prop) :
    μT.toOuterMeasure {T | R T} =
      ∑' T, μT T * ((Fintype.card (ι → Block × Block) : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun f => R (fillAt pos f T)).card : ℝ≥0∞)) := by
  let G : (ι → Block × Block) → TagTable → PMF Bool := fun f T => PMF.pure (decide (R (fillAt pos f T)))
  have ignoresG : ∀ f, True → Ignores (Set.range pos) (G f) := by
    intro f _ T T' agree
    have same : fillAt pos f T = fillAt pos f T' := by
      funext i
      unfold fillAt
      split
      · rfl
      · rename_i miss
        exact agree i fun ⟨k, hk⟩ => miss ⟨k, hk⟩
    simp only [G, same]
  have law := indep Bool G ignoresG
  have atTrue := congrArg (fun p : PMF Bool => p true) law
  simp only [G, fillAt_self] at atTrue
  have lhs : μT.toOuterMeasure {T | R T} = (μT.bind fun T => PMF.pure (decide (R T))) true := by
    rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun T => ?_
    by_cases h : R T
    · rw [Set.indicator_of_mem (show T ∈ {T | R T} from h), PMF.pure_apply, decide_eq_true h, if_pos rfl, mul_one]
    · rw [Set.indicator_of_notMem (show T ∉ {T | R T} from h), PMF.pure_apply, decide_eq_false h,
        if_neg (by decide), mul_zero]
  have inner : ∀ T, (∑' f : ι → Block × Block, (PMF.uniformOfFintype (ι → Block × Block)) f *
      (PMF.pure (decide (R (fillAt pos f T))) : PMF Bool) true) =
      (Fintype.card (ι → Block × Block) : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun f => R (fillAt pos f T)).card : ℝ≥0∞) := by
    intro T
    rw [tsum_fintype, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [PMF.uniformOfFintype_apply]
    by_cases h : R (fillAt pos f T)
    · rw [PMF.pure_apply, decide_eq_true h, if_pos rfl, if_pos h, Nat.cast_one]
    · rw [PMF.pure_apply, decide_eq_false h, if_neg (by decide), if_neg h, Nat.cast_zero]
  rw [lhs, atTrue, PMF.bind_apply]
  simp_rw [PMF.bind_apply]
  calc ∑' f, (PMF.uniformOfFintype (ι → Block × Block)) f *
        ∑' T, μT T * (PMF.pure (decide (R (fillAt pos f T))) : PMF Bool) true
      = ∑' T, ∑' f, (PMF.uniformOfFintype (ι → Block × Block)) f *
          (μT T * (PMF.pure (decide (R (fillAt pos f T))) : PMF Bool) true) := by
        simp_rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_comm
    _ = ∑' T, μT T * ∑' f, (PMF.uniformOfFintype (ι → Block × Block)) f *
          (PMF.pure (decide (R (fillAt pos f T))) : PMF Bool) true := by
        refine tsum_congr fun T => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun f => ?_
        ring
    _ = _ := by simp_rw [inner]

/-- **A table event through an independent uniform family**: if, for every coins and cold part, the refills that
satisfy the event and give the view `v` are at most `ε` of those that give `v`, the event has conditional mass at most
`ε` given the view. -/
theorem outer_family_le {C V ι : Type} [Fintype ι] [DecidableEq ι] (coinsLaw : PMF C) (μT : PMF TagTable)
    (pos : ι → Fin (2 ^ 40))
    (indep : Indep μT (Set.range pos) (PMF.uniformOfFintype (ι → Block × Block)) (fun T => T ∘ pos) (fun _ => True))
    (view : C → TagTable → V) (E : C → TagTable → Prop) (ε : ℝ≥0∞)
    (count : ∀ c T v (inst : DecidablePred fun f => view c (fillAt pos f T) = v ∧ E c (fillAt pos f T))
      (inst' : DecidablePred fun f => view c (fillAt pos f T) = v),
      ((@Finset.filter _ _ inst Finset.univ).card : ℝ≥0∞) ≤ ε * (@Finset.filter _ _ inst' Finset.univ).card)
    (v : V) :
    (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure {ω | view ω.1 ω.2 = v ∧ E ω.1 ω.2} ≤
      ε * (coinsLaw.bind fun c => μT.map fun T => (c, T)).toOuterMeasure {ω | view ω.1 ω.2 = v} := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  have e1 : (fun T => (c, T)) ⁻¹' {ω : C × TagTable | view ω.1 ω.2 = v ∧ E ω.1 ω.2} =
      {T | view c T = v ∧ E c T} := rfl
  have e2 : (fun T => (c, T)) ⁻¹' {ω : C × TagTable | view ω.1 ω.2 = v} = {T | view c T = v} := rfl
  rw [e1, e2, mass_eq μT pos indep (fun T => view c T = v ∧ E c T), mass_eq μT pos indep (fun T => view c T = v),
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun T => ?_
  calc μT T * ((Fintype.card (ι → Block × Block) : ℝ≥0∞)⁻¹ *
        ((@Finset.filter _ (fun f => view c (fillAt pos f T) = v ∧ E c (fillAt pos f T))
          (fun _ => Classical.propDecidable _) Finset.univ).card : ℝ≥0∞))
      ≤ μT T * ((Fintype.card (ι → Block × Block) : ℝ≥0∞)⁻¹ *
        (ε * ((@Finset.filter _ (fun f => view c (fillAt pos f T) = v)
          (fun _ => Classical.propDecidable _) Finset.univ).card : ℝ≥0∞))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (count c T v _ _))
    _ = ε * (μT T * ((Fintype.card (ι → Block × Block) : ℝ≥0∞)⁻¹ *
        ((@Finset.filter _ (fun f => view c (fillAt pos f T) = v)
          (fun _ => Classical.propDecidable _) Finset.univ).card : ℝ≥0∞))) := by ring

/-! ### 8. The two positions and the shift of their refills -/

/-- The family of the two level-5 positions `s` and `s'`. -/
def pairPos (κ s s' : ℕ) (k : Fin 2) : Fin (2 ^ 40) := if k = 0 then treePos κ s else treePos κ s'

theorem pairPos_zero (κ s s' : ℕ) : pairPos κ s s' 0 = treePos κ s := if_pos rfl

theorem pairPos_one (κ s s' : ℕ) : pairPos κ s s' 1 = treePos κ s' := if_neg (by decide)

theorem pairPos_inj {κ s s' : ℕ} (hκ : κ < 2) (hs : s < 65536) (hs' : s' < 65536) (ne : s ≠ s') :
    Function.Injective (pairPos κ s s') := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd (treePos_inj hκ hs hs' (by simpa [pairPos_zero, pairPos_one] using h)) ne
  · exact absurd (treePos_inj hκ hs hs' (by simpa [pairPos_zero, pairPos_one] using h.symm)) ne
  · rfl

theorem pairPos_mem {κ s s' : ℕ} {i : Fin (2 ^ 40)} (hi : i ∈ Set.range (pairPos κ s s')) :
    i = treePos κ s ∨ i = treePos κ s' := by
  obtain ⟨k, rfl⟩ := hi
  fin_cases k
  · exact Or.inl (pairPos_zero κ s s')
  · exact Or.inr (pairPos_one κ s s')

theorem fill_at {κ : Type} [Fintype κ] [DecidableEq κ] (pos : κ → Fin (2 ^ 40)) (inj : Function.Injective pos)
    (f : κ → Block × Block) (A : TagTable) (k : κ) : fillAt pos f A (pos k) = f k :=
  congrFun (fillAt_comp pos inj f A) k

/-- Shift the first blocks of a refill by `d`. -/
def shiftF (d : Block) (f : Fin 2 → Block × Block) : Fin 2 → Block × Block := fun k => ((f k).1 ^^^ d, (f k).2)

theorem shiftF_shiftF (d : Block) (f : Fin 2 → Block × Block) : shiftF d (shiftF d f) = f := by
  funext k
  unfold shiftF
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem shift2_fill {κ s s' : ℕ} (hκ : κ < 2) (hs : s < 65536) (hs' : s' < 65536) (ne : s ≠ s') (d : Block)
    (f : Fin 2 → Block × Block) (T : TagTable) :
    Shift2 (treePos κ s) (treePos κ s') d (fillAt (pairPos κ s s') f T)
      (fillAt (pairPos κ s s') (shiftF d f) T) := by
  have inj := pairPos_inj hκ hs hs' ne
  refine ⟨fun i hP hQ => ?_, ?_, ?_⟩
  · have miss : i ∉ Set.range (pairPos κ s s') := fun hit => by
      rcases pairPos_mem hit with h | h
      · exact hP h
      · exact hQ h
    rw [fillAt_apply_of_not_mem _ _ _ i miss, fillAt_apply_of_not_mem _ _ _ i miss]
  · rw [← pairPos_zero κ s s', fill_at _ inj (shiftF d f) T 0, fill_at _ inj f T 0]
    rfl
  · rw [← pairPos_one κ s s', fill_at _ inj (shiftF d f) T 1, fill_at _ inj f T 1]
    rfl

set_option linter.constructorNameAsVariable false in
/-- **The count**: the refills that give the view `v` and the clipped first block `g` at `P` are `2^-104` of those that
give `v`. -/
theorem count_le (scalar : NonZeroScalar) {κ s s' : ℕ} (hκ : κ < 2) (hs : s < 32) (hs' : s' < 32) (ne : s ≠ s')
    (g : Label) (c : Entry.Coins) (T : TagTable) (v : Instance.crtEntry.Public)
    (inst : DecidablePred fun f => pubT scalar c (fillAt (pairPos κ s s') f T) = v ∧
      clip (fillAt (pairPos κ s s') f T (treePos κ s)).1 = g)
    (inst' : DecidablePred fun f => pubT scalar c (fillAt (pairPos κ s s') f T) = v) :
    ((@Finset.filter _ _ inst Finset.univ).card : ℝ≥0∞) ≤
      ((2 : ℝ≥0∞) ^ labelBits)⁻¹ * (@Finset.filter _ _ inst' Finset.univ).card := by
  classical
  have hs6 : s < 65536 := by omega
  have hs6' : s' < 65536 := by omega
  have inj := pairPos_inj hκ hs6 hs6' ne
  have inv : ∀ d f, pubT scalar c (fillAt (pairPos κ s s') (shiftF d f) T) =
      pubT scalar c (fillAt (pairPos κ s s') f T) :=
    fun d f => pub_shift scalar c hκ hs hs' ne (shift2_fill hκ hs6 hs6' ne d f T)
  have at0 : ∀ f, (fillAt (pairPos κ s s') f T (treePos κ s)).1 = (f 0).1 := by
    intro f
    rw [← pairPos_zero κ s s', fill_at _ inj f T 0]
  set S := @Finset.filter _ _ inst' Finset.univ with hS
  let fib : Label → Finset (Fin 2 → Block × Block) := fun y => S.filter fun f => clip (f 0).1 = y
  have mem_fib : ∀ y f, f ∈ fib y ↔ pubT scalar c (fillAt (pairPos κ s s') f T) = v ∧ clip (f 0).1 = y := by
    intro y f
    simp only [fib, hS, Finset.mem_filter, Finset.mem_univ, true_and]
  have first : @Finset.filter _ _ inst Finset.univ = fib g := by
    ext f
    rw [mem_fib, Finset.mem_filter, at0]
    simp only [Finset.mem_univ, true_and]
  have each : ∀ y, (fib y).card = (fib g).card := by
    intro y
    refine Finset.card_nbij' (shiftF (embed (y ^^^ g))) (shiftF (embed (y ^^^ g))) (fun f hf => ?_) (fun f hf => ?_)
      (fun f _ => shiftF_shiftF _ f) (fun f _ => shiftF_shiftF _ f)
    · rw [Finset.mem_coe, mem_fib] at hf ⊢
      refine ⟨by rw [inv]; exact hf.1, ?_⟩
      show clip ((f 0).1 ^^^ embed (y ^^^ g)) = g
      rw [Narrow.clip_xor_embed]
      rw [hf.2, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [Finset.mem_coe, mem_fib] at hf ⊢
      refine ⟨by rw [inv]; exact hf.1, ?_⟩
      show clip ((f 0).1 ^^^ embed (y ^^^ g)) = y
      rw [Narrow.clip_xor_embed]
      rw [hf.2, BitVec.xor_comm y g, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have total : S.card = 2 ^ labelBits * (fib g).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun f => clip (f 0).1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    rw [Finset.sum_congr rfl fun y _ => each y, Finset.sum_const, Finset.card_univ,
      Narrow.card_label, smul_eq_mul]
  rw [first, total, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
    ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]

end

/-! ### 9. The case -/

open Kriterion.CRT.Privacy.CastNever in
/-- **The 30 never-hot casts.** -/
theorem _root_.Kriterion.CRT.Privacy.StageOneProof.neverCase :
    StageOneProof.OneCase StageOneProof.NeverHotCast ((2 : ℝ≥0∞) ^ labelBits)⁻¹ := by
  intro field group parameter scalar view N never
  by_cases asked : ∃ tape, N ∈ gAsked scalar tape
  · obtain ⟨tape0, h0⟩ := asked
    rw [gAsked_eq] at h0
    obtain ⟨hκ, lo, hi, -⟩ := never_input scalar tape0.1 tape0.2 N h0 never
    have hs : tagSlot (N / 2 ^ 128) - 32 < 32 := by omega
    have ne : tagSlot (N / 2 ^ 128) - 32 ≠ 0 := by omega
    have hs6 : tagSlot (N / 2 ^ 128) - 32 < 65536 := by omega
    have away : ∀ site ∈ crtLayout.sites, ∀ k,
        pairPos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32) 0 k ∉ (siteTags crtLayout site).map tagPos := by
      intro site mem k
      have fam : tagFamily (pairPos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32) 0 k).val = 0 := by
        rcases pairPos_mem (⟨k, rfl⟩ : pairPos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32) 0 k ∈
          Set.range (pairPos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32) 0)) with h | h
        · rw [h]; exact treePos_family hκ hs6
        · rw [h]; exact treePos_family hκ (by norm_num)
      exact away_of_family _ (by rw [fam]; decide) (by rw [fam]; decide) site mem
    let E : Instance.crtEntry.Coins → TagTable → Prop := fun _ T =>
      clip (T (treePos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32))).1 = clip (BitVec.ofNat 128 N)
    have sub : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} ⊆
        {ω : TableTape Instance.crtEntry | pubT scalar ω.1 ω.2 = view ∧ E ω.1 ω.2} := by
      rintro tape ⟨hv, hN⟩
      rw [stageOneView_pubT] at hv
      rw [gAsked_eq] at hN
      refine ⟨hv, ?_⟩
      have label := congrArg clip (never_input scalar tape.1 tape.2 N hN never).2.2.2.symm
      simpa only [Narrow.clip_embed] using label
    refine le_trans (MeasureTheory.measure_mono sub) ?_
    rw [viewSet_eq, swappedTableTape_eq]
    exact outer_family_le _ (swappedTableLaw crtLayout) (pairPos (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128) - 32) 0)
      (indep_swapped_family crtLayout _ (pairPos_inj hκ hs6 (by norm_num) ne) away) (pubT scalar) E _
      (fun c T v inst inst' => count_le scalar hκ hs (by norm_num) ne (clip (BitVec.ofNat 128 N)) c T v inst inst') view
  · have empty : {tape | stageOneView Instance.crtEntry parameter scalar tape = view ∧ N ∈ gAsked scalar tape} = ∅ := by
      ext tape
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ inside
      exact asked ⟨tape, inside⟩
    rw [empty, MeasureTheory.measure_empty]
    exact zero_le

end Kriterion.CRT.Privacy.CastNever
