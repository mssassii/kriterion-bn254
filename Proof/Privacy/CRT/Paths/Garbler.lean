/-
**The garbler's conversion layer and body are `Tagged`**: along every path of `coordGarbleM T S coord`
every query is a labelled input at a key of family 0 to 6 of coordinate `coord`, the keys are pairwise distinct, and
each pad site is asked at one label, for every table `T` whose fields fit `tagCode` (`TableRanges`).
-/

import Proof.Privacy.CRT.Paths.Blocks

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC

/-! ### Folds -/

/-- The keys of the folds at bit positions `start .. start + count − 1` over `m` residues. -/
def foldKeys (coord idx start count m : Nat) : Set TagKey :=
  {k | k.fam = 5 ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = 0 ∧ k.part = 0 ∧ start ≤ k.level ∧
    k.level < start + count ∧ k.slot < m}

theorem fields_fold {coord idx : Nat} (coordLt : coord < 2) (idxLt : idx < 128) : Fields 5 coord idx 0 :=
  ⟨by norm_num, coordLt, idxLt, by norm_num, by norm_num, by norm_num⟩

/-- **The garbler's folds.** -/
theorem foldsGarbleM_tagged (coord idx m : Nat) (coordLt : coord < 2) (idxLt : idx < 128) (mSmall : m ≤ 65536)
    (bitMask : Nat → Block) :
    ∀ (count start : Nat) (labels : Fin m → Block), start + count ≤ 16 →
      Tagged (foldKeys coord idx start count m)
        (foldsGarbleM m (fun position residue => tagCode 5 coord idx 0 position residue 0) bitMask count start
          labels)
  | 0, _, _, _ => Tagged.pure _ _
  | count + 1, position, labels, small => by
      simp only [foldsGarbleM, foldGarbleM]
      have fold := levelHashes_tagged 5 coord idx 0 position m (fields_fold coordLt idxLt) (by omega) mSmall labels
      refine Tagged.bind' (Tagged.bind_pure fold _) (S' := foldKeys coord idx (position + 1) count m)
        (fun step => Tagged.bind_pure (foldsGarbleM_tagged coord idx m coordLt idxLt mSmall bitMask count
          (position + 1) _ (by omega)) _) ?_ ?_ ?_
      · refine Set.disjoint_left.mpr fun k inFold inRest => ?_
        simp only [levelKeys, foldKeys, Set.mem_setOf_eq] at inFold inRest
        omega
      · exact siteDisjoint_of_fam fun k inS => by
          simp only [levelKeys, Set.mem_setOf_eq] at inS
          rw [inS.1]; exact ⟨by norm_num, by norm_num⟩
      · rintro k (inFold | inRest)
        · simp only [levelKeys, foldKeys, Set.mem_setOf_eq] at inFold ⊢
          omega
        · simp only [foldKeys, Set.mem_setOf_eq] at inRest ⊢
          omega

/-! ### The body -/

theorem site_pad {k : TagKey} (six : k.fam = 6) : k.site = some (.pad k.coord k.idx k.slot) := by
  unfold TagKey.site
  rw [six]
  rfl

theorem site_mask {k : TagKey} (seven : k.fam = 7) : k.site = some (.mask k.stage k.slot) := by
  unfold TagKey.site
  rw [seven]
  rfl

/-- The keys of one pad vector (the pad site `(coord, idx, residue)`), `count` answers. -/
def padKeys (coord idx residue count : Nat) : Set TagKey :=
  {k | k.fam = 6 ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = 0 ∧ k.level = 0 ∧ k.slot = residue ∧ k.part < count}

/-- The keys of the pads of the residues below `m`, `count` answers each. -/
def bodyKeys (coord idx m count : Nat) : Set TagKey :=
  {k | k.fam = 6 ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = 0 ∧ k.level = 0 ∧ k.slot < m ∧ k.part < count}

/-- **One pad vector**: `q` answers at one label (one pad site). -/
theorem padVectorM_tagged (coord idx residue m S q : Nat) (coordLt : coord < 2) (idxLt : idx < 128)
    (residueSmall : residue < 65536) (qSmall : q ≤ 64) (label : Block) :
    Tagged (padKeys coord idx residue q)
      (padVectorM m S q label fun part => tagCode 6 coord idx 0 0 residue part) := by
  unfold padVectorM
  refine Tagged.bind_empty ((Tagged.hlongM label _ q (fun part => ⟨6, coord, idx, 0, 0, residue, part⟩)
    (fun _ _ => rfl) (fun part small => ⟨by norm_num, coordLt, idxLt, by norm_num, by norm_num, residueSmall,
      show part < 64 by omega⟩)
    fun i j _ _ same => by cases same; rfl).mono ?_) fun _ => Tagged.pure _ _
  rintro k ⟨part, small, same⟩
  rw [same]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, small⟩

/-- **The garbler's body** of one modulus: every residue's pad vector. -/
theorem bodyGarbleM_tagged (coord idx m S q : Nat) (coordLt : coord < 2) (idxLt : idx < 128)
    (mSmall : m ≤ 65536) (qSmall : q ≤ 64) (final : Fin m → Block) :
    Tagged (bodyKeys coord idx m q)
      (bodyGarbleM m S q coord idx final) := by
  unfold bodyGarbleM
  refine Tagged.bind_empty ((Tagged.tableM (S := fun residue => padKeys coord idx residue q) m
    (fun residue => padVectorM_tagged coord idx residue.val m S q coordLt idxLt (by omega) qSmall (final residue))
    fun i j _ _ different => ⟨?_, ?_⟩).mono ?_) fun _ => Tagged.pure _ _
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [padKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · intro k inI k' inJ sameSite
    simp only [padKeys, Set.mem_setOf_eq] at inI inJ
    rw [site_pad inI.1, site_pad inJ.1] at sameSite
    simp only [Option.some.injEq, Privacy.SiteId.pad.injEq] at sameSite
    omega
  · rintro k ⟨residue, small, inS⟩
    simp only [padKeys, bodyKeys, Set.mem_setOf_eq] at inS ⊢
    omega

/-! ### Chunks and extraction stages -/

/-- The keys of a tree of family `treeFam` and its leaf casts of family `castFam`. -/
def pairKeys (treeFam castFam coord idx stage : Nat) : Set TagKey :=
  {k | (k.fam = treeFam ∨ k.fam = castFam) ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage}

/-- A tree over `width` bits and the casts of its `2 ^ width` leaves. -/
theorem treeCasts_tagged {α : Type} (treeFam castFam coord idx stage width l : Nat)
    (treeFields : Fields treeFam coord idx stage) (castFields : Fields castFam coord idx stage)
    (different : treeFam ≠ castFam) (widthSmall : width ≤ 16) (answers : castAnswers l ≤ 64)
    (delta bit0 : Block) (finish : _ → (Fin (2 ^ width) → Lanes l) → α) :
    Tagged (pairKeys treeFam castFam coord idx stage)
      (treeGarbleM (fun level slot => tagCode treeFam coord idx stage level slot 0) delta bit0 width >>= fun tree =>
        CRT.tableM (2 ^ width) (fun leaf => castM l (tree.1 leaf) fun part =>
          tagCode castFam coord idx stage 0 leaf.val part) >>= fun casts => pure (finish tree casts)) := by
  refine Tagged.bind' (treeGarbleM_tagged treeFam coord idx stage treeFields delta bit0 width widthSmall)
    (fun tree => Tagged.bind_pure (leafCasts_tagged castFam coord idx stage width l castFields widthSmall answers
      _) _) ?_ ?_ ?_
  · refine Set.disjoint_left.mpr fun k inTree inCasts => ?_
    simp only [treeKeys, castKeys, Set.mem_setOf_eq] at inTree inCasts
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [treeKeys, Set.mem_setOf_eq] at inS
      rw [inS.1]; exact ⟨treeFields.noPad, treeFields.noMask⟩
  · rintro k (inTree | inCasts)
    · simp only [treeKeys, pairKeys, Set.mem_setOf_eq] at inTree ⊢
      exact ⟨Or.inl inTree.1, inTree.2.1, inTree.2.2.1, inTree.2.2.2.1⟩
    · simp only [castKeys, pairKeys, Set.mem_setOf_eq] at inCasts ⊢
      exact ⟨Or.inr inCasts.1, inCasts.2.1, inCasts.2.2.1, inCasts.2.2.2.1⟩

/-- **The garbler's chunk** `c`. -/
theorem chunkGarbleM_tagged (T : CrtTable) (coord : Nat) (delta : Block) (zeroLabel : Nat → Block) (c : Nat)
    (coordLt : coord < 2) (cLt : c < 128) (widthSmall : T.chunkWidth c ≤ 16)
    (answers : castAnswers T.castWidth ≤ 64) :
    Tagged (pairKeys 0 1 coord c 0) (chunkGarbleM T coord delta zeroLabel c) :=
  treeCasts_tagged 0 1 coord c 0 (T.chunkWidth c) T.castWidth
    ⟨by norm_num, coordLt, cLt, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, coordLt, cLt, by norm_num, by norm_num, by norm_num⟩ (by norm_num) widthSmall answers _ _ _

/-- **The garbler of one fused extraction stage.** -/
theorem extStageGarbleM_tagged {rb : Nat} (coord idx stage w : Nat) (coordLt : coord < 2) (idxLt : idx < 128)
    (stageLt : stage < 4) (widthSmall : w ≤ 16) (answers : castAnswers rb ≤ 64) (delta : Block)
    (remainder : Lanes rb) :
    Tagged (pairKeys 2 3 coord idx stage)
      (extStageGarbleM w (fun level slot => tagCode 2 coord idx stage level slot 0)
        (fun leaf part => tagCode 3 coord idx stage 0 leaf part) delta remainder) :=
  treeCasts_tagged 2 3 coord idx stage w rb
    ⟨by norm_num, coordLt, idxLt, stageLt, by norm_num, by norm_num⟩
    ⟨by norm_num, coordLt, idxLt, stageLt, by norm_num, by norm_num⟩ (by norm_num) widthSmall answers _ _ _

/-! ### Sites of keys -/

theorem site_cases (k : TagKey) :
    (k.fam = 6 ∧ k.site = some (.pad k.coord k.idx k.slot)) ∨ (k.fam = 7 ∧ k.site = some (.mask k.stage k.slot)) ∨
      (k.fam ≠ 6 ∧ k.fam ≠ 7 ∧ k.site = none) := by
  by_cases six : k.fam = 6
  · exact Or.inl ⟨six, site_pad six⟩
  · by_cases seven : k.fam = 7
    · exact Or.inr (Or.inl ⟨seven, site_mask seven⟩)
    · exact Or.inr (Or.inr ⟨six, seven, site_none six seven⟩)

/-- Key sets without mask keys whose pad keys differ in a field (index or coordinate) share no site. -/
theorem siteDisjoint_of_padField {S S' : Set TagKey} (field : TagKey → Nat)
    (fieldPad : ∀ k k' : TagKey, k.fam = 6 → k'.fam = 6 → (Privacy.SiteId.pad k.coord k.idx k.slot =
      .pad k'.coord k'.idx k'.slot) → field k = field k')
    (noMask : ∀ k ∈ S, k.fam ≠ 7) (noMask' : ∀ k ∈ S', k.fam ≠ 7)
    (different : ∀ k ∈ S, ∀ k' ∈ S', field k ≠ field k') : SiteDisjoint S S' := by
  intro k inS k' inS' same
  rcases site_cases k with ⟨six, hk⟩ | ⟨seven, _⟩ | ⟨_, _, none⟩
  · rcases site_cases k' with ⟨six', hk'⟩ | ⟨seven', _⟩ | ⟨_, _, none'⟩
    · rw [hk, hk', Option.some.injEq] at same
      exact absurd (fieldPad k k' six six' same) (different k inS k' inS')
    · exact absurd seven' (noMask' k' inS')
    · rw [hk, none'] at same
      exact absurd same (by simp)
  · exact absurd ‹k.fam = 7› (noMask k inS)
  · exact none

theorem padField_idx : ∀ k k' : TagKey, k.fam = 6 → k'.fam = 6 → (Privacy.SiteId.pad k.coord k.idx k.slot =
    .pad k'.coord k'.idx k'.slot) → k.idx = k'.idx := by
  intro k k' _ _ same
  simp only [Privacy.SiteId.pad.injEq] at same
  exact same.2.1

theorem padField_coord : ∀ k k' : TagKey, k.fam = 6 → k'.fam = 6 → (Privacy.SiteId.pad k.coord k.idx k.slot =
    .pad k'.coord k'.idx k'.slot) → k.coord = k'.coord := by
  intro k k' _ _ same
  simp only [Privacy.SiteId.pad.injEq] at same
  exact same.1

/-! ### One modulus and one coordinate -/

/-- The fields of an odd row fit `tagCode`, and its casts fit 64 answers. -/
structure RowRanges (row : OddRow) : Prop where
  width0 : row.width0 ≤ 16
  width1 : row.width1 ≤ 16
  keep : row.keep ≤ 16
  ell : row.ell ≤ 16
  cast0 : castAnswers row.ell ≤ 64
  cast1 : castAnswers (row.ell - row.width0) ≤ 64

/-- **The ranges of a table** for `S` encodings: every tag field fits `tagCode`. -/
structure TableRanges (T : CrtTable) (S : Nat) : Prop where
  chunkCount : T.chunkCount ≤ 128
  chunkWidth : ∀ c, c < T.chunkCount → T.chunkWidth c ≤ 16
  castAnswers : castAnswers T.castWidth ≤ 64
  count : T.count ≤ 128
  modulus : ∀ i, T.modulus i ≤ 65536
  pads : ∀ i, T.padAnswers S i ≤ 64
  rows : ∀ i row, T.kind i = .odd row → RowRanges row

/-- The keys of an odd modulus's conversion. -/
def convKeys (coord idx : Nat) : Set TagKey :=
  {k | 2 ≤ k.fam ∧ k.fam ≤ 5 ∧ k.coord = coord ∧ k.idx = idx}

/-- **The garbler's conversion** of an odd modulus. -/
theorem conversionGarbleM_tagged (coord idx : Nat) (row : OddRow) (m : Nat) (coordLt : coord < 2)
    (idxLt : idx < 128) (ranges : RowRanges row) (mSmall : m ≤ 65536) (delta : Block) (word : Lanes row.ell) :
    Tagged (convKeys coord idx) (conversionGarbleM coord idx row m delta word) := by
  unfold conversionGarbleM
  have growFields : Fields 4 coord idx 0 := ⟨by norm_num, coordLt, idxLt, by norm_num, by norm_num, by norm_num⟩
  have ranges' := ranges
  obtain ⟨w0, w1, keep, ell, cast0, cast1⟩ := ranges'
  refine Tagged.bind' (extStageGarbleM_tagged coord idx 0 row.width0 coordLt idxLt (by norm_num) w0 cast0 delta
    word) (S' := pairKeys 2 3 coord idx 1 ∪ (growKeys 4 coord idx 0 row.width0 (row.keep - row.width0) ∪
      foldKeys coord idx row.keep (row.ell - row.keep) m)) (fun g0 => ?_) ?_ ?_ ?_
  · refine Tagged.bind' (extStageGarbleM_tagged coord idx 1 row.width1 coordLt idxLt (by norm_num) w1 cast1 delta
      g0.next) (S' := growKeys 4 coord idx 0 row.width0 (row.keep - row.width0) ∪
        foldKeys coord idx row.keep (row.ell - row.keep) m) (fun g1 => ?_) ?_ ?_ le_rfl
    · refine Tagged.bind' (growGarbleM_tagged 4 coord idx 0 row.width0 growFields _ (row.keep - row.width0)
        (by omega)) (fun grown => Tagged.bind_pure (foldsGarbleM_tagged coord idx m coordLt idxLt mSmall _
          (row.ell - row.keep) row.keep _ (by omega)) _) ?_ ?_ le_rfl
      · refine Set.disjoint_left.mpr fun k inG inF => ?_
        simp only [growKeys, foldKeys, Set.mem_setOf_eq] at inG inF
        omega
      · exact siteDisjoint_of_fam fun k inS => by
          simp only [growKeys, Set.mem_setOf_eq] at inS
          rw [inS.1]; exact ⟨by norm_num, by norm_num⟩
    · refine Set.disjoint_left.mpr fun k inA inB => ?_
      simp only [pairKeys, growKeys, foldKeys, Set.mem_union, Set.mem_setOf_eq] at inA inB
      omega
    · exact siteDisjoint_of_fam fun k inS => by
        simp only [pairKeys, Set.mem_setOf_eq] at inS
        omega
  · refine Set.disjoint_left.mpr fun k inA inB => ?_
    simp only [pairKeys, growKeys, foldKeys, Set.mem_union, Set.mem_setOf_eq] at inA inB
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [pairKeys, Set.mem_setOf_eq] at inS
      omega
  · intro k inside
    simp only [pairKeys, growKeys, foldKeys, convKeys, Set.mem_union, Set.mem_setOf_eq] at inside ⊢
    omega

/-- `materializeM` asks nothing. -/
theorem materializeM_tagged {width : Nat} (lanes : Lanes width) : Tagged ∅ (materializeM lanes) := by
  unfold materializeM storeM
  refine (Tagged.tableM (S := fun _ => ∅) _ (fun _ => Tagged.pure _ _)
    fun _ _ _ _ _ => ⟨Set.disjoint_empty _, fun _ inside => absurd inside id⟩).mono ?_
  rintro k ⟨_, _, inside⟩
  exact inside

/-- The keys of one modulus: its conversion (families 2 to 5) and its body (family 6). -/
def modKeys (coord idx : Nat) : Set TagKey :=
  {k | 2 ≤ k.fam ∧ k.fam ≤ 6 ∧ k.coord = coord ∧ k.idx = idx}

/-- **The garbler of one modulus.** -/
theorem modGarbleM_tagged (T : CrtTable) (S coord : Nat) (ranges : TableRanges T S) (coordLt : coord < 2)
    (delta : Block) (chunks : Nat → ChunkGarbled T.castWidth) (i : Fin T.count) :
    Tagged (modKeys coord i.val) (modGarbleM T S coord delta chunks i) := by
  have idxLt : i.val < 128 := lt_of_lt_of_le i.isLt ranges.count
  have bodySub : bodyKeys coord i.val (T.modulus i) (T.padAnswers S i) ⊆ modKeys coord i.val := by
    intro k inside
    simp only [bodyKeys, modKeys, Set.mem_setOf_eq] at inside ⊢
    omega
  unfold modGarbleM
  split
  · exact (Tagged.bind_pure (bodyGarbleM_tagged coord i.val _ S _ coordLt idxLt (ranges.modulus i) (ranges.pads i)
      _) _).mono bodySub
  · rename_i row kind
    refine Tagged.bind' (materializeM_tagged _) (S' := modKeys coord i.val) (fun word => ?_)
      (Set.empty_disjoint _) (fun _ inside => absurd inside id) (by simp)
    refine Tagged.bind' (conversionGarbleM_tagged coord i.val row _ coordLt idxLt (ranges.rows i row kind)
      (ranges.modulus i) delta word) (fun conversion => Tagged.bind_pure (bodyGarbleM_tagged coord i.val _ S _
        coordLt idxLt (ranges.modulus i) (ranges.pads i) _) _) ?_ ?_ ?_
    · refine Set.disjoint_left.mpr fun k inC inB => ?_
      simp only [convKeys, bodyKeys, Set.mem_setOf_eq] at inC inB
      omega
    · exact siteDisjoint_of_fam fun k inS => by
        simp only [convKeys, Set.mem_setOf_eq] at inS
        omega
    · rintro k (inC | inB)
      · simp only [convKeys, modKeys, Set.mem_setOf_eq] at inC ⊢
        omega
      · exact bodySub inB

/-- The keys of one coordinate's conversion layer and body (families 0 to 6). -/
def coordKeys (coord : Nat) : Set TagKey := {k | k.fam ≤ 6 ∧ k.coord = coord}

/-- **The garbler of one coordinate.** -/
theorem coordGarbleM_tagged (T : CrtTable) (S coord : Nat) (ranges : TableRanges T S) (coordLt : coord < 2)
    (delta : Block) (zeroLabel : Nat → Block) :
    Tagged (coordKeys coord) (coordGarbleM T S coord delta zeroLabel) := by
  unfold coordGarbleM
  refine Tagged.bind' (Tagged.tableM (S := fun c => pairKeys 0 1 coord c 0) T.chunkCount
    (fun c => chunkGarbleM_tagged T coord delta zeroLabel c.val coordLt
      (lt_of_lt_of_le c.isLt ranges.chunkCount) (ranges.chunkWidth c.val c.isLt) ranges.castAnswers)
    fun i j _ _ different => ⟨?_, ?_⟩) (S' := {k | ∃ i < T.count, k ∈ modKeys coord i}) (fun chunkTable => ?_)
      ?_ ?_ ?_
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [pairKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [pairKeys, Set.mem_setOf_eq] at inS
      omega
  · exact Tagged.bind_empty (Tagged.tableM (S := fun i => modKeys coord i) T.count
      (fun i => modGarbleM_tagged T S coord ranges coordLt delta _ i)
      fun i j _ _ different => ⟨Set.disjoint_left.mpr fun k inI inJ => by
          simp only [modKeys, Set.mem_setOf_eq] at inI inJ
          omega,
        siteDisjoint_of_padField TagKey.idx padField_idx
          (fun k inS => by simp only [modKeys, Set.mem_setOf_eq] at inS; omega)
          (fun k inS => by simp only [modKeys, Set.mem_setOf_eq] at inS; omega)
          fun k inS k' inS' => by
            simp only [modKeys, Set.mem_setOf_eq] at inS inS'
            omega⟩) fun _ => Tagged.pure _ _
  · refine Set.disjoint_left.mpr fun k inC inM => ?_
    obtain ⟨c, _, inC⟩ := inC
    obtain ⟨i, _, inM⟩ := inM
    simp only [pairKeys, modKeys, Set.mem_setOf_eq] at inC inM
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      obtain ⟨c, _, inS⟩ := inS
      simp only [pairKeys, Set.mem_setOf_eq] at inS
      omega
  · rintro k (⟨c, _, inC⟩ | ⟨i, _, inM⟩)
    · simp only [pairKeys, coordKeys, Set.mem_setOf_eq] at inC ⊢
      omega
    · simp only [modKeys, coordKeys, Set.mem_setOf_eq] at inM ⊢
      omega

end Kriterion.CRT.Paths
