/-
**Tag paths of the CRT layer's blocks**: the trees, growths, casts, folds and pad vectors of the
conversion layer and the body, garbler and evaluator alike, are `Tagged` by the keys of their tag family
(`Paths/Tags.lean`).

Each lemma is stated for the block's tag function written out as `tagCode` with the block's fixed fields, which is
what `Construction/CRT/{Chunk, Coord, Body}.lean` pass (`chunkTreeTag`, `extTreeTag`, `growTag`, `foldTag`,
`bodyTag`, `chunkCastTag`, `extCastTag` unfold to these by definition).
-/

import Proof.Privacy.CRT.Paths.Tags

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC

/-! ### Keys without a site -/

theorem site_none {k : TagKey} (not6 : k.fam ≠ 6) (not7 : k.fam ≠ 7) : k.site = none := by
  unfold TagKey.site
  split <;> simp_all

/-- Key sets whose families are not 6 or 7 have no site. -/
theorem siteDisjoint_of_fam {S S' : Set TagKey} (fams : ∀ k ∈ S, k.fam ≠ 6 ∧ k.fam ≠ 7) :
    SiteDisjoint S S' :=
  siteDisjoint_of_none fun k inS => site_none (fams k inS).1 (fams k inS).2

theorem singleton_disjoint {k k' : TagKey} (different : k ≠ k') : Disjoint ({k} : Set TagKey) {k'} :=
  Set.disjoint_singleton.mpr different

/-! ### Tree levels -/

/-- The keys of a tree's hashed levels `1 .. levels − 1`. -/
def treeKeys (fam coord idx stage levels : Nat) : Set TagKey :=
  {k | k.fam = fam ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.part = 0 ∧ 1 ≤ k.level ∧
    k.level < levels ∧ k.slot < 2 ^ k.level}

/-- The keys of one level `n` of a tree. -/
def levelKeys (fam coord idx stage n width : Nat) : Set TagKey :=
  {k | k.fam = fam ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.part = 0 ∧ k.level = n ∧ k.slot < width}

/-- The fixed fields of a block are in range. -/
structure Fields (fam coord idx stage : Nat) : Prop where
  famLt : fam < 16
  coordLt : coord < 2
  idxLt : idx < 128
  stageLt : stage < 4
  noPad : fam ≠ 6
  noMask : fam ≠ 7

theorem pow_lt_65536 {n : Nat} (small : n < 16) : 2 ^ n < 65536 :=
  lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) small) (by norm_num)

/-- **One level of the garbler's tree**: every slot hashed once. -/
theorem garbleStepM_tagged (fam coord idx stage n : Nat) (fields : Fields fam coord idx stage)
    (levelSmall : n < 16) (parent : Fin (2 ^ n) → Label) :
    Tagged (levelKeys fam coord idx stage n (2 ^ n))
      (garbleStepM n (fun slot => tagCode fam coord idx stage n slot 0) parent) := by
  unfold garbleStepM
  refine Tagged.bind_pure ((Tagged.tableM (S := fun slot => {⟨fam, coord, idx, stage, n, slot, 0⟩}) (2 ^ n)
    (fun slot => Tagged.hLabelM _ _ _ _ rfl rfl ⟨fields.famLt, fields.coordLt, fields.idxLt, fields.stageLt, levelSmall,
      lt_trans slot.isLt (pow_lt_65536 levelSmall), by norm_num⟩)
    fun i j _ _ different => ⟨singleton_disjoint fun same => different (by cases same; rfl),
      siteDisjoint_of_fam fun k inS => by
        rw [Set.mem_singleton_iff.mp inS]; exact ⟨fields.noPad, fields.noMask⟩⟩).mono ?_) _
  rintro k ⟨slot, small, inS⟩
  rw [Set.mem_singleton_iff.mp inS]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, small⟩

/-- **The garbler's tree** over `levels ≤ 16` bits. -/
theorem treeGarbleM_tagged (fam coord idx stage : Nat) (fields : Fields fam coord idx stage) (delta bit0 : Label) :
    ∀ levels, levels ≤ 16 →
      Tagged (treeKeys fam coord idx stage levels)
        (treeGarbleM (fun level slot => tagCode fam coord idx stage level slot 0) delta bit0 levels)
  | 0, _ => Tagged.pure _ _
  | n + 1, small => by
      simp only [treeGarbleM]
      refine Tagged.bind' (treeGarbleM_tagged fam coord idx stage fields delta bit0 n (by omega))
        (S' := {k | k ∈ levelKeys fam coord idx stage n (2 ^ n) ∧ 1 ≤ k.level}) (fun previous => ?_) ?_ ?_ ?_
      · split
        · exact Tagged.pure _ _
        · rename_i nonzero
          refine (Tagged.bind_pure (garbleStepM_tagged fam coord idx stage n fields (by omega) _) _).mono ?_
          intro k inLevel
          refine ⟨inLevel, ?_⟩
          simp only [levelKeys, Set.mem_setOf_eq] at inLevel
          omega
      · refine Set.disjoint_left.mpr fun k inTree inLevel => ?_
        simp only [treeKeys, levelKeys, Set.mem_setOf_eq] at inTree inLevel
        omega
      · exact siteDisjoint_of_fam fun k inS => by
          simp only [treeKeys, Set.mem_setOf_eq] at inS
          rw [inS.1]; exact ⟨fields.noPad, fields.noMask⟩
      · rintro k (inTree | inLevel)
        · simp only [treeKeys, Set.mem_setOf_eq] at inTree ⊢
          omega
        · simp only [treeKeys, levelKeys, Set.mem_setOf_eq] at inLevel ⊢
          obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := inLevel
          exact ⟨h1, h2, h3, h4, h5, h8, by omega, by rw [h6]; exact h7⟩

/-! ### One level of hashes, growth -/

/-- **A level of `width` one-block hashes at level field `n`** (tree levels, folds). -/
theorem levelHashes_tagged (fam coord idx stage n width : Nat) (fields : Fields fam coord idx stage)
    (levelSmall : n < 16) (widthSmall : width ≤ 65536) (label : Fin width → Label) :
    Tagged (levelKeys fam coord idx stage n width)
      (CRT.tableM width fun slot => hLabelM (label slot) (tagCode fam coord idx stage n slot.val 0)) := by
  have each : ∀ slot : Fin width, Tagged ({⟨fam, coord, idx, stage, n, slot.val, 0⟩} : Set TagKey)
      (hLabelM (label slot) (tagCode fam coord idx stage n slot.val 0)) := fun slot =>
    Tagged.hLabelM _ (label slot) _ ⟨fam, coord, idx, stage, n, slot.val, 0⟩ rfl rfl
      ⟨fields.famLt, fields.coordLt, fields.idxLt, fields.stageLt, levelSmall,
        lt_of_lt_of_le slot.isLt widthSmall, by norm_num⟩
  refine (Tagged.tableM (S := fun slot => {⟨fam, coord, idx, stage, n, slot, 0⟩}) width each
    fun i j _ _ different => ⟨singleton_disjoint fun same => different (by cases same; rfl),
      siteDisjoint_of_fam fun k inS => by
        rw [Set.mem_singleton_iff.mp inS]; exact ⟨fields.noPad, fields.noMask⟩⟩).mono ?_
  rintro k ⟨slot, small, inS⟩
  rw [Set.mem_singleton_iff.mp inS]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, small⟩

/-- The keys of a growth by `count` levels from level `start`. -/
def growKeys (fam coord idx stage start count : Nat) : Set TagKey :=
  {k | k.fam = fam ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.part = 0 ∧ start ≤ k.level ∧
    k.level < start + count ∧ k.slot < 2 ^ k.level}

/-- **The garbler's growth** of a one-hot from level `start` by `count` levels (`start + count ≤ 16`). -/
theorem growGarbleM_tagged (fam coord idx stage start : Nat) (fields : Fields fam coord idx stage)
    (labels : Fin (2 ^ start) → Label) :
    ∀ count, start + count ≤ 16 →
      Tagged (growKeys fam coord idx stage start count)
        (growGarbleM (fun level slot => tagCode fam coord idx stage level slot 0) start labels count)
  | 0, _ => Tagged.pure _ _
  | k + 1, small => by
      simp only [growGarbleM]
      refine Tagged.bind' (growGarbleM_tagged fam coord idx stage start fields labels k (by omega))
        (S' := levelKeys fam coord idx stage (start + k) (2 ^ (start + k))) (fun previous => ?_) ?_ ?_ ?_
      · exact Tagged.bind_pure (garbleStepM_tagged fam coord idx stage (start + k) fields (by omega) _) _
      · refine Set.disjoint_left.mpr fun key inGrow inLevel => ?_
        simp only [growKeys, levelKeys, Set.mem_setOf_eq] at inGrow inLevel
        omega
      · exact siteDisjoint_of_fam fun key inS => by
          simp only [growKeys, Set.mem_setOf_eq] at inS
          rw [inS.1]; exact ⟨fields.noPad, fields.noMask⟩
      · rintro key (inGrow | inLevel)
        · simp only [growKeys, Set.mem_setOf_eq] at inGrow ⊢
          omega
        · simp only [growKeys, levelKeys, Set.mem_setOf_eq] at inLevel ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := inLevel
          exact ⟨h1, h2, h3, h4, h5, by omega, by omega, by rw [h6]; exact h7⟩

/-! ### Casts -/

/-- The keys of one leaf's cast, `count` answers. -/
def leafKeys (fam coord idx stage leaf count : Nat) : Set TagKey :=
  {k | k.fam = fam ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.level = 0 ∧ k.slot = leaf ∧
    k.part < count}

/-- The keys of the casts of the leaves below `leaves`, `count` answers each. -/
def castKeys (fam coord idx stage leaves count : Nat) : Set TagKey :=
  {k | k.fam = fam ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.level = 0 ∧ k.slot < leaves ∧
    k.part < count}

/-- **One cast** of leaf `leaf`: its `castAnswers l` answers at one label. -/
theorem castM_tagged (fam coord idx stage leaf l : Nat) (fields : Fields fam coord idx stage)
    (leafSmall : leaf < 65536) (answers : castAnswers l ≤ 64) (label : Label) :
    Tagged (leafKeys fam coord idx stage leaf (castAnswers l))
      (castM l label fun part => tagCode fam coord idx stage 0 leaf part) := by
  unfold castM
  refine Tagged.bind_pure ((Tagged.hlongM (embed label) _ (castAnswers l)
    (fun part => ⟨fam, coord, idx, stage, 0, leaf, part⟩) (fun _ _ => rfl)
    (fun part small => ⟨fields.famLt, fields.coordLt, fields.idxLt, fields.stageLt, by norm_num, leafSmall,
      show part < 64 by omega⟩)
    fun i j _ _ same => by cases same; rfl).mono ?_) _
  rintro k ⟨part, small, same⟩
  rw [same]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, small⟩

theorem two_pow_le_65536 {width : Nat} (widthSmall : width ≤ 16) : 2 ^ width ≤ 65536 :=
  calc 2 ^ width ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) widthSmall
    _ = 65536 := by norm_num

/-- **The casts of every leaf** below `2 ^ width`. -/
theorem leafCasts_tagged (fam coord idx stage width l : Nat) (fields : Fields fam coord idx stage)
    (widthSmall : width ≤ 16) (answers : castAnswers l ≤ 64) (label : Fin (2 ^ width) → Label) :
    Tagged (castKeys fam coord idx stage (2 ^ width) (castAnswers l))
      (CRT.tableM (2 ^ width) fun leaf => castM l (label leaf) fun part =>
        tagCode fam coord idx stage 0 leaf.val part) := by
  have leaves := two_pow_le_65536 widthSmall
  refine (Tagged.tableM (S := fun leaf => leafKeys fam coord idx stage leaf (castAnswers l)) (2 ^ width)
    (fun leaf => castM_tagged fam coord idx stage leaf.val l fields (by omega) answers (label leaf))
    fun i j _ _ different => ⟨?_, ?_⟩).mono ?_
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [leafKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [leafKeys, Set.mem_setOf_eq] at inS
      rw [inS.1]; exact ⟨fields.noPad, fields.noMask⟩
  · rintro k ⟨leaf, small, inS⟩
    simp only [leafKeys, castKeys, Set.mem_setOf_eq] at inS ⊢
    omega

end Kriterion.CRT.Paths
