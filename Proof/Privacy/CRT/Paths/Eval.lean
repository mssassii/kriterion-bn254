/-
**Tag paths of the evaluator's blocks**: the evaluator asks the same positions as the garbler but
skips the hot ones; its trees, growths, chunk casts, folds and pads are `Tagged` by the garbler's key sets
(`Paths/Blocks.lean`, `Paths/Garbler.lean`).
-/

import Proof.Privacy.CRT.Paths.Garbler

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC

/-! ### Levels with slots skipped -/

/-- **A level of one-block hashes at slots `f t`, some slots skipped** (evaluator levels; `f` injective). -/
theorem levelHashesSkip_tagged (fam coord idx stage n width : Nat) (fields : Fields fam coord idx stage)
    (levelSmall : n < 16) (f : Nat → Nat) (fSmall : ∀ t, t < width → f t < 65536)
    (fInjective : ∀ s t, s < width → t < width → f s = f t → s = t) (skip : Fin width → Prop)
    [DecidablePred skip] (label : Fin width → Block) :
    Tagged {k | k.fam = fam ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.part = 0 ∧ k.level = n ∧
        ∃ t < width, k.slot = f t}
      (CRT.tableM width fun t => if skip t then pure 0 else h128M (label t) (tagCode fam coord idx stage n (f t.val) 0)) := by
  have each : ∀ t : Fin width, Tagged ({⟨fam, coord, idx, stage, n, f t.val, 0⟩} : Set TagKey)
      (if skip t then pure 0 else h128M (label t) (tagCode fam coord idx stage n (f t.val) 0)) := fun t =>
    Tagged.ite (fun _ => Tagged.pure _ _) fun _ =>
      Tagged.h128M _ (label t) _ ⟨fam, coord, idx, stage, n, f t.val, 0⟩ rfl rfl
        ⟨fields.famLt, fields.coordLt, fields.idxLt, fields.stageLt, levelSmall, fSmall t.val t.isLt, by norm_num⟩
  refine (Tagged.tableM (S := fun t => {⟨fam, coord, idx, stage, n, f t, 0⟩}) width each
    fun i j hi hj different => ⟨singleton_disjoint fun same => different (fInjective i j hi hj
        (congrArg TagKey.slot same)),
      siteDisjoint_of_fam fun k inS => by
        rw [Set.mem_singleton_iff.mp inS]; exact ⟨fields.noPad, fields.noMask⟩⟩).mono ?_
  rintro k ⟨t, small, inS⟩
  rw [Set.mem_singleton_iff.mp inS]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, t, small, rfl⟩

/-- **One level of the evaluator's tree**: every slot but the active one. -/
theorem evalStepM_tagged (fam coord idx stage n : Nat) (fields : Fields fam coord idx stage)
    (levelSmall : n < 16) (active : Fin (2 ^ n)) (bitLabel join : Block) (parent : Fin (2 ^ n) → Block) :
    Tagged (levelKeys fam coord idx stage n (2 ^ n))
      (evalStepM n (fun slot => tagCode fam coord idx stage n slot 0) active bitLabel join parent) := by
  unfold evalStepM
  refine Tagged.bind_pure ((levelHashesSkip_tagged fam coord idx stage n (2 ^ n) fields levelSmall id
    (fun t small => lt_trans small (pow_lt_65536 levelSmall)) (fun s t _ _ same => same) (fun slot => slot = active)
    parent).mono ?_) _
  rintro k ⟨h1, h2, h3, h4, h5, h6, t, small, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6, by rw [h7]; exact small⟩

/-- **The evaluator's tree** over `levels ≤ 16` bits (known bits). -/
theorem treeEvalM_tagged (fam coord idx stage : Nat) (fields : Fields fam coord idx stage) (value : Nat)
    (bitLabel join : Nat → Block) :
    ∀ levels, levels ≤ 16 →
      Tagged (treeKeys fam coord idx stage levels)
        (treeEvalM (fun level slot => tagCode fam coord idx stage level slot 0) value bitLabel join levels)
  | 0, _ => Tagged.pure _ _
  | n + 1, small => by
      simp only [treeEvalM]
      refine Tagged.bind' (treeEvalM_tagged fam coord idx stage fields value bitLabel join n (by omega))
        (S' := {k | k ∈ levelKeys fam coord idx stage n (2 ^ n) ∧ 1 ≤ k.level}) (fun previous => ?_) ?_ ?_ ?_
      · split
        · exact Tagged.pure _ _
        · refine (evalStepM_tagged fam coord idx stage n fields (by omega) _ _ _ _).mono ?_
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

/-- **The evaluator's growth** from level `start` by `count` levels. -/
theorem growEvalM_tagged (fam coord idx stage : Nat) (fields : Fields fam coord idx stage) (value : Nat)
    (bitLabel join : Nat → Block) (start : Nat) (labels : Fin (2 ^ start) → Block) :
    ∀ count, start + count ≤ 16 →
      Tagged (growKeys fam coord idx stage start count)
        (growEvalM (fun level slot => tagCode fam coord idx stage level slot 0) value bitLabel join start labels
          count)
  | 0, _ => Tagged.pure _ _
  | k + 1, small => by
      simp only [growEvalM]
      refine Tagged.bind' (growEvalM_tagged fam coord idx stage fields value bitLabel join start labels k (by omega))
        (S' := levelKeys fam coord idx stage (start + k) (2 ^ (start + k)))
        (fun previous => evalStepM_tagged fam coord idx stage (start + k) fields (by omega) _ _ _ _) ?_ ?_ ?_
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

/-! ### Casts with one leaf skipped -/

/-- **The casts of every leaf but one** below `2 ^ width`. -/
theorem leafCastsSkip_tagged (fam coord idx stage width l : Nat) (fields : Fields fam coord idx stage)
    (widthSmall : width ≤ 16) (answers : castAnswers l ≤ 64) (hot : Nat) (label : Fin (2 ^ width) → Block) :
    Tagged (castKeys fam coord idx stage (2 ^ width) (castAnswers l))
      (CRT.tableM (2 ^ width) fun leaf => if leaf.val = hot then pure 0 else castM l (label leaf) fun part =>
        tagCode fam coord idx stage 0 leaf.val part) := by
  have leaves := two_pow_le_65536 widthSmall
  refine (Tagged.tableM (S := fun leaf => leafKeys fam coord idx stage leaf (castAnswers l)) (2 ^ width)
    (fun leaf => Tagged.ite (fun _ => Tagged.pure _ _) fun _ =>
      castM_tagged fam coord idx stage leaf.val l fields (by omega) answers (label leaf))
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

/-- **The evaluator's chunk** `c`. -/
theorem chunkEvalM_tagged (T : CrtTable) (coord : Nat) (labels : Nat → Block) (v : Nat) (joins : Nat → Block)
    (pin : Lanes T.castWidth) (c : Nat) (coordLt : coord < 2) (cLt : c < 128) (widthSmall : T.chunkWidth c ≤ 16)
    (answers : castAnswers T.castWidth ≤ 64) :
    Tagged (pairKeys 0 1 coord c 0) (chunkEvalM T coord labels v joins pin c) := by
  unfold chunkEvalM
  have treeFields : Fields 0 coord c 0 := ⟨by norm_num, coordLt, cLt, by norm_num, by norm_num, by norm_num⟩
  have castFields : Fields 1 coord c 0 := ⟨by norm_num, coordLt, cLt, by norm_num, by norm_num, by norm_num⟩
  refine Tagged.bind' (treeEvalM_tagged 0 coord c 0 treeFields _ _ _ (T.chunkWidth c) widthSmall)
    (fun tree => Tagged.bind_empty (leafCastsSkip_tagged 1 coord c 0 (T.chunkWidth c) T.castWidth castFields
      widthSmall answers _ _) fun _ => Tagged.pure _ _) ?_ ?_ ?_
  · refine Set.disjoint_left.mpr fun k inTree inCasts => ?_
    simp only [treeKeys, castKeys, Set.mem_setOf_eq] at inTree inCasts
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [treeKeys, Set.mem_setOf_eq] at inS
      rw [inS.1]; exact ⟨by norm_num, by norm_num⟩
  · rintro k (inTree | inCasts)
    · simp only [treeKeys, pairKeys, Set.mem_setOf_eq] at inTree ⊢
      exact ⟨Or.inl inTree.1, inTree.2.1, inTree.2.2.1, inTree.2.2.2.1⟩
    · simp only [castKeys, pairKeys, Set.mem_setOf_eq] at inCasts ⊢
      exact ⟨Or.inr inCasts.1, inCasts.2.1, inCasts.2.2.1, inCasts.2.2.2.1⟩

/-! ### Folds and the body with the hot residue skipped -/

/-- **The evaluator's folds.** -/
theorem foldsEvalM_tagged (coord idx m : Nat) (coordLt : coord < 2) (idxLt : idx < 128) (mSmall : m ≤ 65536)
    (value : Nat) (bitLabel join : Nat → Block) :
    ∀ (count start hot : Nat) (labels : Fin m → Block), start + count ≤ 16 →
      Tagged (foldKeys coord idx start count m)
        (foldsEvalM m (fun position residue => tagCode 5 coord idx 0 position residue 0) value bitLabel join count
          start hot labels)
  | 0, _, _, _, _ => Tagged.pure _ _
  | count + 1, position, hot, labels, small => by
      simp only [foldsEvalM, foldEvalM]
      have fold := levelHashesSkip_tagged 5 coord idx 0 position m (fields_fold coordLt idxLt) (by omega) id
        (fun t small => lt_of_lt_of_le small mSmall) (fun s t _ _ same => same) (fun residue => residue.val = hot)
        labels
      refine Tagged.bind' (Tagged.bind_empty fold fun _ => Tagged.pure _ _)
        (S' := foldKeys coord idx (position + 1) count m)
        (fun step => foldsEvalM_tagged coord idx m coordLt idxLt mSmall value bitLabel join count (position + 1) _ _
          (by omega)) ?_ ?_ ?_
      · refine Set.disjoint_left.mpr fun k inFold inRest => ?_
        simp only [foldKeys, Set.mem_setOf_eq] at inFold inRest
        omega
      · exact siteDisjoint_of_fam fun k inS => by
          simp only [Set.mem_setOf_eq] at inS
          rw [inS.1]; exact ⟨by norm_num, by norm_num⟩
      · rintro k (inFold | inRest)
        · simp only [foldKeys, Set.mem_setOf_eq] at inFold ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, t, tSmall, h7⟩ := inFold
          refine ⟨h1, h2, h3, h4, h5, by omega, by omega, ?_⟩
          rw [h7]; exact tSmall
        · simp only [foldKeys, Set.mem_setOf_eq] at inRest ⊢
          omega

/-- **The evaluator's body** of one modulus: every residue's pad vector but the hot one. -/
theorem bodyEvalM_tagged (coord idx m S q : Nat) (coordLt : coord < 2) (idxLt : idx < 128)
    (mSmall : m ≤ 65536) (qSmall : q ≤ 64) (final : Fin m → Block) (hot : Nat) (joins : Fin S → Nat) :
    Tagged (bodyKeys coord idx m q) (bodyEvalM m S q coord idx final hot joins) := by
  unfold bodyEvalM
  refine Tagged.bind_empty ((Tagged.tableM (S := fun residue => padKeys coord idx residue q) m
    (fun residue => Tagged.ite (fun _ => Tagged.pure _ _) fun _ =>
      padVectorM_tagged coord idx residue.val m S q coordLt idxLt (by omega) qSmall (final residue))
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

end Kriterion.CRT.Paths
