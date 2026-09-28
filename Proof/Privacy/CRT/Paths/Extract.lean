/-
**The round-ordered extraction evaluator is `Tagged`**: `extStageEvalM` expands, round by round, the
closed sibling of the active path (`expandM`, `subtreeM`); the expansion of round `j` covers the nodes whose slot is
`slotOf value j` modulo `2 ^ (j + 1)`, and the rounds' slot classes are disjoint, so every tree node and every leaf
cast is asked at most once.
-/

import Proof.Privacy.CRT.Paths.Eval

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC

/-! ### Slot arithmetic -/

/-- The slot of the closed child expanded at round `n`: the prefix of the value with bit `n` flipped. -/
def slotOf (value n : Nat) : Nat := if value.testBit n then value % 2 ^ n else value % 2 ^ n + 2 ^ n

theorem mod_two_pow_succ (value n : Nat) :
    value % 2 ^ (n + 1) = value % 2 ^ n + 2 ^ n * (value / 2 ^ n % 2) := Nat.mod_pow_succ

theorem slotOf_lt (value n : Nat) : slotOf value n < 2 ^ (n + 1) := by
  have below := Nat.mod_lt value (Nat.two_pow_pos n)
  have power : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
  unfold slotOf
  split <;> omega

theorem slotOf_ne (value n : Nat) : slotOf value n ≠ value % 2 ^ (n + 1) := by
  rw [mod_two_pow_succ]
  have positive := Nat.two_pow_pos n
  unfold slotOf
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ n) with zero | one
  · rw [zero]
    simp
  · rw [one]
    simp

/-- A later round's slot has the value's prefix below `2 ^ (n + 1)`. -/
theorem slotOf_mod {value n j : Nat} (later : n < j) : slotOf value j % 2 ^ (n + 1) = value % 2 ^ (n + 1) := by
  have divides : 2 ^ (n + 1) ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨c, hc⟩ := divides
  unfold slotOf
  split
  · exact Nat.mod_mod_of_dvd value ⟨c, hc⟩
  · rw [hc, Nat.add_mul_mod_self_left, ← hc]
    exact Nat.mod_mod_of_dvd value ⟨c, hc⟩

theorem slotOf_zero (value : Nat) : (value % 2) ^^^ 1 = slotOf value 0 := by
  unfold slotOf
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [pow_zero, Nat.div_one, Nat.mod_one, Nat.zero_add]
  rcases Nat.mod_two_eq_zero_or_one value with zero | one
  · rw [zero]; rfl
  · rw [one]; rfl

/-- The slots of a subtree below `(start, slot)`. -/
theorem subtreeSlot_lt {start slot d t : Nat} (slotLt : slot < 2 ^ start) (tLt : t < 2 ^ d) :
    slot + 2 ^ start * t < 2 ^ (start + d) := by
  rw [pow_add]
  calc slot + 2 ^ start * t < 2 ^ start + 2 ^ start * t := by omega
    _ = 2 ^ start * (t + 1) := by ring
    _ ≤ 2 ^ start * 2 ^ d := Nat.mul_le_mul_left _ (by omega)

theorem subtreeSlot_mod {start slot t : Nat} (slotLt : slot < 2 ^ start) :
    (slot + 2 ^ start * t) % 2 ^ start = slot := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt slotLt]

theorem subtreeSlot_injective {start slot s t : Nat} (same : slot + 2 ^ start * s = slot + 2 ^ start * t) :
    s = t :=
  Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos start) (by omega)

/-! ### Subtrees and expansions -/

/-- **A level of one-block hashes at slots `f t`** (no slot skipped; `f` injective). -/
theorem levelHashesF_tagged (fam coord idx stage n width : Nat) (fields : Fields fam coord idx stage)
    (levelSmall : n < 16) (f : Nat → Nat) (fSmall : ∀ t, t < width → f t < 65536)
    (fInjective : ∀ s t, s < width → t < width → f s = f t → s = t) (label : Fin width → Label) :
    Tagged {k | k.fam = fam ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.part = 0 ∧ k.level = n ∧
        ∃ t < width, k.slot = f t}
      (CRT.tableM width fun t => hLabelM (label t) (tagCode fam coord idx stage n (f t.val) 0)) := by
  have each : ∀ t : Fin width, Tagged ({⟨fam, coord, idx, stage, n, f t.val, 0⟩} : Set TagKey)
      (hLabelM (label t) (tagCode fam coord idx stage n (f t.val) 0)) := fun t =>
    Tagged.hLabelM _ (label t) _ ⟨fam, coord, idx, stage, n, f t.val, 0⟩ rfl rfl
      ⟨fields.famLt, fields.coordLt, fields.idxLt, fields.stageLt, levelSmall, fSmall t.val t.isLt, by norm_num⟩
  refine (Tagged.tableM (S := fun t => {⟨fam, coord, idx, stage, n, f t, 0⟩}) width each
    fun i j hi hj different => ⟨singleton_disjoint fun same => different (fInjective i j hi hj
        (congrArg TagKey.slot same)),
      siteDisjoint_of_fam fun k inS => by
        rw [Set.mem_singleton_iff.mp inS]; exact ⟨fields.noPad, fields.noMask⟩⟩).mono ?_
  rintro k ⟨t, small, inS⟩
  rw [Set.mem_singleton_iff.mp inS]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, t, small, rfl⟩

/-- The keys of the subtree below the node `(start, slot)`, relative depths below `depth`. -/
def subtreeKeys (coord idx stage start slot depth : Nat) : Set TagKey :=
  {k | k.fam = 2 ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.part = 0 ∧ start ≤ k.level ∧
    k.level < start + depth ∧ ∃ t < 2 ^ (k.level - start), k.slot = slot + 2 ^ start * t}

theorem fields_ext {coord idx stage : Nat} (coordLt : coord < 2) (idxLt : idx < 128) (stageLt : stage < 4) :
    Fields 2 coord idx stage ∧ Fields 3 coord idx stage :=
  ⟨⟨by norm_num, coordLt, idxLt, stageLt, by norm_num, by norm_num⟩,
    ⟨by norm_num, coordLt, idxLt, stageLt, by norm_num, by norm_num⟩⟩

/-- **The subtree below a closed node** (`subtreeM`). -/
theorem subtreeM_tagged (coord idx stage start slot : Nat) (coordLt : coord < 2) (idxLt : idx < 128)
    (stageLt : stage < 4) (slotLt : slot < 2 ^ start) (label : Label) :
    ∀ depth, start + depth ≤ 16 →
      Tagged (subtreeKeys coord idx stage start slot depth)
        (subtreeM (fun level slot => tagCode 2 coord idx stage level slot 0) start slot label depth)
  | 0, _ => Tagged.pure _ _
  | d + 1, small => by
      simp only [subtreeM, garbleStepM]
      have level := levelHashesF_tagged 2 coord idx stage (start + d) (2 ^ d)
        (fields_ext coordLt idxLt stageLt).1 (by omega) (fun t => slot + 2 ^ start * t)
        (fun t tLt => lt_of_lt_of_le (subtreeSlot_lt slotLt tLt) (two_pow_le_65536 (by omega)))
        (fun s t _ _ same => subtreeSlot_injective same)
      refine Tagged.bind' (subtreeM_tagged coord idx stage start slot coordLt idxLt stageLt slotLt label d
        (by omega)) (fun previous => Tagged.bind_pure (Tagged.bind_pure (level _) _) _) ?_ ?_ ?_
      · refine Set.disjoint_left.mpr fun k inTree inLevel => ?_
        simp only [subtreeKeys, Set.mem_setOf_eq] at inTree inLevel
        omega
      · exact siteDisjoint_of_fam fun k inS => by
          simp only [subtreeKeys, Set.mem_setOf_eq] at inS
          rw [inS.1]; exact ⟨by norm_num, by norm_num⟩
      · rintro k (inTree | inLevel)
        · simp only [subtreeKeys, Set.mem_setOf_eq] at inTree ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, t, tLt, h8⟩ := inTree
          exact ⟨h1, h2, h3, h4, h5, h6, by omega, t, tLt, h8⟩
        · simp only [subtreeKeys, Set.mem_setOf_eq] at inLevel ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, t, tLt, h7⟩ := inLevel
          refine ⟨h1, h2, h3, h4, h5, by omega, by omega, t, ?_, h7⟩
          rw [h6, Nat.add_sub_cancel_left]
          exact tLt

/-- The keys of the casts of the leaves below the node `(start, slot)` (`2 ^ depth` leaves). -/
def subtreeCastKeys (coord idx stage start slot depth count : Nat) : Set TagKey :=
  {k | k.fam = 3 ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage ∧ k.level = 0 ∧ k.part < count ∧
    ∃ t < 2 ^ depth, k.slot = slot + 2 ^ start * t}

/-- The keys of one expansion. -/
def expandKeys (coord idx stage start slot depth count : Nat) : Set TagKey :=
  subtreeKeys coord idx stage start slot depth ∪ subtreeCastKeys coord idx stage start slot depth count

theorem expandKeys_slot {coord idx stage start slot depth count : Nat} (slotLt : slot < 2 ^ start) {k : TagKey}
    (inside : k ∈ expandKeys coord idx stage start slot depth count) : k.slot % 2 ^ start = slot := by
  rcases inside with inTree | inCasts
  · obtain ⟨_, _, _, _, _, _, _, t, _, same⟩ := inTree
    rw [same, subtreeSlot_mod slotLt]
  · obtain ⟨_, _, _, _, _, _, t, _, same⟩ := inCasts
    rw [same, subtreeSlot_mod slotLt]

/-- **One expansion** (`expandM`): the subtree below a closed node, then the casts of its leaves. -/
theorem expandM_tagged {rb : Nat} (w : Nat) (coord idx stage start slot : Nat) (coordLt : coord < 2)
    (idxLt : idx < 128) (stageLt : stage < 4) (slotLt : slot < 2 ^ start) (small : start + (w - start) ≤ 16)
    (answers : castAnswers rb ≤ 64) (label : Label) (state : StageState rb) :
    Tagged (expandKeys coord idx stage start slot (w - start) (castAnswers rb))
      (expandM w (fun level slot => tagCode 2 coord idx stage level slot 0)
        (fun leaf part => tagCode 3 coord idx stage 0 leaf part) start slot label state) := by
  unfold expandM
  have castFields := (fields_ext coordLt idxLt stageLt).2
  refine Tagged.bind' (subtreeM_tagged coord idx stage start slot coordLt idxLt stageLt slotLt label (w - start)
    small) (fun subtree => Tagged.bind_empty ?_ fun _ => Tagged.pure _ _) ?_ ?_ le_rfl
  · refine (Tagged.tableM (S := fun t => leafKeys 3 coord idx stage (slot + 2 ^ start * t) (castAnswers rb))
      (2 ^ (w - start)) (fun t => castM_tagged 3 coord idx stage _ rb castFields
        (lt_of_lt_of_le (subtreeSlot_lt slotLt t.isLt) (two_pow_le_65536 small)) answers _)
      fun i j _ _ different => ⟨?_, ?_⟩).mono ?_
    · refine Set.disjoint_left.mpr fun k inI inJ => ?_
      simp only [leafKeys, Set.mem_setOf_eq] at inI inJ
      exact different (subtreeSlot_injective (inI.2.2.2.2.2.1.symm.trans inJ.2.2.2.2.2.1))
    · exact siteDisjoint_of_fam fun k inS => by
        simp only [leafKeys, Set.mem_setOf_eq] at inS
        rw [inS.1]; exact ⟨by norm_num, by norm_num⟩
    · rintro k ⟨t, tLt, inS⟩
      simp only [leafKeys, Set.mem_setOf_eq] at inS
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := inS
      exact ⟨h1, h2, h3, h4, h5, h7, t, tLt, h6⟩
  · refine Set.disjoint_left.mpr fun k inTree inCasts => ?_
    simp only [subtreeKeys, subtreeCastKeys, Set.mem_setOf_eq] at inTree inCasts
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [subtreeKeys, Set.mem_setOf_eq] at inS
      rw [inS.1]; exact ⟨by norm_num, by norm_num⟩

/-! ### Rounds and one stage -/

/-- The keys of round `j` of a stage of width `w` at stage value `value`. -/
def roundKeys (coord idx stage w value count j : Nat) : Set TagKey :=
  expandKeys coord idx stage (j + 1) (slotOf value j) (w - (j + 1)) count

theorem roundKeys_disjoint {coord idx stage w value count n j : Nat} (later : n < j) :
    Disjoint (roundKeys coord idx stage w value count n) (roundKeys coord idx stage w value count j) := by
  refine Set.disjoint_left.mpr fun k inN inJ => ?_
  have slotN := expandKeys_slot (slotOf_lt value n) inN
  have slotJ := expandKeys_slot (slotOf_lt value j) inJ
  have divides : 2 ^ (n + 1) ∣ 2 ^ (j + 1) := Nat.pow_dvd_pow 2 (by omega)
  have reduce := Nat.mod_mod_of_dvd k.slot divides
  rw [slotJ, slotOf_mod later, slotN] at reduce
  exact slotOf_ne value n reduce.symm

theorem roundKeys_fams {coord idx stage w value count j : Nat} {k : TagKey}
    (inside : k ∈ roundKeys coord idx stage w value count j) :
    (k.fam = 2 ∨ k.fam = 3) ∧ k.coord = coord ∧ k.idx = idx ∧ k.stage = stage := by
  rcases inside with inTree | inCasts
  · exact ⟨Or.inl inTree.1, inTree.2.1, inTree.2.2.1, inTree.2.2.2.1⟩
  · exact ⟨Or.inr inCasts.1, inCasts.2.1, inCasts.2.2.1, inCasts.2.2.2.1⟩

/-- **One round** (`stageRoundM`): the expansion of the closed child at level `n + 1`. -/
theorem stageRoundM_tagged {rb : Nat} (w : Nat) (coord idx stage : Nat) (coordLt : coord < 2) (idxLt : idx < 128)
    (stageLt : stage < 4) (wSmall : w ≤ 16) (answers : castAnswers rb ≤ 64) (sub : Lanes w) (value : Nat)
    (joins : Nat → Label) (pin : Lanes rb) (n : Nat) (nSmall : n < 16) (state : StageState rb) :
    Tagged (roundKeys coord idx stage w value (castAnswers rb) n)
      (stageRoundM w (fun level slot => tagCode 2 coord idx stage level slot 0)
        (fun leaf part => tagCode 3 coord idx stage 0 leaf part) sub value joins pin n state) := by
  unfold stageRoundM
  dsimp only
  have slotLt := slotOf_lt value n
  split
  · rename_i bit
    have same : slotOf value n = value % 2 ^ n := if_pos bit
    unfold roundKeys
    rw [same]
    exact expandM_tagged w coord idx stage (n + 1) (value % 2 ^ n) coordLt idxLt stageLt (same ▸ slotLt)
      (by omega) answers _ _
  · rename_i bit
    have same : slotOf value n = value % 2 ^ n + 2 ^ n := if_neg bit
    unfold roundKeys
    rw [same]
    exact expandM_tagged w coord idx stage (n + 1) (value % 2 ^ n + 2 ^ n) coordLt idxLt stageLt (same ▸ slotLt)
      (by omega) answers _ _

/-- The keys of rounds `n .. n + remaining − 1`. -/
def roundsKeys (coord idx stage w value count n remaining : Nat) : Set TagKey :=
  {k | ∃ j, n ≤ j ∧ j < n + remaining ∧ k ∈ roundKeys coord idx stage w value count j}

/-- **The rounds** (`stageRoundsM`). -/
theorem stageRoundsM_tagged {rb : Nat} (w : Nat) (coord idx stage : Nat) (coordLt : coord < 2)
    (idxLt : idx < 128) (stageLt : stage < 4) (wSmall : w ≤ 16) (answers : castAnswers rb ≤ 64) (sub : Lanes w)
    (value : Nat) (joins : Nat → Label) (pin : Lanes rb) :
    ∀ (remaining n : Nat) (state : StageState rb), n + remaining ≤ 16 →
      Tagged (roundsKeys coord idx stage w value (castAnswers rb) n remaining)
        (stageRoundsM w (fun level slot => tagCode 2 coord idx stage level slot 0)
          (fun leaf part => tagCode 3 coord idx stage 0 leaf part) sub value joins pin remaining n state)
  | 0, _, _, _ => Tagged.pure _ _
  | remaining + 1, n, state, small => by
      simp only [stageRoundsM]
      refine Tagged.bind' (stageRoundM_tagged w coord idx stage coordLt idxLt stageLt wSmall answers sub value joins
        pin n (by omega) state) (fun next => stageRoundsM_tagged w coord idx stage coordLt idxLt stageLt wSmall
          answers sub value joins pin remaining (n + 1) next (by omega)) ?_ ?_ ?_
      · refine Set.disjoint_left.mpr fun k inN inRest => ?_
        obtain ⟨j, low, high, inJ⟩ := inRest
        exact Set.disjoint_left.mp (roundKeys_disjoint (show n < j by omega)) inN inJ
      · exact siteDisjoint_of_fam fun k inS => by
          have := (roundKeys_fams inS).1
          omega
      · rintro k (inN | ⟨j, low, high, inJ⟩)
        · exact ⟨n, le_rfl, by omega, inN⟩
        · exact ⟨j, by omega, by omega, inJ⟩

/-- **One fused extraction stage of the evaluator** (`extStageEvalM`). -/
theorem extStageEvalM_tagged {rb : Nat} (coord idx stage w : Nat) (coordLt : coord < 2) (idxLt : idx < 128)
    (stageLt : stage < 4) (wSmall : w ≤ 16) (answers : castAnswers rb ≤ 64) (remainder : Lanes rb)
    (value : Nat) (joins : Nat → Label) (pin : Lanes rb) :
    Tagged (pairKeys 2 3 coord idx stage)
      (extStageEvalM w (fun level slot => tagCode 2 coord idx stage level slot 0)
        (fun leaf part => tagCode 3 coord idx stage 0 leaf part) remainder value joins pin) := by
  unfold extStageEvalM
  dsimp only
  rw [slotOf_zero]
  refine Tagged.bind' (expandM_tagged w coord idx stage 1 (slotOf value 0) coordLt idxLt stageLt (slotOf_lt value 0)
    (by omega) answers _ _) (S' := roundsKeys coord idx stage w value (castAnswers rb) 1 (w - 1))
    (fun afterZero => Tagged.bind_empty (stageRoundsM_tagged w coord idx stage coordLt idxLt stageLt wSmall answers
      _ value joins pin (w - 1) 1 afterZero (by omega)) fun _ => Tagged.pure _ _) ?_ ?_ ?_
  · refine Set.disjoint_left.mpr fun k inZero inRest => ?_
    obtain ⟨j, low, high, inJ⟩ := inRest
    exact Set.disjoint_left.mp (roundKeys_disjoint (n := 0) (show 0 < j by omega)) inZero inJ
  · exact siteDisjoint_of_fam fun k inS => by
      have := (roundKeys_fams (j := 0) inS).1
      omega
  · rintro k (inZero | ⟨j, _, _, inJ⟩)
    · exact roundKeys_fams (j := 0) inZero
    · exact roundKeys_fams inJ

end Kriterion.CRT.Paths
