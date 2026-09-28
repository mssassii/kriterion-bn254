/-
Query bounds of the CRT layer's programs (the `Bounded` half of L20, package C6), at the exact
budgets of `Construction/CRT/{Tree, Chunk, Extract, Coord}.lean`.

The evaluator's skipped positions depend on the input (the active slot of a level, the hot leaf of
a chunk, the hot residue of a fold or of the body). Where the skipped index is a pure function of
the program's arguments, `FreeQuery.sum_ite_skip` gives the exact count. The body of an odd
modulus skips the hot index that the conversion program returns; `Returns` (a program returns
only values satisfying a predicate) carries the fact that this index is below `m` into the bound
(`Bounded.bind_returns`).
-/

import Construction.CRT.Coord

namespace Kriterion.CRT

open Cryptography Kriterion.ArgoMAC
open FreeQuery (Bounded)

/-! ### What a program can return -/

/-- Every path of the program ends in a value satisfying `P`. -/
inductive Returns {α : Type} : CM α → (α → Prop) → Prop
  | pure {value : α} {P : α → Prop} : P value → Returns (.pure value) P
  | query {request : Nat} {next : Block × Block → CM α} {P : α → Prop} :
      (∀ answer, Returns (next answer) P) → Returns (.query request next) P

namespace Returns

variable {α β : Type}

theorem pure' {value : α} {P : α → Prop} (holds : P value) : Returns (Pure.pure value : CM α) P :=
  .pure holds

theorem trivial (program : CM α) : Returns program fun _ => True := by
  induction program with
  | pure value => exact .pure True.intro
  | query request next ih => exact .query ih

theorem bind {program : CM α} {next : α → CM β} {P : α → Prop} {Q : β → Prop}
    (first : Returns program P) (rest : ∀ value, P value → Returns (next value) Q) :
    Returns (program >>= next) Q := by
  induction first with
  | pure holds => exact rest _ holds
  | query _ ih => exact .query fun answer => ih answer rest

end Returns

/-- A bound for a sequence whose continuation is bounded on the values the first program can
return. -/
theorem Bounded.bind_returns {α β : Type} {program : CM α} {next : α → CM β} {P : α → Prop}
    {first second : Nat} (bounded : program.Bounded first) (returns : Returns program P)
    (rest : ∀ value, P value → (next value).Bounded second) :
    (program >>= next).Bounded (first + second) := by
  induction bounded with
  | pure value budget =>
      cases returns with
      | pure holds => exact (rest value holds).mono (by omega)
  | query request step budget _ ih =>
      cases returns with
      | query holds =>
          show Bounded (.query request fun answer => FreeQuery.bind (step answer) next)
            (budget + 1 + second)
          rw [Nat.add_right_comm]
          exact .query request _ (budget + second) fun answer => ih answer (holds answer)

/-! ### Sums with one skipped index -/

/-- A loop over `Fin count` that skips the index whose value is `skip` costs `(count - 1) * c`
when `skip < count`. -/
theorem sum_ite_val_skip {count : Nat} (skip : Nat) (inRange : skip < count) (c : Nat) :
    (∑ index : Fin count, if index.val = skip then 0 else c) = (count - 1) * c := by
  have same : ∀ index : Fin count, (index.val = skip) = (index = ⟨skip, inRange⟩) := by
    intro index
    exact propext ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  simp only [same]
  exact FreeQuery.sum_ite_skip _ c

/-- The same for an index that is below `count` or a loop over the empty type. -/
theorem sum_ite_val_skip' {count : Nat} (skip : Nat) (inRange : count = 0 ∨ skip < count)
    (c : Nat) : (∑ index : Fin count, if index.val = skip then 0 else c) = (count - 1) * c := by
  rcases inRange with empty | inRange
  · subst empty
    simp
  · exact sum_ite_val_skip skip inRange c

/-! ### Tree steps and trees -/

theorem bounded_garbleStepM (n : Nat) (tagOf : Nat → Nat) (parent : Fin (2 ^ n) → Label) :
    (garbleStepM n tagOf parent).Bounded (2 ^ n) :=
  (Bounded.bind (bounded_tableM (budget := fun _ => 1) fun _ => bounded_hLabelM _ _) fun _ =>
    Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_evalStepM (n : Nat) (tagOf : Nat → Nat) (active : Fin (2 ^ n))
    (bitLabel join : Label) (parent : Fin (2 ^ n) → Label) :
    (evalStepM n tagOf active bitLabel join parent).Bounded (2 ^ n - 1) :=
  (Bounded.bind (bounded_tableM (budget := fun slot => if slot = active then 0 else 1) fun slot =>
      Bounded.ite (fun same => by rw [if_pos same]; exact Bounded.pure' _ 0)
        (fun different => by rw [if_neg different]; exact bounded_hLabelM _ _))
    fun _ => Bounded.pure' _ 0).of_eq (by rw [FreeQuery.sum_ite_skip]; simp)

theorem bounded_treeGarbleM (tagOf : Nat → Nat → Nat) (delta bit0 : Label) (levels : Nat) :
    (treeGarbleM tagOf delta bit0 levels).Bounded (treeGarbleBudget levels) := by
  induction levels with
  | zero => exact Bounded.pure' _ _
  | succ n ih =>
      rw [treeGarbleM, treeGarbleBudget]
      refine Bounded.bind ih fun previous => Bounded.ite (fun zero => ?_) (fun nonzero => ?_)
      · exact Bounded.pure' _ _
      · rw [if_neg nonzero]
        exact (Bounded.bind (bounded_garbleStepM n (tagOf n) previous.1) fun _ =>
          Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_treeEvalM (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel join : Nat → Label)
    (levels : Nat) : (treeEvalM tagOf value bitLabel join levels).Bounded (treeEvalBudget levels) := by
  induction levels with
  | zero => exact Bounded.pure' _ _
  | succ n ih =>
      rw [treeEvalM, treeEvalBudget]
      refine Bounded.bind ih fun previous => Bounded.ite (fun zero => ?_) (fun nonzero => ?_)
      · exact Bounded.pure' _ _
      · rw [if_neg nonzero]
        exact bounded_evalStepM _ _ _ _ _ _

theorem bounded_growGarbleM (tagOf : Nat → Nat → Nat) (start : Nat) (labels : Fin (2 ^ start) → Label)
    (count : Nat) :
    (growGarbleM tagOf start labels count).Bounded (growGarbleBudget start count) := by
  induction count with
  | zero => exact Bounded.pure' _ _
  | succ k ih =>
      rw [growGarbleM, growGarbleBudget]
      exact Bounded.bind ih fun previous =>
        (Bounded.bind (bounded_garbleStepM _ _ previous.1) fun _ => Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_growEvalM (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel join : Nat → Label)
    (start : Nat) (labels : Fin (2 ^ start) → Label) (count : Nat) :
    (growEvalM tagOf value bitLabel join start labels count).Bounded (growEvalBudget start count) := by
  induction count with
  | zero => exact Bounded.pure' _ _
  | succ k ih =>
      rw [growEvalM, growEvalBudget]
      exact Bounded.bind ih fun _ => bounded_evalStepM _ _ _ _ _ _

/-! ### Casts, stores, chunks -/

theorem bounded_castM (l : Nat) (label : Label) (tagOf : Nat → Nat) :
    (castM l label tagOf).Bounded (castAnswers l) :=
  (Bounded.bind (bounded_hlongM _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_materializeM {width : Nat} (lanes : Lanes width) :
    (materializeM lanes).Bounded 0 := bounded_storeM lanes

theorem bounded_chunkGarbleM (T : CrtTable) (coord : Nat) (delta : Label) (zeroLabel : Nat → Label)
    (c : Nat) : (chunkGarbleM T coord delta zeroLabel c).Bounded (chunkGarbleBudget T c) := by
  unfold chunkGarbleM chunkGarbleBudget
  exact (Bounded.bind (bounded_treeGarbleM _ _ _ _) fun tree =>
    Bounded.bind (bounded_tableM (budget := fun _ => castAnswers T.castWidth) fun _ =>
      bounded_castM _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_chunkEvalM (T : CrtTable) (coord : Nat) (labels : Nat → Label) (v : Nat)
    (joins : Nat → Label) (pin : Lanes T.castWidth) (c : Nat) :
    (chunkEvalM T coord labels v joins pin c).Bounded (chunkEvalBudget T c) := by
  unfold chunkEvalM chunkEvalBudget
  have inRange : T.chunkValue v c < 2 ^ T.chunkWidth c := Nat.mod_lt _ (Nat.two_pow_pos _)
  exact (Bounded.bind (bounded_treeEvalM _ _ _ _ _) fun tree =>
    Bounded.bind (bounded_tableM
      (budget := fun leaf => if leaf.val = T.chunkValue v c then 0 else castAnswers T.castWidth)
      fun leaf => Bounded.ite (fun same => by rw [if_pos same]; exact Bounded.pure' _ 0)
        (fun different => by rw [if_neg different]; exact bounded_castM _ _ _)) fun _ =>
      Bounded.pure' _ 0).of_eq (by rw [sum_ite_val_skip _ inRange]; simp)

/-! ### Extraction: the garbler -/

theorem bounded_extStageGarbleM {rb : Nat} (w : Nat) (treeTag castTag : Nat → Nat → Nat)
    (delta : Label) (remainder : Lanes rb) :
    (extStageGarbleM w treeTag castTag delta remainder).Bounded (extGarbleBudget rb w) := by
  unfold extStageGarbleM extGarbleBudget
  exact (Bounded.bind (bounded_treeGarbleM _ _ _ _) fun tree =>
    Bounded.bind (bounded_tableM (budget := fun _ => castAnswers rb) fun _ =>
      bounded_castM _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by simp)

/-! ### Folds, body -/

theorem bounded_foldGarbleM (m : Nat) (tagOf : Nat → Nat) (shift : Nat) (bitMask : Label)
    (labels : Fin m → Label) : (foldGarbleM m tagOf shift bitMask labels).Bounded m :=
  (Bounded.bind (bounded_tableM (budget := fun _ => 1) fun _ => bounded_hLabelM _ _) fun _ =>
    Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_foldsGarbleM (m : Nat) (tagOf : Nat → Nat → Nat) (bitMask : Nat → Label) (count : Nat) :
    ∀ (start : Nat) (labels : Fin m → Label),
      (foldsGarbleM m tagOf bitMask count start labels).Bounded (count * m) := by
  induction count with
  | zero => intro start labels; exact Bounded.pure' _ _
  | succ count ih =>
      intro start labels
      rw [foldsGarbleM]
      exact (Bounded.bind (bounded_foldGarbleM _ _ _ _ _) fun step =>
        Bounded.bind (ih (start + 1) step.1) fun _ => Bounded.pure' _ 0).of_eq (by ring)

theorem bounded_padVectorM (m S q : Nat) (label : Label) (tagOf : Nat → Nat) :
    (padVectorM m S q label tagOf).Bounded q :=
  (Bounded.bind (bounded_hlongM _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_bodyGarbleM (m S q coord i : Nat) (final : Fin m → Label) :
    (bodyGarbleM m S q coord i final).Bounded (m * q) :=
  (Bounded.bind (bounded_tableM (budget := fun _ => q) fun _ => bounded_padVectorM _ _ _ _ _)
    fun _ => Bounded.pure' _ 0).of_eq (by simp)

/-- The evaluator's body skips the hot slot. -/
theorem bounded_bodyEvalM (m S q coord i : Nat) (final : Fin m → Label) (hot : Nat)
    (inRange : m = 0 ∨ hot < m) (joins : Fin S → Nat) :
    (bodyEvalM m S q coord i final hot joins).Bounded ((m - 1) * q) :=
  (Bounded.bind (bounded_tableM (budget := fun residue => if residue.val = hot then 0 else q)
      fun residue => Bounded.ite (fun same => by rw [if_pos same]; exact Bounded.pure' _ 0)
        (fun different => by rw [if_neg different]; exact bounded_padVectorM _ _ _ _ _))
    fun _ => Bounded.pure' _ 0).of_eq (by rw [sum_ite_val_skip' _ inRange]; simp)

/-! ### One coordinate: the garbler -/

theorem bounded_conversionGarbleM (coord i : Nat) (row : OddRow) (m : Nat) (delta : Label)
    (word : Lanes row.ell) :
    (conversionGarbleM coord i row m delta word).Bounded (conversionGarbleBudget m (.odd row)) := by
  unfold conversionGarbleM conversionGarbleBudget
  exact (Bounded.bind (bounded_extStageGarbleM _ _ _ _ _) fun g0 =>
    Bounded.bind (bounded_extStageGarbleM _ _ _ _ _) fun g1 =>
      Bounded.bind (bounded_growGarbleM _ _ _ _) fun grown =>
        Bounded.bind (bounded_foldsGarbleM _ _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq
    (by ring)

theorem bounded_modGarbleM (T : CrtTable) (S coord : Nat) (delta : Label)
    (chunks : Nat → ChunkGarbled T.castWidth) (i : Fin T.count) :
    (modGarbleM T S coord delta chunks i).Bounded
      (conversionGarbleBudget (T.modulus i) (T.kind i) + T.modulus i * T.padAnswers S i) := by
  unfold modGarbleM
  split
  · rename_i kind
    rw [kind, conversionGarbleBudget]
    exact (Bounded.bind (bounded_bodyGarbleM _ _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq
      (by simp)
  · rename_i row kind
    rw [kind]
    exact (Bounded.bind (bounded_materializeM _) fun word =>
      Bounded.bind (bounded_conversionGarbleM _ _ _ _ _ _) fun conversion =>
        Bounded.bind (bounded_bodyGarbleM _ _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq
      (by simp)

/-- **The garbler of one coordinate asks exactly `coordGarbleBudget T S` queries.** -/
theorem bounded_coordGarbleM (T : CrtTable) (S coord : Nat) (delta : Label) (zeroLabel : Nat → Label) :
    (coordGarbleM T S coord delta zeroLabel).Bounded (coordGarbleBudget T S) := by
  unfold coordGarbleM coordGarbleBudget
  exact (Bounded.bind (bounded_tableM fun c => bounded_chunkGarbleM T coord delta zeroLabel c.val)
    fun _ => Bounded.bind (bounded_tableM fun i => bounded_modGarbleM T S coord delta _ i) fun _ =>
      Bounded.pure' _ 0).of_eq (by simp)

/-! ### Extraction: the round-ordered evaluator -/

/-- Queries of the tree below a closed node, `depth` levels: `2 ^ depth - 1`. -/
def subtreeBudget : Nat → Nat
  | 0 => 0
  | d + 1 => subtreeBudget d + 2 ^ d

/-- Queries of the expansion of a closed node at level `start` of a stage of width `w`. -/
def expandBudget (rb w start : Nat) : Nat :=
  subtreeBudget (w - start) + 2 ^ (w - start) * castAnswers rb

/-- Queries of rounds `n, ..., n + remaining - 1` (each expands a node at the next level). -/
def roundsBudget (rb w : Nat) : (remaining n : Nat) → Nat
  | 0, _ => 0
  | remaining + 1, n => expandBudget rb w (n + 1) + roundsBudget rb w remaining (n + 1)

theorem subtreeBudget_add_one (d : Nat) : subtreeBudget d + 1 = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [subtreeBudget, pow_succ]; omega

theorem roundsBudget_add (rb w : Nat) :
    ∀ (remaining n : Nat), n + remaining = w →
      roundsBudget rb w remaining n + (remaining + 1 + castAnswers rb) =
        2 ^ remaining + 2 ^ remaining * castAnswers rb := by
  intro remaining
  induction remaining with
  | zero => intro n _; simp [roundsBudget]
  | succ r ih =>
      intro n total
      have next := ih (n + 1) (by omega)
      have width : w - (n + 1) = r := by omega
      have sub := subtreeBudget_add_one r
      have double : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
      have doubleMul : 2 ^ (r + 1) * castAnswers rb = 2 ^ r * castAnswers rb + 2 ^ r * castAnswers rb := by
        ring
      rw [roundsBudget, expandBudget, width]
      omega

/-- The evaluator's structural count equals the closed form `extEvalBudget` for `w ≥ 1`. -/
theorem stageEvalBudget_eq (rb w : Nat) (positive : 1 ≤ w) :
    expandBudget rb w 1 + roundsBudget rb w (w - 1) 1 = extEvalBudget rb w := by
  obtain ⟨r, rfl⟩ : ∃ r, w = r + 1 := ⟨w - 1, by omega⟩
  have rounds := roundsBudget_add rb (r + 1) r 1 (by omega)
  have sub := subtreeBudget_add_one r
  have double : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
  have doubleMul : 2 ^ (r + 1) * castAnswers rb = 2 ^ r * castAnswers rb + 2 ^ r * castAnswers rb := by
    ring
  have large : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
  have subMul : (2 ^ (r + 1) - 1) * castAnswers rb + castAnswers rb = 2 ^ (r + 1) * castAnswers rb := by
    rw [Nat.sub_one_mul]
    have : castAnswers rb ≤ 2 ^ (r + 1) * castAnswers rb :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  simp only [expandBudget, extEvalBudget, Nat.add_sub_cancel] at rounds ⊢
  omega

theorem bounded_subtreeM (treeTag : Nat → Nat → Nat) (start slot : Nat) (label : Label) (depth : Nat) :
    (subtreeM treeTag start slot label depth).Bounded (subtreeBudget depth) := by
  induction depth with
  | zero => exact Bounded.pure' _ _
  | succ d ih =>
      rw [subtreeM, subtreeBudget]
      exact Bounded.bind ih fun previous =>
        (Bounded.bind (bounded_garbleStepM _ _ previous.1) fun _ => Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_expandM {rb : Nat} (w : Nat) (treeTag castTag : Nat → Nat → Nat) (start slot : Nat)
    (label : Label) (state : StageState rb) :
    (expandM w treeTag castTag start slot label state).Bounded (expandBudget rb w start) := by
  unfold expandM expandBudget
  exact (Bounded.bind (bounded_subtreeM _ _ _ _ _) fun subtree =>
    Bounded.bind (bounded_tableM (budget := fun _ => castAnswers rb) fun _ =>
      bounded_castM _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by simp)

theorem bounded_stageRoundM {rb : Nat} (w : Nat) (treeTag castTag : Nat → Nat → Nat) (sub : Lanes w)
    (value : Nat) (joins : Nat → Label) (pin : Lanes rb) (n : Nat) (state : StageState rb) :
    (stageRoundM w treeTag castTag sub value joins pin n state).Bounded (expandBudget rb w (n + 1)) := by
  unfold stageRoundM
  exact Bounded.ite (fun _ => bounded_expandM _ _ _ _ _ _ _) (fun _ => bounded_expandM _ _ _ _ _ _ _)

theorem bounded_stageRoundsM {rb : Nat} (w : Nat) (treeTag castTag : Nat → Nat → Nat) (sub : Lanes w)
    (value : Nat) (joins : Nat → Label) (pin : Lanes rb) (remaining : Nat) :
    ∀ (n : Nat) (state : StageState rb),
      (stageRoundsM w treeTag castTag sub value joins pin remaining n state).Bounded
        (roundsBudget rb w remaining n) := by
  induction remaining with
  | zero => intro n state; exact Bounded.pure' _ _
  | succ r ih =>
      intro n state
      rw [stageRoundsM, roundsBudget]
      exact Bounded.bind (bounded_stageRoundM _ _ _ _ _ _ _ _ _) fun next => ih (n + 1) next

/-- **One fused stage's evaluator asks exactly `extEvalBudget rb w` queries** (`w ≥ 1`). -/
theorem bounded_extStageEvalM {rb : Nat} (w : Nat) (positive : 1 ≤ w) (treeTag castTag : Nat → Nat → Nat)
    (remainder : Lanes rb) (value : Nat) (joins : Nat → Label) (pin : Lanes rb) :
    (extStageEvalM w treeTag castTag remainder value joins pin).Bounded (extEvalBudget rb w) := by
  unfold extStageEvalM
  exact (Bounded.bind (bounded_expandM _ _ _ _ _ _ _) fun afterZero =>
    Bounded.bind (bounded_stageRoundsM _ _ _ _ _ _ _ _ _ afterZero) fun _ =>
      Bounded.pure' _ 0).of_eq (by rw [← stageEvalBudget_eq rb w positive]; simp)

/-! ### Folds and body: the evaluator -/

theorem bounded_foldEvalM (m : Nat) (tagOf : Nat → Nat) (shift hot : Nat) (inRange : m = 0 ∨ hot < m)
    (bitLabel join : Label) (labels : Fin m → Label) :
    (foldEvalM m tagOf shift hot bitLabel join labels).Bounded (m - 1) :=
  (Bounded.bind (bounded_tableM (budget := fun residue => if residue.val = hot then 0 else 1)
      fun residue => Bounded.ite (fun same => by rw [if_pos same]; exact Bounded.pure' _ 0)
        (fun different => by rw [if_neg different]; exact bounded_hLabelM _ _))
    fun _ => Bounded.pure' _ 0).of_eq (by rw [sum_ite_val_skip' _ inRange]; simp)

theorem mod_inRange (x m : Nat) : m = 0 ∨ x % m < m := by
  rcases Nat.eq_zero_or_pos m with zero | positive
  · exact Or.inl zero
  · exact Or.inr (Nat.mod_lt _ positive)

theorem bounded_foldsEvalM (m : Nat) (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel join : Nat → Label)
    (count : Nat) : ∀ (start x : Nat) (labels : Fin m → Label),
      (foldsEvalM m tagOf value bitLabel join count start (x % m) labels).Bounded (count * (m - 1)) := by
  induction count with
  | zero => intro start x labels; exact Bounded.pure' _ _
  | succ count ih =>
      intro start x labels
      rw [foldsEvalM]
      exact (Bounded.bind (bounded_foldEvalM _ _ _ _ (mod_inRange x m) _ _ _) fun next =>
        ih (start + 1) _ next).of_eq (by ring)

theorem returns_foldsEvalM (m : Nat) (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel join : Nat → Label)
    (count : Nat) : ∀ (start x : Nat) (labels : Fin m → Label),
      Returns (foldsEvalM m tagOf value bitLabel join count start (x % m) labels)
        fun result => m = 0 ∨ result.2 < m := by
  induction count with
  | zero => intro start x labels; exact Returns.pure' (mod_inRange x m)
  | succ count ih =>
      intro start x labels
      rw [foldsEvalM]
      exact Returns.bind (Returns.trivial _) fun next _ => ih (start + 1) _ next

/-! ### One coordinate: the evaluator -/

/-- Every odd row has nonempty extraction stages. -/
def CrtTable.StagesNonempty (T : CrtTable) : Prop :=
  ∀ (i : Fin T.count) (row : OddRow), T.kind i = .odd row → 1 ≤ row.width0 ∧ 1 ≤ row.width1

theorem bounded_conversionEvalM (coord i : Nat) (row : OddRow) (positive0 : 1 ≤ row.width0)
    (positive1 : 1 ≤ row.width1) (m value : Nat) (word : Lanes row.ell) (pub : ConvPublic) :
    (conversionEvalM coord i row m value word pub).Bounded (conversionEvalBudget m (.odd row)) := by
  unfold conversionEvalM conversionEvalBudget
  have folds := bounded_foldsEvalM m (foldTag coord i) value
  exact (Bounded.bind (bounded_extStageEvalM _ positive0 _ _ _ _ _ _) fun e0 =>
    Bounded.bind (bounded_extStageEvalM _ positive1 _ _ _ _ _ _) fun e1 =>
      Bounded.bind (bounded_growEvalM _ _ _ _ _ _ _) fun grown =>
        folds _ _ _ _ _ _).of_eq (by ring)

theorem returns_conversionEvalM (coord i : Nat) (row : OddRow) (m value : Nat) (word : Lanes row.ell)
    (pub : ConvPublic) :
    Returns (conversionEvalM coord i row m value word pub) fun result => m = 0 ∨ result.2 < m := by
  unfold conversionEvalM
  exact Returns.bind (Returns.trivial _) fun _ _ => Returns.bind (Returns.trivial _) fun _ _ =>
    Returns.bind (Returns.trivial _) fun _ _ => returns_foldsEvalM _ _ _ _ _ _ _ _ _

theorem bounded_modEvalM (T : CrtTable) (nonempty : T.StagesNonempty) (S coord : Nat) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → Nat) (v : Nat) (chunks : Nat → ChunkEval T.castWidth)
    (i : Fin T.count) :
    (modEvalM T S coord pub joins v chunks i).Bounded
      (conversionEvalBudget (T.modulus i) (T.kind i) + (T.modulus i - 1) * T.padAnswers S i) := by
  unfold modEvalM
  split
  · rename_i kind
    rw [kind, conversionEvalBudget]
    exact (bounded_bodyEvalM _ _ _ _ _ _ _ (mod_inRange v _) _).of_eq (by simp)
  · rename_i row kind
    rw [kind]
    obtain ⟨positive0, positive1⟩ := nonempty i row kind
    exact (Bounded.bind (bounded_materializeM _) fun word =>
      Bounded.bind_returns (bounded_conversionEvalM _ _ _ positive0 positive1 _ _ _ _)
        (returns_conversionEvalM _ _ _ _ _ _ _) fun conversion inRange =>
          bounded_bodyEvalM _ _ _ _ _ _ _ inRange _).of_eq (by simp)

/-- **The evaluator of one coordinate asks exactly `coordEvalBudget T S` queries.** -/
theorem bounded_coordEvalM (T : CrtTable) (nonempty : T.StagesNonempty) (S coord : Nat) (pub : ConvPublic)
    (records : Fin S → Nat) (v : Nat) (labels : Nat → Label) :
    (coordEvalM T S coord pub records v labels).Bounded (coordEvalBudget T S) := by
  unfold coordEvalM coordEvalBudget
  exact (Bounded.bind (bounded_tableM fun c => bounded_chunkEvalM T coord labels v _ _ c.val)
    fun _ => Bounded.bind (bounded_tableM fun i => bounded_modEvalM T nonempty S coord pub _ v _ i)
      fun _ => Bounded.pure' _ 0).of_eq (by simp)

end Kriterion.CRT
