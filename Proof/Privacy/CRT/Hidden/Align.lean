/-
**The reach against the garbler, tag by tag** (P2a).

The containment `DesignedReached` (H5) says that every garbler entry the designed rule shows at an input is asked by
the honest evaluator's reach at that input. On the table oracle an entry is determined by its input (the answer is the
table at the input's tag), so the containment is a statement about the inputs the two programs ask. This file holds
the generic part:

* `asked H p`: the inputs a CRT program asks on a hash, in order, with its laws for `pure`, `>>=`, `vector`, `tableM`,
  `askN`, `h128M`, `hlongM`, `castM`, `padVectorM`, `storeM`, `materializeM`;
* `Covers P l m`: every element of `l` satisfying `P` is in `m`, with its combinators;
* `slots_covers`: the common shape of every gadget of the conversion layer: the garbler asks a query program at every
  slot, the evaluator at every slot but the hot one, at the same labels off the hot slot; then every query of the
  garbler whose tag is cold is asked by the evaluator.
-/

import Construction.CRT.Entry
import Proof.Correctness.CRT.Delivery
import Proof.Privacy.CRT.Sites
import Proof.Privacy.CRT.Paths.Table

namespace Kriterion.CRT.Privacy.Align

open Cryptography Kriterion.ArgoMAC Kriterion.CRT

/-! ### The inputs a program asks -/

section Asked

variable {α β : Type} (H : HashN)

/-- The inputs a CRT program asks on the hash `H`, in order. -/
def asked : CM α → List ℕ
  | .pure _ => []
  | .query n next => n :: asked (next (H n))

@[simp] theorem asked_pure (value : α) : asked H (Pure.pure value : CM α) = [] := rfl

theorem asked_bind (program : CM α) (next : α → CM β) :
    asked H (program >>= next) = asked H program ++ asked H (next (program.eval H)) := by
  induction program with
  | pure value => rfl
  | query n rest ih =>
      show n :: asked H (rest (H n) >>= next) =
        n :: (asked H (rest (H n)) ++ asked H (next ((rest (H n)).eval H)))
      rw [ih (H n)]

@[simp] theorem asked_askN (n : ℕ) : asked H (askN n) = [n] := rfl

@[simp] theorem asked_h128M (label : Block) (tag : ℕ) : asked H (h128M label tag) = [hashInput label tag] := by
  unfold h128M
  rw [asked_bind]
  rfl

theorem asked_vector (count : ℕ) (program : Fin count → CM α) :
    asked H (FreeQuery.vector count program) = (List.finRange count).flatMap fun i => asked H (program i) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [FreeQuery.vector]
      rw [asked_bind, asked_bind, ih, List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      simp only [asked_pure, List.append_nil, List.flatMap_cons, List.flatMap_nil]

theorem asked_tableM (count : ℕ) (program : Fin count → CM α) :
    asked H (tableM count program) = (List.finRange count).flatMap fun i => asked H (program i) := by
  unfold tableM
  rw [asked_bind, asked_vector]
  simp

@[simp] theorem asked_storeM {count : ℕ} (family : Fin count → α) : asked H (storeM family) = [] := by
  unfold storeM
  rw [asked_tableM]
  simp

@[simp] theorem asked_materializeM {width : ℕ} (lanes : Lanes width) : asked H (materializeM lanes) = [] :=
  asked_storeM H lanes

theorem flatMap_singleton_eq_map {ι : Type} (l : List ι) (f : ι → ℕ) : l.flatMap (fun i => [f i]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem asked_hlongM (label : Block) (tagOf : ℕ → ℕ) (count : ℕ) :
    asked H (hlongM label tagOf count) = (List.finRange count).map fun j => hashInput label (tagOf j.val) := by
  unfold hlongM
  rw [asked_bind, asked_vector]
  simp only [asked_askN, asked_pure, List.append_nil]
  exact flatMap_singleton_eq_map _ _

theorem asked_castM (l : ℕ) (label : Block) (tagOf : ℕ → ℕ) :
    asked H (castM l label tagOf) = (List.finRange (castAnswers l)).map fun j => hashInput label (tagOf j.val) := by
  unfold castM
  rw [asked_bind, asked_hlongM]
  simp

theorem asked_padVectorM (m S q : ℕ) (label : Block) (tagOf : ℕ → ℕ) :
    asked H (padVectorM m S q label tagOf) = (List.finRange q).map fun j => hashInput label (tagOf j.val) := by
  unfold padVectorM
  rw [asked_bind, asked_hlongM]
  simp

theorem asked_ite (c : Prop) [Decidable c] (yes no : CM α) :
    asked H (if c then yes else no) = if c then asked H yes else asked H no := by
  split <;> rfl

end Asked

/-! ### Coverage -/

section Covers

/-- **Coverage**: every element of `l` satisfying `P` is in `m`. -/
def Covers (P : ℕ → Prop) (l m : List ℕ) : Prop := ∀ x ∈ l, P x → x ∈ m

variable {P : ℕ → Prop}

theorem Covers.nil (m : List ℕ) : Covers P [] m := fun _ inside => absurd inside List.not_mem_nil

theorem Covers.append {l l' m : List ℕ} (first : Covers P l m) (second : Covers P l' m) : Covers P (l ++ l') m :=
  fun x inside holds => (List.mem_append.mp inside).elim (fun a => first x a holds) (fun b => second x b holds)

theorem Covers.mono {l m m' : List ℕ} (covers : Covers P l m) (sub : ∀ x ∈ m, x ∈ m') : Covers P l m' :=
  fun x inside holds => sub x (covers x inside holds)

theorem Covers.left {l m m' : List ℕ} (covers : Covers P l m) : Covers P l (m ++ m') :=
  covers.mono fun _ inside => List.mem_append_left _ inside

theorem Covers.right {l m m' : List ℕ} (covers : Covers P l m') : Covers P l (m ++ m') :=
  covers.mono fun _ inside => List.mem_append_right _ inside

theorem Covers.refl (l : List ℕ) : Covers P l l := fun _ inside _ => inside

theorem Covers.flatMap {ι : Type} (index : List ι) (f : ι → List ℕ) {m : List ℕ}
    (each : ∀ i ∈ index, Covers P (f i) m) : Covers P (index.flatMap f) m := by
  intro x inside holds
  obtain ⟨i, member, x_in⟩ := List.mem_flatMap.mp inside
  exact each i member x x_in holds

theorem Covers.into_flatMap {ι : Type} (index : List ι) (f : ι → List ℕ) {l : List ℕ} {i : ι} (member : i ∈ index)
    (covers : Covers P l (f i)) : Covers P l (index.flatMap f) :=
  covers.mono fun _ x_in => List.mem_flatMap.mpr ⟨i, member, x_in⟩

/-- Nothing of `l` satisfies `P`. -/
theorem Covers.of_none {l m : List ℕ} (none : ∀ x ∈ l, ¬ P x) : Covers P l m :=
  fun x inside holds => absurd holds (none x inside)

end Covers

/-! ### The common shape: every slot against every slot but the hot one -/

/-- A labelled input reads back its tag. -/
theorem hashInput_div (label : Block) (tag : ℕ) : hashInput label tag / 2 ^ 128 = tag := by
  unfold hashInput
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.div_eq_of_lt label.isLt, Nat.zero_add]

/-- The cold predicate on inputs, from a cold predicate on tags. -/
def ColdAt (cold : ℕ → Prop) (x : ℕ) : Prop := cold (x / 2 ^ 128)

/-- **The slot shape.** The garbler asks `query (G s) s` at every slot `s`, the evaluator `query (E s) s` at every
slot but `hot` (nothing at `hot`); off the hot slot the labels agree, and every query of the hot slot has a hot tag.
Then every cold query of the garbler is the evaluator's. -/
theorem slots_covers {count : ℕ} (cold : ℕ → Prop) (hot : Fin count) (query : Block → Fin count → List ℕ)
    (G E : Fin count → Block) (agree : ∀ s, s ≠ hot → E s = G s)
    (hotTags : ∀ x ∈ query (G hot) hot, ¬ cold (x / 2 ^ 128)) :
    Covers (ColdAt cold) ((List.finRange count).flatMap fun s => query (G s) s)
      ((List.finRange count).flatMap fun s => if s = hot then [] else query (E s) s) := by
  refine Covers.flatMap _ _ fun s _ => ?_
  by_cases same : s = hot
  · subst same
    exact Covers.of_none hotTags
  · refine Covers.into_flatMap _ _ (List.mem_finRange s) ?_
    rw [if_neg same, agree s same]
    exact Covers.refl _

/-! ### Alignment: both directions -/

/-- **Alignment** of a garbler's inputs `g` with an evaluator's `e` under a cold predicate `P` on inputs: every cold
input of the garbler is the evaluator's, and every input of the evaluator is cold and the garbler's. -/
structure Aligned (P : ℕ → Prop) (g e : List ℕ) : Prop where
  covers : ∀ x ∈ g, P x → x ∈ e
  sound : ∀ x ∈ e, P x ∧ x ∈ g

namespace Aligned

variable {P : ℕ → Prop}

theorem nil : Aligned P [] [] :=
  ⟨fun _ inside => absurd inside List.not_mem_nil, fun _ inside => absurd inside List.not_mem_nil⟩

theorem append {g g' e e' : List ℕ} (first : Aligned P g e) (second : Aligned P g' e') :
    Aligned P (g ++ g') (e ++ e') := by
  refine ⟨fun x inside holds => ?_, fun x inside => ?_⟩
  · rcases List.mem_append.mp inside with a | b
    · exact List.mem_append_left _ (first.covers x a holds)
    · exact List.mem_append_right _ (second.covers x b holds)
  · rcases List.mem_append.mp inside with a | b
    · exact ⟨(first.sound x a).1, List.mem_append_left _ (first.sound x a).2⟩
    · exact ⟨(second.sound x b).1, List.mem_append_right _ (second.sound x b).2⟩

theorem flatMap {ι : Type} (index : List ι) (f f' : ι → List ℕ) (each : ∀ i ∈ index, Aligned P (f i) (f' i)) :
    Aligned P (index.flatMap f) (index.flatMap f') := by
  refine ⟨fun x inside holds => ?_, fun x inside => ?_⟩
  · obtain ⟨i, member, x_in⟩ := List.mem_flatMap.mp inside
    exact List.mem_flatMap.mpr ⟨i, member, (each i member).covers x x_in holds⟩
  · obtain ⟨i, member, x_in⟩ := List.mem_flatMap.mp inside
    exact ⟨((each i member).sound x x_in).1, List.mem_flatMap.mpr ⟨i, member, ((each i member).sound x x_in).2⟩⟩

/-- A garbler block whose inputs are all hot, against nothing. -/
theorem hot {g : List ℕ} (none : ∀ x ∈ g, ¬ P x) : Aligned P g [] :=
  ⟨fun x inside holds => absurd holds (none x inside), fun _ inside => absurd inside List.not_mem_nil⟩

/-- The same cold block on both sides. -/
theorem same {l : List ℕ} (all : ∀ x ∈ l, P x) : Aligned P l l :=
  ⟨fun _ inside _ => inside, fun x inside => ⟨all x inside, inside⟩⟩

end Aligned

/-- **The slot shape, both directions.** The garbler asks `query (G s) s` at every slot, the evaluator `query (E s) s`
at every slot that is not hot; off the hot slots the labels agree, and a query of slot `s` is cold exactly when `s`
is not hot. -/
theorem slots_aligned {count : ℕ} (P : ℕ → Prop) (isHot : Fin count → Prop) [DecidablePred isHot]
    (query : Block → Fin count → List ℕ) (G E : Fin count → Block) (agree : ∀ s, ¬ isHot s → E s = G s)
    (tags : ∀ label s, ∀ x ∈ query label s, (P x ↔ ¬ isHot s)) :
    Aligned P ((List.finRange count).flatMap fun s => query (G s) s)
      ((List.finRange count).flatMap fun s => if isHot s then [] else query (E s) s) := by
  refine Aligned.flatMap _ _ _ fun s _ => ?_
  by_cases hotHere : isHot s
  · rw [if_pos hotHere]
    exact Aligned.hot fun x inside holds => (tags _ s x inside).mp holds hotHere
  · rw [if_neg hotHere, agree s hotHere]
    exact Aligned.same fun x inside => (tags _ s x inside).mpr hotHere

/-- The singleton query of a tag function, read at a cold predicate on tags. -/
theorem single_tags (cold : ℕ → Prop) (tagOf : ℕ → ℕ) {count : ℕ} (isHot : Fin count → Prop)
    (tags : ∀ s : Fin count, cold (tagOf s.val) ↔ ¬ isHot s) :
    ∀ (label : Block) (s : Fin count), ∀ x ∈ [hashInput label (tagOf s.val)], (ColdAt cold x ↔ ¬ isHot s) := by
  intro label s x inside
  rw [List.mem_singleton.mp inside]
  unfold ColdAt
  rw [hashInput_div]
  exact tags s

/-- The part queries of a labelled long hash, read at a cold predicate on tags. -/
theorem parts_tags (cold : ℕ → Prop) (partTag : ℕ → ℕ → ℕ) (parts : ℕ) {count : ℕ} (isHot : Fin count → Prop)
    (tags : ∀ s : Fin count, ∀ j < parts, cold (partTag s.val j) ↔ ¬ isHot s) :
    ∀ (label : Block) (s : Fin count), ∀ x ∈ (List.finRange parts).map (fun j => hashInput label (partTag s.val j.val)),
      (ColdAt cold x ↔ ¬ isHot s) := by
  intro label s x inside
  obtain ⟨j, _, same⟩ := List.mem_map.mp inside
  subst same
  unfold ColdAt
  rw [hashInput_div]
  exact tags s j.val j.isLt

/-! ### The one-hot tree: a level, the tree, the growth -/

section Trees

variable (H : HashN)

theorem asked_garbleStepM (n : ℕ) (tagOf : ℕ → ℕ) (parent : Fin (2 ^ n) → Block) :
    asked H (garbleStepM n tagOf parent) =
      (List.finRange (2 ^ n)).flatMap fun s => [hashInput (parent s) (tagOf s.val)] := by
  unfold garbleStepM
  rw [asked_bind, asked_tableM]
  simp

theorem asked_evalStepM (n : ℕ) (tagOf : ℕ → ℕ) (active : Fin (2 ^ n)) (bitLabel join : Block)
    (parent : Fin (2 ^ n) → Block) :
    asked H (evalStepM n tagOf active bitLabel join parent) =
      (List.finRange (2 ^ n)).flatMap fun s => if s = active then [] else [hashInput (parent s) (tagOf s.val)] := by
  unfold evalStepM
  rw [asked_bind, asked_tableM]
  simp only [asked_ite, asked_pure, asked_h128M, List.append_nil]

/-- **One level.** -/
theorem step_aligned (cold : ℕ → Prop) (n : ℕ) (tagOf : ℕ → ℕ) (active : Fin (2 ^ n)) (bitLabel join : Block)
    (G E : Fin (2 ^ n) → Block) (agree : ∀ s, s ≠ active → E s = G s)
    (tags : ∀ s : Fin (2 ^ n), cold (tagOf s.val) ↔ s ≠ active) :
    Aligned (ColdAt cold) (asked H (garbleStepM n tagOf G))
      (asked H (evalStepM n tagOf active bitLabel join E)) := by
  rw [asked_garbleStepM, asked_evalStepM]
  exact slots_aligned _ (fun s => s = active) (fun label s => [hashInput label (tagOf s.val)]) G E agree
    (single_tags cold tagOf _ tags)

/-- **The tree with known bits** (every hashed level `1 .. total - 1`), under the hypotheses of
`SliceC.treeEvalM_correct`. -/
theorem tree_aligned (cold : ℕ → Prop) (tagOf : ℕ → ℕ → ℕ) (Δ : Block) (value : ℕ)
    (bitMask bitLabel join : ℕ → Block) (total : ℕ)
    (hbit : ∀ j < total, bitLabel j = bitMask j ^^^ (if value.testBit j then Δ else 0))
    (hjoin : ∀ j, 1 ≤ j → j < total →
      join j = ((treeGarbleM tagOf Δ (bitMask 0) total).eval H).2 j ^^^ bitMask j)
    (tags : ∀ n, 1 ≤ n → n < total → ∀ s : Fin (2 ^ n), cold (tagOf n s.val) ↔ s.val ≠ value % 2 ^ n) :
    ∀ n ≤ total, Aligned (ColdAt cold) (asked H (treeGarbleM tagOf Δ (bitMask 0) n))
      (asked H (treeEvalM tagOf value bitLabel join n)) := by
  intro n
  induction n with
  | zero => intro _; exact Aligned.nil
  | succ n ih =>
    intro hn
    have ihn := ih (by omega)
    simp only [treeGarbleM, treeEvalM]
    rw [asked_bind, asked_bind]
    by_cases hn0 : n = 0
    · simp only [hn0, if_true, asked_pure]
      subst hn0
      simpa using ihn
    · simp only [hn0, if_false, asked_bind, asked_pure, List.append_nil]
      refine ihn.append (step_aligned H cold n (tagOf n) _ _ _ _ _ (fun s hs => ?_) (fun s => ?_))
      · have correct := SliceC.treeEvalM_correct H tagOf Δ value bitMask bitLabel join total hbit hjoin n
          (by omega) s
        rw [correct, if_neg (show ¬ (s.val = value % 2 ^ n) from fun h => hs (Fin.ext h)),
          SliceC.xor_zero_block]
      · rw [tags n (Nat.one_le_iff_ne_zero.mpr hn0) (by omega) s]
        constructor
        · intro ne same
          exact ne (congrArg Fin.val same)
        · intro ne same
          exact ne (Fin.ext same)

/-- **The growth of a one-hot by known bits**, under the hypotheses of `SliceC.growEvalM_correct`. -/
theorem grow_aligned (cold : ℕ → Prop) (tagOf : ℕ → ℕ → ℕ) (start : ℕ) (G E : Fin (2 ^ start) → Block) (Δ : Block)
    (value : ℕ) (bitMask bitLabel join : ℕ → Block) (total : ℕ)
    (hE : ∀ x, E x = G x ^^^ (if x.val = value % 2 ^ start then Δ else 0))
    (hbit : ∀ j, j < start + total → bitLabel j = bitMask j ^^^ (if value.testBit j then Δ else 0))
    (hjoin : ∀ j, join j = ((growGarbleM tagOf start G total).eval H).2 j ^^^ bitMask j)
    (tags : ∀ k < total, ∀ s : Fin (2 ^ (start + k)),
      cold (tagOf (start + k) s.val) ↔ s.val ≠ value % 2 ^ (start + k)) :
    ∀ count ≤ total, Aligned (ColdAt cold) (asked H (growGarbleM tagOf start G count))
      (asked H (growEvalM tagOf value bitLabel join start E count)) := by
  intro count
  induction count with
  | zero => intro _; exact Aligned.nil
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    simp only [growGarbleM, growEvalM]
    rw [asked_bind, asked_bind, asked_bind]
    simp only [asked_pure, List.append_nil]
    refine ihk.append (step_aligned H cold (start + k) (tagOf (start + k)) _ _ _ _ _ (fun s hs => ?_) (fun s => ?_))
    · have correct := SliceC.growEvalM_correct H tagOf start G E Δ value bitMask bitLabel join total hE hbit hjoin
        k (by omega) s
      rw [correct, if_neg (show ¬ (s.val = value % 2 ^ (start + k)) from fun h => hs (Fin.ext h)),
        SliceC.xor_zero_block]
    · rw [tags k (by omega) s]
      constructor
      · intro ne same
        exact ne (congrArg Fin.val same)
      · intro ne same
        exact ne (Fin.ext same)

end Trees

/-! ### A chunk: its tree, then the casts of its leaves -/

section Chunk

variable (H : HashN) (T : CrtTable) (coord : ℕ) (Δ : Block) (Z : ℕ → Block) (c : ℕ)

theorem asked_chunkGarbleM :
    asked H (chunkGarbleM T coord Δ Z c) =
      asked H (treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)) ++
        (List.finRange (2 ^ T.chunkWidth c)).flatMap fun leaf =>
          (List.finRange (castAnswers T.castWidth)).map fun j =>
            hashInput (((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0))
              (T.chunkWidth c)).eval H).1 leaf) (chunkCastTag coord c leaf.val j.val) := by
  unfold chunkGarbleM
  simp only [asked_bind, asked_tableM, asked_castM, asked_pure, List.append_nil]

theorem asked_chunkEvalM (labels : ℕ → Block) (v : ℕ) (joins : ℕ → Block) (pin : Lanes T.castWidth) :
    asked H (chunkEvalM T coord labels v joins pin c) =
      asked H (treeEvalM (chunkTreeTag coord c) (T.chunkValue v c) (fun n => labels (T.chunkOffset c + n)) joins
          (T.chunkWidth c)) ++
        (List.finRange (2 ^ T.chunkWidth c)).flatMap fun leaf =>
          if leaf.val = T.chunkValue v c then [] else
          (List.finRange (castAnswers T.castWidth)).map fun j =>
            hashInput (((treeEvalM (chunkTreeTag coord c) (T.chunkValue v c)
              (fun n => labels (T.chunkOffset c + n)) joins (T.chunkWidth c)).eval H) leaf)
              (chunkCastTag coord c leaf.val j.val) := by
  unfold chunkEvalM
  simp only [asked_bind, asked_tableM, asked_ite, asked_castM, asked_pure, List.append_nil]

theorem chunkGarbleM_joins :
    ((chunkGarbleM T coord Δ Z c).eval H).joins = fun n =>
      ((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0)) (T.chunkWidth c)).eval H).2 n ^^^
        Z (T.chunkOffset c + n) := by
  simp [chunkGarbleM]

/-- **A chunk**: with the honest labels `Z_j ⊕ v_j·Δ` and the garbler's joins and pin (`SliceC.chunk_correct`'s
setting), the garbler's cold tree and cast queries are the evaluator's, and the evaluator asks nothing else. -/
theorem chunk_aligned (v : ℕ) (cold : ℕ → Prop)
    (treeTags : ∀ n, 1 ≤ n → n < T.chunkWidth c → ∀ s : Fin (2 ^ n),
      cold (chunkTreeTag coord c n s.val) ↔ s.val ≠ T.chunkValue v c % 2 ^ n)
    (castTags : ∀ leaf : Fin (2 ^ T.chunkWidth c), ∀ j < castAnswers T.castWidth,
      cold (chunkCastTag coord c leaf.val j) ↔ ¬ leaf.val = T.chunkValue v c) :
    Aligned (ColdAt cold) (asked H (chunkGarbleM T coord Δ Z c))
      (asked H (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v
        ((chunkGarbleM T coord Δ Z c).eval H).joins ((chunkGarbleM T coord Δ Z c).eval H).pin c)) := by
  rw [asked_chunkGarbleM, asked_chunkEvalM, chunkGarbleM_joins]
  have hbit : ∀ j < T.chunkWidth c, (fun n => Z (T.chunkOffset c + n) ^^^
      (if v.testBit (T.chunkOffset c + n) then Δ else 0)) j =
      Z (T.chunkOffset c + j) ^^^ (if (T.chunkValue v c).testBit j then Δ else 0) := by
    intro j hj
    simp only
    rw [SliceC.chunkValue_testBit T v c j hj]
  have correct := SliceC.treeEvalM_correct H (chunkTreeTag coord c) Δ (T.chunkValue v c)
    (fun n => Z (T.chunkOffset c + n))
    (fun n => Z (T.chunkOffset c + n) ^^^ (if v.testBit (T.chunkOffset c + n) then Δ else 0))
    (fun n => ((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0))
      (T.chunkWidth c)).eval H).2 n ^^^ Z (T.chunkOffset c + n)) (T.chunkWidth c) hbit
    (fun j _ _ => rfl)
  refine Aligned.append ?_ ?_
  · exact tree_aligned H cold (chunkTreeTag coord c) Δ (T.chunkValue v c) (fun n => Z (T.chunkOffset c + n))
      (fun n => Z (T.chunkOffset c + n) ^^^ (if v.testBit (T.chunkOffset c + n) then Δ else 0))
      (fun n => ((treeGarbleM (chunkTreeTag coord c) Δ (Z (T.chunkOffset c + 0))
        (T.chunkWidth c)).eval H).2 n ^^^ Z (T.chunkOffset c + n)) (T.chunkWidth c) hbit
      (fun j _ _ => rfl) treeTags (T.chunkWidth c) le_rfl
  · have hlt := SliceC.chunkValue_lt T v c
    refine slots_aligned (ColdAt cold) (fun leaf => leaf.val = T.chunkValue v c)
      (fun label leaf => (List.finRange (castAnswers T.castWidth)).map fun j =>
        hashInput label (chunkCastTag coord c leaf.val j.val)) _ _ (fun leaf hot => ?_)
      (parts_tags cold (chunkCastTag coord c) (castAnswers T.castWidth) _ castTags)
    rw [correct (T.chunkWidth c) le_rfl leaf, Nat.mod_eq_of_lt hlt, if_neg hot, SliceC.xor_zero_block]

end Chunk

/-! ### The folds and the body -/

section FoldsBody

variable (H : HashN)

theorem asked_foldGarbleM (m : ℕ) (tagOf : ℕ → ℕ) (shift : ℕ) (bitMask : Block) (labels : Fin m → Block) :
    asked H (foldGarbleM m tagOf shift bitMask labels) =
      (List.finRange m).flatMap fun r => [hashInput (labels r) (tagOf r.val)] := by
  unfold foldGarbleM
  simp only [asked_bind, asked_tableM, asked_h128M, asked_pure, List.append_nil]

theorem asked_foldEvalM (m : ℕ) (tagOf : ℕ → ℕ) (shift hot : ℕ) (bitLabel join : Block) (labels : Fin m → Block) :
    asked H (foldEvalM m tagOf shift hot bitLabel join labels) =
      (List.finRange m).flatMap fun r => if r.val = hot then [] else [hashInput (labels r) (tagOf r.val)] := by
  unfold foldEvalM
  simp only [asked_bind, asked_tableM, asked_ite, asked_h128M, asked_pure, List.append_nil]

/-- **The folds** at positions `position, ..., position + count - 1`, under the hypotheses of
`SliceC.foldsEvalM_correct`, from the hot index `(value mod 2^position) mod m`. -/
theorem folds_aligned (cold : ℕ → Prop) (m : ℕ) (hm : 0 < m) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (Δ : Block)
    (bitMask bitLabel join : ℕ → Block) :
    ∀ count position hot (G E : Fin m → Block), hot = value % 2 ^ position % m →
      (∀ ρ, E ρ = G ρ ^^^ (if ρ.val = hot then Δ else 0)) →
      (∀ j, position ≤ j → j < position + count →
        bitLabel j = bitMask j ^^^ (if value.testBit j then Δ else 0)) →
      (∀ j, position ≤ j → j < position + count →
        join j = ((foldsGarbleM m tagOf bitMask count position G).eval H).2 j) →
      (∀ j, position ≤ j → j < position + count → ∀ r : Fin m,
        cold (tagOf j r.val) ↔ r.val ≠ value % 2 ^ j % m) →
      Aligned (ColdAt cold) (asked H (foldsGarbleM m tagOf bitMask count position G))
        (asked H (foldsEvalM m tagOf value bitLabel join count position hot E)) := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _ _ _ _; exact Aligned.nil
  | succ c ih =>
    intro position hot G E hhot hE hbit hjoin tags
    have hhotm : hot < m := by rw [hhot]; exact Nat.mod_lt _ hm
    have hjoin' := hjoin position le_rfl (by omega)
    rw [SliceC.eval_foldsGarbleM_succ] at hjoin'
    simp only [if_true] at hjoin'
    simp only [foldsGarbleM, foldsEvalM, asked_bind, asked_pure, List.append_nil]
    refine Aligned.append ?_ ?_
    · rw [asked_foldGarbleM, asked_foldEvalM]
      refine slots_aligned _ (fun r => r.val = hot) (fun label r => [hashInput label (tagOf position r.val)]) G E
        (fun r hr => by rw [hE, if_neg hr, SliceC.xor_zero_block])
        (single_tags cold (tagOf position) _ fun r => ?_)
      rw [tags position le_rfl (by omega) r, hhot]
    · rw [hbit position le_rfl (by omega), hjoin']
      have hstep := SliceC.foldEvalM_correct H m (tagOf position) (foldShift m position) G E Δ hot hhotm
        (value.testBit position) (bitMask position) hE
      have hnext : (hot + (if value.testBit position then foldShift m position else 0)) % m =
          value % 2 ^ (position + 1) % m := by
        have := SliceC.foldHot_eq m value hm 1 position hot hhot
        simpa [SliceC.foldHot] using this
      refine ih (position + 1) _ _ _ hnext (fun ρ => by rw [hstep ρ, hnext]) (fun j h1 h2 => hbit j (by omega)
        (by omega)) (fun j h1 h2 => ?_) (fun j h1 h2 => tags j (by omega) (by omega))
      rw [hjoin j (by omega) (by omega), SliceC.eval_foldsGarbleM_succ]
      simp only
      rw [if_neg (by omega)]

theorem asked_bodyGarbleM (m S q coord i : ℕ) (final : Fin m → Block) :
    asked H (bodyGarbleM m S q coord i final) =
      (List.finRange m).flatMap fun r =>
        (List.finRange q).map fun j => hashInput (final r) (bodyTag coord i r.val j.val) := by
  unfold bodyGarbleM
  simp only [asked_bind, asked_tableM, asked_padVectorM, asked_pure, List.append_nil]

theorem asked_bodyEvalM (m S q coord i : ℕ) (final : Fin m → Block) (hot : ℕ) (joins : Fin S → ℕ) :
    asked H (bodyEvalM m S q coord i final hot joins) =
      (List.finRange m).flatMap fun r => if r.val = hot then [] else
        (List.finRange q).map fun j => hashInput (final r) (bodyTag coord i r.val j.val) := by
  unfold bodyEvalM
  simp only [asked_bind, asked_tableM, asked_ite, asked_padVectorM, asked_pure, List.append_nil]

/-- **The body** of one modulus: the evaluator's final one-hot is the garbler's off the hot slot. -/
theorem body_aligned (cold : ℕ → Prop) (m S q coord i : ℕ) (final finalE : Fin m → Block) (Δ : Block) (hot : ℕ)
    (joins : Fin S → ℕ) (hE : ∀ ρ, finalE ρ = final ρ ^^^ (if ρ.val = hot then Δ else 0))
    (tags : ∀ r : Fin m, ∀ j < q, cold (bodyTag coord i r.val j) ↔ ¬ r.val = hot) :
    Aligned (ColdAt cold) (asked H (bodyGarbleM m S q coord i final))
      (asked H (bodyEvalM m S q coord i finalE hot joins)) := by
  rw [asked_bodyGarbleM, asked_bodyEvalM]
  exact slots_aligned _ (fun r => r.val = hot)
    (fun label r => (List.finRange q).map fun j => hashInput label (bodyTag coord i r.val j.val)) final finalE
    (fun r hr => by rw [hE, if_neg hr, SliceC.xor_zero_block]) (parts_tags cold (bodyTag coord i) q _ tags)

end FoldsBody

/-! ### The fused extraction stage: the lists -/

section StageLists

variable (H : HashN)

/-- The garbler's tree queries, level by level. -/
theorem asked_treeGarbleM_list (tagOf : ℕ → ℕ → ℕ) (Δ b0 : Block) :
    ∀ levels, asked H (treeGarbleM tagOf Δ b0 levels) =
      (List.range levels).flatMap fun n => if n = 0 then [] else
        (List.finRange (2 ^ n)).flatMap fun y =>
          [hashInput (((treeGarbleM tagOf Δ b0 n).eval H).1 y) (tagOf n y.val)] := by
  intro levels
  induction levels with
  | zero => rfl
  | succ k ih =>
    simp only [treeGarbleM]
    rw [asked_bind, ih, List.range_succ, List.flatMap_append]
    congr 1
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, if_false, asked_bind, asked_pure, List.append_nil, List.flatMap_cons, List.flatMap_nil]
      rw [asked_garbleStepM]

/-- The subtree's queries, relative level by relative level. -/
theorem asked_subtreeM_list (treeTag : ℕ → ℕ → ℕ) (start slot : ℕ) (label : Block) :
    ∀ d, asked H (subtreeM treeTag start slot label d) =
      (List.range d).flatMap fun d' =>
        (List.finRange (2 ^ d')).flatMap fun t =>
          [hashInput (((subtreeM treeTag start slot label d').eval H).1 t)
            (treeTag (start + d') (slot + 2 ^ start * t.val))] := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [subtreeM]
    rw [asked_bind, ih, List.range_succ, List.flatMap_append]
    congr 1
    simp only [asked_bind, asked_pure, List.append_nil, List.flatMap_cons, List.flatMap_nil]
    rw [asked_garbleStepM]

/-- An expansion's queries: its subtree, then the casts of its leaves; the state does not matter. -/
theorem asked_expandM {rb : ℕ} (w : ℕ) (treeTag castTag : ℕ → ℕ → ℕ) (start slot : ℕ) (label : Block)
    (state : StageState rb) :
    asked H (expandM w treeTag castTag start slot label state) =
      asked H (subtreeM treeTag start slot label (w - start)) ++
        (List.finRange (2 ^ (w - start))).flatMap fun t =>
          (List.finRange (castAnswers rb)).map fun j =>
            hashInput (((subtreeM treeTag start slot label (w - start)).eval H).1 t)
              (castTag (slot + 2 ^ start * t.val) j.val) := by
  unfold expandM
  simp only [asked_bind, asked_tableM, asked_castM, asked_pure, List.append_nil]

/-- The garbler's stage queries: the tree, then every leaf's cast. -/
theorem asked_extStageGarbleM {rb : ℕ} (w : ℕ) (treeTag castTag : ℕ → ℕ → ℕ) (Δ : Block) (R : Lanes rb) :
    asked H (extStageGarbleM w treeTag castTag Δ R) =
      asked H (treeGarbleM treeTag Δ (laneBit (materialize (reduceTo w R)) 0) w) ++
        (List.finRange (2 ^ w)).flatMap fun leaf =>
          (List.finRange (castAnswers rb)).map fun j =>
            hashInput (((treeGarbleM treeTag Δ (laneBit (materialize (reduceTo w R)) 0) w).eval H).1 leaf)
              (castTag leaf.val j.val) := by
  unfold extStageGarbleM
  simp only [asked_bind, asked_tableM, asked_castM, asked_pure, List.append_nil]

/-- The evaluator's stage queries: the expansion of round 0, then the rounds. -/
theorem asked_extStageEvalM {rb : ℕ} (w : ℕ) (treeTag castTag : ℕ → ℕ → ℕ) (R : Lanes rb) (value : ℕ)
    (joins : ℕ → Block) (pin : Lanes rb) :
    let sub := materialize (reduceTo w R)
    let start : StageState rb :=
      { levelSum := fun _ => 0
        classSum := fun _ => 0
        castSum := fun _ => 0
        leaves := fun _ => 0
        active := laneBit sub 0
        bits := fun k => if k = 0 then laneBit sub 0 else 0 }
    asked H (extStageEvalM w treeTag castTag R value joins pin) =
      asked H (expandM w treeTag castTag 1 ((value % 2) ^^^ 1) (laneBit sub 0) start) ++
        asked H (stageRoundsM w treeTag castTag sub value joins pin (w - 1) 1
          ((expandM w treeTag castTag 1 ((value % 2) ^^^ 1) (laneBit sub 0) start).eval H)) := by
  intro sub start
  unfold extStageEvalM
  simp only [asked_bind, asked_pure, List.append_nil]
  rfl

theorem asked_stageRoundsM_succ {rb : ℕ} (w : ℕ) (treeTag castTag : ℕ → ℕ → ℕ) (sub : Lanes w) (value : ℕ)
    (joins : ℕ → Block) (pin : Lanes rb) (r n : ℕ) (state : StageState rb) :
    asked H (stageRoundsM w treeTag castTag sub value joins pin (r + 1) n state) =
      asked H (stageRoundM w treeTag castTag sub value joins pin n state) ++
        asked H (stageRoundsM w treeTag castTag sub value joins pin r (n + 1)
          ((stageRoundM w treeTag castTag sub value joins pin n state).eval H)) := by
  simp only [stageRoundsM]
  rw [asked_bind]

end StageLists

/-! ### The fused extraction stage: the closed slots -/

section Closed

open Kriterion.CRT.SliceC

/-- The closed slot of round `n` at the stage value `s`: the child of the active node of level `n` that the active path
does not take. -/
def closedSlot (s n : ℕ) : ℕ := if s.testBit n then s % 2 ^ n else s % 2 ^ n + 2 ^ n

theorem closedSlot_lt (s n : ℕ) : closedSlot s n < 2 ^ (n + 1) := by
  unfold closedSlot
  have := Nat.mod_lt s (Nat.two_pow_pos n)
  split <;> rw [pow_succ] <;> omega

theorem closedSlot_mod (s n : ℕ) : closedSlot s n % 2 ^ n = s % 2 ^ n := by
  unfold closedSlot
  have hlt := Nat.mod_lt s (Nat.two_pow_pos n)
  split
  · exact Nat.mod_mod _ _
  · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

theorem closedSlot_testBit (s n : ℕ) : (closedSlot s n).testBit n ≠ s.testBit n := by
  unfold closedSlot
  have hlt := Nat.mod_lt s (Nat.two_pow_pos n)
  cases hsb : s.testBit n
  · simp only [Bool.false_eq_true, if_false]
    rw [show s % 2 ^ n + 2 ^ n = 2 ^ n * 1 + s % 2 ^ n by ring, Nat.testBit_two_pow_mul_add 1 hlt,
      if_neg (by omega)]
    simp
  · simp only [if_true]
    rw [Nat.testBit_lt_two_pow hlt]
    simp

theorem closedSlot_zero (s : ℕ) : closedSlot s 0 = (s % 2) ^^^ 1 := by
  unfold closedSlot
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · have hb : s.testBit 0 = false := by rw [Nat.testBit_zero, h]; decide
    rw [hb, h]
    simp [Nat.mod_one]
  · have hb : s.testBit 0 = true := by rw [Nat.testBit_zero, h]; decide
    rw [hb, h]
    simp [Nat.mod_one]

/-- **Off the active path**: a slot is off the path of `s` at level `ℓ` exactly when it lies below the closed slot of
some round `k < ℓ`. -/
theorem off_path_iff (s : ℕ) : ∀ ℓ y, (y % 2 ^ ℓ ≠ s % 2 ^ ℓ ↔ ∃ k, k < ℓ ∧ y % 2 ^ (k + 1) = closedSlot s k) := by
  intro ℓ
  induction ℓ with
  | zero => intro y; simp [Nat.mod_one]
  | succ ℓ ih =>
    intro y
    rw [branch_succ_iff (closedSlot_lt s ℓ) (closedSlot_mod s ℓ) (closedSlot_testBit s ℓ), ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨ℓ, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      by_cases hkl : k = ℓ
      · subst hkl
        exact Or.inr h
      · exact Or.inl ⟨k, by omega, h⟩

end Closed

theorem mem_ite_nil {c : Prop} [Decidable c] (l : List ℕ) (x : ℕ) : x ∈ (if c then [] else l) ↔ ¬ c ∧ x ∈ l := by
  split <;> simp_all

/-! ### The fused extraction stage: membership and alignment -/

section Stage

open Kriterion.CRT.ExtractSpec Kriterion.CRT.SliceC

theorem slot_lt {start d slot t : ℕ} (hslot : slot < 2 ^ start) (ht : t < 2 ^ d) :
    slot + 2 ^ start * t < 2 ^ (start + d) := by
  rw [pow_add]
  calc slot + 2 ^ start * t < 2 ^ start * (t + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    _ ≤ 2 ^ start * 2 ^ d := Nat.mul_le_mul_left _ ht

theorem slot_mod_start {start slot t : ℕ} (hslot : slot < 2 ^ start) : (slot + 2 ^ start * t) % 2 ^ start = slot := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hslot]

theorem div_lt_of_lt_pow_add {start d y : ℕ} (hy : y < 2 ^ (start + d)) : y / 2 ^ start < 2 ^ d := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos start), ← pow_add, Nat.add_comm]
  exact hy

theorem eq_slot_of_mod {start slot y : ℕ} (hmod : y % 2 ^ start = slot) : slot + 2 ^ start * (y / 2 ^ start) = y := by
  rw [← hmod]
  exact Nat.mod_add_div y (2 ^ start)

variable (H : HashN) {rb : ℕ} (w : ℕ) (hw : w ≤ rb) (treeTag castTag : ℕ → ℕ → ℕ)

theorem mem_asked_treeGarbleM (tagOf : ℕ → ℕ → ℕ) (Δ b0 : Block) (levels x : ℕ) :
    x ∈ asked H (treeGarbleM tagOf Δ b0 levels) ↔
      ∃ n, 1 ≤ n ∧ n < levels ∧ ∃ y : Fin (2 ^ n),
        x = hashInput (((treeGarbleM tagOf Δ b0 n).eval H).1 y) (tagOf n y.val) := by
  rw [asked_treeGarbleM_list]
  simp only [List.mem_flatMap, List.mem_range, mem_ite_nil, List.mem_finRange, List.mem_singleton, true_and]
  constructor
  · rintro ⟨n, hn, hn0, y, rfl⟩
    exact ⟨n, Nat.one_le_iff_ne_zero.mpr hn0, hn, y, rfl⟩
  · rintro ⟨n, hn1, hn, y, rfl⟩
    exact ⟨n, hn, Nat.one_le_iff_ne_zero.mp hn1, y, rfl⟩

/-- The garbler's stage queries: every node of levels `1 .. w - 1` and every part of every leaf's cast, at the
garbler's labels. -/
theorem mem_garbler_stage (Δ : Block) (R : Lanes rb) (x : ℕ) :
    x ∈ asked H (extStageGarbleM w treeTag castTag Δ R) ↔
      (∃ ℓ y, 1 ≤ ℓ ∧ ℓ < w ∧ y < 2 ^ ℓ ∧
        x = hashInput (gNode (hashStage H w hw treeTag castTag) (gBit0 (hashStage H w hw treeTag castTag) R) Δ ℓ y)
          (treeTag ℓ y)) ∨
      (∃ α j, α < 2 ^ w ∧ j < castAnswers rb ∧
        x = hashInput (gNode (hashStage H w hw treeTag castTag) (gBit0 (hashStage H w hw treeTag castTag) R) Δ w α)
          (castTag α j)) := by
  have htree := fun levels => (eval_treeGarbleM H treeTag Δ (laneBit (reduceTo w R) 0)
    (hashStage H w hw treeTag castTag) (fun _ _ _ => rfl) levels).1
  rw [asked_extStageGarbleM, List.mem_append, mem_asked_treeGarbleM, materialize_eq]
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  constructor
  · rintro (⟨n, hn1, hn, y, rfl⟩ | ⟨leaf, j, rfl⟩)
    · exact Or.inl ⟨n, y.val, hn1, hn, y.isLt, by rw [htree n y]; rfl⟩
    · exact Or.inr ⟨leaf.val, j.val, leaf.isLt, j.isLt, by rw [htree w leaf]; rfl⟩
  · rintro (⟨ℓ, y, hℓ1, hℓ, hy, rfl⟩ | ⟨α, j, hα, hj, rfl⟩)
    · exact Or.inl ⟨ℓ, hℓ1, hℓ, ⟨y, hy⟩, by rw [htree ℓ ⟨y, hy⟩]; rfl⟩
    · exact Or.inr ⟨⟨α, hα⟩, ⟨j, hj⟩, by rw [htree w ⟨α, hα⟩]; rfl⟩

/-- What an expansion at `(start, slot)` asks, at the garbler's labels. -/
def ExpMem (sp : StageParams rb) (b0 Δ : Block) (start slot x : ℕ) : Prop :=
  (∃ ℓ y, start ≤ ℓ ∧ ℓ < w ∧ y < 2 ^ ℓ ∧ y % 2 ^ start = slot ∧
    x = hashInput (gNode sp b0 Δ ℓ y) (treeTag ℓ y)) ∨
  (∃ α j, α < 2 ^ w ∧ α % 2 ^ start = slot ∧ j < castAnswers rb ∧ x = hashInput (gNode sp b0 Δ w α) (castTag α j))

/-- **An expansion with the garbler's label** asks the garbler's queries of the closed node's subtree and leaves. -/
theorem mem_expandM (b0 Δ : Block) (start slot : ℕ) (hstart : 1 ≤ start) (hle : start ≤ w)
    (hslot : slot < 2 ^ start) (state : StageState rb) (x : ℕ) :
    x ∈ asked H (expandM w treeTag castTag start slot (gNode (hashStage H w hw treeTag castTag) b0 Δ start slot)
        state) ↔ ExpMem w treeTag castTag (hashStage H w hw treeTag castTag) b0 Δ start slot x := by
  have hsub := fun d => (eval_subtreeM H treeTag (hashStage H w hw treeTag castTag) (fun _ _ _ => rfl) b0 Δ
    start slot hstart hslot d).1
  unfold ExpMem
  rw [asked_expandM, List.mem_append, asked_subtreeM_list]
  simp only [List.mem_flatMap, List.mem_range, List.mem_finRange, List.mem_singleton, List.mem_map, true_and]
  have hw' : start + (w - start) = w := by omega
  constructor
  · rintro (⟨d', hd', t, rfl⟩ | ⟨t, j, rfl⟩)
    · refine Or.inl ⟨start + d', slot + 2 ^ start * t.val, by omega, by omega, slot_lt hslot t.isLt,
        slot_mod_start hslot, ?_⟩
      rw [hsub d' t]
    · refine Or.inr ⟨slot + 2 ^ start * t.val, j.val, ?_, slot_mod_start hslot, j.isLt, ?_⟩
      · have := slot_lt hslot t.isLt
        rwa [hw'] at this
      · rw [hsub (w - start) t, hw']
  · rintro (⟨ℓ, y, hℓs, hℓ, hy, hmod, rfl⟩ | ⟨α, j, hα, hmod, hj, rfl⟩)
    · have hℓ' : start + (ℓ - start) = ℓ := by omega
      have hy' : y < 2 ^ (start + (ℓ - start)) := by rwa [hℓ']
      refine Or.inl ⟨ℓ - start, by omega, ⟨y / 2 ^ start, div_lt_of_lt_pow_add hy'⟩, ?_⟩
      rw [hsub (ℓ - start) ⟨y / 2 ^ start, div_lt_of_lt_pow_add hy'⟩]
      simp only
      rw [eq_slot_of_mod hmod, hℓ']
    · have hα' : α < 2 ^ (start + (w - start)) := by rwa [hw']
      refine Or.inr ⟨⟨α / 2 ^ start, div_lt_of_lt_pow_add hα'⟩, ⟨j, hj⟩, ?_⟩
      rw [hsub (w - start) ⟨α / 2 ^ start, div_lt_of_lt_pow_add hα'⟩]
      simp only
      rw [eq_slot_of_mod hmod, hw']

theorem asked_expandM_congr (start slot : ℕ) {label label' : Block} (same : label = label')
    (state state' : StageState rb) :
    asked H (expandM w treeTag castTag start slot label state) =
      asked H (expandM w treeTag castTag start slot label' state') := by
  rw [asked_expandM, asked_expandM, same]

theorem asked_expandM_label (start slot : ℕ) {label label' : Block} (same : label = label')
    (state : StageState rb) :
    asked H (expandM w treeTag castTag start slot label state) =
      asked H (expandM w treeTag castTag start slot label' state) := by
  rw [same]

/-- **One round asks the expansion of its closed slot at the garbler's label** (the label computation of
`SliceC.stageRoundM_inv`). -/
theorem asked_stageRoundM_eq (R : Lanes rb) (Δ : Block) (σ : ℕ) (joins : ℕ → Block) (pin : Lanes rb)
    (hJ : ∀ n, 1 ≤ n → n < w → joins n = gJoin (hashStage H w hw treeTag castTag) R Δ n)
    (hP : pin = gPin (hashStage H w hw treeTag castTag) R Δ)
    (n : ℕ) (hn1 : 1 ≤ n) (hn : n < w) (st : StageState rb)
    (hinv : Inv (hashStage H w hw treeTag castTag) R Δ (σ % 2 ^ w) n st) :
    asked H (stageRoundM w treeTag castTag (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)))
        (σ % 2 ^ w) joins pin n st) =
      asked H (expandM w treeTag castTag (n + 1) (closedSlot (σ % 2 ^ w) n)
        (gNode (hashStage H w hw treeTag castTag) (gBit0 (hashStage H w hw treeTag castTag) R) Δ (n + 1)
          (closedSlot (σ % 2 ^ w) n)) st) := by
  set sp := hashStage H w hw treeTag castTag with hsp
  set s := σ % 2 ^ w with hs
  obtain ⟨hact, hsums, hbits⟩ := hinv
  obtain ⟨hL, hC, hT, hE⟩ := hsums
  have hspw : sp.w = w := rfl
  simp only [hspw] at hL hC hT hE
  have hq : s % 2 ^ n = σ % 2 ^ n := mod_two_pow_mod_of_le (Nat.le_of_lt hn)
  have hsn : s.testBit n = σ.testBit n := by rw [hs, Nat.testBit_mod_two_pow]; simp [hn]
  have hqlt : s % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hclass : materialize (st.classSum n + scaleLanes (s % 2 ^ n) (pin - st.castSum n)) =
      gRes sp R Δ n + ((σ % 2 ^ n : Nat) : ZMod (2 ^ rb)) • deltaLanes rb Δ := by
    rw [materialize_eq, scaleLanes_eq, hC n (Nat.le_of_lt hn), hT n (Nat.le_of_lt hn), Nat.min_self, hP]
    unfold gPin gRes
    simp only [hspw]
    rw [classSum_identity, hq]
  have hbit : laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) -
      reduceTo w (materialize (st.classSum n + scaleLanes (s % 2 ^ n) (pin - st.castSum n)))) n =
      gBit sp R Δ n ^^^ (if s.testBit n then Δ else 0) := by
    rw [hclass, materialize_eq, hsn]
    exact bit_of_classSum sp R Δ σ n hn (by omega)
  have hlev : gLevelSum sp R Δ n =
      sp.mat n (s % 2 ^ n) (gNode sp (gBit0 sp R) Δ n (s % 2 ^ n)) ^^^ st.levelSum n := by
    rw [hL n hn1 hn, Nat.min_self]
    exact xsum_single_out n _ hqlt _
  have hhot : laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) -
      reduceTo w (materialize (st.classSum n + scaleLanes (s % 2 ^ n) (pin - st.castSum n)))) n ^^^
        joins n ^^^ st.levelSum n =
      stepMat sp (gBit0 sp R) n (s % 2 ^ n) (gNode sp (gBit0 sp R) Δ n (s % 2 ^ n)) ^^^
        (if s.testBit n then Δ else 0) := by
    rw [hbit, hJ n hn1 hn, stepMat_pos sp _ hn1]
    unfold gJoin
    rw [hlev]
    exact xor_hot_solve _ _ _ _
  unfold stageRoundM
  simp only
  rw [hhot, hact]
  unfold closedSlot
  cases hsb : s.testBit n
  · simp only [Bool.false_eq_true, if_false, xor_zero_block]
    refine asked_expandM_congr H w treeTag castTag _ _ ?_ _ _
    have hcs : (s % 2 ^ n + 2 ^ n) % 2 ^ n = s % 2 ^ n := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hqlt]
    have hcb' : (s % 2 ^ n + 2 ^ n).testBit n = true := by
      rw [show s % 2 ^ n + 2 ^ n = 2 ^ n * 1 + s % 2 ^ n by ring, Nat.testBit_two_pow_mul_add 1 hqlt,
        if_neg (by omega)]
      simp
    rw [gNode_succ, hcs, hcb']
    rfl
  · simp only [if_true]
    refine asked_expandM_congr H w treeTag castTag _ _ ?_ _ _
    have hcs : (s % 2 ^ n) % 2 ^ n = s % 2 ^ n := Nat.mod_mod _ _
    have hcb' : (s % 2 ^ n).testBit n = false := Nat.testBit_lt_two_pow hqlt
    rw [xor_cancel_mid, gNode_succ, hcs, hcb']
    rfl

/-- **The rounds `n, ..., n + r - 1`** ask exactly the expansions of their closed slots at the garbler's labels. -/
theorem mem_stageRoundsM (R : Lanes rb) (Δ : Block) (σ : ℕ) (joins : ℕ → Block) (pin : Lanes rb)
    (hJ : ∀ n, 1 ≤ n → n < w → joins n = gJoin (hashStage H w hw treeTag castTag) R Δ n)
    (hP : pin = gPin (hashStage H w hw treeTag castTag) R Δ) :
    ∀ r n, 1 ≤ n → n + r ≤ w → ∀ st : StageState rb,
      Inv (hashStage H w hw treeTag castTag) R Δ (σ % 2 ^ w) n st → ∀ x,
      x ∈ asked H (stageRoundsM w treeTag castTag (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) •
          deltaLanes rb Δ))) (σ % 2 ^ w) joins pin r n st) ↔
        ∃ k, n ≤ k ∧ k < n + r ∧ ExpMem w treeTag castTag (hashStage H w hw treeTag castTag)
          (gBit0 (hashStage H w hw treeTag castTag) R) Δ (k + 1) (closedSlot (σ % 2 ^ w) k) x := by
  intro r
  induction r with
  | zero =>
    intro n _ _ st _ x
    simp only [stageRoundsM, asked_pure, List.not_mem_nil, false_iff, not_exists, not_and]
    intro k h1 h2
    omega
  | succ r ih =>
    intro n hn1 hnr st hinv x
    rw [asked_stageRoundsM_succ, List.mem_append,
      asked_stageRoundM_eq H w hw treeTag castTag R Δ σ joins pin hJ hP n hn1 (by omega) st hinv,
      mem_expandM H w hw treeTag castTag _ Δ (n + 1) _ (by omega) (by omega) (closedSlot_lt _ n),
      ih (n + 1) (by omega) (by omega) _
        (stageRoundM_inv H w hw treeTag castTag R Δ σ joins pin hJ hP n hn1 (by omega) st hinv)]
    constructor
    · rintro (here | ⟨k, hk1, hk2, rest⟩)
      · exact ⟨n, le_rfl, by omega, here⟩
      · exact ⟨k, by omega, by omega, rest⟩
    · rintro ⟨k, hk1, hk2, rest⟩
      by_cases hkn : k = n
      · subst hkn
        exact Or.inl rest
      · exact Or.inr ⟨k, by omega, by omega, rest⟩

/-- **The evaluator's stage queries**: the expansions of the closed slots of rounds `0 .. w - 1`, at the garbler's
labels. -/
theorem mem_evaluator_stage (hw1 : 1 ≤ w) (Δ : Block) (R : Lanes rb) (σ x : ℕ) :
    x ∈ asked H (extStageEvalM w treeTag castTag (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) (σ % 2 ^ w)
        ((extStageGarbleM w treeTag castTag Δ R).eval H).joins ((extStageGarbleM w treeTag castTag Δ R).eval H).pin) ↔
      ∃ k, k < w ∧ ExpMem w treeTag castTag (hashStage H w hw treeTag castTag)
        (gBit0 (hashStage H w hw treeTag castTag) R) Δ (k + 1) (closedSlot (σ % 2 ^ w) k) x := by
  obtain ⟨_, _, hgj, hgp, _⟩ := extStageGarbleM_eval H w hw treeTag castTag Δ R
  set sp := hashStage H w hw treeTag castTag with hsp
  set s := σ % 2 ^ w with hs
  have hinv0 := initial_inv H w hw treeTag castTag hw1 R Δ σ
  have hs0 : s.testBit 0 = σ.testBit 0 := by
    rw [hs, Nat.testBit_mod_two_pow]; simp [show 0 < w by omega]
  have hb0 : laneBit (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ)) 0 =
      gBit0 sp R ^^^ (if s.testBit 0 then Δ else 0) := by
    rw [hs0]
    exact bit0_label sp hw1 R Δ σ
  have hG1 : ∀ y, gNode sp (gBit0 sp R) Δ 1 y = if y.testBit 0 then gBit0 sp R else Δ ^^^ gBit0 sp R :=
    fun y => rfl
  have hmod2 : s % 2 = 0 ∨ s % 2 = 1 := Nat.mod_two_eq_zero_or_one s
  have hsb0 : s.testBit 0 = decide (s % 2 = 1) := Nat.testBit_zero s
  have hlabel : laneBit (materialize (reduceTo w (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ))) 0 =
      gNode sp (gBit0 sp R) Δ 1 ((s % 2) ^^^ 1) := by
    rw [materialize_eq, hb0, hG1]
    rcases hmod2 with h | h
    · have hsb : s.testBit 0 = false := by rw [hsb0, h]; decide
      rw [h, hsb]
      simp only [Bool.false_eq_true, if_false, xor_zero_block]
      have : (0 ^^^ 1 : Nat).testBit 0 = true := by decide
      rw [this]
      rfl
    · have hsb : s.testBit 0 = true := by rw [hsb0, h]; decide
      rw [h, hsb]
      simp only [if_true]
      have : (1 ^^^ 1 : Nat).testBit 0 = false := by decide
      rw [this]
      simp only [Bool.false_eq_true, if_false]
      exact BitVec.xor_comm _ _
  have hc0 : (s % 2) ^^^ 1 < 2 ^ 1 := by
    rw [← closedSlot_zero]
    exact closedSlot_lt s 0
  rw [asked_extStageEvalM]
  rw [List.mem_append, asked_expandM_label H w treeTag castTag 1 _ hlabel,
    mem_expandM H w hw treeTag castTag _ Δ 1 _ le_rfl hw1 hc0,
    mem_stageRoundsM H w hw treeTag castTag R Δ σ _ _ hgj hgp (w - 1) 1 le_rfl (by omega) _ hinv0]
  rw [← closedSlot_zero]
  constructor
  · rintro (here | ⟨k, hk1, hk2, rest⟩)
    · exact ⟨0, by omega, here⟩
    · exact ⟨k, by omega, rest⟩
  · rintro ⟨k, hk, rest⟩
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl rest
    · exact Or.inr ⟨k, by omega, by omega, rest⟩

include hw in
/-- **The fused extraction stage** (`SliceC.extStage_correct`'s setting): the garbler's cold queries are the
evaluator's, and the evaluator asks only cold garbler queries. -/
theorem stage_aligned (hw1 : 1 ≤ w) (cold : ℕ → Prop) (Δ : Block) (R : Lanes rb) (σ : ℕ)
    (treeTags : ∀ ℓ, 1 ≤ ℓ → ℓ < w → ∀ y < 2 ^ ℓ, cold (treeTag ℓ y) ↔ y ≠ σ % 2 ^ w % 2 ^ ℓ)
    (castTags : ∀ α < 2 ^ w, ∀ j < castAnswers rb, cold (castTag α j) ↔ α ≠ σ % 2 ^ w) :
    Aligned (ColdAt cold) (asked H (extStageGarbleM w treeTag castTag Δ R))
      (asked H (extStageEvalM w treeTag castTag (R + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ) (σ % 2 ^ w)
        ((extStageGarbleM w treeTag castTag Δ R).eval H).joins
        ((extStageGarbleM w treeTag castTag Δ R).eval H).pin)) := by
  set s := σ % 2 ^ w with hs
  have hslt : s < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  refine ⟨fun x inside coldx => ?_, fun x inside => ?_⟩
  · rw [mem_garbler_stage H w hw treeTag castTag] at inside
    rw [mem_evaluator_stage H w hw treeTag castTag hw1]
    unfold ColdAt at coldx
    rcases inside with ⟨ℓ, y, hℓ1, hℓ, hy, rfl⟩ | ⟨α, j, hα, hj, rfl⟩
    · rw [hashInput_div, treeTags ℓ hℓ1 hℓ y hy] at coldx
      have off : y % 2 ^ ℓ ≠ s % 2 ^ ℓ := by rwa [Nat.mod_eq_of_lt hy]
      obtain ⟨k, hk, hmod⟩ := (off_path_iff s ℓ y).mp off
      exact ⟨k, by omega, Or.inl ⟨ℓ, y, by omega, hℓ, hy, hmod, rfl⟩⟩
    · rw [hashInput_div, castTags α hα j hj] at coldx
      have off : α % 2 ^ w ≠ s % 2 ^ w := by rwa [Nat.mod_eq_of_lt hα, Nat.mod_eq_of_lt hslt]
      obtain ⟨k, hk, hmod⟩ := (off_path_iff s w α).mp off
      exact ⟨k, hk, Or.inr ⟨α, j, hα, hmod, hj, rfl⟩⟩
  · rw [mem_evaluator_stage H w hw treeTag castTag hw1] at inside
    obtain ⟨k, hk, here⟩ := inside
    rcases here with ⟨ℓ, y, hkℓ, hℓ, hy, hmod, rfl⟩ | ⟨α, j, hα, hmod, hj, rfl⟩
    · refine ⟨?_, (mem_garbler_stage H w hw treeTag castTag Δ R _).mpr (Or.inl ⟨ℓ, y, by omega, hℓ, hy, rfl⟩)⟩
      unfold ColdAt
      rw [hashInput_div, treeTags ℓ (by omega) hℓ y hy]
      have := (off_path_iff s ℓ y).mpr ⟨k, by omega, hmod⟩
      rwa [Nat.mod_eq_of_lt hy] at this
    · refine ⟨?_, (mem_garbler_stage H w hw treeTag castTag Δ R _).mpr (Or.inr ⟨α, j, hα, hj, rfl⟩)⟩
      unfold ColdAt
      rw [hashInput_div, castTags α hα j hj]
      have := (off_path_iff s w α).mpr ⟨k, hk, hmod⟩
      rwa [Nat.mod_eq_of_lt hα, Nat.mod_eq_of_lt hslt] at this

end Stage

/-! ### One odd modulus: the conversion -/

section Conversion

open Kriterion.CRT.ExtractSpec Kriterion.CRT.SliceC

variable (H : HashN)

/-- The tag conditions of one odd modulus's conversion at a cold predicate on tags (the hot slot of every block, as
`hotTag` reads it, at the word value `σ`). -/
structure ConvTags (cold : ℕ → Prop) (coord i : ℕ) (row : OddRow) (m σ : ℕ) : Prop where
  tree0 : ∀ ℓ, 1 ≤ ℓ → ℓ < row.width0 → ∀ y < 2 ^ ℓ,
    cold (extTreeTag coord i 0 ℓ y) ↔ y ≠ σ % 2 ^ row.width0 % 2 ^ ℓ
  cast0 : ∀ α < 2 ^ row.width0, ∀ j < castAnswers row.ell,
    cold (extCastTag coord i 0 α j) ↔ α ≠ σ % 2 ^ row.width0
  tree1 : ∀ ℓ, 1 ≤ ℓ → ℓ < row.width1 → ∀ y < 2 ^ ℓ,
    cold (extTreeTag coord i 1 ℓ y) ↔ y ≠ σ / 2 ^ row.width0 % 2 ^ row.width1 % 2 ^ ℓ
  cast1 : ∀ α < 2 ^ row.width1, ∀ j < castAnswers (row.ell - row.width0),
    cold (extCastTag coord i 1 α j) ↔ α ≠ σ / 2 ^ row.width0 % 2 ^ row.width1
  grow : ∀ k < row.keep - row.width0, ∀ s : Fin (2 ^ (row.width0 + k)),
    cold (growTag coord i (row.width0 + k) s.val) ↔ s.val ≠ σ % 2 ^ (row.width0 + k)
  fold : ∀ j, row.keep ≤ j → j < row.keep + (row.ell - row.keep) → ∀ r : Fin m,
    cold (foldTag coord i j r.val) ↔ r.val ≠ σ % 2 ^ j % m

/-- **One odd modulus's conversion** (`SliceC.conversion_final`'s setting): the two fused stages, the growth and the
folds. -/
theorem conversion_aligned (coord i : ℕ) (row : OddRow) (m : ℕ) (Δ : Block) (W : Lanes row.ell) (σ : ℕ)
    (pub : ConvPublic) (cold : ℕ → Prop)
    (h0 : 1 ≤ row.width0) (h1 : 1 ≤ row.width1) (hell : row.width0 + row.width1 + 1 = row.ell)
    (hk0 : row.width0 ≤ row.keep) (hk1 : row.keep ≤ row.ell) (hm : 0 < m)
    (hpJ : pub.stageJoin i = ((conversionGarbleM coord i row m Δ W).eval H).stageJoins)
    (hpP : pub.stagePin i = ((conversionGarbleM coord i row m Δ W).eval H).stagePins)
    (hpG : pub.growJoin i = ((conversionGarbleM coord i row m Δ W).eval H).growJoins)
    (hpF : pub.foldJoin i = ((conversionGarbleM coord i row m Δ W).eval H).foldJoins)
    (tags : ConvTags cold coord i row m σ) :
    Aligned (ColdAt cold) (asked H (conversionGarbleM coord i row m Δ W))
      (asked H (conversionEvalM coord i row m σ (W + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ) pub)) := by
  have hw0 : row.width0 ≤ row.ell := by omega
  have hw1' : row.width1 ≤ row.ell - row.width0 := by omega
  have hs0 := extStage_correct H row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0) h0 Δ W σ
  have hs1 := extStage_correct H row.width1 hw1' (extTreeTag coord i 1) (extCastTag coord i 1) h1 Δ
    ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).next
    (σ / 2 ^ row.width0)
  simp only at hs0 hs1
  obtain ⟨hl0, hb0, hn0⟩ := hs0
  obtain ⟨_, hb1, hn1⟩ := hs1
  simp only [conversionGarbleM, FreeQuery.eval_bind, FreeQuery.eval_pure] at hpJ hpP hpG hpF
  have hJ0 : pub.stageJoin i 0 =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).joins := by
    rw [hpJ]
    rfl
  have hJ1 : pub.stageJoin i 1 = ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).next).eval H).joins := by
    rw [hpJ]
    rfl
  have hP0 : (pinOfBlocks row.ell fun k => pub.stagePin i 0 k.val) =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).pin := by
    rw [hpP]
    exact pinOfBlocks_atNat (by omega) _
  have hP1 : (pinOfBlocks (row.ell - row.width0) fun k => pub.stagePin i 1 k.val) =
      ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ
        ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H).next).eval H).pin := by
    rw [hpP]
    exact pinOfBlocks_atNat (by omega) _
  simp only [conversionGarbleM, conversionEvalM, asked_bind, asked_pure, List.append_nil]
  rw [hJ0, hP0, hn0, hJ1, hP1, hpG, hpF]
  set g0 := (extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ W).eval H with hg0
  set g1 := (extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ g0.next).eval H with hg1
  set e0 := (extStageEvalM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0)
    (W + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ) (σ % 2 ^ row.width0) g0.joins g0.pin).eval H with he0
  set e1 := (extStageEvalM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1)
    (g0.next + ((σ / 2 ^ row.width0 : Nat) : ZMod (2 ^ (row.ell - row.width0))) •
      deltaLanes (row.ell - row.width0) Δ) (σ / 2 ^ row.width0 % 2 ^ row.width1) g1.joins g1.pin).eval H with he1
  set bitMask := wordBit row g0.bits g1.bits (laneBit g1.next 0) with hbitMask
  set bitLabel := wordBit row e0.bits e1.bits (laneBit e1.next 0) with hbitLabel
  -- the bit labels of the word (`SliceC.after_stages_correct`)
  have hbit : ∀ p < row.ell, bitLabel p = bitMask p ^^^ (if σ.testBit p then Δ else 0) := by
    intro p hp
    simp only [bitLabel, bitMask, wordBit]
    by_cases hp0 : p < row.width0
    · rw [if_pos hp0, if_pos hp0, hb0 p hp0]
    · rw [if_neg hp0, if_neg hp0]
      by_cases hp1 : p < row.width0 + row.width1
      · rw [if_pos hp1, if_pos hp1, hb1 (p - row.width0) (by omega), Nat.testBit_div_two_pow,
          Nat.sub_add_cancel (by omega)]
      · rw [if_neg hp1, if_neg hp1, hn1,
          laneBit_add_smul_delta_zero (by omega : 0 < row.ell - row.width0 - row.width1)]
        have hpe : p = row.width0 + row.width1 := by omega
        rw [hpe, Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul, ← pow_add]
        simp only [decide_eq_true_eq]
  set grown := (growGarbleM (growTag coord i) row.width0 (stored fun leaf => g0.leaves leaf.val)
    (row.keep - row.width0)).eval H with hgrown
  have hgrow := growEvalM_correct H (growTag coord i) row.width0
    (stored fun leaf => g0.leaves leaf.val) (stored fun leaf => e0.leaves leaf.val) Δ σ bitMask
    bitLabel (fun p => grown.2 p ^^^ bitMask p) (row.keep - row.width0)
    (by intro x; simp only [stored_eq]; exact hl0 x.val x.isLt)
    (fun j hj => hbit j (by omega)) (fun j => rfl) (row.keep - row.width0) le_rfl
  have hkeep : row.width0 + (row.keep - row.width0) = row.keep := by omega
  have hhot : σ % 2 ^ (row.width0 + (row.keep - row.width0)) % m = σ % 2 ^ row.keep % m := by rw [hkeep]
  have hre := fun ρ => reindex_invariant (row.width0 + (row.keep - row.width0)) m grown.1
    ((growEvalM (growTag coord i) σ bitLabel (fun p => grown.2 p ^^^ bitMask p) row.width0
      (stored fun leaf => e0.leaves leaf.val) (row.keep - row.width0)).eval H) Δ
    (σ % 2 ^ (row.width0 + (row.keep - row.width0))) (Nat.mod_lt _ (Nat.two_pow_pos _)) hgrow ρ
  refine Aligned.append ?_ (Aligned.append ?_ (Aligned.append ?_ ?_))
  · exact stage_aligned H row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0) h0 cold Δ W σ
      tags.tree0 tags.cast0
  · exact stage_aligned H row.width1 hw1' (extTreeTag coord i 1) (extCastTag coord i 1) h1 cold Δ g0.next
      (σ / 2 ^ row.width0) tags.tree1 tags.cast1
  · exact grow_aligned H cold (growTag coord i) row.width0 (stored fun leaf => g0.leaves leaf.val)
      (stored fun leaf => e0.leaves leaf.val) Δ σ bitMask bitLabel (fun p => grown.2 p ^^^ bitMask p)
      (row.keep - row.width0) (by intro x; simp only [stored_eq]; exact hl0 x.val x.isLt)
      (fun j hj => hbit j (by omega)) (fun j => rfl) tags.grow (row.keep - row.width0) le_rfl
  · exact folds_aligned H cold m hm (foldTag coord i) σ Δ bitMask bitLabel _ (row.ell - row.keep) row.keep
      (σ % 2 ^ row.keep % m) _ _ rfl (by intro ρ; rw [hre ρ, hhot]) (fun j _ h2 => hbit j (by omega))
      (fun j _ _ => rfl) tags.fold

/-- **One modulus**: the conversion (odd row) and the body (`SliceC.mod_residue`'s setting). -/
theorem mod_aligned (T : CrtTable) (S coord : ℕ) (Δ : Block) (v : ℕ) (hT : CorrectTable T)
    (hv : v < 2 ^ T.inputBits) (pub : ConvPublic) (joinsE : Fin T.count → Fin S → ℕ)
    (chunksG : ℕ → ChunkGarbled T.castWidth) (chunksE : ℕ → ChunkEval T.castWidth)
    (hL : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunksG c).leaves α ^^^ (if α = T.chunkValue v c then Δ else 0))
    (hC : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunksG c).casts α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ else 0))
    (i : Fin T.count)
    (hpJ : pub.stageJoin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).stageJoins)
    (hpP : pub.stagePin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).stagePins)
    (hpG : pub.growJoin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).growJoins)
    (hpF : pub.foldJoin i.val = ((modGarbleM T S coord Δ chunksG i).eval H).foldJoins)
    (cold : ℕ → Prop)
    (convTags : ∀ row, T.kind i = .odd row →
      ConvTags cold coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v))
    (bodyTags : ∀ r : Fin (T.modulus i), ∀ j < T.padAnswers S i,
      cold (bodyTag coord i.val r.val j) ↔ ¬ r.val = v % T.modulus i) :
    Aligned (ColdAt cold) (asked H (modGarbleM T S coord Δ chunksG i))
      (asked H (modEvalM T S coord pub joinsE v chunksE i)) := by
  have hm := hT.modulus_pos i
  cases hk : T.kind i with
  | chunkZero =>
    have hmod : T.modulus i = 2 ^ T.chunkWidth 0 := hT.chunkZero i hk
    have hc0 := chunkCount_pos T hT.chunkBits_pos hT.inputBits_pos
    simp only [modGarbleM, modEvalM, hk, asked_bind, asked_pure, List.append_nil]
    refine body_aligned H cold (T.modulus i) S (T.padAnswers S i) coord i.val
      (stored fun ρ : Fin (T.modulus i) => (chunksG 0).leaves ρ.val)
      (stored fun ρ : Fin (T.modulus i) => (chunksE 0).leaves ρ.val) Δ (v % T.modulus i) (joinsE i)
      (fun ρ => ?_) bodyTags
    simp only [stored_eq]
    have hρ : ρ.val < 2 ^ T.chunkWidth 0 := hmod ▸ ρ.isLt
    rw [hL 0 hc0 ρ.val hρ, chunkValue_zero, ← hmod]
  | odd row =>
    obtain ⟨h0, h1, hell, hk0, hk1, hcw, hcount⟩ := hT.odd i row hk
    have hσlt : T.wordValue (T.modulus i) v < 2 ^ row.ell :=
      wordValue_lt T (T.modulus i) v row.ell hm hcount
    have hσ : T.wordValue (T.modulus i) v ≡ v [MOD T.modulus i] :=
      wordValue_modEq T hT.chunkBits_pos (T.modulus i) v hv
    have hW := truthWord_label T (T.modulus i) row.ell hcw (fun c leaf => (chunksG c).casts leaf)
      (fun c leaf => (chunksE c).casts leaf) Δ v (fun c hc α hα => hC c hc α hα)
    simp only [modGarbleM, hk, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_materializeM]
      at hpJ hpP hpG hpF
    simp only [modGarbleM, modEvalM, hk, asked_bind, asked_pure, asked_materializeM, eval_materializeM,
      List.nil_append, List.append_nil]
    rw [hW]
    obtain ⟨hconv2, hconv1⟩ := conversion_final H coord i.val row (T.modulus i) Δ
      (truthWord T (T.modulus i) row.ell fun c leaf => (chunksG c).casts leaf)
      (T.wordValue (T.modulus i) v) pub h0 h1 hell hk0 hk1 hm hσlt hpJ hpP hpG hpF
    rw [hconv2]
    refine Aligned.append (conversion_aligned H coord i.val row (T.modulus i) Δ _ _ pub cold h0 h1 hell hk0 hk1 hm
      hpJ hpP hpG hpF (convTags row hk)) ?_
    refine body_aligned H cold (T.modulus i) S (T.padAnswers S i) coord i.val _ _ Δ
      (T.wordValue (T.modulus i) v % T.modulus i) (joinsE i) hconv1 (fun r j hj => ?_)
    rw [bodyTags r j hj]
    have hσ' : T.wordValue (T.modulus i) v % T.modulus i = v % T.modulus i := hσ
    rw [hσ']

end Conversion

/-! ### One coordinate -/

section Coordinate

open Kriterion.CRT.ExtractSpec Kriterion.CRT.SliceC

variable (H : HashN)

/-- The tag conditions of one coordinate at a cold predicate on tags, at the coordinate value `v`. -/
structure CoordTags (cold : ℕ → Prop) (T : CrtTable) (S coord v : ℕ) : Prop where
  chunkTree : ∀ c < T.chunkCount, ∀ n, 1 ≤ n → n < T.chunkWidth c → ∀ s : Fin (2 ^ n),
    cold (chunkTreeTag coord c n s.val) ↔ s.val ≠ T.chunkValue v c % 2 ^ n
  chunkCast : ∀ c < T.chunkCount, ∀ leaf : Fin (2 ^ T.chunkWidth c), ∀ j < castAnswers T.castWidth,
    cold (chunkCastTag coord c leaf.val j) ↔ ¬ leaf.val = T.chunkValue v c
  conv : ∀ (i : Fin T.count) row, T.kind i = .odd row →
    ConvTags cold coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v)
  body : ∀ (i : Fin T.count) (r : Fin (T.modulus i)), ∀ j < T.padAnswers S i,
    cold (bodyTag coord i.val r.val j) ↔ ¬ r.val = v % T.modulus i

/-- **One coordinate** (`SliceC.coord_delivery`'s setting): with the honest labels, the published material and the
records of the garbler, the evaluator asks every cold garbler query of the coordinate and nothing else. -/
theorem coord_aligned (T : CrtTable) (S coord : ℕ) (Δ : Block) (Z : ℕ → Block) (slopes : Fin S → ℕ) (v : ℕ)
    (hT : CorrectTable T) (hv : v < 2 ^ T.inputBits) (cold : ℕ → Prop) (tags : CoordTags cold T S coord v) :
    Aligned (ColdAt cold) (asked H (coordGarbleM T S coord Δ Z))
      (asked H (coordEvalM T S coord ((coordGarbleM T S coord Δ Z).eval H).pub
        (((coordGarbleM T S coord Δ Z).eval H).records slopes) v
        (fun j => Z j ^^^ (if v.testBit j then Δ else 0)))) := by
  obtain ⟨fJ, fP, fM, _, _, _⟩ := coordGarbleM_fields H T S coord Δ Z
  simp only at fJ fP fM
  set g := (coordGarbleM T S coord Δ Z).eval H with hg
  have hchunk : ∀ c (hc : c < T.chunkCount),
      asked H (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v (g.pub.chunkJoin c)
        (pinOfBlocks T.castWidth fun k => g.pub.chunkPin c k.val) c) =
      asked H (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v
        ((chunkGarbleM T coord Δ Z c).eval H).joins ((chunkGarbleM T coord Δ Z c).eval H).pin c) := by
    intro c hc
    rw [fJ c, fP c hc, pinOfBlocks_pinBlocks hT.castWidth_pos, atNat_of_lt _ _ hc]
  have hchunkEval : ∀ c (hc : c < T.chunkCount),
      (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v (g.pub.chunkJoin c)
        (pinOfBlocks T.castWidth fun k => g.pub.chunkPin c k.val) c).eval H =
      (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v
        ((chunkGarbleM T coord Δ Z c).eval H).joins ((chunkGarbleM T coord Δ Z c).eval H).pin c).eval H := by
    intro c hc
    rw [fJ c, fP c hc, pinOfBlocks_pinBlocks hT.castWidth_pos, atNat_of_lt _ _ hc]
  set chunksG := atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ Z c.val).eval H)
    (ChunkGarbled.empty T.castWidth) with hchunksG
  set chunksE := atNat (fun index : Fin T.chunkCount =>
    (chunkEvalM T coord (fun j => Z j ^^^ (if v.testBit j then Δ else 0)) v (g.pub.chunkJoin index.val)
      (pinOfBlocks T.castWidth fun k => g.pub.chunkPin index.val k.val) index.val).eval H)
    (ChunkEval.empty T.castWidth) with hchunksE
  have hL : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunksG c).leaves α ^^^ (if α = T.chunkValue v c then Δ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunksG, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    simp only
    rw [hchunkEval c hc]
    exact (chunk_correct H T coord Δ Z v c).1 α hα
  have hC : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunksG c).casts α +
        (if α = T.chunkValue v c then deltaLanes T.castWidth Δ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunksG, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    simp only
    rw [hchunkEval c hc]
    exact (chunk_correct H T coord Δ Z v c).2 α hα
  simp only [coordGarbleM, coordEvalM, asked_bind, asked_tableM, asked_pure, List.append_nil, eval_tableM]
  refine Aligned.append (Aligned.flatMap _ _ _ fun c _ => ?_) (Aligned.flatMap _ _ _ fun i _ => ?_)
  · rw [hchunk c.val c.isLt]
    exact chunk_aligned H T coord Δ Z c.val v cold (tags.chunkTree c.val c.isLt)
      (tags.chunkCast c.val c.isLt)
  · exact mod_aligned H T S coord Δ v hT hv g.pub _ chunksG chunksE hL hC i (fM i).1 (fM i).2.1 (fM i).2.2.1
      (fM i).2.2.2 cold (tags.conv i) (tags.body i)

end Coordinate

/-! ### The hot tags of the conversion layer, decoded -/

section HotTags

theorem hotTag_chunkTree (T : CrtTable) (u : BN254.AffineInput) {κ c n s : ℕ} (range : TagInRange κ c 0 n s 0) :
    hotTag T u (chunkTreeTag κ c n s) = (s == T.chunkValue (coordValue u κ) c % 2 ^ n) := by
  unfold chunkTreeTag
  simp only [hotTag, tagFamily_tagCode range, tagCoord_tagCode range, tagIdx_tagCode range,
    tagLevel_tagCode range, tagSlot_tagCode range, Family.chunkTree]

theorem hotTag_chunkCast (T : CrtTable) (u : BN254.AffineInput) {κ c leaf part : ℕ} (range : TagInRange κ c 0 0 leaf part) :
    hotTag T u (chunkCastTag κ c leaf part) = (leaf == T.chunkValue (coordValue u κ) c) := by
  unfold chunkCastTag
  simp only [hotTag, tagFamily_tagCode range, tagCoord_tagCode range, tagIdx_tagCode range,
    tagSlot_tagCode range, Family.chunkCast]

theorem hotTag_body (T : CrtTable) (u : BN254.AffineInput) {κ : ℕ} (i : Fin T.count) {r part : ℕ}
    (range : TagInRange κ i.val 0 0 r part) :
    hotTag T u (bodyTag κ i.val r part) = (r == coordValue u κ % T.modulus i) := by
  unfold bodyTag
  simp only [hotTag, tagFamily_tagCode range, tagCoord_tagCode range, tagIdx_tagCode range,
    tagSlot_tagCode range, Family.body, dif_pos i.isLt]

theorem hotTag_odd (T : CrtTable) (u : BN254.AffineInput) (i : Fin T.count) (row : OddRow) (hk : T.kind i = .odd row)
    {fam κ stage level slot part : ℕ} (range : TagInRange κ i.val stage level slot part) (two : 2 ≤ fam)
    (five : fam ≤ 5) :
    hotTag T u (tagCode fam κ i.val stage level slot part) =
      (let σ := T.wordValue (T.modulus i) (coordValue u κ)
       match fam with
       | 2 => slot == stageValue row σ stage % 2 ^ level
       | 3 => slot == stageValue row σ stage
       | 4 => slot == σ % 2 ^ level
       | 5 => slot == σ % 2 ^ level % T.modulus i
       | _ => false) := by
  have hk' : T.kind ⟨i.val, i.isLt⟩ = .odd row := hk
  simp only [hotTag, tagFamily_tagCode range, tagCoord_tagCode range, tagIdx_tagCode range,
    tagLevel_tagCode range, tagSlot_tagCode range, tagStage_tagCode range, dif_pos i.isLt, hk']
  interval_cases fam <;> rfl

theorem lt_65536_of_pow {n y : ℕ} (hn : n ≤ 16) (hy : y < 2 ^ n) : y < 65536 :=
  lt_of_lt_of_le hy (le_trans (Nat.pow_le_pow_right (by norm_num) hn) (by norm_num))

open Kriterion.CRT.Paths in
/-- **The tag conditions of a coordinate at the cold predicate `hotTag = false`**, for a table whose fields fit
`tagCode`. -/
theorem coordTags_cold (T : CrtTable) (u : BN254.AffineInput) (S κ : ℕ) (hκ : κ < 2) (ranges : TableRanges T S) :
    CoordTags (fun tag => hotTag T u tag = false) T S κ (coordValue u κ) := by
  refine ⟨fun c hc n hn1 hn s => ?_, fun c hc leaf j hj => ?_, fun i row hk => ?_, fun i r j hj => ?_⟩
  · have hw := ranges.chunkWidth c hc
    have range : TagInRange κ c 0 n s.val 0 :=
      ⟨hκ, by have := ranges.chunkCount; omega, by norm_num, by omega, lt_65536_of_pow (by omega) s.isLt,
        by norm_num⟩
    rw [hotTag_chunkTree T u range, beq_eq_false_iff_ne]
  · have hw := ranges.chunkWidth c hc
    have range : TagInRange κ c 0 0 leaf.val j :=
      ⟨hκ, by have := ranges.chunkCount; omega, by norm_num, by norm_num, lt_65536_of_pow hw leaf.isLt,
        by have := ranges.castAnswers; omega⟩
    rw [hotTag_chunkCast T u range, beq_eq_false_iff_ne]
  · obtain ⟨w0, w1, keep, ell, cast0, cast1⟩ := ranges.rows i row hk
    have hi : i.val < 128 := by have := ranges.count; have := i.isLt; omega
    have hm := ranges.modulus i
    refine ⟨fun ℓ hℓ1 hℓ y hy => ?_, fun α hα j hj => ?_, fun ℓ hℓ1 hℓ y hy => ?_, fun α hα j hj => ?_,
      fun k hkeep s => ?_, fun j hj1 hj2 r => ?_⟩
    · have range : TagInRange κ i.val 0 ℓ y 0 :=
        ⟨hκ, hi, by norm_num, by omega, lt_65536_of_pow (by omega) hy, by norm_num⟩
      unfold extTreeTag
      rw [hotTag_odd T u i row hk range (by simp [Family.extTree]) (by simp [Family.extTree])]
      simp only [Family.extTree, stageValue, if_true, beq_eq_false_iff_ne]
    · have range : TagInRange κ i.val 0 0 α j :=
        ⟨hκ, hi, by norm_num, by norm_num, lt_65536_of_pow w0 hα, by omega⟩
      unfold extCastTag
      rw [hotTag_odd T u i row hk range (by simp [Family.extCast]) (by simp [Family.extCast])]
      simp only [Family.extCast, stageValue, if_true, beq_eq_false_iff_ne]
    · have range : TagInRange κ i.val 1 ℓ y 0 :=
        ⟨hκ, hi, by norm_num, by omega, lt_65536_of_pow (by omega) hy, by norm_num⟩
      unfold extTreeTag
      rw [hotTag_odd T u i row hk range (by simp [Family.extTree]) (by simp [Family.extTree])]
      simp only [Family.extTree, stageValue, one_ne_zero, if_false, beq_eq_false_iff_ne]
    · have range : TagInRange κ i.val 1 0 α j :=
        ⟨hκ, hi, by norm_num, by norm_num, lt_65536_of_pow w1 hα, by omega⟩
      unfold extCastTag
      rw [hotTag_odd T u i row hk range (by simp [Family.extCast]) (by simp [Family.extCast])]
      simp only [Family.extCast, stageValue, one_ne_zero, if_false, beq_eq_false_iff_ne]
    · have range : TagInRange κ i.val 0 (row.width0 + k) s.val 0 :=
        ⟨hκ, hi, by norm_num, by omega, lt_65536_of_pow (by omega) s.isLt, by norm_num⟩
      unfold growTag
      rw [hotTag_odd T u i row hk range (by simp [Family.grow]) (by simp [Family.grow])]
      simp only [Family.grow, beq_eq_false_iff_ne]
    · have range : TagInRange κ i.val 0 j r.val 0 :=
        ⟨hκ, hi, by norm_num, by omega, by have := r.isLt; omega, by norm_num⟩
      unfold foldTag
      rw [hotTag_odd T u i row hk range (by simp [Family.fold]) (by simp [Family.fold])]
      simp only [Family.fold, beq_eq_false_iff_ne]
  · have hi : i.val < 128 := by have := ranges.count; have := i.isLt; omega
    have range : TagInRange κ i.val 0 0 r.val j :=
      ⟨hκ, hi, by norm_num, by norm_num, by have := ranges.modulus i; have := r.isLt; omega,
        by have := ranges.pads i; omega⟩
    rw [hotTag_body T u i range, beq_eq_false_iff_ne]

end HotTags

end Kriterion.CRT.Privacy.Align
