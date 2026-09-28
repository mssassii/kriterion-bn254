/-
**Two garbler runs of one coordinate, position by position** (`coord_relational`; the shared core of H7's `convHot`
 and `digestOther`).

Two runs of `coordGarbleM T S coord` with coins `(Z₁, Δ₁)` and `(Z₂, Δ₂)` on hashes `H₁`, `H₂` such that
* the labels of `u` agree (`Z₁ j ⊕ v_j Δ₁ = Z₂ j ⊕ v_j Δ₂`),
* the published conversion material agrees on every cell the evaluator reads, and
* the hashes agree, whatever the labels, at every tag that is not a hot conversion tag of `coord` (families `0` to
  `5`) at `u`,
ask the same tags in the same order; at a cold tag they ask the same input, at a hot tag (families `0` to `6`) the
labels differ by `embed (Δ₁ ⊕ Δ₂)` for narrow deltas; and their residues, pad sums, offsets and hints agree.
-/

import Proof.Privacy.CRT.Hidden.Align
import Proof.Correctness.CRT.RealTable
import Proof.Correctness.CRT.FlatLayout
import Proof.Correctness.CRT.EntryDelivery

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.Align

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy

/-- Position by position: equal tags; equal inputs off the hot tags; at hot tags the labels differ by `δ`. -/
def RelAsked (hot : ℕ → Prop) (δ : Block) (A₁ A₂ : List ℕ) : Prop :=
  List.Forall₂ (fun n₁ n₂ => n₁ / 2 ^ 128 = n₂ / 2 ^ 128 ∧ (¬ hot (n₁ / 2 ^ 128) → n₁ = n₂) ∧
    (hot (n₁ / 2 ^ 128) → BitVec.ofNat 128 n₁ = BitVec.ofNat 128 n₂ ^^^ δ)) A₁ A₂

namespace Rel

/-! ### 1. The relation, position by position -/

/-- The labels `a`, `b` of one position with tag `τ`: equal off the hot tags, differing by `δ` at them. -/
def LabelRel (hot : ℕ → Prop) (δ : Label) (τ : ℕ) (a b : Label) : Prop :=
  (hot τ → a = b ^^^ δ) ∧ (¬ hot τ → a = b)

theorem ofNat_hashInput (label : Block) (tag : ℕ) : BitVec.ofNat 128 (hashInput label tag) = label := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  unfold hashInput
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt label.isLt]

theorem hashInput_label_inj {a b : Block} {τ τ' : ℕ} (same : hashInput a τ = hashInput b τ') : a = b := by
  rw [← ofNat_hashInput a τ, same, ofNat_hashInput]

theorem hashInput_self (x : ℕ) : hashInput (BitVec.ofNat 128 x) (x / 2 ^ 128) = x := by
  unfold hashInput
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_add_div x (2 ^ 128)

theorem xor_shift (e Δ₁ Δ₂ : Label) : e ^^^ Δ₁ = (e ^^^ Δ₂) ^^^ (Δ₁ ^^^ Δ₂) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases e.getLsbD i <;> cases Δ₁.getLsbD i <;> cases Δ₂.getLsbD i <;> rfl

/-- Two labels that differ from one common label by `[c]·Δ₁` and `[c]·Δ₂`. -/
theorem labelRel_of_eq (hot : ℕ → Prop) (τ : ℕ) (c : Prop) [Decidable c] (hc : hot τ ↔ c) {a b Δ₁ Δ₂ : Label}
    (same : a ^^^ (if c then Δ₁ else 0) = b ^^^ (if c then Δ₂ else 0)) : LabelRel hot (Δ₁ ^^^ Δ₂) τ a b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [if_pos (hc.mp h), if_pos (hc.mp h)] at same
    apply BitVec.eq_of_getLsbD_eq; intro i _
    have bit := congrArg (fun v : Label => v.getLsbD i) same
    simp only [BitVec.getLsbD_xor] at bit ⊢
    revert bit
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases Δ₁.getLsbD i <;> cases Δ₂.getLsbD i <;> decide
  · rw [if_neg (fun h' => h (hc.mpr h')), if_neg (fun h' => h (hc.mpr h')), SliceC.xor_zero_block,
      SliceC.xor_zero_block] at same
    exact same

theorem relAsked_nil (hot : ℕ → Prop) (δ : Block) : RelAsked hot δ [] [] := List.Forall₂.nil

theorem relAsked_append {hot : ℕ → Prop} {δ : Block} {A₁ A₂ B₁ B₂ : List ℕ} (first : RelAsked hot δ A₁ A₂)
    (second : RelAsked hot δ B₁ B₂) : RelAsked hot δ (A₁ ++ B₁) (A₂ ++ B₂) :=
  List.rel_append first second

theorem relAsked_single {hot : ℕ → Prop} {δ : Label} {τ : ℕ} {a b : Label} (rel : LabelRel hot δ τ a b) :
    RelAsked hot (embed δ) [hashInput (embed a) τ] [hashInput (embed b) τ] := by
  refine List.Forall₂.cons ⟨?_, fun h => ?_, fun h => ?_⟩ List.Forall₂.nil
  · rw [hashInput_div, hashInput_div]
  · rw [hashInput_div] at h
    rw [rel.2 h]
  · rw [hashInput_div] at h
    rw [ofNat_hashInput, ofNat_hashInput]
    rw [rel.1 h, Narrow.embed_xor]

theorem relAsked_flatMap {ι : Type} {hot : ℕ → Prop} {δ : Block} (index : List ι) (f₁ f₂ : ι → List ℕ)
    (each : ∀ i ∈ index, RelAsked hot δ (f₁ i) (f₂ i)) :
    RelAsked hot δ (index.flatMap f₁) (index.flatMap f₂) := by
  induction index with
  | nil => exact List.Forall₂.nil
  | cons i rest ih =>
      simp only [List.flatMap_cons]
      exact relAsked_append (each i (List.mem_cons_self ..)) (ih fun j member => each j (List.mem_cons_of_mem _ member))

theorem relAsked_map {ι : Type} {hot : ℕ → Prop} {δ : Label} (index : List ι) (a b : Label) (tagOf : ι → ℕ)
    (each : ∀ i ∈ index, LabelRel hot δ (tagOf i) a b) :
    RelAsked hot (embed δ) (index.map fun i => hashInput (embed a) (tagOf i)) (index.map fun i => hashInput (embed b) (tagOf i)) := by
  rw [← flatMap_singleton_eq_map index (fun i => hashInput (embed a) (tagOf i)),
    ← flatMap_singleton_eq_map index (fun i => hashInput (embed b) (tagOf i))]
  exact relAsked_flatMap index _ _ fun i member => relAsked_single (each i member)

/-! ### 2. Hash agreement along a program -/

/-- The two hashes agree on every input of a list. -/
def AgreeOn (H₁ H₂ : HashN) (l : List ℕ) : Prop := ∀ x ∈ l, H₁ x = H₂ x

theorem agreeOn_append_left {H₁ H₂ : HashN} {l l' : List ℕ} (agree : AgreeOn H₁ H₂ (l ++ l')) : AgreeOn H₁ H₂ l :=
  fun x member => agree x (List.mem_append_left _ member)

theorem agreeOn_append_right {H₁ H₂ : HashN} {l l' : List ℕ} (agree : AgreeOn H₁ H₂ (l ++ l')) :
    AgreeOn H₁ H₂ l' :=
  fun x member => agree x (List.mem_append_right _ member)

theorem eval_eq_of_agreeOn {α : Type} (H₁ H₂ : HashN) :
    ∀ (P : CM α), AgreeOn H₁ H₂ (asked H₁ P) → P.eval H₁ = P.eval H₂ ∧ asked H₁ P = asked H₂ P
  | .pure _, _ => ⟨rfl, rfl⟩
  | .query n next, agree => by
      have head : H₁ n = H₂ n := agree n (List.mem_cons_self ..)
      have rest := eval_eq_of_agreeOn H₁ H₂ (next (H₁ n)) fun x member => agree x (List.mem_cons_of_mem _ member)
      refine ⟨?_, ?_⟩
      · show (next (H₁ n)).eval H₁ = (next (H₂ n)).eval H₂
        rw [← head]
        exact rest.1
      · show n :: asked H₁ (next (H₁ n)) = n :: asked H₂ (next (H₂ n))
        rw [← head, rest.2]

theorem agreeOn_bind_left {α β : Type} {H₁ H₂ : HashN} (P : CM α) (f : α → CM β)
    (agree : AgreeOn H₁ H₂ (asked H₁ (P >>= f))) : AgreeOn H₁ H₂ (asked H₁ P) := by
  rw [asked_bind] at agree
  exact agreeOn_append_left agree

theorem agreeOn_bind_right {α β : Type} {H₁ H₂ : HashN} (P : CM α) (f : α → CM β)
    (agree : AgreeOn H₁ H₂ (asked H₁ (P >>= f))) : AgreeOn H₁ H₂ (asked H₁ (f (P.eval H₁))) := by
  rw [asked_bind] at agree
  exact agreeOn_append_right agree

/-- The cold tags with their range: a tag that is not hot at `u` and fits `2^40`. -/
def Cold (T : CrtTable) (u : AffineInput) (τ : ℕ) : Prop := hotTag T u τ = false ∧ τ < 2 ^ 40

/-- The evaluator side of an alignment at the cold tags asks only where the hashes agree. -/
theorem agreeOn_of_aligned (T : CrtTable) (u : AffineInput) (coord : ℕ) {H₁ H₂ : HashN}
    (hagree : ∀ (label₁ label₂ : Block) (τ : ℕ), τ < 2 ^ 40 →
      ¬ (tagFamily τ ≤ 5 ∧ tagCoord τ = coord ∧ hotTag T u τ = true) →
      H₁ (hashInput label₁ τ) = H₂ (hashInput label₂ τ))
    {g e : List ℕ} (aligned : Aligned (ColdAt (Cold T u)) g e) : AgreeOn H₁ H₂ e := by
  intro x member
  obtain ⟨⟨cold, range⟩, _⟩ := aligned.sound x member
  rw [← hashInput_self x]
  refine hagree _ _ _ range fun ⟨_, _, hot⟩ => ?_
  rw [cold] at hot
  exact Bool.false_ne_true hot

/-! ### 3. The tree with known bits -/

section Tree

variable (H₁ H₂ : HashN)

theorem asked_treeEvalM_prefix (H : HashN) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Label) (n : ℕ) :
    ∀ k, ∀ x ∈ asked H (treeEvalM tagOf value bitLabel join n), x ∈ asked H (treeEvalM tagOf value bitLabel join (n + k)) := by
  intro k
  induction k with
  | zero => exact fun x member => member
  | succ k ih =>
      intro x member
      rw [← Nat.add_assoc]
      simp only [treeEvalM]
      rw [asked_bind]
      exact List.mem_append_left _ (ih x member)

/-- **The tree, two runs.** -/
theorem tree_rel (hot : ℕ → Prop) (tagOf : ℕ → ℕ → ℕ) (Δ₁ Δ₂ : Label) (value : ℕ)
    (bitMask₁ bitMask₂ bitLabel join₁ join₂ : ℕ → Label) (total : ℕ)
    (hbit₁ : ∀ j < total, bitLabel j = bitMask₁ j ^^^ (if value.testBit j then Δ₁ else 0))
    (hbit₂ : ∀ j < total, bitLabel j = bitMask₂ j ^^^ (if value.testBit j then Δ₂ else 0))
    (hjoin₁ : ∀ j, 1 ≤ j → j < total →
      join₁ j = ((treeGarbleM tagOf Δ₁ (bitMask₁ 0) total).eval H₁).2 j ^^^ bitMask₁ j)
    (hjoin₂ : ∀ j, 1 ≤ j → j < total →
      join₂ j = ((treeGarbleM tagOf Δ₂ (bitMask₂ 0) total).eval H₂).2 j ^^^ bitMask₂ j)
    (hJ : ∀ j, 1 ≤ j → j < total → join₁ j = join₂ j)
    (agree : AgreeOn H₁ H₂ (asked H₁ (treeEvalM tagOf value bitLabel join₁ total)))
    (hotTags : ∀ n, 1 ≤ n → n < total → ∀ s : Fin (2 ^ n), hot (tagOf n s.val) ↔ s.val = value % 2 ^ n) :
    (∀ n ≤ total, ∀ x : Fin (2 ^ n),
      ((treeGarbleM tagOf Δ₁ (bitMask₁ 0) n).eval H₁).1 x ^^^ (if x.val = value % 2 ^ n then Δ₁ else 0) =
        ((treeGarbleM tagOf Δ₂ (bitMask₂ 0) n).eval H₂).1 x ^^^ (if x.val = value % 2 ^ n then Δ₂ else 0)) ∧
      RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (treeGarbleM tagOf Δ₁ (bitMask₁ 0) total))
        (asked H₂ (treeGarbleM tagOf Δ₂ (bitMask₂ 0) total)) := by
  have levels : ∀ n ≤ total, ∀ x : Fin (2 ^ n),
      ((treeGarbleM tagOf Δ₁ (bitMask₁ 0) n).eval H₁).1 x ^^^ (if x.val = value % 2 ^ n then Δ₁ else 0) =
        ((treeGarbleM tagOf Δ₂ (bitMask₂ 0) n).eval H₂).1 x ^^^ (if x.val = value % 2 ^ n then Δ₂ else 0) := by
    intro n hn x
    have c₁ := SliceC.treeEvalM_correct H₁ tagOf Δ₁ value bitMask₁ bitLabel join₁ total hbit₁ hjoin₁ n hn x
    have c₂ := SliceC.treeEvalM_correct H₂ tagOf Δ₂ value bitMask₂ bitLabel join₂ total hbit₂ hjoin₂ n hn x
    have prog : treeEvalM tagOf value bitLabel join₂ n = treeEvalM tagOf value bitLabel join₁ n :=
      FlatLayout.treeEvalM_congr tagOf value bitLabel join₂ join₁ n fun j h1 h2 => (hJ j h1 (by omega)).symm
    have agreeN : AgreeOn H₁ H₂ (asked H₁ (treeEvalM tagOf value bitLabel join₁ n)) := by
      intro y member
      refine agree y ?_
      have := asked_treeEvalM_prefix H₁ tagOf value bitLabel join₁ n (total - n) y member
      rwa [Nat.add_sub_cancel' hn] at this
    rw [prog, ← (eval_eq_of_agreeOn H₁ H₂ _ agreeN).1] at c₂
    rw [← c₁, ← c₂]
  refine ⟨levels, ?_⟩
  rw [asked_treeGarbleM_list, asked_treeGarbleM_list]
  refine relAsked_flatMap _ _ _ fun n member => ?_
  rw [List.mem_range] at member
  by_cases hn0 : n = 0
  · rw [if_pos hn0, if_pos hn0]
    exact relAsked_nil _ _
  · rw [if_neg hn0, if_neg hn0]
    refine relAsked_flatMap _ _ _ fun y _ => relAsked_single ?_
    exact labelRel_of_eq hot _ _ (hotTags n (Nat.one_le_iff_ne_zero.mpr hn0) member y) (levels n (by omega) y)

end Tree

/-! ### 4. A chunk -/

section Chunk

variable (H₁ H₂ : HashN) (T : CrtTable) (coord c : ℕ)

theorem chunkEvalM_congr (labels₁ labels₂ : ℕ → Label) (v : ℕ) (joins₁ joins₂ : ℕ → Label)
    (pin : Lanes T.castWidth) (hL : ∀ j < T.inputBits, labels₁ j = labels₂ j)
    (hJ : ∀ n, 1 ≤ n → n < T.chunkWidth c → joins₁ n = joins₂ n) :
    chunkEvalM T coord labels₁ v joins₁ pin c = chunkEvalM T coord labels₂ v joins₂ pin c := by
  have tree := FlatLayout.treeEvalM_congr (chunkTreeTag coord c) (T.chunkValue v c)
    (fun n => labels₁ (T.chunkOffset c + n)) joins₁ joins₂ (T.chunkWidth c) hJ
  have bits := EntryDelivery.treeEvalM_bits_congr (chunkTreeTag coord c) (T.chunkValue v c)
    (fun n => labels₁ (T.chunkOffset c + n)) (fun n => labels₂ (T.chunkOffset c + n)) joins₂ (T.chunkWidth c)
    fun n lower => hL _ (EntryDelivery.chunkWidth_add_offset_le T c n lower)
  unfold chunkEvalM
  simp only [tree, bits]

/-- **A chunk, two runs**: the tree and the casts, and the common evaluator of the chunk. -/
theorem chunk_rel (hot : ℕ → Prop) (Δ₁ Δ₂ : Label) (Z₁ Z₂ : ℕ → Label) (v : ℕ)
    (hE : ∀ j < T.inputBits, Z₁ j ^^^ (if v.testBit j then Δ₁ else 0) = Z₂ j ^^^ (if v.testBit j then Δ₂ else 0))
    (hJ : ∀ n, 1 ≤ n → n < T.chunkWidth c →
      ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).joins n = ((chunkGarbleM T coord Δ₂ Z₂ c).eval H₂).joins n)
    (hP : ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).pin = ((chunkGarbleM T coord Δ₂ Z₂ c).eval H₂).pin)
    (agree : AgreeOn H₁ H₂ (asked H₁ (chunkEvalM T coord (fun j => Z₁ j ^^^ (if v.testBit j then Δ₁ else 0)) v
      ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).joins ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).pin c)))
    (treeHot : ∀ n, 1 ≤ n → n < T.chunkWidth c → ∀ s : Fin (2 ^ n),
      hot (chunkTreeTag coord c n s.val) ↔ s.val = T.chunkValue v c % 2 ^ n)
    (castHot : ∀ leaf : Fin (2 ^ T.chunkWidth c), ∀ j < castAnswers T.castWidth,
      hot (chunkCastTag coord c leaf.val j) ↔ leaf.val = T.chunkValue v c) :
    RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (chunkGarbleM T coord Δ₁ Z₁ c)) (asked H₂ (chunkGarbleM T coord Δ₂ Z₂ c)) ∧
      (chunkEvalM T coord (fun j => Z₂ j ^^^ (if v.testBit j then Δ₂ else 0)) v
          ((chunkGarbleM T coord Δ₂ Z₂ c).eval H₂).joins ((chunkGarbleM T coord Δ₂ Z₂ c).eval H₂).pin c).eval H₂ =
        (chunkEvalM T coord (fun j => Z₁ j ^^^ (if v.testBit j then Δ₁ else 0)) v
          ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).joins ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).pin c).eval H₁ := by
  set g₁ := (chunkGarbleM T coord Δ₁ Z₁ c).eval H₁ with hg₁
  set g₂ := (chunkGarbleM T coord Δ₂ Z₂ c).eval H₂ with hg₂
  set labels₁ : ℕ → Label := fun j => Z₁ j ^^^ (if v.testBit j then Δ₁ else 0) with hlabels₁
  have hbit : ∀ (Z : ℕ → Label) (Δ : Label), ∀ j < T.chunkWidth c,
      (fun n => Z (T.chunkOffset c + n) ^^^ (if v.testBit (T.chunkOffset c + n) then Δ else 0)) j =
        Z (T.chunkOffset c + j) ^^^ (if (T.chunkValue v c).testBit j then Δ else 0) := by
    intro Z Δ j hj
    simp only
    rw [SliceC.chunkValue_testBit T v c j hj]
  have hbit₂ : ∀ j < T.chunkWidth c, (fun n => labels₁ (T.chunkOffset c + n)) j =
      Z₂ (T.chunkOffset c + j) ^^^ (if (T.chunkValue v c).testBit j then Δ₂ else 0) := by
    intro j hj
    rw [← hbit Z₂ Δ₂ j hj]
    exact hE _ (EntryDelivery.chunkWidth_add_offset_le T c j hj)
  have agreeTree : AgreeOn H₁ H₂ (asked H₁ (treeEvalM (chunkTreeTag coord c) (T.chunkValue v c)
      (fun n => labels₁ (T.chunkOffset c + n)) g₁.joins (T.chunkWidth c))) := by
    have := agree
    rw [asked_chunkEvalM] at this
    exact agreeOn_append_left this
  obtain ⟨levels, treeRel⟩ := tree_rel H₁ H₂ hot (chunkTreeTag coord c) Δ₁ Δ₂ (T.chunkValue v c)
    (fun n => Z₁ (T.chunkOffset c + n)) (fun n => Z₂ (T.chunkOffset c + n)) (fun n => labels₁ (T.chunkOffset c + n))
    g₁.joins g₂.joins (T.chunkWidth c) (hbit Z₁ Δ₁) hbit₂
    (fun j _ _ => by rw [hg₁, chunkGarbleM_joins]) (fun j _ _ => by rw [hg₂, chunkGarbleM_joins]) hJ agreeTree
    treeHot
  have hlt := SliceC.chunkValue_lt T v c
  refine ⟨?_, ?_⟩
  · rw [asked_chunkGarbleM, asked_chunkGarbleM]
    refine relAsked_append treeRel (relAsked_flatMap _ _ _ fun leaf _ => relAsked_map _ _ _ _ fun j _ => ?_)
    have same := levels (T.chunkWidth c) le_rfl leaf
    rw [Nat.mod_eq_of_lt hlt] at same
    exact labelRel_of_eq hot _ _ (castHot leaf j.val j.isLt) same
  · have prog := chunkEvalM_congr T coord c (fun j => Z₂ j ^^^ (if v.testBit j then Δ₂ else 0)) labels₁ v g₂.joins
      g₁.joins g₂.pin (fun j hj => (hE j hj).symm) fun n h1 h2 => (hJ n h1 h2).symm
    rw [prog, ← hP]
    exact (eval_eq_of_agreeOn H₁ H₂ _ agree).1.symm

end Chunk

/-! ### 5. The growth, the folds, the body -/

section GrowFoldBody

variable (H₁ H₂ : HashN)

theorem asked_growGarbleM_list (H : HashN) (tagOf : ℕ → ℕ → ℕ) (start : ℕ) (G : Fin (2 ^ start) → Label) :
    ∀ count, asked H (growGarbleM tagOf start G count) =
      (List.range count).flatMap fun k => (List.finRange (2 ^ (start + k))).flatMap fun s =>
        [hashInput (embed (((growGarbleM tagOf start G k).eval H).1 s)) (tagOf (start + k) s.val)] := by
  intro count
  induction count with
  | zero => rfl
  | succ k ih =>
      simp only [growGarbleM]
      rw [asked_bind, ih, List.range_succ, List.flatMap_append, asked_bind, asked_garbleStepM]
      simp only [asked_pure, List.append_nil, List.flatMap_cons, List.flatMap_nil]

theorem asked_growEvalM_prefix (H : HashN) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Label) (start : ℕ)
    (labels : Fin (2 ^ start) → Label) (n : ℕ) :
    ∀ k, ∀ x ∈ asked H (growEvalM tagOf value bitLabel join start labels n),
      x ∈ asked H (growEvalM tagOf value bitLabel join start labels (n + k)) := by
  intro k
  induction k with
  | zero => exact fun x member => member
  | succ k ih =>
      intro x member
      show x ∈ asked H (growEvalM tagOf value bitLabel join start labels (n + k + 1))
      simp only [growEvalM]
      rw [asked_bind]
      exact List.mem_append_left _ (ih x member)

/-- **The growth, two runs**, with one evaluator (the joins of run 1). -/
theorem grow_rel (hot : ℕ → Prop) (tagOf : ℕ → ℕ → ℕ) (start : ℕ) (G₁ G₂ E : Fin (2 ^ start) → Label)
    (Δ₁ Δ₂ : Label) (value : ℕ) (bitMask₁ bitMask₂ bitLabel : ℕ → Label) (total : ℕ)
    (hE₁ : ∀ x, E x = G₁ x ^^^ (if x.val = value % 2 ^ start then Δ₁ else 0))
    (hE₂ : ∀ x, E x = G₂ x ^^^ (if x.val = value % 2 ^ start then Δ₂ else 0))
    (hbit₁ : ∀ j, j < start + total → bitLabel j = bitMask₁ j ^^^ (if value.testBit j then Δ₁ else 0))
    (hbit₂ : ∀ j, j < start + total → bitLabel j = bitMask₂ j ^^^ (if value.testBit j then Δ₂ else 0))
    (hJ : ∀ k < total, ((growGarbleM tagOf start G₁ total).eval H₁).2 (start + k) ^^^ bitMask₁ (start + k) =
      ((growGarbleM tagOf start G₂ total).eval H₂).2 (start + k) ^^^ bitMask₂ (start + k))
    (agree : AgreeOn H₁ H₂ (asked H₁ (growEvalM tagOf value bitLabel
      (fun p => ((growGarbleM tagOf start G₁ total).eval H₁).2 p ^^^ bitMask₁ p) start E total)))
    (hotTags : ∀ k < total, ∀ s : Fin (2 ^ (start + k)),
      hot (tagOf (start + k) s.val) ↔ s.val = value % 2 ^ (start + k)) :
    (∀ count ≤ total, ∀ x,
      (growEvalM tagOf value bitLabel (fun p => ((growGarbleM tagOf start G₁ total).eval H₁).2 p ^^^ bitMask₁ p)
          start E count).eval H₁ x =
        ((growGarbleM tagOf start G₁ count).eval H₁).1 x ^^^ (if x.val = value % 2 ^ (start + count) then Δ₁ else 0) ∧
      (growEvalM tagOf value bitLabel (fun p => ((growGarbleM tagOf start G₁ total).eval H₁).2 p ^^^ bitMask₁ p)
          start E count).eval H₁ x =
        ((growGarbleM tagOf start G₂ count).eval H₂).1 x ^^^ (if x.val = value % 2 ^ (start + count) then Δ₂ else 0)) ∧
      RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (growGarbleM tagOf start G₁ total))
        (asked H₂ (growGarbleM tagOf start G₂ total)) := by
  set join₁ : ℕ → Label := fun p => ((growGarbleM tagOf start G₁ total).eval H₁).2 p ^^^ bitMask₁ p with hjoin₁
  set join₂ : ℕ → Label := fun p => ((growGarbleM tagOf start G₂ total).eval H₂).2 p ^^^ bitMask₂ p with hjoin₂
  have levels : ∀ count ≤ total, ∀ x,
      (growEvalM tagOf value bitLabel join₁ start E count).eval H₁ x =
        ((growGarbleM tagOf start G₁ count).eval H₁).1 x ^^^ (if x.val = value % 2 ^ (start + count) then Δ₁ else 0) ∧
      (growEvalM tagOf value bitLabel join₁ start E count).eval H₁ x =
        ((growGarbleM tagOf start G₂ count).eval H₂).1 x ^^^ (if x.val = value % 2 ^ (start + count) then Δ₂ else 0) := by
    intro count hcount x
    have c₁ := SliceC.growEvalM_correct H₁ tagOf start G₁ E Δ₁ value bitMask₁ bitLabel join₁ total hE₁ hbit₁
      (fun j => rfl) count hcount x
    have c₂ := SliceC.growEvalM_correct H₂ tagOf start G₂ E Δ₂ value bitMask₂ bitLabel join₂ total hE₂ hbit₂
      (fun j => rfl) count hcount x
    have prog : growEvalM tagOf value bitLabel join₂ start E count = growEvalM tagOf value bitLabel join₁ start E count :=
      FlatLayout.growEvalM_congr tagOf value bitLabel join₂ join₁ start E count fun k hk => (hJ k (by omega)).symm
    have agreeN : AgreeOn H₁ H₂ (asked H₁ (growEvalM tagOf value bitLabel join₁ start E count)) := by
      intro y member
      refine agree y ?_
      have := asked_growEvalM_prefix H₁ tagOf value bitLabel join₁ start E count (total - count) y member
      rwa [Nat.add_sub_cancel' hcount] at this
    rw [prog, ← (eval_eq_of_agreeOn H₁ H₂ _ agreeN).1] at c₂
    exact ⟨c₁, c₂⟩
  refine ⟨levels, ?_⟩
  rw [asked_growGarbleM_list, asked_growGarbleM_list]
  refine relAsked_flatMap _ _ _ fun k member => relAsked_flatMap _ _ _ fun s _ => relAsked_single ?_
  rw [List.mem_range] at member
  obtain ⟨l₁, l₂⟩ := levels k (by omega) s
  exact labelRel_of_eq hot _ _ (hotTags k member s) (l₁.symm.trans l₂)

theorem asked_foldsGarbleM_succ (H : HashN) (m : ℕ) (tagOf : ℕ → ℕ → ℕ) (bitMask : ℕ → Label) (count position : ℕ)
    (labels : Fin m → Label) :
    asked H (foldsGarbleM m tagOf bitMask (count + 1) position labels) =
      asked H (foldGarbleM m (tagOf position) (foldShift m position) (bitMask position) labels) ++
        asked H (foldsGarbleM m tagOf bitMask count (position + 1)
          ((foldGarbleM m (tagOf position) (foldShift m position) (bitMask position) labels).eval H).1) := by
  simp only [foldsGarbleM, asked_bind, asked_pure, List.append_nil]

theorem asked_foldsEvalM_succ (H : HashN) (m : ℕ) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Label)
    (count position hot : ℕ) (labels : Fin m → Label) :
    asked H (foldsEvalM m tagOf value bitLabel join (count + 1) position hot labels) =
      asked H (foldEvalM m (tagOf position) (foldShift m position) hot (bitLabel position) (join position) labels) ++
        asked H (foldsEvalM m tagOf value bitLabel join count (position + 1)
          ((hot + (if value.testBit position then foldShift m position else 0)) % m)
          ((foldEvalM m (tagOf position) (foldShift m position) hot (bitLabel position) (join position)
            labels).eval H)) := by
  simp only [foldsEvalM, asked_bind]

/-- **The folds, two runs**, with one evaluator. -/
theorem folds_rel (hot : ℕ → Prop) (m : ℕ) (hm : 0 < m) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (Δ₁ Δ₂ : Label)
    (bitMask₁ bitMask₂ bitLabel join : ℕ → Label) :
    ∀ count position h (G₁ G₂ E : Fin m → Label), h = value % 2 ^ position % m →
      (∀ ρ, E ρ = G₁ ρ ^^^ (if ρ.val = h then Δ₁ else 0)) →
      (∀ ρ, E ρ = G₂ ρ ^^^ (if ρ.val = h then Δ₂ else 0)) →
      (∀ j, position ≤ j → j < position + count →
        bitLabel j = bitMask₁ j ^^^ (if value.testBit j then Δ₁ else 0)) →
      (∀ j, position ≤ j → j < position + count →
        bitLabel j = bitMask₂ j ^^^ (if value.testBit j then Δ₂ else 0)) →
      (∀ j, position ≤ j → j < position + count →
        join j = ((foldsGarbleM m tagOf bitMask₁ count position G₁).eval H₁).2 j) →
      (∀ j, position ≤ j → j < position + count →
        join j = ((foldsGarbleM m tagOf bitMask₂ count position G₂).eval H₂).2 j) →
      AgreeOn H₁ H₂ (asked H₁ (foldsEvalM m tagOf value bitLabel join count position h E)) →
      (∀ j, position ≤ j → j < position + count → ∀ r : Fin m,
        hot (tagOf j r.val) ↔ r.val = value % 2 ^ j % m) →
      RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (foldsGarbleM m tagOf bitMask₁ count position G₁))
          (asked H₂ (foldsGarbleM m tagOf bitMask₂ count position G₂)) ∧
        (foldsEvalM m tagOf value bitLabel join count position h E).eval H₂ =
          (foldsEvalM m tagOf value bitLabel join count position h E).eval H₁ := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact ⟨relAsked_nil _ _, rfl⟩
  | succ c ih =>
    intro position h G₁ G₂ E hh hE₁ hE₂ hbit₁ hbit₂ hjoin₁ hjoin₂ agree tags
    have hhm : h < m := by rw [hh]; exact Nat.mod_lt _ hm
    set step₁ := (foldGarbleM m (tagOf position) (foldShift m position) (bitMask₁ position) G₁).eval H₁ with hstep₁
    set step₂ := (foldGarbleM m (tagOf position) (foldShift m position) (bitMask₂ position) G₂).eval H₂ with hstep₂
    have j₁ : join position = step₁.2 := by
      have := hjoin₁ position le_rfl (by omega)
      rw [SliceC.eval_foldsGarbleM_succ] at this
      simpa using this
    have j₂ : join position = step₂.2 := by
      have := hjoin₂ position le_rfl (by omega)
      rw [SliceC.eval_foldsGarbleM_succ] at this
      simpa using this
    set β := value.testBit position with hβ
    set h' := (h + (if β then foldShift m position else 0)) % m with hh'
    set E' := (foldEvalM m (tagOf position) (foldShift m position) h (bitLabel position) (join position) E).eval H₁
      with hE'
    have agreeStep : AgreeOn H₁ H₂
        (asked H₁ (foldEvalM m (tagOf position) (foldShift m position) h (bitLabel position) (join position) E)) := by
      have := agree
      rw [asked_foldsEvalM_succ] at this
      exact agreeOn_append_left this
    have agreeRest : AgreeOn H₁ H₂ (asked H₁ (foldsEvalM m tagOf value bitLabel join c (position + 1) h' E')) := by
      have := agree
      rw [asked_foldsEvalM_succ] at this
      exact agreeOn_append_right this
    have stepEq := (eval_eq_of_agreeOn H₁ H₂ _ agreeStep).1
    have next₁ : ∀ ρ, E' ρ = step₁.1 ρ ^^^ (if ρ.val = h' then Δ₁ else 0) := by
      intro ρ
      have := SliceC.foldEvalM_correct H₁ m (tagOf position) (foldShift m position) G₁ E Δ₁ h hhm β
        (bitMask₁ position) hE₁ ρ
      rw [← hbit₁ position le_rfl (by omega), ← hstep₁, ← j₁] at this
      exact this
    have next₂ : ∀ ρ, E' ρ = step₂.1 ρ ^^^ (if ρ.val = h' then Δ₂ else 0) := by
      intro ρ
      have := SliceC.foldEvalM_correct H₂ m (tagOf position) (foldShift m position) G₂ E Δ₂ h hhm β
        (bitMask₂ position) hE₂ ρ
      rw [← hbit₂ position le_rfl (by omega), ← hstep₂, ← j₂, ← stepEq] at this
      exact this
    have hnext : h' = value % 2 ^ (position + 1) % m := by
      have := SliceC.foldHot_eq m value hm 1 position h hh
      simpa [SliceC.foldHot] using this
    obtain ⟨restRel, restEq⟩ := ih (position + 1) h' step₁.1 step₂.1 E' hnext next₁ next₂
      (fun j h1 h2 => hbit₁ j (by omega) (by omega)) (fun j h1 h2 => hbit₂ j (by omega) (by omega))
      (fun j h1 h2 => by
        rw [hjoin₁ j (by omega) (by omega), SliceC.eval_foldsGarbleM_succ]
        simp only
        rw [if_neg (by omega)])
      (fun j h1 h2 => by
        rw [hjoin₂ j (by omega) (by omega), SliceC.eval_foldsGarbleM_succ]
        simp only
        rw [if_neg (by omega)])
      agreeRest (fun j h1 h2 => tags j (by omega) (by omega))
    refine ⟨?_, ?_⟩
    · rw [asked_foldsGarbleM_succ, asked_foldsGarbleM_succ]
      refine relAsked_append ?_ restRel
      rw [asked_foldGarbleM, asked_foldGarbleM]
      refine relAsked_flatMap _ _ _ fun r _ => relAsked_single ?_
      refine labelRel_of_eq hot _ (r.val = h) ?_ ((hE₁ r).symm.trans (hE₂ r))
      rw [tags position le_rfl (by omega) r, hh]
    · simp only [foldsEvalM, FreeQuery.eval_bind]
      rw [← stepEq]
      exact restEq

theorem body_eval_eq (m S q coord i : ℕ) (final₁ final₂ : Fin m → Label)
    (pads : ∀ ρ : Fin m, ∀ j < q, H₁ (hashInput (embed (final₁ ρ)) (bodyTag coord i ρ.val j)) =
      H₂ (hashInput (embed (final₂ ρ)) (bodyTag coord i ρ.val j))) :
    (bodyGarbleM m S q coord i final₁).eval H₁ = (bodyGarbleM m S q coord i final₂).eval H₂ := by
  have hl : ∀ ρ : Fin m, hlong H₁ (embed (final₁ ρ)) (bodyTag coord i ρ.val) q = hlong H₂ (embed (final₂ ρ)) (bodyTag coord i ρ.val) q := by
    intro ρ
    unfold hlong
    congr 1
    funext j
    exact pads ρ j.val j.isLt
  simp only [bodyGarbleM, FreeQuery.eval_bind, eval_tableM, SliceC.eval_padVectorM, FreeQuery.eval_pure, hl]

/-- **The body, two runs.** -/
theorem body_rel (hot : ℕ → Prop) (m S q coord i : ℕ) (final₁ final₂ : Fin m → Label) (Δ₁ Δ₂ : Label) (h : ℕ)
    (same : ∀ ρ : Fin m, final₁ ρ ^^^ (if ρ.val = h then Δ₁ else 0) = final₂ ρ ^^^ (if ρ.val = h then Δ₂ else 0))
    (tags : ∀ r : Fin m, ∀ j < q, hot (bodyTag coord i r.val j) ↔ r.val = h) :
    RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (bodyGarbleM m S q coord i final₁))
      (asked H₂ (bodyGarbleM m S q coord i final₂)) := by
  rw [asked_bodyGarbleM, asked_bodyGarbleM]
  exact relAsked_flatMap _ _ _ fun r _ => relAsked_map _ _ _ _ fun j _ =>
    labelRel_of_eq hot _ _ (tags r j.val j.isLt) (same r)

end GrowFoldBody

/-! ### 6. The fused extraction stage -/

section Stage

open Kriterion.CRT.ExtractSpec Kriterion.CRT.SliceC

variable (H₁ H₂ : HashN) {rb : ℕ} (w : ℕ) (hw : w ≤ rb) (treeTag castTag : ℕ → ℕ → ℕ)

/-- The garbler's stage queries in order, at the garbler's node labels. -/
theorem asked_stage_list (H : HashN) (Δ : Label) (R : Lanes rb) :
    asked H (extStageGarbleM w treeTag castTag Δ R) =
      ((List.range w).flatMap fun n => if n = 0 then [] else
        (List.finRange (2 ^ n)).flatMap fun y =>
          [hashInput (embed (gNode (hashStage H w hw treeTag castTag) (gBit0 (hashStage H w hw treeTag castTag) R) Δ n y.val))
            (treeTag n y.val)]) ++
        (List.finRange (2 ^ w)).flatMap fun leaf => (List.finRange (castAnswers rb)).map fun j =>
          hashInput (embed (gNode (hashStage H w hw treeTag castTag) (gBit0 (hashStage H w hw treeTag castTag) R) Δ w leaf.val))
            (castTag leaf.val j.val) := by
  have ht : ∀ n (x : Fin (2 ^ n)), ((treeGarbleM treeTag Δ (laneBit (reduceTo w R) 0) n).eval H).1 x =
      gNode (hashStage H w hw treeTag castTag) (gBit0 (hashStage H w hw treeTag castTag) R) Δ n x.val :=
    fun n => (eval_treeGarbleM H treeTag Δ (laneBit (reduceTo w R) 0) (hashStage H w hw treeTag castTag)
      (fun _ _ _ => rfl) n).1
  rw [asked_extStageGarbleM, asked_treeGarbleM_list, materialize_eq]
  simp only [ht]

include hw in
/-- **One fused stage, two runs**: the queries, and one evaluator for both. -/
theorem stage_rel (hw1 : 1 ≤ w) (hot cold : ℕ → Prop) (Δ₁ Δ₂ : Label) (R₁ R₂ : Lanes rb) (σ : ℕ)
    (hR : R₁ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₁ = R₂ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₂)
    (hJ : ∀ n, 1 ≤ n → n < w → ((extStageGarbleM w treeTag castTag Δ₁ R₁).eval H₁).joins n =
      ((extStageGarbleM w treeTag castTag Δ₂ R₂).eval H₂).joins n)
    (hP : ((extStageGarbleM w treeTag castTag Δ₁ R₁).eval H₁).pin =
      ((extStageGarbleM w treeTag castTag Δ₂ R₂).eval H₂).pin)
    (agree : AgreeOn H₁ H₂ (asked H₁ (extStageEvalM w treeTag castTag (R₁ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₁)
      (σ % 2 ^ w) ((extStageGarbleM w treeTag castTag Δ₁ R₁).eval H₁).joins
      ((extStageGarbleM w treeTag castTag Δ₁ R₁).eval H₁).pin)))
    (treeHot : ∀ ℓ, 1 ≤ ℓ → ℓ < w → ∀ y < 2 ^ ℓ, hot (treeTag ℓ y) ↔ y = σ % 2 ^ w % 2 ^ ℓ)
    (castHot : ∀ α < 2 ^ w, ∀ j < castAnswers rb, hot (castTag α j) ↔ α = σ % 2 ^ w)
    (treeCold : ∀ ℓ, 1 ≤ ℓ → ℓ < w → ∀ y < 2 ^ ℓ, cold (treeTag ℓ y) ↔ y ≠ σ % 2 ^ w % 2 ^ ℓ)
    (castCold : ∀ α < 2 ^ w, ∀ j < castAnswers rb, cold (castTag α j) ↔ α ≠ σ % 2 ^ w)
    (treeInj : ∀ ℓ y ℓ' y', ℓ < w → y < 2 ^ ℓ → ℓ' < w → y' < 2 ^ ℓ' → treeTag ℓ y = treeTag ℓ' y' →
      ℓ = ℓ' ∧ y = y')
    (castInj : ∀ α j α' j', α < 2 ^ w → j < castAnswers rb → α' < 2 ^ w → j' < castAnswers rb →
      castTag α j = castTag α' j' → α = α')
    (treeCast : ∀ ℓ y α j, ℓ < w → y < 2 ^ ℓ → α < 2 ^ w → j < castAnswers rb → treeTag ℓ y ≠ castTag α j) :
    RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (extStageGarbleM w treeTag castTag Δ₁ R₁))
        (asked H₂ (extStageGarbleM w treeTag castTag Δ₂ R₂)) ∧
      (extStageEvalM w treeTag castTag (R₂ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₂) (σ % 2 ^ w)
          ((extStageGarbleM w treeTag castTag Δ₂ R₂).eval H₂).joins
          ((extStageGarbleM w treeTag castTag Δ₂ R₂).eval H₂).pin).eval H₂ =
        (extStageEvalM w treeTag castTag (R₁ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₁) (σ % 2 ^ w)
          ((extStageGarbleM w treeTag castTag Δ₁ R₁).eval H₁).joins
          ((extStageGarbleM w treeTag castTag Δ₁ R₁).eval H₁).pin).eval H₁ := by
  have al₁ := stage_aligned H₁ w hw treeTag castTag hw1 cold Δ₁ R₁ σ treeCold castCold
  have al₂ := stage_aligned H₂ w hw treeTag castTag hw1 cold Δ₂ R₂ σ treeCold castCold
  set g₁ := (extStageGarbleM w treeTag castTag Δ₁ R₁).eval H₁ with hg₁
  set g₂ := (extStageGarbleM w treeTag castTag Δ₂ R₂).eval H₂ with hg₂
  set sp₁ := hashStage H₁ w hw treeTag castTag with hsp₁
  set sp₂ := hashStage H₂ w hw treeTag castTag with hsp₂
  have prog : extStageEvalM w treeTag castTag (R₂ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₂) (σ % 2 ^ w) g₂.joins g₂.pin =
      extStageEvalM w treeTag castTag (R₁ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₁) (σ % 2 ^ w) g₁.joins g₁.pin := by
    rw [← hR, ← hP]
    exact FlatLayout.extStageEvalM_congr w treeTag castTag _ _ g₂.joins g₁.joins _
      fun n h1 h2 => (hJ n h1 h2).symm
  have evalEq := eval_eq_of_agreeOn H₁ H₂ _ agree
  refine ⟨?_, by rw [prog]; exact evalEq.1.symm⟩
  set s := σ % 2 ^ w with hs
  have hslt : s < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  obtain ⟨_, _, hgj₁, hgp₁, _⟩ := extStageGarbleM_eval H₁ w hw treeTag castTag Δ₁ R₁
  obtain ⟨_, _, hgj₂, hgp₂, _⟩ := extStageGarbleM_eval H₂ w hw treeTag castTag Δ₂ R₂
  have hJ₂ : ∀ n, 1 ≤ n → n < w → g₁.joins n = gJoin sp₂ R₂ Δ₂ n :=
    fun n h1 h2 => (hJ n h1 h2).trans (hgj₂ n h1 h2)
  have hP₂ : g₁.pin = gPin sp₂ R₂ Δ₂ := hP.trans hgp₂
  -- the evaluator's states are common; the active labels give the path
  have agreeSplit := agree
  rw [asked_extStageEvalM] at agreeSplit
  have agreeExp := agreeOn_append_left agreeSplit
  have agreeRounds := agreeOn_append_right agreeSplit
  have inv₁ := initial_inv H₁ w hw treeTag castTag hw1 R₁ Δ₁ σ
  have inv₂ := initial_inv H₂ w hw treeTag castTag hw1 R₂ Δ₂ σ
  rw [← hR, ← (eval_eq_of_agreeOn H₁ H₂ _ agreeExp).1] at inv₂
  have rounds : ∀ r n, 1 ≤ n → n + r ≤ w → ∀ st : StageState rb, Inv sp₁ R₁ Δ₁ s n st → Inv sp₂ R₂ Δ₂ s n st →
      AgreeOn H₁ H₂ (asked H₁ (stageRoundsM w treeTag castTag
        (materialize (reduceTo w (R₁ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₁))) s g₁.joins g₁.pin r n st)) →
      ∀ k, n ≤ k → k ≤ n + r →
        gNode sp₁ (gBit0 sp₁ R₁) Δ₁ k (s % 2 ^ k) ^^^ Δ₁ = gNode sp₂ (gBit0 sp₂ R₂) Δ₂ k (s % 2 ^ k) ^^^ Δ₂ := by
    intro r
    induction r with
    | zero =>
      intro n _ _ st i₁ i₂ _ k hk1 hk2
      have hkn : k = n := by omega
      subst hkn
      exact i₁.1.symm.trans i₂.1
    | succ r ih =>
      intro n hn1 hnr st i₁ i₂ ag k hk1 hk2
      by_cases hkn : k = n
      · subst hkn
        exact i₁.1.symm.trans i₂.1
      · rw [asked_stageRoundsM_succ] at ag
        have agStep := agreeOn_append_left ag
        have agRest := agreeOn_append_right ag
        have i₁' := stageRoundM_inv H₁ w hw treeTag castTag R₁ Δ₁ σ g₁.joins g₁.pin hgj₁ hgp₁ n hn1 (by omega) st i₁
        have i₂' := stageRoundM_inv H₂ w hw treeTag castTag R₂ Δ₂ σ g₁.joins g₁.pin hJ₂ hP₂ n hn1 (by omega) st i₂
        rw [← hR, ← (eval_eq_of_agreeOn H₁ H₂ _ agStep).1] at i₂'
        exact ih (n + 1) (by omega) (by omega) _ i₁' i₂' agRest k (by omega) (by omega)
  have onPath : ∀ k, 1 ≤ k → k ≤ w →
      gNode sp₁ (gBit0 sp₁ R₁) Δ₁ k (s % 2 ^ k) ^^^ Δ₁ = gNode sp₂ (gBit0 sp₂ R₂) Δ₂ k (s % 2 ^ k) ^^^ Δ₂ :=
    fun k hk1 hk2 => rounds (w - 1) 1 le_rfl (by omega) _ inv₁ inv₂ agreeRounds k hk1 (by omega)
  -- off the path the queries are the evaluator's, which both runs share
  have lists : asked H₂ (extStageEvalM w treeTag castTag (R₂ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₂) s g₂.joins g₂.pin) =
      asked H₁ (extStageEvalM w treeTag castTag (R₁ + (σ : ZMod (2 ^ rb)) • deltaLanes rb Δ₁) s g₁.joins g₁.pin) := by
    rw [prog, evalEq.2]
  have shared : ∀ x, x ∈ asked H₁ (extStageGarbleM w treeTag castTag Δ₁ R₁) → ColdAt cold x →
      x ∈ asked H₂ (extStageGarbleM w treeTag castTag Δ₂ R₂) := by
    intro x member coldx
    have inE := al₁.covers x member coldx
    rw [← lists] at inE
    exact (al₂.sound x inE).2
  have offTree : ∀ ℓ y, 1 ≤ ℓ → ℓ < w → y < 2 ^ ℓ → y ≠ s % 2 ^ ℓ →
      gNode sp₁ (gBit0 sp₁ R₁) Δ₁ ℓ y = gNode sp₂ (gBit0 sp₂ R₂) Δ₂ ℓ y := by
    intro ℓ y h1 h2 hy hne
    have member := (mem_garbler_stage H₁ w hw treeTag castTag Δ₁ R₁ _).mpr (Or.inl ⟨ℓ, y, h1, h2, hy, rfl⟩)
    have coldx : ColdAt cold (hashInput (embed (gNode sp₁ (gBit0 sp₁ R₁) Δ₁ ℓ y)) (treeTag ℓ y)) := by
      unfold ColdAt
      rw [hashInput_div]
      exact (treeCold ℓ h1 h2 y hy).mpr hne
    rcases (mem_garbler_stage H₂ w hw treeTag castTag Δ₂ R₂ _).mp (shared _ member coldx) with
      ⟨ℓ', y', h1', h2', hy', same⟩ | ⟨α, j, hα, hj, same⟩
    · have tags := congrArg (· / 2 ^ 128) same
      simp only [hashInput_div] at tags
      obtain ⟨rfl, rfl⟩ := treeInj ℓ y ℓ' y' h2 hy h2' hy' tags
      exact Narrow.embed_injective (hashInput_label_inj same)
    · have tags := congrArg (· / 2 ^ 128) same
      simp only [hashInput_div] at tags
      exact absurd tags (treeCast ℓ y α j h2 hy hα hj)
  have offCast : ∀ α j, α < 2 ^ w → j < castAnswers rb → α ≠ s →
      gNode sp₁ (gBit0 sp₁ R₁) Δ₁ w α = gNode sp₂ (gBit0 sp₂ R₂) Δ₂ w α := by
    intro α j hα hj hne
    have member := (mem_garbler_stage H₁ w hw treeTag castTag Δ₁ R₁ _).mpr (Or.inr ⟨α, j, hα, hj, rfl⟩)
    have coldx : ColdAt cold (hashInput (embed (gNode sp₁ (gBit0 sp₁ R₁) Δ₁ w α)) (castTag α j)) := by
      unfold ColdAt
      rw [hashInput_div]
      exact (castCold α hα j hj).mpr hne
    rcases (mem_garbler_stage H₂ w hw treeTag castTag Δ₂ R₂ _).mp (shared _ member coldx) with
      ⟨ℓ', y', h1', h2', hy', same⟩ | ⟨α', j', hα', hj', same⟩
    · have tags := congrArg (· / 2 ^ 128) same
      simp only [hashInput_div] at tags
      exact absurd tags.symm (treeCast ℓ' y' α j h2' hy' hα hj)
    · have tags := congrArg (· / 2 ^ 128) same
      simp only [hashInput_div] at tags
      obtain rfl := castInj α j α' j' hα hj hα' hj' tags
      exact Narrow.embed_injective (hashInput_label_inj same)
  -- position by position
  rw [asked_stage_list w hw treeTag castTag H₁ Δ₁ R₁, asked_stage_list w hw treeTag castTag H₂ Δ₂ R₂]
  refine relAsked_append (relAsked_flatMap _ _ _ fun n member => ?_)
    (relAsked_flatMap _ _ _ fun leaf _ => relAsked_map _ _ _ _ fun j _ => ?_)
  · rw [List.mem_range] at member
    by_cases hn0 : n = 0
    · rw [if_pos hn0, if_pos hn0]
      exact relAsked_nil _ _
    · rw [if_neg hn0, if_neg hn0]
      refine relAsked_flatMap _ _ _ fun y _ => relAsked_single ?_
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      refine labelRel_of_eq hot _ (y.val = s % 2 ^ n) (treeHot n hn1 member y.val y.isLt) ?_
      by_cases on : y.val = s % 2 ^ n
      · rw [if_pos on, if_pos on, on]
        exact onPath n hn1 (by omega)
      · rw [if_neg on, if_neg on, SliceC.xor_zero_block, SliceC.xor_zero_block]
        exact offTree n y.val hn1 member y.isLt on
  · refine labelRel_of_eq hot _ (leaf.val = s) (castHot leaf.val leaf.isLt j.val j.isLt) ?_
    by_cases on : leaf.val = s
    · rw [if_pos on, if_pos on, on]
      have := onPath w hw1 le_rfl
      rwa [Nat.mod_eq_of_lt hslt] at this
    · rw [if_neg on, if_neg on, SliceC.xor_zero_block, SliceC.xor_zero_block]
      exact offCast leaf.val j.val leaf.isLt j.isLt on

end Stage

/-! ### 7. One odd modulus: the conversion -/

section Conversion

open Kriterion.CRT.ExtractSpec Kriterion.CRT.SliceC

variable (H₁ H₂ : HashN)

theorem modAgree_symm {row : OddRow} {i : ℕ} {p q : ConvPublic} (h : FlatLayout.ModAgree row i p q) :
    FlatLayout.ModAgree row i q p := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨fun n h1 h2 => (a n h1 h2).symm, fun n h1 h2 => (b n h1 h2).symm, fun k hk => (c k hk).symm,
    fun k hk => (d k hk).symm, fun j h1 h2 => (e j h1 h2).symm, fun j h1 h2 => (f j h1 h2).symm⟩

theorem lt_65536_of_pow' {n y : ℕ} (hn : n ≤ 16) (hy : y < 2 ^ n) : y < 65536 :=
  lt_of_lt_of_le hy (le_trans (Nat.pow_le_pow_right (by norm_num) hn) (by norm_num))

theorem extTree_inj {coord i stage w : ℕ} (hc : coord < 2) (hi : i < 128) (hs : stage < 4) (hw : w ≤ 16) :
    ∀ ℓ y ℓ' y', ℓ < w → y < 2 ^ ℓ → ℓ' < w → y' < 2 ^ ℓ' →
      extTreeTag coord i stage ℓ y = extTreeTag coord i stage ℓ' y' → ℓ = ℓ' ∧ y = y' := by
  intro ℓ y ℓ' y' hℓ hy hℓ' hy' same
  have r : TagInRange coord i stage ℓ y 0 := ⟨hc, hi, hs, by omega, lt_65536_of_pow' (by omega) hy, by norm_num⟩
  have r' : TagInRange coord i stage ℓ' y' 0 := ⟨hc, hi, hs, by omega, lt_65536_of_pow' (by omega) hy', by norm_num⟩
  obtain ⟨_, _, _, _, e1, e2, _⟩ := tagCode_injective r r' same
  exact ⟨e1, e2⟩

theorem extCast_inj {coord i stage w L : ℕ} (hc : coord < 2) (hi : i < 128) (hs : stage < 4) (hw : w ≤ 16)
    (hL : castAnswers L ≤ 64) :
    ∀ α j α' j', α < 2 ^ w → j < castAnswers L → α' < 2 ^ w → j' < castAnswers L →
      extCastTag coord i stage α j = extCastTag coord i stage α' j' → α = α' := by
  intro α j α' j' hα hj hα' hj' same
  have r : TagInRange coord i stage 0 α j := ⟨hc, hi, hs, by norm_num, lt_65536_of_pow' hw hα, by omega⟩
  have r' : TagInRange coord i stage 0 α' j' := ⟨hc, hi, hs, by norm_num, lt_65536_of_pow' hw hα', by omega⟩
  exact (tagCode_injective r r' same).2.2.2.2.2.1

theorem extTree_ne_cast {coord i stage w L : ℕ} (hc : coord < 2) (hi : i < 128) (hs : stage < 4) (hw : w ≤ 16)
    (hL : castAnswers L ≤ 64) :
    ∀ ℓ y α j, ℓ < w → y < 2 ^ ℓ → α < 2 ^ w → j < castAnswers L →
      extTreeTag coord i stage ℓ y ≠ extCastTag coord i stage α j := by
  intro ℓ y α j hℓ hy hα hj same
  have r : TagInRange coord i stage ℓ y 0 := ⟨hc, hi, hs, by omega, lt_65536_of_pow' (by omega) hy, by norm_num⟩
  have r' : TagInRange coord i stage 0 α j := ⟨hc, hi, hs, by norm_num, lt_65536_of_pow' hw hα, by omega⟩
  have := (tagCode_injective r r' same).1
  simp [Family.extTree, Family.extCast] at this

theorem wordBit_label (row : OddRow) (hell : row.width0 + row.width1 + 1 = row.ell) (Δ : Label)
    (σ : ℕ) (gb0 gb1 eb0 eb1 : ℕ → Label) (gnext enext : Lanes (row.ell - row.width0 - row.width1))
    (hb0 : ∀ n < row.width0, eb0 n = gb0 n ^^^ (if σ.testBit n then Δ else 0))
    (hb1 : ∀ n < row.width1, eb1 n = gb1 n ^^^ (if (σ / 2 ^ row.width0).testBit n then Δ else 0))
    (hn1 : enext = gnext + ((σ / 2 ^ row.width0 / 2 ^ row.width1 : ℕ) :
      ZMod (2 ^ (row.ell - row.width0 - row.width1))) • deltaLanes (row.ell - row.width0 - row.width1) Δ) :
    ∀ p < row.ell, wordBit row eb0 eb1 (laneBit enext 0) p =
      wordBit row gb0 gb1 (laneBit gnext 0) p ^^^ (if σ.testBit p then Δ else 0) := by
  intro p hp
  simp only [wordBit]
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

/-- **One odd modulus's conversion, two runs**: the queries, and the final one-hots around one evaluator. -/
theorem conv_rel (hot cold : ℕ → Prop) (coord i : ℕ) (row : OddRow) (m : ℕ) (Δ₁ Δ₂ : Label) (W₁ W₂ : Lanes row.ell)
    (σ : ℕ) (pub₁ pub₂ : ConvPublic)
    (h0 : 1 ≤ row.width0) (h1 : 1 ≤ row.width1) (hell : row.width0 + row.width1 + 1 = row.ell)
    (hk0 : row.width0 ≤ row.keep) (hk1 : row.keep ≤ row.ell) (hm : 0 < m) (hσ : σ < 2 ^ row.ell)
    (hcoord : coord < 2) (hi : i < 128) (hw0r : row.width0 ≤ 16) (hw1r : row.width1 ≤ 16)
    (hc0 : castAnswers row.ell ≤ 64) (hc1 : castAnswers (row.ell - row.width0) ≤ 64)
    (hW : W₁ + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ₁ = W₂ + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ₂)
    (hpJ₁ : pub₁.stageJoin i = ((conversionGarbleM coord i row m Δ₁ W₁).eval H₁).stageJoins)
    (hpP₁ : pub₁.stagePin i = ((conversionGarbleM coord i row m Δ₁ W₁).eval H₁).stagePins)
    (hpG₁ : pub₁.growJoin i = ((conversionGarbleM coord i row m Δ₁ W₁).eval H₁).growJoins)
    (hpF₁ : pub₁.foldJoin i = ((conversionGarbleM coord i row m Δ₁ W₁).eval H₁).foldJoins)
    (hpJ₂ : pub₂.stageJoin i = ((conversionGarbleM coord i row m Δ₂ W₂).eval H₂).stageJoins)
    (hpP₂ : pub₂.stagePin i = ((conversionGarbleM coord i row m Δ₂ W₂).eval H₂).stagePins)
    (hpG₂ : pub₂.growJoin i = ((conversionGarbleM coord i row m Δ₂ W₂).eval H₂).growJoins)
    (hpF₂ : pub₂.foldJoin i = ((conversionGarbleM coord i row m Δ₂ W₂).eval H₂).foldJoins)
    (hmod : FlatLayout.ModAgree row i pub₁ pub₂)
    (agree : AgreeOn H₁ H₂ (asked H₁ (conversionEvalM coord i row m σ
      (W₁ + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ₁) pub₁)))
    (hotTags : ConvTags (fun τ => ¬ hot τ) coord i row m σ) (coldTags : ConvTags cold coord i row m σ) :
    RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (conversionGarbleM coord i row m Δ₁ W₁))
        (asked H₂ (conversionGarbleM coord i row m Δ₂ W₂)) ∧
      ∀ ρ : Fin m, ((conversionGarbleM coord i row m Δ₁ W₁).eval H₁).final ρ ^^^ (if ρ.val = σ % m then Δ₁ else 0) =
        ((conversionGarbleM coord i row m Δ₂ W₂).eval H₂).final ρ ^^^ (if ρ.val = σ % m then Δ₂ else 0) := by
  have hw0 : row.width0 ≤ row.ell := by omega
  have hw1' : row.width1 ≤ row.ell - row.width0 := by omega
  -- the finals, around one evaluator
  have fin₁ := (conversion_final H₁ coord i row m Δ₁ W₁ σ pub₁ h0 h1 hell hk0 hk1 hm hσ hpJ₁ hpP₁ hpG₁ hpF₁).2
  have fin₂ := (conversion_final H₂ coord i row m Δ₂ W₂ σ pub₂ h0 h1 hell hk0 hk1 hm hσ hpJ₂ hpP₂ hpG₂ hpF₂).2
  have convProg : conversionEvalM coord i row m σ (W₂ + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ₂) pub₂ =
      conversionEvalM coord i row m σ (W₁ + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ₁) pub₁ := by
    rw [← hW]
    exact FlatLayout.conversionEvalM_congr coord i row m σ _ pub₂ pub₁ (modAgree_symm hmod)
  have convEq := (eval_eq_of_agreeOn H₁ H₂ _ agree).1
  have finals : ∀ ρ : Fin m,
      ((conversionGarbleM coord i row m Δ₁ W₁).eval H₁).final ρ ^^^ (if ρ.val = σ % m then Δ₁ else 0) =
        ((conversionGarbleM coord i row m Δ₂ W₂).eval H₂).final ρ ^^^ (if ρ.val = σ % m then Δ₂ else 0) := by
    intro ρ
    rw [← fin₁ ρ, ← fin₂ ρ, convProg, convEq]
  refine ⟨?_, finals⟩
  -- the published material is each run's garbler's
  obtain ⟨j0, j1, p0, p1, gJ, fJ⟩ := hmod
  simp only [conversionGarbleM, FreeQuery.eval_bind, FreeQuery.eval_pure] at hpJ₁ hpP₁ hpG₁ hpF₁ hpJ₂ hpP₂ hpG₂ hpF₂
  have hJ0₁ : pub₁.stageJoin i 0 =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₁ W₁).eval H₁).joins := by
    rw [hpJ₁]; rfl
  have hJ0₂ : pub₂.stageJoin i 0 =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₂ W₂).eval H₂).joins := by
    rw [hpJ₂]; rfl
  have hJ1₁ : pub₁.stageJoin i 1 = ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ₁
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₁ W₁).eval H₁).next).eval H₁).joins := by
    rw [hpJ₁]; rfl
  have hJ1₂ : pub₂.stageJoin i 1 = ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ₂
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₂ W₂).eval H₂).next).eval H₂).joins := by
    rw [hpJ₂]; rfl
  have hP0₁ : (Parity.pinExpand row.ell (pinOfBlocks (row.ell - 1) fun k => pub₁.stagePin i 0 k.val)) =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₁ W₁).eval H₁).pin := by
    rw [hpP₁]; exact expand_pinOfBlocks_atNat _ _ (extStageGarbleM_pin_even _ _ _ _ _ _)
  have hP0₂ : (Parity.pinExpand row.ell (pinOfBlocks (row.ell - 1) fun k => pub₂.stagePin i 0 k.val)) =
      ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₂ W₂).eval H₂).pin := by
    rw [hpP₂]; exact expand_pinOfBlocks_atNat _ _ (extStageGarbleM_pin_even _ _ _ _ _ _)
  have hP1₁ : (Parity.pinExpand (row.ell - row.width0) (pinOfBlocks (row.ell - row.width0 - 1) fun k => pub₁.stagePin i 1 k.val)) =
      ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ₁
        ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₁ W₁).eval H₁).next).eval H₁).pin := by
    rw [hpP₁]; exact expand_pinOfBlocks_atNat _ _ (extStageGarbleM_pin_even _ _ _ _ _ _)
  have hP1₂ : (Parity.pinExpand (row.ell - row.width0) (pinOfBlocks (row.ell - row.width0 - 1) fun k => pub₂.stagePin i 1 k.val)) =
      ((extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ₂
        ((extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₂ W₂).eval H₂).next).eval H₂).pin := by
    rw [hpP₂]; exact expand_pinOfBlocks_atNat _ _ (extStageGarbleM_pin_even _ _ _ _ _ _)
  set g0₁ := (extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₁ W₁).eval H₁ with hg0₁
  set g0₂ := (extStageGarbleM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) Δ₂ W₂).eval H₂ with hg0₂
  set g1₁ := (extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ₁ g0₁.next).eval H₁ with hg1₁
  set g1₂ := (extStageGarbleM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) Δ₂ g0₂.next).eval H₂ with hg1₂
  -- stage 0
  have hs0₁ := extStage_correct H₁ row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0) h0 Δ₁ W₁ σ
  have hs0₂ := extStage_correct H₂ row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0) h0 Δ₂ W₂ σ
  simp only at hs0₁ hs0₂
  -- the evaluator's queries, in its four blocks (run 1's published material)
  have agreeParts := agree
  simp only [conversionEvalM, asked_bind] at agreeParts
  rw [hJ0₁, hP0₁] at agreeParts
  obtain ⟨hl0₁, hb0₁, hn0₁⟩ := hs0₁
  rw [hn0₁, hJ1₁, hP1₁, hpG₁] at agreeParts
  have agree0 := agreeOn_append_left agreeParts
  have agree123 := agreeOn_append_right agreeParts
  have agree1 := agreeOn_append_left agree123
  have agree23 := agreeOn_append_right agree123
  have agree2 := agreeOn_append_left agree23
  have agree3 := agreeOn_append_right agree23
  obtain ⟨rel0, e0Eq⟩ := stage_rel H₁ H₂ row.width0 hw0 (extTreeTag coord i 0) (extCastTag coord i 0) h0 hot cold Δ₁ Δ₂
    W₁ W₂ σ hW
    (fun n h1' h2' => by rw [← hJ0₁, ← hJ0₂]; exact j0 n h1' h2')
    (by rw [← hP0₁, ← hP0₂]; exact congrArg (Parity.pinExpand _) (FlatLayout.pinOfBlocks_congr _ _ _ fun k => p0 k.val k.isLt))
    agree0
    (fun ℓ h1' h2' y hy => not_iff_not.mp (hotTags.tree0 ℓ h1' h2' y hy))
    (fun α hα j hj => not_iff_not.mp (hotTags.cast0 α hα j hj))
    coldTags.tree0 coldTags.cast0
    (extTree_inj hcoord hi (by norm_num) hw0r) (extCast_inj hcoord hi (by norm_num) hw0r hc0)
    (extTree_ne_cast hcoord hi (by norm_num) hw0r hc0)
  obtain ⟨hl0₂, hb0₂, hn0₂⟩ := hs0₂
  rw [e0Eq] at hl0₂ hb0₂ hn0₂
  set e0 := (extStageEvalM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0)
    (W₁ + (σ : ZMod (2 ^ row.ell)) • deltaLanes row.ell Δ₁) (σ % 2 ^ row.width0) g0₁.joins g0₁.pin).eval H₁ with he0
  -- stage 1
  have hR1 : g0₁.next + ((σ / 2 ^ row.width0 : ℕ) : ZMod (2 ^ (row.ell - row.width0))) •
      deltaLanes (row.ell - row.width0) Δ₁ =
      g0₂.next + ((σ / 2 ^ row.width0 : ℕ) : ZMod (2 ^ (row.ell - row.width0))) •
        deltaLanes (row.ell - row.width0) Δ₂ := hn0₁.symm.trans hn0₂
  have hs1₁ := extStage_correct H₁ row.width1 hw1' (extTreeTag coord i 1) (extCastTag coord i 1) h1 Δ₁ g0₁.next
    (σ / 2 ^ row.width0)
  have hs1₂ := extStage_correct H₂ row.width1 hw1' (extTreeTag coord i 1) (extCastTag coord i 1) h1 Δ₂ g0₂.next
    (σ / 2 ^ row.width0)
  simp only at hs1₁ hs1₂
  obtain ⟨rel1, e1Eq⟩ := stage_rel H₁ H₂ row.width1 hw1' (extTreeTag coord i 1) (extCastTag coord i 1) h1 hot cold
    Δ₁ Δ₂ g0₁.next g0₂.next (σ / 2 ^ row.width0) hR1
    (fun n h1' h2' => by rw [← hJ1₁, ← hJ1₂]; exact j1 n h1' h2')
    (by rw [← hP1₁, ← hP1₂]; exact congrArg (Parity.pinExpand _) (FlatLayout.pinOfBlocks_congr _ _ _ fun k => p1 k.val k.isLt))
    agree1
    (fun ℓ h1' h2' y hy => not_iff_not.mp (hotTags.tree1 ℓ h1' h2' y hy))
    (fun α hα j hj => not_iff_not.mp (hotTags.cast1 α hα j hj))
    coldTags.tree1 coldTags.cast1
    (extTree_inj hcoord hi (by norm_num) hw1r) (extCast_inj hcoord hi (by norm_num) hw1r hc1)
    (extTree_ne_cast hcoord hi (by norm_num) hw1r hc1)
  obtain ⟨_, hb1₁, hn1₁⟩ := hs1₁
  obtain ⟨_, hb1₂, hn1₂⟩ := hs1₂
  rw [e1Eq] at hb1₂ hn1₂
  set e1 := (extStageEvalM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1)
    (g0₁.next + ((σ / 2 ^ row.width0 : ℕ) : ZMod (2 ^ (row.ell - row.width0))) • deltaLanes (row.ell - row.width0) Δ₁)
    (σ / 2 ^ row.width0 % 2 ^ row.width1) g1₁.joins g1₁.pin).eval H₁ with he1
  -- the word's bit labels
  set bitMask₁ := wordBit row g0₁.bits g1₁.bits (laneBit g1₁.next 0) with hbitMask₁
  set bitMask₂ := wordBit row g0₂.bits g1₂.bits (laneBit g1₂.next 0) with hbitMask₂
  set bitLabel := wordBit row e0.bits e1.bits (laneBit e1.next 0) with hbitLabel
  have hbit₁ := wordBit_label row hell Δ₁ σ g0₁.bits g1₁.bits e0.bits e1.bits g1₁.next e1.next hb0₁ hb1₁ hn1₁
  have hbit₂ := wordBit_label row hell Δ₂ σ g0₂.bits g1₂.bits e0.bits e1.bits g1₂.next e1.next hb0₂ hb1₂ hn1₂
  -- growth
  set grown₁ := (growGarbleM (growTag coord i) row.width0 (stored fun leaf => g0₁.leaves leaf.val)
    (row.keep - row.width0)).eval H₁ with hgrown₁
  set grown₂ := (growGarbleM (growTag coord i) row.width0 (stored fun leaf => g0₂.leaves leaf.val)
    (row.keep - row.width0)).eval H₂ with hgrown₂
  obtain ⟨levels, rel2⟩ := grow_rel H₁ H₂ hot (growTag coord i) row.width0 (stored fun leaf => g0₁.leaves leaf.val)
    (stored fun leaf => g0₂.leaves leaf.val) (stored fun leaf => e0.leaves leaf.val) Δ₁ Δ₂ σ bitMask₁ bitMask₂ bitLabel
    (row.keep - row.width0)
    (by intro x; simp only [stored_eq]; exact hl0₁ x.val x.isLt)
    (by intro x; simp only [stored_eq]; exact hl0₂ x.val x.isLt)
    (fun j hj => hbit₁ j (by omega)) (fun j hj => hbit₂ j (by omega))
    (fun k hk => by
      have := gJ (row.width0 + k) (by omega) (by omega)
      rw [hpG₁, hpG₂] at this
      exact this)
    agree2
    (fun k hk s => not_iff_not.mp (hotTags.grow k hk s))
  -- reindex and folds
  have hkeep : row.width0 + (row.keep - row.width0) = row.keep := by omega
  have hhot : σ % 2 ^ (row.width0 + (row.keep - row.width0)) % m = σ % 2 ^ row.keep % m := by rw [hkeep]
  set Egrown := (growEvalM (growTag coord i) σ bitLabel (fun p => grown₁.2 p ^^^ bitMask₁ p) row.width0
    (stored fun leaf => e0.leaves leaf.val) (row.keep - row.width0)).eval H₁ with hEgrown
  have re₁ := fun ρ => reindex_invariant (row.width0 + (row.keep - row.width0)) m grown₁.1 Egrown Δ₁
    (σ % 2 ^ (row.width0 + (row.keep - row.width0))) (Nat.mod_lt _ (Nat.two_pow_pos _))
    (fun x => (levels (row.keep - row.width0) le_rfl x).1) ρ
  have re₂ := fun ρ => reindex_invariant (row.width0 + (row.keep - row.width0)) m grown₂.1 Egrown Δ₂
    (σ % 2 ^ (row.width0 + (row.keep - row.width0))) (Nat.mod_lt _ (Nat.two_pow_pos _))
    (fun x => (levels (row.keep - row.width0) le_rfl x).2) ρ
  obtain ⟨rel3, _⟩ := folds_rel H₁ H₂ hot m hm (foldTag coord i) σ Δ₁ Δ₂ bitMask₁ bitMask₂ bitLabel (pub₁.foldJoin i)
    (row.ell - row.keep) row.keep (σ % 2 ^ row.keep % m) (reindex _ grown₁.1 m) (reindex _ grown₂.1 m)
    (reindex _ Egrown m) rfl (by intro ρ; rw [re₁ ρ, hhot]) (by intro ρ; rw [re₂ ρ, hhot])
    (fun j _ h2 => hbit₁ j (by omega)) (fun j _ h2 => hbit₂ j (by omega))
    (fun j _ _ => by rw [hpF₁])
    (fun j h1' h2' => by rw [fJ j h1' (by omega), hpF₂])
    agree3
    (fun j h1' h2' r => not_iff_not.mp (hotTags.fold j h1' h2' r))
  simp only [conversionGarbleM, asked_bind, asked_pure, List.append_nil]
  exact relAsked_append rel0 (relAsked_append rel1 (relAsked_append rel2 rel3))

end Conversion

/-! ### 8. One modulus -/

section Modulus

open Kriterion.CRT.ExtractSpec Kriterion.CRT.SliceC

variable (H₁ H₂ : HashN)

/-- The evaluator side of an alignment asks only where the hashes agree. -/
theorem agreeOn_of_cold {cold : ℕ → Prop} (coldAgree : ∀ x, ColdAt cold x → H₁ x = H₂ x) {g e : List ℕ}
    (aligned : Aligned (ColdAt cold) g e) : AgreeOn H₁ H₂ e :=
  fun x member => coldAgree x (aligned.sound x member).1

/-- **One modulus, two runs**: the queries of its conversion and body, and its body's outputs. -/
theorem mod_rel (hot cold : ℕ → Prop) (T : CrtTable) (S coord : ℕ) (Δ₁ Δ₂ : Label) (v : ℕ) (hT : CorrectTable T)
    (hv : v < 2 ^ T.inputBits) (hcoord : coord < 2) (ranges : Paths.TableRanges T S)
    (pub₁ pub₂ : ConvPublic) (chunks₁ chunks₂ : ℕ → ChunkGarbled T.castWidth) (chunksE : ℕ → ChunkEval T.castWidth)
    (hL₁ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunks₁ c).leaves α ^^^ (if α = T.chunkValue v c then Δ₁ else 0))
    (hL₂ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunks₂ c).leaves α ^^^ (if α = T.chunkValue v c then Δ₂ else 0))
    (hC₁ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunks₁ c).casts α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ₁ else 0))
    (hC₂ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunks₂ c).casts α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ₂ else 0))
    (i : Fin T.count)
    (hpJ₁ : pub₁.stageJoin i.val = ((modGarbleM T S coord Δ₁ chunks₁ i).eval H₁).stageJoins)
    (hpP₁ : pub₁.stagePin i.val = ((modGarbleM T S coord Δ₁ chunks₁ i).eval H₁).stagePins)
    (hpG₁ : pub₁.growJoin i.val = ((modGarbleM T S coord Δ₁ chunks₁ i).eval H₁).growJoins)
    (hpF₁ : pub₁.foldJoin i.val = ((modGarbleM T S coord Δ₁ chunks₁ i).eval H₁).foldJoins)
    (hpJ₂ : pub₂.stageJoin i.val = ((modGarbleM T S coord Δ₂ chunks₂ i).eval H₂).stageJoins)
    (hpP₂ : pub₂.stagePin i.val = ((modGarbleM T S coord Δ₂ chunks₂ i).eval H₂).stagePins)
    (hpG₂ : pub₂.growJoin i.val = ((modGarbleM T S coord Δ₂ chunks₂ i).eval H₂).growJoins)
    (hpF₂ : pub₂.foldJoin i.val = ((modGarbleM T S coord Δ₂ chunks₂ i).eval H₂).foldJoins)
    (hmod : ∀ row, T.kind i = .odd row → FlatLayout.ModAgree row i.val pub₁ pub₂)
    (coldAgree : ∀ x, ColdAt cold x → H₁ x = H₂ x)
    (pads : ∀ (f₁ f₂ : Fin (T.modulus i) → Label) (ρ : Fin (T.modulus i)), ∀ j < T.padAnswers S i,
      H₁ (hashInput (embed (f₁ ρ)) (bodyTag coord i.val ρ.val j)) = H₂ (hashInput (embed (f₂ ρ)) (bodyTag coord i.val ρ.val j)))
    (hotConv : ∀ row, T.kind i = .odd row →
      ConvTags (fun τ => ¬ hot τ) coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v))
    (coldConv : ∀ row, T.kind i = .odd row → ConvTags cold coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v))
    (hotBody : ∀ r : Fin (T.modulus i), ∀ j < T.padAnswers S i,
      hot (bodyTag coord i.val r.val j) ↔ r.val = v % T.modulus i) :
    RelAsked hot (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (modGarbleM T S coord Δ₁ chunks₁ i))
        (asked H₂ (modGarbleM T S coord Δ₂ chunks₂ i)) ∧
      ((modGarbleM T S coord Δ₁ chunks₁ i).eval H₁).body = ((modGarbleM T S coord Δ₂ chunks₂ i).eval H₂).body := by
  have hm := hT.modulus_pos i
  cases hk : T.kind i with
  | chunkZero =>
    have hmod0 : T.modulus i = 2 ^ T.chunkWidth 0 := hT.chunkZero i hk
    have hc0 := chunkCount_pos T hT.chunkBits_pos hT.inputBits_pos
    have same : ∀ ρ : Fin (T.modulus i),
        (stored fun ρ : Fin (T.modulus i) => (chunks₁ 0).leaves ρ.val) ρ ^^^
            (if ρ.val = v % T.modulus i then Δ₁ else 0) =
          (stored fun ρ : Fin (T.modulus i) => (chunks₂ 0).leaves ρ.val) ρ ^^^
            (if ρ.val = v % T.modulus i then Δ₂ else 0) := by
      intro ρ
      simp only [stored_eq]
      have hρ : ρ.val < 2 ^ T.chunkWidth 0 := hmod0 ▸ ρ.isLt
      have e₁ := hL₁ 0 hc0 ρ.val hρ
      have e₂ := hL₂ 0 hc0 ρ.val hρ
      rw [chunkValue_zero, ← hmod0] at e₁ e₂
      rw [← e₁, ← e₂]
    refine ⟨?_, ?_⟩
    · simp only [modGarbleM, hk, asked_bind, asked_pure, List.append_nil]
      exact body_rel H₁ H₂ hot _ S _ coord i.val _ _ Δ₁ Δ₂ (v % T.modulus i) same hotBody
    · simp only [modGarbleM, hk, FreeQuery.eval_bind, FreeQuery.eval_pure]
      exact body_eval_eq H₁ H₂ _ S _ coord i.val _ _ (pads _ _)
  | odd row =>
    obtain ⟨h0, h1, hell, hk0, hk1, hcw, hcount⟩ := hT.odd i row hk
    have rr := ranges.rows i row hk
    have hi : i.val < 128 := lt_of_lt_of_le i.isLt ranges.count
    have hσlt : T.wordValue (T.modulus i) v < 2 ^ row.ell := wordValue_lt T (T.modulus i) v row.ell hm hcount
    have hσ : T.wordValue (T.modulus i) v ≡ v [MOD T.modulus i] := wordValue_modEq T hT.chunkBits_pos (T.modulus i) v hv
    have hW₁ := truthWord_label T (T.modulus i) row.ell hcw (fun c leaf => (chunks₁ c).casts leaf)
      (fun c leaf => (chunksE c).casts leaf) Δ₁ v hC₁
    have hW₂ := truthWord_label T (T.modulus i) row.ell hcw (fun c leaf => (chunks₂ c).casts leaf)
      (fun c leaf => (chunksE c).casts leaf) Δ₂ v hC₂
    simp only [modGarbleM, hk, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_materializeM]
      at hpJ₁ hpP₁ hpG₁ hpF₁ hpJ₂ hpP₂ hpG₂ hpF₂
    have al := conversion_aligned H₁ coord i.val row (T.modulus i) Δ₁
      (truthWord T (T.modulus i) row.ell fun c leaf => (chunks₁ c).casts leaf) (T.wordValue (T.modulus i) v) pub₁ cold
      h0 h1 hell hk0 hk1 hm hpJ₁ hpP₁ hpG₁ hpF₁ (coldConv row hk)
    obtain ⟨relC, finals⟩ := conv_rel H₁ H₂ hot cold coord i.val row (T.modulus i) Δ₁ Δ₂
      (truthWord T (T.modulus i) row.ell fun c leaf => (chunks₁ c).casts leaf)
      (truthWord T (T.modulus i) row.ell fun c leaf => (chunks₂ c).casts leaf) (T.wordValue (T.modulus i) v) pub₁ pub₂
      h0 h1 hell hk0 hk1 hm hσlt hcoord hi rr.width0 rr.width1 rr.cast0 rr.cast1 (hW₁.symm.trans hW₂)
      hpJ₁ hpP₁ hpG₁ hpF₁ hpJ₂ hpP₂ hpG₂ hpF₂ (hmod row hk) (agreeOn_of_cold H₁ H₂ coldAgree al)
      (hotConv row hk) (coldConv row hk)
    have hσ' : T.wordValue (T.modulus i) v % T.modulus i = v % T.modulus i := hσ
    rw [hσ'] at finals
    refine ⟨?_, ?_⟩
    · simp only [modGarbleM, hk, asked_bind, asked_pure, asked_materializeM, eval_materializeM, List.nil_append,
        List.append_nil]
      exact relAsked_append relC (body_rel H₁ H₂ hot _ S _ coord i.val _ _ Δ₁ Δ₂ (v % T.modulus i) finals hotBody)
    · simp only [modGarbleM, hk, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_materializeM]
      exact body_eval_eq H₁ H₂ _ S _ coord i.val _ _ (pads _ _)

end Modulus

/-! ### 9. The tags of a coordinate -/

section Tags

theorem tagCode_lt_pow40 {fam coord idx stage level slot part : ℕ} (hfam : fam < 8)
    (r : TagInRange coord idx stage level slot part) : tagCode fam coord idx stage level slot part < 2 ^ 40 := by
  have := r.coord; have := r.idx; have := r.stage; have := r.level; have := r.slot; have := r.part
  rw [show (2 : ℕ) ^ 40 = 1099511627776 by norm_num]
  unfold tagCode
  omega

theorem cold_iff {T : CrtTable} {u : AffineInput} {τ : ℕ} {P : Prop} (base : hotTag T u τ = false ↔ P)
    (lt : τ < 2 ^ 40) : Cold T u τ ↔ P :=
  ⟨fun h => base.mp h.1, fun h => ⟨base.mpr h, lt⟩⟩

theorem convTags_congr {P Q : ℕ → Prop} (h : ∀ τ, P τ ↔ Q τ) {coord i : ℕ} {row : OddRow} {m σ : ℕ}
    (t : ConvTags P coord i row m σ) : ConvTags Q coord i row m σ :=
  ⟨fun ℓ h1 h2 y hy => (h _).symm.trans (t.tree0 ℓ h1 h2 y hy), fun α hα j hj => (h _).symm.trans (t.cast0 α hα j hj),
    fun ℓ h1 h2 y hy => (h _).symm.trans (t.tree1 ℓ h1 h2 y hy), fun α hα j hj => (h _).symm.trans (t.cast1 α hα j hj),
    fun k hk s => (h _).symm.trans (t.grow k hk s), fun j h1 h2 r => (h _).symm.trans (t.fold j h1 h2 r)⟩

theorem coordTags_congr {P Q : ℕ → Prop} (h : ∀ τ, P τ ↔ Q τ) {T : CrtTable} {S coord v : ℕ}
    (t : CoordTags P T S coord v) : CoordTags Q T S coord v :=
  ⟨fun c hc n h1 h2 s => (h _).symm.trans (t.chunkTree c hc n h1 h2 s),
    fun c hc leaf j hj => (h _).symm.trans (t.chunkCast c hc leaf j hj),
    fun i row hk => convTags_congr h (t.conv i row hk), fun i r j hj => (h _).symm.trans (t.body i r j hj)⟩

open Kriterion.CRT.Paths in
/-- **The tag conditions at the cold tags with their range.** -/
theorem coordTags_Cold (T : CrtTable) (u : AffineInput) (S κ : ℕ) (hκ : κ < 2) (ranges : TableRanges T S) :
    CoordTags (Cold T u) T S κ (coordValue u κ) := by
  have base := coordTags_cold T u S κ hκ ranges
  refine ⟨fun c hc n hn1 hn s => ?_, fun c hc leaf j hj => ?_, fun i row hk => ?_, fun i r j hj => ?_⟩
  · have hw := ranges.chunkWidth c hc
    have range : TagInRange κ c 0 n s.val 0 :=
      ⟨hκ, by have := ranges.chunkCount; omega, by norm_num, by omega, lt_65536_of_pow (by omega) s.isLt,
        by norm_num⟩
    exact cold_iff (base.chunkTree c hc n hn1 hn s) (tagCode_lt_pow40 (by simp [Family.chunkTree]) range)
  · have hw := ranges.chunkWidth c hc
    have range : TagInRange κ c 0 0 leaf.val j :=
      ⟨hκ, by have := ranges.chunkCount; omega, by norm_num, by norm_num, lt_65536_of_pow hw leaf.isLt,
        by have := ranges.castAnswers; omega⟩
    exact cold_iff (base.chunkCast c hc leaf j hj) (tagCode_lt_pow40 (by simp [Family.chunkCast]) range)
  · obtain ⟨w0, w1, keep, ell, cast0, cast1⟩ := ranges.rows i row hk
    have hi : i.val < 128 := by have := ranges.count; have := i.isLt; omega
    have hm := ranges.modulus i
    have b := base.conv i row hk
    refine ⟨fun ℓ hℓ1 hℓ y hy => ?_, fun α hα j hj => ?_, fun ℓ hℓ1 hℓ y hy => ?_, fun α hα j hj => ?_,
      fun k hkeep s => ?_, fun j hj1 hj2 r => ?_⟩
    · have range : TagInRange κ i.val 0 ℓ y 0 :=
        ⟨hκ, hi, by norm_num, by omega, lt_65536_of_pow (by omega) hy, by norm_num⟩
      exact cold_iff (b.tree0 ℓ hℓ1 hℓ y hy) (tagCode_lt_pow40 (by simp [Family.extTree]) range)
    · have range : TagInRange κ i.val 0 0 α j :=
        ⟨hκ, hi, by norm_num, by norm_num, lt_65536_of_pow w0 hα, by omega⟩
      exact cold_iff (b.cast0 α hα j hj) (tagCode_lt_pow40 (by simp [Family.extCast]) range)
    · have range : TagInRange κ i.val 1 ℓ y 0 :=
        ⟨hκ, hi, by norm_num, by omega, lt_65536_of_pow (by omega) hy, by norm_num⟩
      exact cold_iff (b.tree1 ℓ hℓ1 hℓ y hy) (tagCode_lt_pow40 (by simp [Family.extTree]) range)
    · have range : TagInRange κ i.val 1 0 α j :=
        ⟨hκ, hi, by norm_num, by norm_num, lt_65536_of_pow w1 hα, by omega⟩
      exact cold_iff (b.cast1 α hα j hj) (tagCode_lt_pow40 (by simp [Family.extCast]) range)
    · have range : TagInRange κ i.val 0 (row.width0 + k) s.val 0 :=
        ⟨hκ, hi, by norm_num, by omega, lt_65536_of_pow (by omega) s.isLt, by norm_num⟩
      exact cold_iff (b.grow k hkeep s) (tagCode_lt_pow40 (by simp [Family.grow]) range)
    · have range : TagInRange κ i.val 0 j r.val 0 :=
        ⟨hκ, hi, by norm_num, by omega, by have := r.isLt; omega, by norm_num⟩
      exact cold_iff (b.fold j hj1 hj2 r) (tagCode_lt_pow40 (by simp [Family.fold]) range)
  · have hi : i.val < 128 := by have := ranges.count; have := i.isLt; omega
    have range : TagInRange κ i.val 0 0 r.val j :=
      ⟨hκ, hi, by norm_num, by norm_num, by have := ranges.modulus i; have := r.isLt; omega,
        by have := ranges.pads i; omega⟩
    exact cold_iff (base.body i r j hj) (tagCode_lt_pow40 (by simp [Family.body]) range)

end Tags

/-! ### 10. One coordinate -/

section Coordinate

open Kriterion.CRT.ExtractSpec Kriterion.CRT.SliceC

variable (H₁ H₂ : HashN)

theorem convAgree_of_eq {T : CrtTable} {p q : ConvPublic} (same : p = q) : FlatLayout.ConvAgree T p q := by
  subst same
  exact ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

/-- **One coordinate, two runs**, for a correct table whose fields fit `tagCode`. -/
theorem coord_rel (T : CrtTable) (S coord : ℕ) (hT : CorrectTable T) (ranges : Paths.TableRanges T S)
    (hcoord : coord < 2) (u : AffineInput) (hv : coordValue u coord < 2 ^ T.inputBits)
    (Δ₁ Δ₂ : Label) (Z₁ Z₂ : ℕ → Label)
    (hE : ∀ j < T.inputBits, Z₁ j ^^^ (if (coordValue u coord).testBit j then Δ₁ else 0) =
      Z₂ j ^^^ (if (coordValue u coord).testBit j then Δ₂ else 0))
    (hpub : FlatLayout.ConvAgree T ((coordGarbleM T S coord Δ₁ Z₁).eval H₁).pub
      ((coordGarbleM T S coord Δ₂ Z₂).eval H₂).pub)
    (hagree : ∀ (label₁ label₂ : Block) (τ : ℕ), τ < 2 ^ 40 →
      ¬ (tagFamily τ ≤ 5 ∧ tagCoord τ = coord ∧ hotTag T u τ = true) →
      H₁ (hashInput label₁ τ) = H₂ (hashInput label₂ τ)) :
    RelAsked (fun τ => hotTag T u τ = true) (embed (Δ₁ ^^^ Δ₂))
        (asked H₁ (coordGarbleM T S coord Δ₁ Z₁)) (asked H₂ (coordGarbleM T S coord Δ₂ Z₂)) ∧
      ((coordGarbleM T S coord Δ₁ Z₁).eval H₁).residue = ((coordGarbleM T S coord Δ₂ Z₂).eval H₂).residue ∧
      ((coordGarbleM T S coord Δ₁ Z₁).eval H₁).padSum = ((coordGarbleM T S coord Δ₂ Z₂).eval H₂).padSum ∧
      ((coordGarbleM T S coord Δ₁ Z₁).eval H₁).offset = ((coordGarbleM T S coord Δ₂ Z₂).eval H₂).offset ∧
      ((coordGarbleM T S coord Δ₁ Z₁).eval H₁).hint = ((coordGarbleM T S coord Δ₂ Z₂).eval H₂).hint := by
  set v := coordValue u coord with hvdef
  have coldAgree : ∀ x, ColdAt (Cold T u) x → H₁ x = H₂ x := by
    intro x hx
    unfold ColdAt Cold at hx
    obtain ⟨cold, range⟩ := hx
    rw [← hashInput_self x]
    refine hagree _ _ _ range fun ⟨_, _, hot⟩ => ?_
    rw [cold] at hot
    exact Bool.false_ne_true hot
  have tagsHot : CoordTags (fun τ => ¬ (hotTag T u τ = true)) T S coord v :=
    coordTags_congr (fun τ => by simp) (coordTags_cold T u S coord hcoord ranges)
  have tagsCold : CoordTags (Cold T u) T S coord v := coordTags_Cold T u S coord hcoord ranges
  obtain ⟨fJ₁, fP₁, fM₁, _, _, _⟩ := coordGarbleM_fields H₁ T S coord Δ₁ Z₁
  obtain ⟨fJ₂, fP₂, fM₂, _, _, _⟩ := coordGarbleM_fields H₂ T S coord Δ₂ Z₂
  simp only at fJ₁ fP₁ fM₁ fJ₂ fP₂ fM₂
  obtain ⟨cJ, cP, mA⟩ := hpub
  -- the chunks
  have chunkPin : ∀ (Δ : Label) (Z : ℕ → Label) (H : HashN) c (hc : c < T.chunkCount),
      (fun k : Fin (T.castWidth - 1) => ((coordGarbleM T S coord Δ Z).eval H).pub.chunkPin c k.val) =
        pinBlocks (Parity.pinHalf T.castWidth ((chunkGarbleM T coord Δ Z c).eval H).pin) →
      ((chunkGarbleM T coord Δ Z c).eval H).pin =
        Parity.pinExpand T.castWidth (pinOfBlocks (T.castWidth - 1)
          fun k => ((coordGarbleM T S coord Δ Z).eval H).pub.chunkPin c k.val) := by
    intro Δ Z H c hc same
    rw [same, pinOfBlocks_pinBlocks_all,
      Parity.pinExpand_pinHalf _ _ (chunkGarbleM_pin_even H T coord Δ Z c)]
  have chunkFacts : ∀ c (hc : c < T.chunkCount),
      RelAsked (fun τ => hotTag T u τ = true) (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (chunkGarbleM T coord Δ₁ Z₁ c))
          (asked H₂ (chunkGarbleM T coord Δ₂ Z₂ c)) ∧
        (chunkEvalM T coord (fun j => Z₂ j ^^^ (if v.testBit j then Δ₂ else 0)) v
            ((chunkGarbleM T coord Δ₂ Z₂ c).eval H₂).joins ((chunkGarbleM T coord Δ₂ Z₂ c).eval H₂).pin c).eval H₂ =
          (chunkEvalM T coord (fun j => Z₁ j ^^^ (if v.testBit j then Δ₁ else 0)) v
            ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).joins ((chunkGarbleM T coord Δ₁ Z₁ c).eval H₁).pin c).eval H₁ := by
    intro c hc
    refine chunk_rel H₁ H₂ T coord c _ Δ₁ Δ₂ Z₁ Z₂ v hE (fun n h1 h2 => ?_) ?_
      (agreeOn_of_cold H₁ H₂ coldAgree (chunk_aligned H₁ T coord Δ₁ Z₁ c v (Cold T u) (tagsCold.chunkTree c hc)
        (tagsCold.chunkCast c hc)))
      (fun n h1 h2 s => not_iff_not.mp (tagsHot.chunkTree c hc n h1 h2 s))
      (fun leaf j hj => not_iff_not.mp (tagsHot.chunkCast c hc leaf j hj))
    · have := cJ c hc n h1 h2
      rw [fJ₁ c, fJ₂ c, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc] at this
      exact this
    · rw [chunkPin Δ₁ Z₁ H₁ c hc (fP₁ c hc), chunkPin Δ₂ Z₂ H₂ c hc (fP₂ c hc)]
      exact congrArg (Parity.pinExpand _) (FlatLayout.pinOfBlocks_congr _ _ _ fun k => cP c hc k.val k.isLt)
  set chunks₁ := atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ₁ Z₁ c.val).eval H₁)
    (ChunkGarbled.empty T.castWidth) with hchunks₁
  set chunks₂ := atNat (fun c : Fin T.chunkCount => (chunkGarbleM T coord Δ₂ Z₂ c.val).eval H₂)
    (ChunkGarbled.empty T.castWidth) with hchunks₂
  set chunksE := atNat (fun c : Fin T.chunkCount =>
    (chunkEvalM T coord (fun j => Z₁ j ^^^ (if v.testBit j then Δ₁ else 0)) v
      ((chunkGarbleM T coord Δ₁ Z₁ c.val).eval H₁).joins ((chunkGarbleM T coord Δ₁ Z₁ c.val).eval H₁).pin c.val).eval H₁)
    (ChunkEval.empty T.castWidth) with hchunksE
  have hL₁ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunks₁ c).leaves α ^^^ (if α = T.chunkValue v c then Δ₁ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunks₁, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    exact (chunk_correct H₁ T coord Δ₁ Z₁ v c).1 α hα
  have hL₂ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).leaves α = (chunks₂ c).leaves α ^^^ (if α = T.chunkValue v c then Δ₂ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunks₂, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    simp only
    rw [← (chunkFacts c hc).2]
    exact (chunk_correct H₂ T coord Δ₂ Z₂ v c).1 α hα
  have hC₁ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunks₁ c).casts α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ₁ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunks₁, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    exact (chunk_correct H₁ T coord Δ₁ Z₁ v c).2 α hα
  have hC₂ : ∀ c < T.chunkCount, ∀ α < 2 ^ T.chunkWidth c,
      (chunksE c).casts α = (chunks₂ c).casts α + (if α = T.chunkValue v c then deltaLanes T.castWidth Δ₂ else 0) := by
    intro c hc α hα
    rw [hchunksE, hchunks₂, atNat_of_lt _ _ hc, atNat_of_lt _ _ hc]
    simp only
    rw [← (chunkFacts c hc).2]
    exact (chunk_correct H₂ T coord Δ₂ Z₂ v c).2 α hα
  -- the moduli
  have pads : ∀ (i : Fin T.count) (f₁ f₂ : Fin (T.modulus i) → Label) (ρ : Fin (T.modulus i)), ∀ j < T.padAnswers S i,
      H₁ (hashInput (embed (f₁ ρ)) (bodyTag coord i.val ρ.val j)) = H₂ (hashInput (embed (f₂ ρ)) (bodyTag coord i.val ρ.val j)) := by
    intro i f₁ f₂ ρ j hj
    have hi : i.val < 128 := by have := ranges.count; have := i.isLt; omega
    have range : TagInRange coord i.val 0 0 ρ.val j :=
      ⟨hcoord, hi, by norm_num, by norm_num, by have := ranges.modulus i; have := ρ.isLt; omega,
        by have := ranges.pads i; omega⟩
    refine hagree _ _ _ (tagCode_lt_pow40 (by simp [Family.body]) range) fun ⟨fam, _, _⟩ => ?_
    unfold bodyTag at fam
    rw [tagFamily_tagCode range] at fam
    simp [Family.body] at fam
  have modFacts : ∀ i : Fin T.count,
      RelAsked (fun τ => hotTag T u τ = true) (embed (Δ₁ ^^^ Δ₂)) (asked H₁ (modGarbleM T S coord Δ₁ chunks₁ i))
          (asked H₂ (modGarbleM T S coord Δ₂ chunks₂ i)) ∧
        ((modGarbleM T S coord Δ₁ chunks₁ i).eval H₁).body = ((modGarbleM T S coord Δ₂ chunks₂ i).eval H₂).body :=
    fun i => mod_rel H₁ H₂ _ (Cold T u) T S coord Δ₁ Δ₂ v hT hv hcoord ranges _ _ chunks₁ chunks₂ chunksE
      hL₁ hL₂ hC₁ hC₂ i (fM₁ i).1 (fM₁ i).2.1 (fM₁ i).2.2.1 (fM₁ i).2.2.2 (fM₂ i).1 (fM₂ i).2.1 (fM₂ i).2.2.1
      (fM₂ i).2.2.2 (fun row hk => mA i row hk) coldAgree (pads i) (tagsHot.conv i) (tagsCold.conv i)
      (fun r j hj => not_iff_not.mp (tagsHot.body i r j hj))
  have bodies : ∀ i : Fin T.count,
      ((modGarbleM T S coord Δ₁ chunks₁ i).eval H₁).body = ((modGarbleM T S coord Δ₂ chunks₂ i).eval H₂).body :=
    fun i => (modFacts i).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [coordGarbleM, asked_bind, asked_tableM, asked_pure, List.append_nil, eval_tableM]
    exact relAsked_append (relAsked_flatMap _ _ _ fun c _ => (chunkFacts c.val c.isLt).1)
      (relAsked_flatMap _ _ _ fun i _ => (modFacts i).1)
  all_goals
    simp only [coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure]
    rw [← hchunks₁, ← hchunks₂]
    simp only [bodies]

end Coordinate

end Rel

/-- **Two garbler runs of one coordinate** (the real table, `Entry.table`). -/
theorem coord_relational (H₁ H₂ : HashN) (S coord : ℕ) (hS : S ≤ 1000) (hcoord : coord < 2) (u : AffineInput)
    (Δ₁ Δ₂ : Label) (Z₁ Z₂ : ℕ → Label)
    (hE : ∀ j < 254, Z₁ j ^^^ (if (coordValue u coord).testBit j then Δ₁ else 0) =
      Z₂ j ^^^ (if (coordValue u coord).testBit j then Δ₂ else 0))
    (hpub : FlatLayout.ConvAgree Entry.table ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).pub
      ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).pub)
    (hagree : ∀ (label₁ label₂ : Block) (τ : ℕ), τ < 2 ^ 40 →
      ¬ (tagFamily τ ≤ 5 ∧ tagCoord τ = coord ∧ hotTag Entry.table u τ = true) →
      H₁ (hashInput label₁ τ) = H₂ (hashInput label₂ τ)) :
    RelAsked (fun τ => hotTag Entry.table u τ = true) (embed (Δ₁ ^^^ Δ₂))
        (asked H₁ (coordGarbleM Entry.table S coord Δ₁ Z₁)) (asked H₂ (coordGarbleM Entry.table S coord Δ₂ Z₂)) ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).residue = ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).residue ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).padSum = ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).padSum ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).offset = ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).offset ∧
      ((coordGarbleM Entry.table S coord Δ₁ Z₁).eval H₁).hint = ((coordGarbleM Entry.table S coord Δ₂ Z₂).eval H₂).hint := by
  have hv : coordValue u coord < 2 ^ Entry.table.inputBits := by
    show coordValue u coord < 2 ^ 254
    unfold coordValue
    split
    · exact lt_trans (ZMod.val_lt u.x) (by show baseFieldModulus < 2 ^ 254; unfold baseFieldModulus; norm_num)
    · exact lt_trans (ZMod.val_lt u.y) (by show baseFieldModulus < 2 ^ 254; unfold baseFieldModulus; norm_num)
  exact Rel.coord_rel H₁ H₂ Entry.table S coord SliceC.bn254_correctTable (Paths.bn254_ranges S hS) hcoord u hv Δ₁ Δ₂
    Z₁ Z₂ (fun j hj => hE j hj) hpub hagree

/-! ### The published material, as the view holds it -/

theorem modAgree_trans {row : OddRow} {i : ℕ} {p q r : ConvPublic} (h : FlatLayout.ModAgree row i p q)
    (h' : FlatLayout.ModAgree row i q r) : FlatLayout.ModAgree row i p r := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  obtain ⟨a', b', c', d', e', f'⟩ := h'
  exact ⟨fun n h1 h2 => (a n h1 h2).trans (a' n h1 h2), fun n h1 h2 => (b n h1 h2).trans (b' n h1 h2),
    fun k hk => (c k hk).trans (c' k hk), fun k hk => (d k hk).trans (d' k hk),
    fun j h1 h2 => (e j h1 h2).trans (e' j h1 h2), fun j h1 h2 => (f j h1 h2).trans (f' j h1 h2)⟩

theorem convAgree_symm {T : CrtTable} {p q : ConvPublic} (h : FlatLayout.ConvAgree T p q) :
    FlatLayout.ConvAgree T q p :=
  ⟨fun c hc n h1 h2 => (h.1 c hc n h1 h2).symm, fun c hc k hk => (h.2.1 c hc k hk).symm,
    fun i row hk => Rel.modAgree_symm (h.2.2 i row hk)⟩

theorem convAgree_trans {T : CrtTable} {p q r : ConvPublic} (h : FlatLayout.ConvAgree T p q)
    (h' : FlatLayout.ConvAgree T q r) : FlatLayout.ConvAgree T p r :=
  ⟨fun c hc n h1 h2 => (h.1 c hc n h1 h2).trans (h'.1 c hc n h1 h2),
    fun c hc k hk => (h.2.1 c hc k hk).trans (h'.2.1 c hc k hk),
    fun i row hk => modAgree_trans (h.2.2 i row hk) (h'.2.2 i row hk)⟩

/-- Equal flat vectors give agreeing published material. -/
theorem convAgree_of_convVector_eq {p q : ConvPublic} (same : Entry.convVector p = Entry.convVector q) :
    FlatLayout.ConvAgree Entry.table p q := by
  have hp := EntryDelivery.convAgree_convOf p
  have hq := EntryDelivery.convAgree_convOf q
  rw [same] at hp
  exact convAgree_trans (convAgree_symm hp) hq

end Kriterion.CRT.Privacy.Align
