/-
**The replay asks only cold tags, for any published material** (for the containment input of (B)).

`Align` proves that the evaluator's queries are the garbler's cold ones for the garbler's own published
material. Route M's replay reads a stage-1 source instead, so the published material is arbitrary. The tags the
evaluator asks do not depend on that material: at every tree level it asks every slot except the one its own value
selects, at every cast every leaf except its value, at every fold every residue except its hot one, and at every
body every residue except `v mod m`. This file proves it block by block, on every hash:

* `AllAsked P p`: every input `p` asks, on every hash, satisfies `P`, with its combinators;
* `treeEvalM_all`, `growEvalM_all`, `chunkEvalM_all`, `expandM_all`, `stageRoundsM_all`, `extStageEvalM_all`,
  `foldsEvalM_all`, `conversionEvalM_all`, `bodyEvalM_all`, `modEvalM_all`, `coordEvalM_all`: the evaluator's blocks
  ask only at slots off their hot slots;
* `foldsEvalM_snd`, `conversionEvalM_snd`: the hot index the folds end at is data-independent;
* **`coordEvalM_cold`**, **`replayConv_cold`**: on the real table, every conversion or body input of the replay has a
  cold tag (`hotTag = false`), whatever the published material, records and labels.
-/

import Proof.Privacy.CRT.Hidden.AlignEntry
import Proof.Correctness.CRT.RealTable

namespace Kriterion.CRT.Privacy.Contain

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_askN asked_h128M asked_tableM asked_hlongM
  asked_castM asked_padVectorM asked_materializeM asked_evalStepM asked_expandM asked_subtreeM_list hashInput_div
  closedSlot closedSlot_lt closedSlot_mod closedSlot_testBit closedSlot_zero CoordTags ConvTags coordTags_cold
  slot_lt slot_mod_start)

/-! ### Every asked input -/

section AllAsked

variable {α β : Type}

/-- Every input the program asks, on every hash, satisfies `P`. -/
def AllAsked (P : ℕ → Prop) (program : CM α) : Prop := ∀ H : HashN, ∀ x ∈ asked H program, P x

namespace AllAsked

variable {P : ℕ → Prop}

theorem pure' (value : α) : AllAsked P (Pure.pure value : CM α) := fun H x inside => by
  rw [asked_pure] at inside
  exact absurd inside List.not_mem_nil

theorem bind {program : CM α} {next : α → CM β} (first : AllAsked P program) (second : ∀ a, AllAsked P (next a)) :
    AllAsked P (program >>= next) := fun H x inside => by
  rw [asked_bind] at inside
  rcases List.mem_append.mp inside with a | b
  · exact first H x a
  · exact second _ H x b

/-- A bind whose continuation only needs to hold at the program's value. -/
theorem bind' {program : CM α} {next : α → CM β} (first : AllAsked P program)
    (second : ∀ H : HashN, ∀ x ∈ asked H (next (program.eval H)), P x) : AllAsked P (program >>= next) :=
  fun H x inside => by
    rw [asked_bind] at inside
    rcases List.mem_append.mp inside with a | b
    · exact first H x a
    · exact second H x b

theorem tableM {count : ℕ} {program : Fin count → CM α} (each : ∀ i, AllAsked P (program i)) :
    AllAsked P (Kriterion.CRT.tableM count program) := fun H x inside => by
  rw [asked_tableM] at inside
  obtain ⟨i, _, x_in⟩ := List.mem_flatMap.mp inside
  exact each i H x x_in

theorem ite {c : Prop} [Decidable c] {yes no : CM α} (onYes : c → AllAsked P yes) (onNo : ¬ c → AllAsked P no) :
    AllAsked P (if c then yes else no) := by
  split
  · exact onYes ‹_›
  · exact onNo ‹_›

theorem askN {n : ℕ} (holds : P n) : AllAsked P (Kriterion.CRT.askN n) := fun H x inside => by
  rw [asked_askN, List.mem_singleton] at inside
  rw [inside]
  exact holds

theorem h128M {label : Block} {tag : ℕ} (holds : P (hashInput label tag)) : AllAsked P (Kriterion.CRT.h128M label tag) :=
  fun H x inside => by
    rw [asked_h128M, List.mem_singleton] at inside
    rw [inside]
    exact holds

theorem hlongM {label : Block} {tagOf : ℕ → ℕ} {count : ℕ} (holds : ∀ j < count, P (hashInput label (tagOf j))) :
    AllAsked P (Kriterion.CRT.hlongM label tagOf count) := fun H x inside => by
  rw [asked_hlongM] at inside
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp inside
  exact holds j.val j.isLt

theorem castM {l : ℕ} {label : Block} {tagOf : ℕ → ℕ} (holds : ∀ j < castAnswers l, P (hashInput label (tagOf j))) :
    AllAsked P (Kriterion.CRT.castM l label tagOf) := fun H x inside => by
  rw [asked_castM] at inside
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp inside
  exact holds j.val j.isLt

theorem padVectorM {m S q : ℕ} {label : Block} {tagOf : ℕ → ℕ} (holds : ∀ j < q, P (hashInput label (tagOf j))) :
    AllAsked P (Kriterion.CRT.padVectorM m S q label tagOf) := fun H x inside => by
  rw [asked_padVectorM] at inside
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp inside
  exact holds j.val j.isLt

theorem materializeM {width : ℕ} (lanes : Lanes width) : AllAsked P (Kriterion.CRT.materializeM lanes) :=
  fun H x inside => by
    rw [asked_materializeM] at inside
    exact absurd inside List.not_mem_nil

theorem mono {Q : ℕ → Prop} {program : CM α} (holds : AllAsked P program) (imp : ∀ x, P x → Q x) :
    AllAsked Q program := fun H x inside => imp x (holds H x inside)

end AllAsked

end AllAsked

/-! ### Trees and growth -/

section Trees

variable (P : ℕ → Prop)

theorem evalStepM_all (n : ℕ) (tagOf : ℕ → ℕ) (active : Fin (2 ^ n)) (bitLabel join : Block)
    (parent : Fin (2 ^ n) → Block) (off : ∀ s : Fin (2 ^ n), s ≠ active → ∀ label, P (hashInput label (tagOf s.val))) :
    AllAsked P (evalStepM n tagOf active bitLabel join parent) := fun H x inside => by
  rw [asked_evalStepM] at inside
  obtain ⟨s, _, x_in⟩ := List.mem_flatMap.mp inside
  by_cases hot : s = active
  · rw [if_pos hot] at x_in
    exact absurd x_in List.not_mem_nil
  · rw [if_neg hot, List.mem_singleton] at x_in
    rw [x_in]
    exact off s hot _

/-- **The tree** with the value `value`: every hashed level `n` asks only slots other than `value mod 2 ^ n`. -/
theorem treeEvalM_all (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Block) (total : ℕ)
    (off : ∀ n, 1 ≤ n → n < total → ∀ s : Fin (2 ^ n), s.val ≠ value % 2 ^ n → ∀ label,
      P (hashInput label (tagOf n s.val))) :
    ∀ levels, levels ≤ total → AllAsked P (treeEvalM tagOf value bitLabel join levels)
  | 0, _ => AllAsked.pure' _
  | n + 1, le => by
      simp only [treeEvalM]
      refine AllAsked.bind (treeEvalM_all tagOf value bitLabel join total off n (by omega)) fun previous => ?_
      refine AllAsked.ite (fun _ => AllAsked.pure' _) fun nonzero => ?_
      exact evalStepM_all P n (tagOf n) _ _ _ _ fun s ne label =>
        off n (Nat.one_le_iff_ne_zero.mpr nonzero) (by omega) s (fun same => ne (Fin.ext same)) label

/-- **The growth** at levels `start, ..., start + count - 1`. -/
theorem growEvalM_all (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Block) (start : ℕ)
    (labels : Fin (2 ^ start) → Block) (total : ℕ)
    (off : ∀ k < total, ∀ s : Fin (2 ^ (start + k)), s.val ≠ value % 2 ^ (start + k) → ∀ label,
      P (hashInput label (tagOf (start + k) s.val))) :
    ∀ count, count ≤ total → AllAsked P (growEvalM tagOf value bitLabel join start labels count)
  | 0, _ => AllAsked.pure' _
  | k + 1, le => by
      simp only [growEvalM]
      refine AllAsked.bind (growEvalM_all tagOf value bitLabel join start labels total off k (by omega))
        fun previous => ?_
      exact evalStepM_all P (start + k) (tagOf (start + k)) _ _ _ _ fun s ne label =>
        off k (by omega) s (fun same => ne (Fin.ext same)) label

end Trees

/-! ### A chunk -/

theorem chunkEvalM_all (P : ℕ → Prop) (T : CrtTable) (coord : ℕ) (labels : ℕ → Block) (v : ℕ) (joins : ℕ → Block)
    (pin : Lanes T.castWidth) (c : ℕ)
    (tree : ∀ n, 1 ≤ n → n < T.chunkWidth c → ∀ s : Fin (2 ^ n), s.val ≠ T.chunkValue v c % 2 ^ n → ∀ label,
      P (hashInput label (chunkTreeTag coord c n s.val)))
    (cast : ∀ leaf : Fin (2 ^ T.chunkWidth c), leaf.val ≠ T.chunkValue v c → ∀ j < castAnswers T.castWidth,
      ∀ label, P (hashInput label (chunkCastTag coord c leaf.val j))) :
    AllAsked P (chunkEvalM T coord labels v joins pin c) := by
  unfold chunkEvalM
  dsimp only
  refine AllAsked.bind (treeEvalM_all P _ _ _ _ (T.chunkWidth c) tree _ le_rfl) fun tree' => ?_
  refine AllAsked.bind (AllAsked.tableM fun leaf => ?_) fun _ => AllAsked.pure' _
  exact AllAsked.ite (fun _ => AllAsked.pure' _) fun ne => AllAsked.castM fun j hj => cast leaf ne j hj _

/-! ### The fused extraction stage -/

section Stage

variable (P : ℕ → Prop) {rb : ℕ} (w : ℕ) (treeTag castTag : ℕ → ℕ → ℕ) (value : ℕ)

/-- **An expansion off the path**: at a slot of level `start` other than the value's, the subtree's nodes and leaves
are off the path. -/
theorem expandM_all (start slot : ℕ) (label : Block) (state : StageState rb) (hstart : 1 ≤ start) (hw : start ≤ w)
    (hslot : slot < 2 ^ start) (away : slot ≠ value % 2 ^ start)
    (tree : ∀ ℓ, 1 ≤ ℓ → ℓ < w → ∀ y < 2 ^ ℓ, y ≠ value % 2 ^ ℓ → ∀ lbl, P (hashInput lbl (treeTag ℓ y)))
    (cast : ∀ α < 2 ^ w, α ≠ value → ∀ j < castAnswers rb, ∀ lbl, P (hashInput lbl (castTag α j))) :
    AllAsked P (expandM w treeTag castTag start slot label state) := fun H x inside => by
  rw [asked_expandM, List.mem_append, asked_subtreeM_list] at inside
  rcases inside with inTree | inCast
  · obtain ⟨d', hd', inLevel⟩ := List.mem_flatMap.mp inTree
    rw [List.mem_range] at hd'
    obtain ⟨t, _, x_in⟩ := List.mem_flatMap.mp inLevel
    rw [List.mem_singleton] at x_in
    rw [x_in]
    have hy : slot + 2 ^ start * t.val < 2 ^ (start + d') := slot_lt hslot t.isLt
    refine tree (start + d') (by omega) (by omega) _ hy (fun same => away ?_) _
    have hmod := slot_mod_start (t := t.val) hslot
    rw [same, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_add_right start d'))] at hmod
    exact hmod.symm
  · obtain ⟨t, _, x_in⟩ := List.mem_flatMap.mp inCast
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp x_in
    have hα : slot + 2 ^ start * t.val < 2 ^ w := by
      have := slot_lt hslot t.isLt
      rwa [show start + (w - start) = w by omega] at this
    refine cast _ hα (fun same => away ?_) j.val j.isLt _
    have hmod := slot_mod_start (t := t.val) hslot
    rw [same] at hmod
    exact hmod.symm

theorem closedSlot_ne (n : ℕ) : closedSlot value n ≠ value % 2 ^ (n + 1) := by
  intro same
  have bit := closedSlot_testBit value n
  rw [same, Nat.testBit_mod_two_pow] at bit
  simp at bit

theorem stageRoundM_all (sub : Lanes w) (joins : ℕ → Block) (pin : Lanes rb) (n : ℕ) (state : StageState rb)
    (hn : n < w)
    (tree : ∀ ℓ, 1 ≤ ℓ → ℓ < w → ∀ y < 2 ^ ℓ, y ≠ value % 2 ^ ℓ → ∀ lbl, P (hashInput lbl (treeTag ℓ y)))
    (cast : ∀ α < 2 ^ w, α ≠ value → ∀ j < castAnswers rb, ∀ lbl, P (hashInput lbl (castTag α j))) :
    AllAsked P (stageRoundM w treeTag castTag sub value joins pin n state) := by
  unfold stageRoundM
  dsimp only
  split
  · rename_i bit
    have slotEq : value % 2 ^ n = closedSlot value n := by
      unfold closedSlot
      rw [if_pos bit]
    rw [slotEq]
    exact expandM_all P w treeTag castTag value (n + 1) _ _ _ (by omega) (by omega) (closedSlot_lt value n)
      (closedSlot_ne value n) tree cast
  · rename_i bit
    have slotEq : value % 2 ^ n + 2 ^ n = closedSlot value n := by
      unfold closedSlot
      rw [if_neg bit]
    rw [slotEq]
    exact expandM_all P w treeTag castTag value (n + 1) _ _ _ (by omega) (by omega) (closedSlot_lt value n)
      (closedSlot_ne value n) tree cast

theorem stageRoundsM_all (sub : Lanes w) (joins : ℕ → Block) (pin : Lanes rb)
    (tree : ∀ ℓ, 1 ≤ ℓ → ℓ < w → ∀ y < 2 ^ ℓ, y ≠ value % 2 ^ ℓ → ∀ lbl, P (hashInput lbl (treeTag ℓ y)))
    (cast : ∀ α < 2 ^ w, α ≠ value → ∀ j < castAnswers rb, ∀ lbl, P (hashInput lbl (castTag α j))) :
    ∀ remaining n (state : StageState rb), n + remaining ≤ w →
      AllAsked P (stageRoundsM w treeTag castTag sub value joins pin remaining n state)
  | 0, _, _, _ => AllAsked.pure' _
  | r + 1, n, state, le => by
      simp only [stageRoundsM]
      exact AllAsked.bind (stageRoundM_all P w treeTag castTag value sub joins pin n state (by omega) tree cast)
        fun next => stageRoundsM_all sub joins pin tree cast r (n + 1) next (by omega)

/-- **A fused extraction stage** at the stage value `value`. -/
theorem extStageEvalM_all (remainder : Lanes rb) (joins : ℕ → Block) (pin : Lanes rb) (hw : 1 ≤ w)
    (tree : ∀ ℓ, 1 ≤ ℓ → ℓ < w → ∀ y < 2 ^ ℓ, y ≠ value % 2 ^ ℓ → ∀ lbl, P (hashInput lbl (treeTag ℓ y)))
    (cast : ∀ α < 2 ^ w, α ≠ value → ∀ j < castAnswers rb, ∀ lbl, P (hashInput lbl (castTag α j))) :
    AllAsked P (extStageEvalM w treeTag castTag remainder value joins pin) := by
  unfold extStageEvalM
  dsimp only
  rw [← closedSlot_zero]
  refine AllAsked.bind (expandM_all P w treeTag castTag value 1 _ _ _ le_rfl hw (closedSlot_lt value 0)
    (closedSlot_ne value 0) tree cast) fun afterZero => ?_
  exact AllAsked.bind (stageRoundsM_all P w treeTag castTag value _ joins pin tree cast (w - 1) 1 afterZero
    (by omega)) fun _ => AllAsked.pure' _

end Stage

/-! ### The folds -/

section Folds

variable (P : ℕ → Prop) (m : ℕ) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Block)

theorem foldEvalM_all (tag : ℕ → ℕ) (shift hot : ℕ) (bitLabel' join' : Block) (labels : Fin m → Block)
    (off : ∀ r : Fin m, r.val ≠ hot → ∀ label, P (hashInput label (tag r.val))) :
    AllAsked P (foldEvalM m tag shift hot bitLabel' join' labels) := by
  unfold foldEvalM
  refine AllAsked.bind (AllAsked.tableM fun r => ?_) fun _ => AllAsked.pure' _
  exact AllAsked.ite (fun _ => AllAsked.pure' _) fun ne => AllAsked.h128M (off r ne _)

/-- **The folds**, from the hot index `value mod 2 ^ position mod m`. -/
theorem foldsEvalM_all (hm : 0 < m) (total start : ℕ)
    (off : ∀ j, start ≤ j → j < start + total → ∀ r : Fin m, r.val ≠ value % 2 ^ j % m → ∀ label,
      P (hashInput label (tagOf j r.val))) :
    ∀ count position hot (labels : Fin m → Block), start ≤ position → position + count ≤ start + total →
      hot = value % 2 ^ position % m → AllAsked P (foldsEvalM m tagOf value bitLabel join count position hot labels)
  | 0, _, _, _, _, _, _ => AllAsked.pure' _
  | count + 1, position, hot, labels, lower, upper, hotEq => by
      simp only [foldsEvalM]
      refine AllAsked.bind (foldEvalM_all P m (tagOf position) _ hot _ _ labels fun r ne label =>
        off position lower (by omega) r (by rw [← hotEq]; exact ne) label) fun next => ?_
      refine foldsEvalM_all hm total start off count (position + 1) _ next (by omega) (by omega) ?_
      have := SliceC.foldHot_eq m value hm 1 position hot hotEq
      simpa [SliceC.foldHot] using this

/-- The hot index the folds end at does not depend on the labels or the hash. -/
theorem foldsEvalM_snd (H : HashN) :
    ∀ count position hot (labels : Fin m → Block),
      ((foldsEvalM m tagOf value bitLabel join count position hot labels).eval H).2 =
        SliceC.foldHot m value count position hot
  | 0, _, _, _ => rfl
  | count + 1, position, hot, labels => by
      simp only [foldsEvalM, FreeQuery.eval_bind]
      rw [foldsEvalM_snd H count (position + 1)]
      rfl

end Folds

/-! ### One odd modulus's conversion, the body, one modulus, one coordinate -/

section Coordinate

variable (P : ℕ → Prop)

/-- The tag conditions of `ConvTags`, read one way: every tag off the value's path satisfies `P` at every label. -/
structure ConvOff (coord i : ℕ) (row : OddRow) (m σ : ℕ) : Prop where
  tree0 : ∀ ℓ, 1 ≤ ℓ → ℓ < row.width0 → ∀ y < 2 ^ ℓ, y ≠ σ % 2 ^ row.width0 % 2 ^ ℓ → ∀ label,
    P (hashInput label (extTreeTag coord i 0 ℓ y))
  cast0 : ∀ α < 2 ^ row.width0, α ≠ σ % 2 ^ row.width0 → ∀ j < castAnswers row.ell, ∀ label,
    P (hashInput label (extCastTag coord i 0 α j))
  tree1 : ∀ ℓ, 1 ≤ ℓ → ℓ < row.width1 → ∀ y < 2 ^ ℓ, y ≠ σ / 2 ^ row.width0 % 2 ^ row.width1 % 2 ^ ℓ → ∀ label,
    P (hashInput label (extTreeTag coord i 1 ℓ y))
  cast1 : ∀ α < 2 ^ row.width1, α ≠ σ / 2 ^ row.width0 % 2 ^ row.width1 → ∀ j < castAnswers (row.ell - row.width0),
    ∀ label, P (hashInput label (extCastTag coord i 1 α j))
  grow : ∀ k < row.keep - row.width0, ∀ s : Fin (2 ^ (row.width0 + k)), s.val ≠ σ % 2 ^ (row.width0 + k) →
    ∀ label, P (hashInput label (growTag coord i (row.width0 + k) s.val))
  fold : ∀ j, row.keep ≤ j → j < row.keep + (row.ell - row.keep) → ∀ r : Fin m, r.val ≠ σ % 2 ^ j % m →
    ∀ label, P (hashInput label (foldTag coord i j r.val))

theorem conversionEvalM_all (coord i : ℕ) (row : OddRow) (m σ : ℕ) (word : Lanes row.ell) (pub : ConvPublic)
    (hm : 0 < m) (h0 : 1 ≤ row.width0) (h1 : 1 ≤ row.width1)
    (off : ConvOff P coord i row m σ) :
    AllAsked P (conversionEvalM coord i row m σ word pub) := by
  unfold conversionEvalM
  dsimp only
  refine AllAsked.bind (extStageEvalM_all P row.width0 _ _ (σ % 2 ^ row.width0) word _ _ h0 off.tree0 off.cast0)
    fun e0 => ?_
  refine AllAsked.bind (extStageEvalM_all P row.width1 _ _ (σ / 2 ^ row.width0 % 2 ^ row.width1) e0.next _ _ h1
    off.tree1 off.cast1) fun e1 => ?_
  refine AllAsked.bind (growEvalM_all P _ σ _ _ row.width0 _ (row.keep - row.width0) off.grow _ le_rfl)
    fun grown => ?_
  exact foldsEvalM_all P m (foldTag coord i) σ _ _ hm (row.ell - row.keep) row.keep off.fold _ _ _ _ le_rfl
    le_rfl rfl

theorem conversionEvalM_snd (H : HashN) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (word : Lanes row.ell)
    (pub : ConvPublic) (hm : 0 < m) (hk : row.keep ≤ row.ell) :
    ((conversionEvalM coord i row m σ word pub).eval H).2 = σ % 2 ^ row.ell % m := by
  unfold conversionEvalM
  simp only [FreeQuery.eval_bind]
  rw [foldsEvalM_snd, SliceC.foldHot_eq m σ hm _ _ _ rfl, show row.keep + (row.ell - row.keep) = row.ell by omega]

theorem bodyEvalM_all (m S q coord i : ℕ) (final : Fin m → Block) (hot : ℕ) (joins : Fin S → ℕ)
    (off : ∀ r : Fin m, r.val ≠ hot → ∀ j < q, ∀ label, P (hashInput label (bodyTag coord i r.val j))) :
    AllAsked P (bodyEvalM m S q coord i final hot joins) := by
  unfold bodyEvalM
  refine AllAsked.bind (AllAsked.tableM fun r => ?_) fun _ => AllAsked.pure' _
  exact AllAsked.ite (fun _ => AllAsked.pure' _) fun ne => AllAsked.padVectorM fun j hj => off r ne j hj _

/-- The tag conditions of one coordinate, read one way. -/
structure CoordOff (T : CrtTable) (S coord v : ℕ) : Prop where
  chunkTree : ∀ c < T.chunkCount, ∀ n, 1 ≤ n → n < T.chunkWidth c → ∀ s : Fin (2 ^ n),
    s.val ≠ T.chunkValue v c % 2 ^ n → ∀ label, P (hashInput label (chunkTreeTag coord c n s.val))
  chunkCast : ∀ c < T.chunkCount, ∀ leaf : Fin (2 ^ T.chunkWidth c), leaf.val ≠ T.chunkValue v c →
    ∀ j < castAnswers T.castWidth, ∀ label, P (hashInput label (chunkCastTag coord c leaf.val j))
  conv : ∀ (i : Fin T.count) row, T.kind i = .odd row → ConvOff P coord i.val row (T.modulus i)
    (T.wordValue (T.modulus i) v)
  body : ∀ (i : Fin T.count) (r : Fin (T.modulus i)), r.val ≠ v % T.modulus i → ∀ j < T.padAnswers S i, ∀ label,
    P (hashInput label (bodyTag coord i.val r.val j))

theorem modEvalM_all (T : CrtTable) (S coord : ℕ) (pub : ConvPublic) (joins : Fin T.count → Fin S → ℕ) (v : ℕ)
    (chunks : ℕ → ChunkEval T.castWidth) (i : Fin T.count) (hT : SliceC.CorrectTable T) (hv : v < 2 ^ T.inputBits)
    (off : CoordOff P T S coord v) :
    AllAsked P (modEvalM T S coord pub joins v chunks i) := by
  have hm := hT.modulus_pos i
  unfold modEvalM
  dsimp only
  split
  · exact bodyEvalM_all P _ _ _ _ _ _ _ _ fun r ne j hj label => off.body i r ne j hj label
  · rename_i row kind
    obtain ⟨h0, h1, hell, hk0, hk1, _, hcount⟩ := hT.odd i row kind
    have hσlt : T.wordValue (T.modulus i) v < 2 ^ row.ell :=
      SliceC.wordValue_lt T (T.modulus i) v row.ell hm hcount
    have hσ : T.wordValue (T.modulus i) v ≡ v [MOD T.modulus i] :=
      SliceC.wordValue_modEq T hT.chunkBits_pos (T.modulus i) v hv
    refine AllAsked.bind (AllAsked.materializeM _) fun word => ?_
    refine AllAsked.bind' (conversionEvalM_all P coord i.val row _ _ word pub hm h0 h1 (off.conv i row kind))
      fun H x inside => ?_
    rw [conversionEvalM_snd H coord i.val row _ _ word pub hm hk1, Nat.mod_eq_of_lt hσlt] at inside
    have hot : T.wordValue (T.modulus i) v % T.modulus i = v % T.modulus i := hσ
    rw [hot] at inside
    exact bodyEvalM_all P _ _ _ _ _ _ _ _ (fun r ne j hj label => off.body i r ne j hj label) H x inside

theorem coordEvalM_all (T : CrtTable) (S coord : ℕ) (pub : ConvPublic) (records : Fin S → ℕ) (v : ℕ)
    (labels : ℕ → Block) (hT : SliceC.CorrectTable T) (hv : v < 2 ^ T.inputBits) (off : CoordOff P T S coord v) :
    AllAsked P (coordEvalM T S coord pub records v labels) := by
  unfold coordEvalM
  dsimp only
  refine AllAsked.bind (AllAsked.tableM fun c => ?_) fun chunkTable => ?_
  · exact chunkEvalM_all P T coord labels v _ _ c.val (off.chunkTree c.val c.isLt) (off.chunkCast c.val c.isLt)
  · exact AllAsked.bind (AllAsked.tableM fun i => modEvalM_all P T S coord pub _ v _ i hT hv off)
      fun _ => AllAsked.pure' _

end Coordinate

/-! ### Cold on the real table -/

/-- A cold input: its tag is not hot at `u`. -/
def ColdInput (u : AffineInput) (x : ℕ) : Prop := hotTag Kriterion.CRT.Entry.table u (x / 2 ^ 128) = false

theorem coordOff_cold (u : AffineInput) (S κ : ℕ) (hκ : κ < 2) (small : S ≤ 1000) :
    CoordOff (ColdInput u) Kriterion.CRT.Entry.table S κ (coordValue u κ) := by
  have tags : CoordTags (fun tag => hotTag Kriterion.CRT.Entry.table u tag = false) Kriterion.CRT.Entry.table S κ (coordValue u κ) :=
    coordTags_cold Kriterion.CRT.Entry.table u S κ hκ (Paths.bn254_ranges S small)
  refine ⟨fun c hc n h1 hn s ne label => ?_, fun c hc leaf ne j hj label => ?_, fun i row kind => ?_,
    fun i r ne j hj label => ?_⟩
  · unfold ColdInput
    rw [hashInput_div]
    exact (tags.chunkTree c hc n h1 hn s).mpr ne
  · unfold ColdInput
    rw [hashInput_div]
    exact (tags.chunkCast c hc leaf j hj).mpr ne
  · have conv := tags.conv i row kind
    refine ⟨fun ℓ h1 hℓ y hy ne label => ?_, fun α hα ne j hj label => ?_, fun ℓ h1 hℓ y hy ne label => ?_,
      fun α hα ne j hj label => ?_, fun k hk s ne label => ?_, fun j h1 h2 r ne label => ?_⟩ <;>
      unfold ColdInput <;> rw [hashInput_div]
    · exact (conv.tree0 ℓ h1 hℓ y hy).mpr ne
    · exact (conv.cast0 α hα j hj).mpr ne
    · exact (conv.tree1 ℓ h1 hℓ y hy).mpr ne
    · exact (conv.cast1 α hα j hj).mpr ne
    · exact (conv.grow k hk s).mpr ne
    · exact (conv.fold j h1 h2 r).mpr ne
  · unfold ColdInput
    rw [hashInput_div]
    exact (tags.body i r j hj).mpr ne

theorem coordValue_lt (u : AffineInput) (κ : ℕ) : coordValue u κ < 2 ^ Kriterion.CRT.Entry.table.inputBits := by
  have bound : baseFieldModulus < 2 ^ 254 := by unfold baseFieldModulus; decide
  have inputBits : Kriterion.CRT.Entry.table.inputBits = 254 := rfl
  rw [inputBits]
  unfold coordValue
  split
  · exact lt_trans u.x.val_lt bound
  · exact lt_trans u.y.val_lt bound

/-- **One coordinate of the replay asks only cold inputs**, whatever the published material, records and labels. -/
theorem coordEvalM_cold (u : AffineInput) (S κ : ℕ) (hκ : κ < 2) (small : S ≤ 1000) (pub : ConvPublic)
    (records : Fin S → ℕ) (labels : ℕ → Block) :
    AllAsked (ColdInput u) (coordEvalM Kriterion.CRT.Entry.table S κ pub records (coordValue u κ) labels) :=
  coordEvalM_all (ColdInput u) Kriterion.CRT.Entry.table S κ pub records _ labels SliceC.bn254_correctTable (coordValue_lt u κ)
    (coordOff_cold u S κ hκ small)

/-- **The replay's conversion blocks ask only cold inputs**, for every published value and labels. -/
theorem replayConv_cold (pub : Kriterion.CRT.Entry.Public) (u : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    AllAsked (ColdInput u) (Kriterion.CRT.Entry.replayConv pub u labels) := by
  unfold Kriterion.CRT.Entry.replayConv
  refine AllAsked.bind (coordEvalM_cold u _ 0 (by norm_num) (by decide) _ _ _) fun ex => ?_
  exact AllAsked.bind (coordEvalM_cold u _ 1 (by norm_num) (by decide) _ _ _) fun _ => AllAsked.pure' _

end Kriterion.CRT.Privacy.Contain
