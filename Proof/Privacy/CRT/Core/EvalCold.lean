/-
**The evaluator asks only cold tags, for any material** (for OffDecomp).

At an input `u`, the evaluator of a coordinate skips exactly the slots that `u`'s value makes hot: the active slot of
every tree and growth level, the hot leaf of every cast, the closed subtrees of the two fused extraction stages (their
slots leave the active path), the fold's hot index (which moves by `u`'s bits whatever the answers,
`ReplayDelivered.eval_conversionEvalM_hot`) and the body's hot residue. None of this reads the published material,
the labels or the hash. So on **any** published material, labels and hash, every input `Entry.replayConv` asks is
`hashInput label tag` with `hotTag Entry.table u tag = false` (`replayConv_cold`), and, with the tag run, at
a key in range of family at most 6 (`replayConv_cold_labelled`).

`Align.coord_aligned` gives the same for the honest garbling only; this file reuses its `asked`
formulas (`asked_evalStepM`, `asked_chunkEvalM`, `asked_subtreeM_list`, `asked_expandM`, `asked_foldEvalM`,
`asked_bodyEvalM`) and its tag conditions (`CoordTags`, `coordTags_cold`), with the cold direction only.
-/

import Proof.Privacy.CRT.Hidden.AlignEntry
import Proof.Privacy.CRT.Core.ReplayDelivered
import Proof.Privacy.CRT.Paths.Reach

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.EvalCold

open Cryptography Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_tableM asked_ite asked_castM asked_evalStepM
  asked_foldEvalM asked_bodyEvalM asked_subtreeM_list asked_expandM asked_stageRoundsM_succ asked_extStageEvalM
  asked_materializeM closedSlot closedSlot_lt closedSlot_mod closedSlot_testBit closedSlot_zero slot_lt CoordTags
  ConvTags)

noncomputable section

/-! ### Cold lists -/

section Lists

variable (cold : ℕ → Prop)

/-- Every input of the list is a labelled input at a cold tag. -/
def AllCold (l : List ℕ) : Prop := ∀ x ∈ l, ∃ label tag, x = hashInput label tag ∧ cold tag

theorem allCold_nil : AllCold cold [] := fun _ h => absurd h List.not_mem_nil

theorem allCold_append {l l' : List ℕ} (h : AllCold cold l) (h' : AllCold cold l') : AllCold cold (l ++ l') := by
  intro x hx
  rcases List.mem_append.mp hx with a | b
  · exact h x a
  · exact h' x b

theorem allCold_flatMap {ι : Type} (L : List ι) (f : ι → List ℕ) (h : ∀ i ∈ L, AllCold cold (f i)) :
    AllCold cold (L.flatMap f) := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
  exact h i hi x hx

theorem allCold_single (label : Block) (tag : ℕ) (h : cold tag) : AllCold cold [hashInput label tag] := by
  intro x hx
  rw [List.mem_singleton] at hx
  exact ⟨label, tag, hx, h⟩

theorem allCold_map {ι : Type} (L : List ι) (label : ι → Block) (tag : ι → ℕ) (h : ∀ i ∈ L, cold (tag i)) :
    AllCold cold (L.map fun i => hashInput (label i) (tag i)) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact ⟨label i, tag i, rfl, h i hi⟩

theorem allCold_ite (c : Prop) [Decidable c] (l : List ℕ) (h : ¬ c → AllCold cold l) :
    AllCold cold (if c then [] else l) := by
  split
  · exact allCold_nil cold
  · rename_i hc
    exact h hc

end Lists

/-! ### Trees and growth -/

section Trees

variable (H : HashN) (cold : ℕ → Prop)

theorem evalStep_cold (n : ℕ) (tagOf : ℕ → ℕ) (active : Fin (2 ^ n)) (bitLabel join : Block)
    (parent : Fin (2 ^ n) → Block) (h : ∀ s : Fin (2 ^ n), s ≠ active → cold (tagOf s.val)) :
    AllCold cold (asked H (evalStepM n tagOf active bitLabel join parent)) := by
  rw [asked_evalStepM]
  refine allCold_flatMap cold _ _ fun s _ => ?_
  split
  · exact allCold_nil cold
  · rename_i hs
    exact allCold_single cold _ _ (h s hs)

theorem ne_active {n value : ℕ} {s : Fin (2 ^ n)} (hs : s ≠ activeAt value n) : s.val ≠ value % 2 ^ n :=
  fun e => hs (Fin.ext e)

theorem treeEval_cold (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Block) :
    ∀ levels, (∀ n, 1 ≤ n → n < levels → ∀ s : Fin (2 ^ n), s.val ≠ value % 2 ^ n → cold (tagOf n s.val)) →
      AllCold cold (asked H (treeEvalM tagOf value bitLabel join levels))
  | 0, _ => allCold_nil cold
  | n + 1, h => by
      rw [treeEvalM, asked_bind]
      refine allCold_append cold
        (treeEval_cold tagOf value bitLabel join n fun k hk1 hk s hs => h k hk1 (by omega) s hs) ?_
      rw [asked_ite]
      split
      · simp only [asked_pure]
        exact allCold_nil cold
      · rename_i hn
        exact evalStep_cold H cold n (tagOf n) (activeAt value n) _ _ _ fun s hs =>
          h n (by omega) (by omega) s (ne_active hs)

theorem growEval_cold (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Block) (start : ℕ)
    (labels : Fin (2 ^ start) → Block) :
    ∀ count, (∀ k < count, ∀ s : Fin (2 ^ (start + k)), s.val ≠ value % 2 ^ (start + k) →
        cold (tagOf (start + k) s.val)) →
      AllCold cold (asked H (growEvalM tagOf value bitLabel join start labels count))
  | 0, _ => allCold_nil cold
  | k + 1, h => by
      rw [growEvalM, asked_bind]
      exact allCold_append cold (growEval_cold tagOf value bitLabel join start labels k fun k' hk' => h k' (by omega))
        (evalStep_cold H cold _ _ _ _ _ _ fun s hs => h k (by omega) s (ne_active hs))

end Trees

/-! ### Chunks -/

theorem chunkEval_cold (H : HashN) (cold : ℕ → Prop) (T : CrtTable) (coord : ℕ) (labels : ℕ → Block) (v : ℕ)
    (joins : ℕ → Block) (pin : Lanes T.castWidth) (c : ℕ)
    (htree : ∀ n, 1 ≤ n → n < T.chunkWidth c → ∀ s : Fin (2 ^ n), s.val ≠ T.chunkValue v c % 2 ^ n →
      cold (chunkTreeTag coord c n s.val))
    (hcast : ∀ leaf : Fin (2 ^ T.chunkWidth c), ¬ leaf.val = T.chunkValue v c → ∀ j < castAnswers T.castWidth,
      cold (chunkCastTag coord c leaf.val j)) :
    AllCold cold (asked H (chunkEvalM T coord labels v joins pin c)) := by
  rw [Align.asked_chunkEvalM]
  refine allCold_append cold (treeEval_cold H cold _ _ _ _ _ htree) (allCold_flatMap cold _ _ fun leaf _ => ?_)
  refine allCold_ite cold _ _ fun hl => ?_
  exact allCold_map cold _ _ _ fun j _ => hcast leaf hl j.val j.isLt

/-! ### The fused extraction stage -/

section Stage

variable (H : HashN) (cold : ℕ → Prop) {rb : ℕ} (w : ℕ) (treeTag castTag : ℕ → ℕ → ℕ)

theorem subtree_cold (start slot : ℕ) (label : Block) (d : ℕ)
    (h : ∀ d' < d, ∀ t : Fin (2 ^ d'), cold (treeTag (start + d') (slot + 2 ^ start * t.val))) :
    AllCold cold (asked H (subtreeM treeTag start slot label d)) := by
  rw [asked_subtreeM_list]
  exact allCold_flatMap cold _ _ fun d' hd' => allCold_flatMap cold _ _ fun t _ =>
    allCold_single cold _ _ (h d' (List.mem_range.mp hd') t)

theorem expand_cold (start slot : ℕ) (label : Block) (state : StageState rb)
    (htree : ∀ d' < w - start, ∀ t : Fin (2 ^ d'), cold (treeTag (start + d') (slot + 2 ^ start * t.val)))
    (hcast : ∀ t : Fin (2 ^ (w - start)), ∀ j < castAnswers rb, cold (castTag (slot + 2 ^ start * t.val) j)) :
    AllCold cold (asked H (expandM w treeTag castTag start slot label state)) := by
  rw [asked_expandM]
  exact allCold_append cold (subtree_cold H cold treeTag _ _ _ _ htree)
    (allCold_flatMap cold _ _ fun t _ => allCold_map cold _ _ _ fun j _ => hcast t j.val j.isLt)

/-- A closed slot leaves the active path at its own level. -/
theorem closedSlot_ne (s k : ℕ) : closedSlot s k % 2 ^ (k + 1) ≠ s % 2 ^ (k + 1) := by
  intro e
  have hb := congrArg (fun x => x.testBit k) e
  simp only [Nat.testBit_mod_two_pow, show k < k + 1 by omega, decide_true, Bool.true_and] at hb
  exact closedSlot_testBit s k hb

/-- **The expansion of the closed slot of round `k` asks only cold tags**, from the stage's tag conditions at the
stage value `s`. -/
theorem closed_expand_cold (s : ℕ)
    (htreeS : ∀ ℓ y, 1 ≤ ℓ → ℓ < w → y < 2 ^ ℓ → y ≠ s % 2 ^ ℓ → cold (treeTag ℓ y))
    (hcastS : ∀ α < 2 ^ w, α ≠ s → ∀ j < castAnswers rb, cold (castTag α j))
    (k : ℕ) (hk : k < w) (slot : ℕ) (hslot : slot = closedSlot s k) (label : Block) (state : StageState rb) :
    AllCold cold (asked H (expandM w treeTag castTag (k + 1) slot label state)) := by
  subst hslot
  have hlt := closedSlot_lt s k
  have hne := closedSlot_ne s k
  have hmod : ∀ t, (closedSlot s k + 2 ^ (k + 1) * t) % 2 ^ (k + 1) = closedSlot s k := fun t => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  refine expand_cold H cold w treeTag castTag _ _ _ _ (fun d' hd' t => ?_) (fun t j hj => ?_)
  · refine htreeS _ _ (by omega) (by omega) (slot_lt hlt t.isLt) fun e => hne ?_
    have := congrArg (· % 2 ^ (k + 1)) e
    simp only [hmod] at this
    rw [Nat.mod_eq_of_lt hlt, this, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))]
  · have hα : closedSlot s k + 2 ^ (k + 1) * t.val < 2 ^ w := by
      have := slot_lt hlt t.isLt
      rwa [show k + 1 + (w - (k + 1)) = w by omega] at this
    refine hcastS _ hα (fun e => hne ?_) j hj
    have := congrArg (· % 2 ^ (k + 1)) e
    simp only [hmod] at this
    rw [Nat.mod_eq_of_lt hlt]
    exact this

theorem stageRound_cold (s : ℕ)
    (htreeS : ∀ ℓ y, 1 ≤ ℓ → ℓ < w → y < 2 ^ ℓ → y ≠ s % 2 ^ ℓ → cold (treeTag ℓ y))
    (hcastS : ∀ α < 2 ^ w, α ≠ s → ∀ j < castAnswers rb, cold (castTag α j))
    (sub : Lanes w) (joins : ℕ → Block) (pin : Lanes rb) (n : ℕ) (hn : n < w) (state : StageState rb) :
    AllCold cold (asked H (stageRoundM w treeTag castTag sub s joins pin n state)) := by
  unfold stageRoundM
  dsimp only
  split
  · rename_i hb
    exact closed_expand_cold H cold w treeTag castTag s htreeS hcastS n hn _ (by simp [closedSlot, hb]) _ _
  · rename_i hb
    exact closed_expand_cold H cold w treeTag castTag s htreeS hcastS n hn _ (by simp [closedSlot, hb]) _ _

theorem stageRounds_cold (s : ℕ)
    (htreeS : ∀ ℓ y, 1 ≤ ℓ → ℓ < w → y < 2 ^ ℓ → y ≠ s % 2 ^ ℓ → cold (treeTag ℓ y))
    (hcastS : ∀ α < 2 ^ w, α ≠ s → ∀ j < castAnswers rb, cold (castTag α j))
    (sub : Lanes w) (joins : ℕ → Block) (pin : Lanes rb) :
    ∀ remaining n (state : StageState rb), n + remaining ≤ w →
      AllCold cold (asked H (stageRoundsM w treeTag castTag sub s joins pin remaining n state))
  | 0, _, _, _ => by
      simp only [stageRoundsM, asked_pure]
      exact allCold_nil cold
  | r + 1, n, state, hn => by
      rw [asked_stageRoundsM_succ]
      exact allCold_append cold (stageRound_cold H cold w treeTag castTag s htreeS hcastS sub joins pin n (by omega) _)
        (stageRounds_cold s htreeS hcastS sub joins pin r (n + 1) _ (by omega))

/-- **A fused extraction stage asks only cold tags**, at the stage value `s < 2 ^ w`, on any remainder, joins, pin
and hash. -/
theorem extStageEval_cold (hw1 : 1 ≤ w) (R : Lanes rb) (s : ℕ) (joins : ℕ → Block) (pin : Lanes rb)
    (htreeS : ∀ ℓ y, 1 ≤ ℓ → ℓ < w → y < 2 ^ ℓ → y ≠ s % 2 ^ ℓ → cold (treeTag ℓ y))
    (hcastS : ∀ α < 2 ^ w, α ≠ s → ∀ j < castAnswers rb, cold (castTag α j)) :
    AllCold cold (asked H (extStageEvalM w treeTag castTag R s joins pin)) := by
  have e := asked_extStageEvalM H w treeTag castTag R s joins pin
  dsimp only at e
  rw [e]
  refine allCold_append cold ?_ (stageRounds_cold H cold w treeTag castTag s htreeS hcastS _ joins pin _ 1 _
    (by omega))
  exact closed_expand_cold H cold w treeTag castTag s htreeS hcastS 0 (by omega) _ (closedSlot_zero s).symm _ _

end Stage

/-! ### Folds and body -/

section FoldsBody

variable (H : HashN) (cold : ℕ → Prop)

theorem foldsEval_cold (m : ℕ) (hm : 0 < m) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Block) :
    ∀ count position hot (labels : Fin m → Block), hot = value % 2 ^ position % m →
      (∀ j, position ≤ j → j < position + count → ∀ r : Fin m, r.val ≠ value % 2 ^ j % m → cold (tagOf j r.val)) →
      AllCold cold (asked H (foldsEvalM m tagOf value bitLabel join count position hot labels))
  | 0, _, _, _, _, _ => by
      simp only [foldsEvalM, asked_pure]
      exact allCold_nil cold
  | count + 1, position, hot, labels, hhot, h => by
      rw [foldsEvalM, asked_bind]
      refine allCold_append cold ?_ (foldsEval_cold m hm tagOf value bitLabel join count (position + 1) _ _ ?_
        fun j hj1 hj2 r hr => h j (by omega) (by omega) r hr)
      · rw [asked_foldEvalM]
        refine allCold_flatMap cold _ _ fun r _ => allCold_ite cold _ _ fun hr => ?_
        exact allCold_single cold _ _ (h position le_rfl (by omega) r (by rw [← hhot]; exact hr))
      · have step := SliceC.foldHot_eq m value hm 1 position hot hhot
        simpa [SliceC.foldHot] using step

theorem bodyEval_cold (m S q coord i : ℕ) (final : Fin m → Block) (hot : ℕ) (joins : Fin S → ℕ)
    (h : ∀ r : Fin m, ¬ r.val = hot → ∀ j < q, cold (bodyTag coord i r.val j)) :
    AllCold cold (asked H (bodyEvalM m S q coord i final hot joins)) := by
  rw [asked_bodyEvalM]
  exact allCold_flatMap cold _ _ fun r _ => allCold_ite cold _ _ fun hr =>
    allCold_map cold _ _ _ fun j _ => h r hr j.val j.isLt

end FoldsBody

/-! ### A modulus and a coordinate -/

section Coordinate

variable (H : HashN) (cold : ℕ → Prop)

/-- **An odd modulus's conversion asks only cold tags**, at the word value `σ`, on any word and material. -/
theorem conversionEval_cold (coord i : ℕ) (row : OddRow) (m σ : ℕ) (word : Lanes row.ell) (pub : ConvPublic)
    (hm : 0 < m) (h0 : 1 ≤ row.width0) (h1 : 1 ≤ row.width1) (tags : ConvTags cold coord i row m σ) :
    AllCold cold (asked H (conversionEvalM coord i row m σ word pub)) := by
  unfold conversionEvalM
  dsimp only
  simp only [asked_bind]
  refine allCold_append cold (extStageEval_cold H cold _ _ _ h0 _ _ _ _ ?_ ?_)
    (allCold_append cold (extStageEval_cold H cold _ _ _ h1 _ _ _ _ ?_ ?_)
      (allCold_append cold (growEval_cold H cold _ _ _ _ _ _ _ ?_)
        (foldsEval_cold H cold m hm _ _ _ _ _ _ _ _ rfl ?_)))
  · intro ℓ y hℓ1 hℓ hy hne
    exact (tags.tree0 ℓ hℓ1 hℓ y hy).mpr hne
  · intro α hα hne j hj
    exact (tags.cast0 α hα j hj).mpr hne
  · intro ℓ y hℓ1 hℓ hy hne
    exact (tags.tree1 ℓ hℓ1 hℓ y hy).mpr hne
  · intro α hα hne j hj
    exact (tags.cast1 α hα j hj).mpr hne
  · intro k hk s hs
    exact (tags.grow k hk s).mpr hs
  · intro j hj1 hj2 r hr
    exact (tags.fold j hj1 hj2 r).mpr hr

/-- **A modulus asks only cold tags** (its conversion and its body at the hot residue `v mod m`). -/
theorem modEval_cold (T : CrtTable) (hT : SliceC.CorrectTable T) (S coord : ℕ) (pub : ConvPublic)
    (joins : Fin T.count → Fin S → ℕ) (v : ℕ) (hv : v < 2 ^ T.inputBits) (chunks : ℕ → ChunkEval T.castWidth)
    (i : Fin T.count) (tags : CoordTags cold T S coord v) :
    AllCold cold (asked H (modEvalM T S coord pub joins v chunks i)) := by
  unfold modEvalM
  split
  · exact bodyEval_cold H cold _ _ _ _ _ _ _ _ fun r hr j hj => (tags.body i r j hj).mpr hr
  · rename_i row hk
    obtain ⟨h0, h1, _, _, _, _, _⟩ := hT.odd i row hk
    simp only [asked_bind, asked_materializeM, List.nil_append]
    refine allCold_append cold (conversionEval_cold H cold _ _ _ _ _ _ _ (hT.modulus_pos i) h0 h1
      (tags.conv i row hk)) (bodyEval_cold H cold _ _ _ _ _ _ _ _ fun r hr j hj => ?_)
    refine (tags.body i r j hj).mpr fun e => hr ?_
    rw [ReplayDelivered.eval_conversionEvalM_hot, ReplayDelivered.conversion_hot T hT i row hk v hv, e]

/-- **A coordinate's evaluator asks only cold tags**, on any published material, records, labels and hash. -/
theorem coordEval_cold (T : CrtTable) (hT : SliceC.CorrectTable T) (S coord : ℕ) (pub : ConvPublic)
    (records : Fin S → ℕ) (v : ℕ) (hv : v < 2 ^ T.inputBits) (labels : ℕ → Block)
    (tags : CoordTags cold T S coord v) :
    AllCold cold (asked H (coordEvalM T S coord pub records v labels)) := by
  unfold coordEvalM
  dsimp only
  simp only [asked_bind, asked_tableM, asked_pure, List.append_nil]
  refine allCold_append cold (allCold_flatMap cold _ _ fun c _ => ?_) (allCold_flatMap cold _ _ fun i _ =>
    modEval_cold H cold T hT S coord pub _ v hv _ i tags)
  exact chunkEval_cold H cold T coord labels v _ _ c.val
    (fun n hn1 hn s hs => (tags.chunkTree c.val c.isLt n hn1 hn s).mpr hs)
    (fun leaf hl j hj => (tags.chunkCast c.val c.isLt leaf j hj).mpr hl)

end Coordinate

/-! ### The replay's conversion blocks at an input -/

theorem coordTags_x (u : BN254.AffineInput) :
    CoordTags (fun tag => hotTag Entry.table u tag = false) Entry.table Entry.xCount 0 u.x.val := by
  have tags := Align.coordTags_cold Entry.table u Entry.xCount 0 (by norm_num) (Paths.bn254_ranges _ (by decide))
  rwa [Align.coordValue_zero] at tags

theorem coordTags_y (u : BN254.AffineInput) :
    CoordTags (fun tag => hotTag Entry.table u tag = false) Entry.table Entry.yCount 1 u.y.val := by
  have tags := Align.coordTags_cold Entry.table u Entry.yCount 1 (by norm_num) (Paths.bn254_ranges _ (by decide))
  rwa [Align.coordValue_one] at tags

/-- **`Entry.replayConv` asks only tags cold at `u`**, on any published value, labels and hash. -/
theorem replayConv_cold (H : HashN) (pub : Entry.Public) (u : BN254.AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    AllCold (fun tag => hotTag Entry.table u tag = false) (asked H (Entry.replayConv pub u labels)) := by
  unfold Entry.replayConv
  simp only [asked_bind, asked_pure, List.append_nil]
  exact allCold_append _
    (coordEval_cold H _ Entry.table SliceC.bn254_correctTable _ 0 _ _ _ (ReplayDelivered.val_lt_inputBits u.x) _
      (coordTags_x u))
    (coordEval_cold H _ Entry.table SliceC.bn254_correctTable _ 1 _ _ _ (ReplayDelivered.val_lt_inputBits u.y) _
      (coordTags_y u))

/-- **Every input of `Entry.replayConv` is labelled at a key in range, of family at most 6, and cold at `u`.** -/
theorem replayConv_cold_labelled (H : HashN) (pub : Entry.Public) (u : BN254.AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    ∀ x ∈ asked H (Entry.replayConv pub u labels), ∃ label tag, x = hashInput label tag ∧ tag < 2 ^ 40 ∧
      tagFamily tag ≤ 6 ∧ hotTag Entry.table u tag = false := by
  intro x hx
  obtain ⟨label, tag, rfl, hcold⟩ := replayConv_cold H pub u labels _ hx
  obtain ⟨k, member, range, label', same⟩ :=
    Align.asked_of_tagged (Paths.replayConv_tagged pub u labels) H _ hx
  have htag : tag = k.code := by
    have := congrArg (· / 2 ^ 128) same
    simpa only [Align.hashInput_div] using this
  subst htag
  exact ⟨label, k.code, rfl, Paths.TagKey.code_lt range,
    by rw [Align.tagFamily_key range]; exact Paths.replayConvKeys_fam k member, hcold⟩

end

end Kriterion.CRT.Privacy.EvalCold
