/-
**The parts of the on-curve decomposition** (for `OnDecomp`).

* lookups of installations (`installEntries_map_lookup`) and of the collector programs (`programHashAll_lookup`);
* the programmed table (`programmedTable_off`, `programmedTable_hit`, `programmedTable_agree`) and the collector
  indices (`collectorList_indices`);
* the tags of the full replay's inputs on the curve: labelled, visible, never family 8 (`entryReplay_inputs`), and of
  route M's replay (`viewReplay_family`);
* the digest labels of `u` (`digestInputs`, their tags);
* the reach's transcript on a table oracle, on the curve (`reach_transcript`).
-/

import Proof.Privacy.CRT.Glue.ReplayPoints
import Proof.Privacy.CRT.Laws.MiddleCrt
import Proof.Privacy.CRT.Paths.ReachTranscript

namespace Kriterion.CRT.Privacy.Contain

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Align (asked asked_bind asked_pure asked_askN asked_tableM hashInput_div asked_of_tagged
  tagFamily_key ftranscript transcript_toProgram ftranscript_liftHash ftranscript_bind_pure asked_digestKeyM
  asked_digestEvalM)
open Kriterion.CRT.Privacy.Laws (plantHash plantHash_lookup installOne installOne_hash installEntries_cons
  entryInput HashEntries program_hash_fresh)
open Kriterion.ArgoMAC.PlanB (digitCount)

noncomputable section

/-! ### Installations and programs -/

section Lookups

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- **Installing the entries of a function of the input** stores the function's value at every new input. -/
theorem installEntries_map_lookup (g : BaseField → Block × Block) :
    ∀ (xs : List BaseField) (σ : LazyOracle.State FI EI) (y : BaseField),
      (Privacy.installEntries (xs.map fun x => (⟨.hash x, g x⟩ : Entry FI EI)) σ).hash.lookup y =
        match σ.hash.lookup y with
        | some v => some v
        | none => if y ∈ xs then some (Fintype.equivFin (Block × Block) (g y)) else none
  | [], σ, y => by
      cases h : σ.hash.lookup y <;> simp [Privacy.installEntries, h]
  | x :: rest, σ, y => by
      rw [List.map_cons, installEntries_cons, installEntries_map_lookup g rest, installOne_hash]
      by_cases fresh : σ.hash.lookup x = none
      · rw [if_pos fresh, plantHash_lookup]
        by_cases same : y = x
        · subst same
          rw [if_pos rfl, fresh]
          simp
        · rw [if_neg same]
          cases h : σ.hash.lookup y with
          | some v => rfl
          | none => simp [same]
      · rw [if_neg fresh]
        cases h : σ.hash.lookup y with
        | some v => rfl
        | none =>
            by_cases same : y = x
            · subst same
              exact absurd h fresh
            · simp [same]

/-- The answer a request list gives at an input (its first request there). -/
def requestAnswer (requests : List (BaseField × (Block × Block))) (y : BaseField) : Option (Block × Block) :=
  (requests.find? fun r => decide (r.1 = y)).map Prod.snd

/-- **A successful program list** stores each request's answer at its fresh point and keeps the rest. -/
theorem programHashAll_lookup :
    ∀ (requests : List (BaseField × (Block × Block))) (σ σ' : LazyOracle.State FI EI),
      programHashAll requests σ = some σ' →
        (∀ r ∈ requests, σ.hash.lookup r.1 = none) ∧
        ∀ y, σ'.hash.lookup y = match requestAnswer requests y with
          | some a => some (Fintype.equivFin (Block × Block) a)
          | none => σ.hash.lookup y
  | [], σ, σ', done => by
      have same : σ = σ' := Option.some.inj done
      subst same
      exact ⟨fun r inside => absurd inside List.not_mem_nil, fun y => rfl⟩
  | (point, answer) :: rest, σ, σ', done => by
      have unfolded : programHashAll ((point, answer) :: rest) σ =
          (LazyOracle.program (.hash point) answer σ).bind (programHashAll rest) := rfl
      rw [unfolded] at done
      by_cases fresh : σ.hash.lookup point = none
      · rw [program_hash_fresh σ point answer fresh] at done
        obtain ⟨freshRest, lookupRest⟩ := programHashAll_lookup rest _ σ' done
        have notRest : ∀ r ∈ rest, r.1 ≠ point := fun r inside same => by
          have := freshRest r inside
          rw [same, plantHash_lookup, if_pos rfl] at this
          cases this
        refine ⟨fun r inside => ?_, fun y => ?_⟩
        · rcases List.mem_cons.mp inside with same | later
          · subst same
            exact fresh
          · have := freshRest r later
            rw [plantHash_lookup, if_neg (notRest r later)] at this
            exact this
        · rw [lookupRest y]
          unfold requestAnswer
          rw [List.find?_cons]
          by_cases same : point = y
          · subst same
            have none : (rest.find? fun r => decide (r.1 = point)) = none := by
              rw [List.find?_eq_none]
              intro r inside
              simpa using notRest r inside
            simp only [decide_true, Option.map_some]
            rw [none, Option.map_none, plantHash_lookup, if_pos rfl]
          · have ne : ¬ (y = point) := fun h => same h.symm
            simp only [same, decide_false]
            cases (rest.find? fun r => decide (r.1 = y)).map Prod.snd with
            | some a => rfl
            | none => rw [plantHash_lookup, if_neg ne]
      · have none : LazyOracle.program (.hash point) answer σ = none := by
          rw [Laws.program_hash, if_neg fresh]
        rw [none] at done
        cases done

end Lookups

/-! ### The programmed table -/

section Programmed

open Kriterion.CRT.Privacy.H8 (programmedTable collectorTag)

theorem collectorTag_val {k j : ℕ} (hk : k < 65536) (hj : j < 64) :
    (collectorTag k j).val = tagCode Family.mask 0 0 0 0 k j := by
  have small : tagCode Family.mask 0 0 0 0 k j < 2 ^ 40 := by
    unfold tagCode Family.mask
    omega
  exact Nat.mod_eq_of_lt small

theorem collectorTag_fields {k j : ℕ} (hk : k < 65536) (hj : j < 64) :
    tagFamily (collectorTag k j).val = 7 ∧ tagStage (collectorTag k j).val = 0 ∧ tagSlot (collectorTag k j).val = k ∧
      tagPart (collectorTag k j).val = j := by
  have range : TagInRange 0 0 0 0 k j := ⟨by norm_num, by norm_num, by norm_num, by norm_num, hk, hj⟩
  rw [collectorTag_val hk hj]
  exact ⟨tagFamily_tagCode range, tagStage_tagCode range, tagSlot_tagCode range, tagPart_tagCode range⟩

theorem collectorTag_inj {k j k' j' : ℕ} (hk : k < 65536) (hj : j < 64) (hk' : k' < 65536) (hj' : j' < 64)
    (same : collectorTag k j = collectorTag k' j') : k = k' ∧ j = j' := by
  have one := collectorTag_fields hk hj
  have two := collectorTag_fields hk' hj'
  rw [same] at one
  exact ⟨one.2.2.1.symm.trans two.2.2.1, one.2.2.2.symm.trans two.2.2.2⟩

theorem collectorIndex_lt (c : BMR.Collector) : collectorIndex c < 273 := by
  unfold collectorIndex
  have := c.1.1.isLt
  split <;> omega

/-- The programmed table off the collectors' tags is the table. -/
theorem programmedTable_off (tag : Fin (2 ^ 40)) :
    ∀ (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (table : TagTable),
      (∀ e ∈ drawn, ∀ j, j < 2 → tag ≠ collectorTag (collectorIndex e.1) j) → programmedTable table drawn tag = table tag
  | [], _, _ => rfl
  | e :: rest, table, away => by
      show programmedTable _ rest tag = _
      rw [programmedTable_off tag rest _ fun e' inside => away e' (List.mem_cons_of_mem _ inside)]
      dsimp only
      rw [Function.update_of_ne (away e List.mem_cons_self 1 (by norm_num)),
        Function.update_of_ne (away e List.mem_cons_self 0 (by norm_num))]

/-- Two tables that agree off `P` stay so after the programming, when the collectors' tags avoid nothing. -/
theorem programmedTable_agree (P : Set (Fin (2 ^ 40))) :
    ∀ (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (t t' : TagTable),
      (∀ p, p ∉ P → t p = t' p) → ∀ p, p ∉ P → programmedTable t drawn p = programmedTable t' drawn p
  | [], _, _, agree => agree
  | e :: rest, t, t', agree => by
      refine programmedTable_agree P rest _ _ fun p outside => ?_
      dsimp only
      by_cases one : p = collectorTag (collectorIndex e.1) 1
      · subst one
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne one, Function.update_of_ne one]
        by_cases zero : p = collectorTag (collectorIndex e.1) 0
        · subst zero
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne zero, Function.update_of_ne zero]
          exact agree p outside

/-- **The programmed table at a drawn collector's tags** holds the drawn answers, when the collectors differ. -/
theorem programmedTable_hit :
    ∀ (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (table : TagTable),
      (drawn.map fun e => collectorIndex e.1).Nodup → ∀ e ∈ drawn,
        programmedTable table drawn (collectorTag (collectorIndex e.1) 0) = (e.2.1.1, e.2.1.2.1) ∧
        programmedTable table drawn (collectorTag (collectorIndex e.1) 1) = (e.2.1.2.2, e.2.2)
  | [], _, _, e, inside => absurd inside List.not_mem_nil
  | first :: rest, table, distinct, e, inside => by
      rw [List.map_cons, List.nodup_cons] at distinct
      show programmedTable _ rest _ = _ ∧ programmedTable _ rest _ = _
      rcases List.mem_cons.mp inside with same | later
      · subst same
        have away : ∀ j, j < 2 → ∀ e' ∈ rest, ∀ j', j' < 2 →
            collectorTag (collectorIndex e.1) j ≠ collectorTag (collectorIndex e'.1) j' := by
          intro j hj e' member j' hj' same
          have := (collectorTag_inj (lt_trans (collectorIndex_lt _) (by norm_num)) (by omega)
            (lt_trans (collectorIndex_lt _) (by norm_num)) (by omega) same).1
          exact distinct.1 (List.mem_map.mpr ⟨e', member, this.symm⟩)
        rw [programmedTable_off _ rest _ fun e' member j' hj' => away 0 (by norm_num) e' member j' hj',
          programmedTable_off _ rest _ fun e' member j' hj' => away 1 (by norm_num) e' member j' hj']
        have ne : collectorTag (collectorIndex e.1) 0 ≠ collectorTag (collectorIndex e.1) 1 := fun same => by
          have := (collectorTag_inj (lt_trans (collectorIndex_lt _) (by norm_num)) (by norm_num)
            (lt_trans (collectorIndex_lt _) (by norm_num)) (by norm_num) same).2
          cases this
        dsimp only
        rw [Function.update_self, Function.update_of_ne ne, Function.update_self]
        exact ⟨rfl, rfl⟩
      · exact programmedTable_hit rest _ distinct.2 e later

/-- The collectors in order of their numbers. -/
theorem collectorList_indices : collectorList.map collectorIndex = List.range 273 := by
  decide +kernel

end Programmed

end

end Kriterion.CRT.Privacy.Contain
