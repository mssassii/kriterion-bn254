/-
**H2's facts on the concrete entry**: `GarblerTableFacts crtEntry` (`Laws/Table.lean`).

* `coordInjective_of_keyRun`: a tag run of a CRT program (`Paths/Tags.lean`) lifts, through `liftHash` and
  `FreeQuery.toProgram`, to tag injectivity on the contest's query program: a labelled input
  `hashInput label (tagCode …)` with its fields in range is below `2 ^ 168 < p`, so its field element reads back its
  tag (`tagOfInput_hashInput`), and distinct keys have distinct tags;
* `crtEntry_garblerTableFacts`: `garble_eval` from `eval_liftHash` and `FreeQuery.eval_toProgram`; `tagInjective`
  from `garbleCM_tagged`.
-/

import Proof.Privacy.CRT.Paths.Entry
import Proof.Privacy.CRT.Laws.Table
import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws

/-- The field element of a (key, label) pair's input. -/
noncomputable def inputOf (p : TagKey × Block) : BaseField := ((hashInput p.2 p.1.code : Nat) : BaseField)

theorem hashInput_lt {label : Block} {key : TagKey} (range : key.InRange) :
    hashInput label key.code < baseFieldModulus := by
  have codeLt := TagKey.code_lt range
  have labelLt := label.isLt
  unfold hashInput
  calc label.toNat + 2 ^ 128 * key.code < 2 ^ 128 + 2 ^ 128 * key.code := by omega
    _ = 2 ^ 128 * (key.code + 1) := by ring
    _ ≤ 2 ^ 128 * 2 ^ 40 := Nat.mul_le_mul_left _ (by omega)
    _ < baseFieldModulus := by unfold baseFieldModulus; norm_num

/-- **A labelled input reads back its tag.** -/
theorem tagOfInput_hashInput {label : Block} {key : TagKey} (range : key.InRange) :
    (tagOfInput ((hashInput label key.code : Nat) : BaseField)).val = key.code := by
  unfold tagOfInput
  simp only
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hashInput_lt range), hashInput_tag,
    Nat.mod_eq_of_lt (TagKey.code_lt range)]

/-- **Tag runs are tag-injective** on the lifted, budgeted program. -/
theorem coordInjective_of_keyRun {α : Type} {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop} :
    ∀ {seen : List (TagKey × Block)} {program : CM α}, KeyRun S Q seen program →
      (∀ p ∈ seen, p.1.InRange) → ∀ (budget : Nat) (bounded : (liftHash (FixedIndex := Empty)
        (EncIndex := Empty) program).Bounded budget),
        CoordInjective (FI := Empty) (EI := Empty) tagOfInput (seen.map inputOf)
          (FreeQuery.toProgram (liftHash program) budget bounded)
  | _, _, .pure seen value _, _, budget, bounded => by
      show CoordInjective tagOfInput _ (QueryProgram.pure value)
      exact .pure _ value
  | _, _, .query seen label tag key next coded member range fresh sameLabel rest, inRange, budget, bounded => by
      cases budget with
      | zero => exact absurd bounded FreeQuery.Bounded.not_zero
      | succ budget =>
          show CoordInjective tagOfInput _ (QueryProgram.query (PublicQuery.hash ((hashInput label tag : Nat) :
            BaseField)) fun answer => FreeQuery.toProgram (liftHash (next answer)) budget (bounded.next answer))
          refine .hash _ _ _ (fun y inside sameTag => ?_) fun answer => ?_
          · exfalso
            obtain ⟨p, inSeen, yIs⟩ := List.mem_map.mp inside
            subst yIs
            have tags := congrArg Fin.val sameTag
            rw [← coded, tagOfInput_hashInput range] at tags
            unfold inputOf at tags
            rw [tagOfInput_hashInput (inRange p inSeen)] at tags
            have same := TagKey.code_injective range (inRange p inSeen) tags
            exact fresh (List.mem_map.mpr ⟨p, inSeen, same.symm⟩)
          · have next := coordInjective_of_keyRun (rest answer) (fun p inside => by
              rcases List.mem_cons.mp inside with first | old
              · rw [first]; exact range
              · exact inRange p old) budget (bounded.next answer)
            rw [List.map_cons] at next
            unfold inputOf at next
            rw [coded] at next
            exact next

/-- `garble_eval` at the entry's own types. -/
theorem entry_garble_eval (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ)
    (scalar : NonZeroScalar) (coins : Kriterion.CRT.Entry.Coins) (oracle : PublicOracle Empty Empty) :
    (@Kriterion.CRT.Entry.scheme field group).garble parameter scalar (coins, oracle) =
      (Kriterion.CRT.Entry.garbleProgram scalar coins).eval (publicAnswer oracle) := by
  unfold Kriterion.CRT.Entry.garbleProgram
  rw [FreeQuery.eval_toProgram]
  unfold Kriterion.CRT.Entry.garbleM
  rw [eval_liftHash]
  unfold Kriterion.CRT.Entry.scheme
  dsimp only

/-- `tagInjective` at the entry's own types. -/
theorem entry_tagInjective (scalar : NonZeroScalar) (coins : Kriterion.CRT.Entry.Coins) :
    CoordInjective (FI := Empty) (EI := Empty) tagOfInput [] (Kriterion.CRT.Entry.garbleProgram scalar coins) :=
  coordInjective_of_keyRun (garbleCM_tagged scalar coins) (fun _ inside => absurd inside List.not_mem_nil) _ _

/-- **H2's named facts hold for the concrete entry.** -/
theorem crtEntry_garblerTableFacts : GarblerTableFacts Instance.crtEntry := by
  refine ⟨fun field group parameter scalar coins oracle => ?_, fun field group parameter scalar coins => ?_⟩
  · dsimp only [Instance.crtEntry]
    exact entry_garble_eval field group parameter scalar coins oracle
  · dsimp only [Instance.crtEntry]
    exact entry_tagInjective scalar coins

end Kriterion.CRT.Paths
