/-
**The garbler's transcript on the concrete entry** (for `viewEntriesPerm_of` in
`Laws/Upper.lean`): on any oracle, every entry of the garbler's transcript is a hash entry whose tag family is at most
10 (`crtEntry_garbler_small`), and the entries' inputs are pairwise distinct (`crtEntry_garbler_distinct`).

Both come from the garbler's tag run (`garbleCM_tagged`): along the path the oracle's answers select, every query is a
labelled input `hashInput label (tagCode …)` at a key of `garblerKeys` (families 0 to 10), in range, and the keys are
pairwise distinct; a labelled input in range reads back its tag (`tagOfInput_hashInput`), so distinct keys give
distinct field elements (`transcript_of_keyRun`).
-/

import Proof.Privacy.CRT.Paths.TableFacts
import Proof.Privacy.CRT.Paths.SingleLabel
import Proof.Privacy.CRT.Laws.Upper

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws

/-- **The transcript of a tag run**, on any answers: every entry is the hash of a labelled input at a key of `S`, in
range, and the entries' inputs are distinct from each other and from the history's. -/
theorem transcript_of_keyRun {α : Type} {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop}
    (answer : ∀ query : PublicQuery Empty Empty, query.Answer) :
    ∀ {seen : List (TagKey × Block)} {program : CM α}, KeyRun S Q seen program →
      (∀ p ∈ seen, p.1.InRange) → (seen.map inputOf).Nodup →
      ∀ (budget : Nat) (bounded : (liftHash (FixedIndex := Empty) (EncIndex := Empty) program).Bounded budget),
        (∀ entry ∈ programTranscript answer (FreeQuery.toProgram (liftHash program) budget bounded),
          ∃ key ∈ S, key.InRange ∧ ∃ label : Block, entry.1 = .hash (inputOf (key, label))) ∧
        ((programTranscript answer (FreeQuery.toProgram (liftHash program) budget bounded)).map entryInput ++
          seen.map inputOf).Nodup
  | _, _, .pure seen value _, _, nodup, budget, bounded => by
      have empty : programTranscript answer (FreeQuery.toProgram (liftHash (FreeQuery.pure value : CM α)) budget
          bounded) = [] := rfl
      rw [empty]
      exact ⟨fun entry inside => absurd inside List.not_mem_nil, by simpa using nodup⟩
  | _, _, .query seen label tag key next coded member range fresh sameLabel rest, inRange, nodup, budget,
      bounded => by
      cases budget with
      | zero => exact absurd bounded FreeQuery.Bounded.not_zero
      | succ budget =>
          subst coded
          have unfolded : programTranscript answer (FreeQuery.toProgram
              (liftHash (FreeQuery.query (hashInput label key.code) next)) (budget + 1) bounded) =
              ⟨.hash (inputOf (key, label)), answer (.hash (inputOf (key, label)))⟩ ::
                programTranscript answer (FreeQuery.toProgram (liftHash (next (answer (.hash (inputOf (key, label))))))
                  budget (bounded.next _)) := rfl
          rw [unfolded]
          have newInput : inputOf (key, label) ∉ seen.map inputOf := by
            intro inside
            obtain ⟨p, inSeen, same⟩ := List.mem_map.mp inside
            have tags := congrArg (fun x => (tagOfInput x).val) same
            unfold inputOf at tags
            rw [tagOfInput_hashInput (inRange p inSeen), tagOfInput_hashInput range] at tags
            exact fresh (List.mem_map.mpr ⟨p, inSeen, TagKey.code_injective (inRange p inSeen) range tags⟩)
          have inRange' : ∀ p ∈ (key, label) :: seen, p.1.InRange := fun p inside => by
            rcases List.mem_cons.mp inside with first | old
            · rw [first]; exact range
            · exact inRange p old
          have nodup' : (((key, label) :: seen).map inputOf).Nodup := by
            rw [List.map_cons]
            exact List.nodup_cons.mpr ⟨newInput, nodup⟩
          obtain ⟨keys, distinct⟩ := transcript_of_keyRun answer (rest (answer (.hash (inputOf (key, label)))))
            inRange' nodup' budget (bounded.next _)
          refine ⟨fun entry inside => ?_, ?_⟩
          · rcases List.mem_cons.mp inside with first | later
            · exact ⟨key, member, range, label, by rw [first]⟩
            · exact keys entry later
          · rw [List.map_cons] at distinct
            rw [List.map_cons, List.cons_append]
            exact List.nodup_middle.mp distinct

/-! ### The garbler -/

theorem garblerKeys_fam : ∀ k ∈ garblerKeys, k.fam ≤ 10 := by
  rintro k (inC | inC | inKey | inMask | inDigest)
  · simp only [coordKeys, Set.mem_setOf_eq] at inC
    omega
  · simp only [coordKeys, Set.mem_setOf_eq] at inC
    omega
  · rw [Set.mem_singleton_iff.mp inKey]
    decide
  · simp only [maskKeys, nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inMask
    omega
  · simp only [digestKeys, digestLabelKeys, digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at inDigest
    omega

/-- The value of a labelled input in range, and its tag family. -/
theorem tagFamily_inputOf {key : TagKey} (range : key.InRange) (label : Block) :
    tagFamily ((inputOf (key, label)).val / 2 ^ 128) = key.fam := by
  unfold inputOf
  simp only
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hashInput_lt range), hashInput_tag, TagKey.code,
    tagFamily_tagCode (tagInRange_of range)]

/-- `small` at the entry's own program, on any answers. -/
theorem entry_garbler_small (scalar : NonZeroScalar) (coins : Kriterion.CRT.Entry.Coins)
    (answer : ∀ query : PublicQuery Empty Empty, query.Answer) :
    ∀ entry ∈ programTranscript answer (Kriterion.CRT.Entry.garbleProgram scalar coins),
      ∃ x, entry.1 = .hash x ∧ tagFamily (x.val / 2 ^ 128) ≤ 10 := by
  intro entry member
  unfold Kriterion.CRT.Entry.garbleProgram Kriterion.CRT.Entry.garbleM at member
  obtain ⟨key, inKeys, range, label, isHash⟩ :=
    (transcript_of_keyRun answer (garbleCM_tagged scalar coins) (fun _ inside => absurd inside List.not_mem_nil)
      List.nodup_nil Kriterion.CRT.Entry.garbleBudget (Kriterion.CRT.Entry.bounded_garbleM scalar coins)).1
      entry member
  refine ⟨inputOf (key, label), isHash, ?_⟩
  rw [tagFamily_inputOf range]
  exact garblerKeys_fam key inKeys

/-- `distinct` at the entry's own program, on any answers. -/
theorem entry_garbler_distinct (scalar : NonZeroScalar) (coins : Kriterion.CRT.Entry.Coins)
    (answer : ∀ query : PublicQuery Empty Empty, query.Answer) :
    ((programTranscript answer (Kriterion.CRT.Entry.garbleProgram scalar coins)).map entryInput).Nodup := by
  unfold Kriterion.CRT.Entry.garbleProgram Kriterion.CRT.Entry.garbleM
  have distinct := (transcript_of_keyRun answer (garbleCM_tagged scalar coins)
    (fun _ inside => absurd inside List.not_mem_nil) List.nodup_nil Kriterion.CRT.Entry.garbleBudget
    (Kriterion.CRT.Entry.bounded_garbleM scalar coins)).2
  rw [List.map_nil, List.append_nil] at distinct
  exact distinct

/-- **`small` of `viewEntriesPerm_of` for the concrete entry.** -/
theorem crtEntry_garbler_small :
    ∀ [FieldCertificate] [GroupCertificate] [Fintype Empty] [Fintype Empty] [DecidableEq Empty] [DecidableEq Empty]
      (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry),
      ∀ entry ∈ garblerEntries Instance.crtEntry parameter scalar tape,
        ∃ x, entry.1 = .hash x ∧ tagFamily (x.val / 2 ^ 128) ≤ 10 := by
  intro _ _ _ _ _ _ parameter scalar tape
  unfold garblerEntries
  dsimp only [Instance.crtEntry]
  exact entry_garbler_small scalar tape.1 _

/-- **`distinct` of `viewEntriesPerm_of` for the concrete entry.** -/
theorem crtEntry_garbler_distinct :
    ∀ [FieldCertificate] [GroupCertificate] [Fintype Empty] [Fintype Empty] [DecidableEq Empty] [DecidableEq Empty]
      (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry),
      ((garblerEntries Instance.crtEntry parameter scalar tape).map entryInput).Nodup := by
  intro _ _ _ _ _ _ parameter scalar tape
  unfold garblerEntries
  dsimp only [Instance.crtEntry]
  exact entry_garbler_distinct scalar tape.1 _

end Kriterion.CRT.Paths
