/-
**Families 0 to 6 never coincide** (`CrtConvCoincide`).

A conversion or body entry of the garbler (tag family at most 6) that the designed rule hides has a hot tag at `u`
(`designTag_conv`). If the reach asked the same input, then:
* the reach's input is below `p`, since every reach input is a labelled input at a key in range (`reachCM_tagged`,
  `reachOffCM_tagged`), so it is the garbler's input itself;
* its tag has family at most 6, so it is a query of the reach's conversion layer `replayConv`: the key, the masks and
  the digest ask at families 10, 7, 8 and 9;
* every query of `replayConv` has a cold tag (`replayConv_aligned`).
So no such entry exists (`crtConvNever`), whatever the input deltas; `CrtConvCoincide` follows.
-/

import Proof.Privacy.CRT.Flags.CoincidenceSplit
import Proof.Privacy.CRT.Hidden.AlignEntry
import Proof.Privacy.CRT.Paths.ReachTranscript

set_option autoImplicit false

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.Instance
open Kriterion.CRT.Privacy.Align

namespace ConvCoincideProof

/-- A reach input of family at most 6 is a query of the reach's conversion layer. -/
theorem mem_replayConv_of_fam (H : HashN) (pub : Entry.Public) (u : AffineInput) (labels : LamportSignature)
    (x : ℕ) (small : tagFamily (x / 2 ^ 128) ≤ 6)
    (inReach : x ∈ asked H (Entry.reachCM pub u labels) ∨ x ∈ asked H (EntryReading.reachOffCM pub u labels)) :
    x ∈ asked H (Entry.replayConv pub u labels) := by
  have famOf : ∀ {S : Set Paths.TagKey} {α : Type} {P : CM α}, Paths.Tagged S P → x ∈ asked H P →
      ∃ k ∈ S, tagFamily (x / 2 ^ 128) = k.fam := by
    intro S α P tagged member
    obtain ⟨k, inS, range, label, rfl⟩ := asked_of_tagged tagged H x member
    exact ⟨k, inS, by rw [hashInput_div, tagFamily_key range]⟩
  rcases inReach with onCurve | offCurve
  · unfold Entry.reachCM Entry.replay at onCurve
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at onCurve
    rcases onCurve with (conv | key | mask) | digest
    · exact conv
    · obtain ⟨k, inS, fam⟩ := famOf (Paths.keyM_tagged _) key
      rw [Set.mem_singleton_iff.mp inS] at fam
      simp only [Paths.keyKey] at fam
      omega
    · obtain ⟨k, inS, fam⟩ := famOf (Paths.maskAnswersM_tagged _ PlanB.digitCount (by decide) (by decide)) mask
      have := Paths.maskKeys_fam k inS
      omega
    · obtain ⟨k, inS, fam⟩ := famOf (Paths.entryDigest_tagged _ _ _) digest
      have := Paths.digestKeys_fam k inS
      omega
  · unfold EntryReading.reachOffCM at offCurve
    simp only [asked_bind, asked_pure, List.append_nil, List.mem_append] at offCurve
    rcases offCurve with conv | digest
    · exact conv
    · obtain ⟨k, inS, fam⟩ := famOf (Paths.entryDigest_tagged _ _ _) digest
      have := Paths.digestKeys_fam k inS
      omega

/-- Every reach input is below `p`. -/
theorem reach_input_lt (H : HashN) (pub : Entry.Public) (u : AffineInput) (labels : LamportSignature) (x : ℕ)
    (inReach : x ∈ asked H (Entry.reachCM pub u labels) ∨ x ∈ asked H (EntryReading.reachOffCM pub u labels)) :
    x < baseFieldModulus := by
  rcases inReach with onCurve | offCurve
  · obtain ⟨k, _, range, label, rfl⟩ := asked_of_tagged (Paths.reachCM_tagged pub u labels) H x onCurve
    exact Paths.hashInput_lt range
  · obtain ⟨k, _, range, label, rfl⟩ := asked_of_tagged (Paths.reachOffCM_tagged pub u labels) H x offCurve
    exact Paths.hashInput_lt range

end ConvCoincideProof

open ConvCoincideProof in
/-- **No conversion or body entry is hidden and reached**: a garbler entry of tag family at most 6 that the reach asks
is one the designed rule shows. -/
theorem crtConvNever : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ)
    (scalar : NonZeroScalar) (tape : TableTape crtEntry) (u : AffineInput) (e : Entry Empty Empty),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    HiddenReached crtEntry Entry.table parameter scalar tape u e → entryFamily e ≤ 6 → False := by
  intro field group parameter scalar tape u e hidden small
  obtain ⟨coins, table⟩ := tape
  obtain ⟨inGarbler, inReach, isHidden⟩ := hidden
  -- the garbler's input
  have transcriptG := transcript_toProgram (publicAnswer (tableOracle (FI := Empty) (EI := Empty) table))
    (liftHash (Entry.garbleCM scalar coins)) Entry.garbleBudget (Entry.bounded_garbleM scalar coins)
  unfold garblerEntries tapeOracle at inGarbler
  dsimp only [Instance.crtEntry] at inGarbler
  unfold Entry.garbleProgram Entry.garbleM at inGarbler
  rw [transcriptG, ftranscript_liftHash] at inGarbler
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp inGarbler
  have xlt := garbler_input_lt (schemeHash (tableOracle table)) scalar coins x hx
  -- its tag is hot
  simp only [entryFamily] at small
  rw [val_natCast_of_lt xlt] at small
  rw [crtDesigned_hash, val_natCast_of_lt xlt, designTag_conv _ _ _ small] at isHidden
  have hot : hotTag Entry.table u (x / 2 ^ 128) = true := by simpa using isHidden
  -- the reach's inputs
  have hgarble : (@Entry.scheme field group).garble parameter scalar (coins, tableOracle table) =
      (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins,
        EntryCorrect.keyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins) := by
    refine (Paths.entry_garble_eval field group parameter scalar coins (tableOracle table)).trans ?_
    unfold Entry.garbleProgram
    rw [FreeQuery.eval_toProgram]
    unfold Entry.garbleM
    rw [eval_liftHash]
    exact EntryCorrect.garbleCM_eval _ scalar coins
  have hencode : (@Entry.scheme field group).encode
      (EntryCorrect.keyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins) u =
      EntryCorrect.labelsFor (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins u := by
    unfold Entry.scheme EntryCorrect.labelsFor
    rfl
  have transcriptR := transcript_toProgram (publicAnswer (tableOracle (FI := Empty) (EI := Empty) table))
    (EntryReading.reachDecodedM (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table))
      scalar coins) u (EntryCorrect.labelsFor (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins u)) Entry.evaluateBudget
    (EntryReading.bounded_reachDecodedM (EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty)
      table)) scalar coins) u (EntryCorrect.labelsFor (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) coins u))
  unfold reachedEntries tapeOracle at inReach
  dsimp only [Instance.crtEntry] at inReach
  rw [hgarble] at inReach
  dsimp only at inReach
  unfold EntryReading.reachProgram at inReach
  rw [hencode, transcriptR] at inReach
  unfold EntryReading.reachDecodedM at inReach
  rw [ftranscript_bind_pure] at inReach
  set H := schemeHash (tableOracle (FI := Empty) (EI := Empty) table) with hH
  set pub := EntryCorrect.pubOf H scalar coins with hpub
  set labels := EntryCorrect.labelsFor H coins u with hlabels
  have asks : ∃ y, (y ∈ asked H (Entry.reachCM pub u labels) ∨ y ∈ asked H (EntryReading.reachOffCM pub u labels)) ∧
      ((y : BaseField)) = ((x : BaseField)) := by
    split at inReach
    · unfold Entry.reachM at inReach
      rw [ftranscript_liftHash, List.map_map] at inReach
      obtain ⟨y, hy, same⟩ := List.mem_map.mp inReach
      exact ⟨y, Or.inl hy, by simpa using same⟩
    · rw [ftranscript_liftHash, List.map_map] at inReach
      obtain ⟨y, hy, same⟩ := List.mem_map.mp inReach
      exact ⟨y, Or.inr hy, by simpa using same⟩
  obtain ⟨y, hy, same⟩ := asks
  have ylt := reach_input_lt H pub u labels y hy
  have hyx : y = x := by
    have := congrArg ZMod.val same
    rwa [val_natCast_of_lt ylt, val_natCast_of_lt xlt] at this
  subst hyx
  have conv := mem_replayConv_of_fam H pub u labels y small hy
  have cold := ((replayConv_aligned H scalar coins u).sound y conv).1
  unfold ColdAt at cold
  rw [cold] at hot
  exact Bool.false_ne_true hot

/-- **`CrtConvCoincide`** (families 0 to 6): it holds because its hypothesis never does. -/
theorem crtConvCoincide : CrtConvCoincide := by
  intro field group parameter scalar tape u e hidden small
  exact (crtConvNever field group parameter scalar tape u e hidden small).elim

end Kriterion.CRT.Privacy.Flags
