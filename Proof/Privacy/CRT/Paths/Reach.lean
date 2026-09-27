/-
**The evaluator's reach is `Tagged`** (for `viewOnce` and `CrtThirdSwap`):

* `digestKeyM_tagged`, `digestEvalM_tagged`: the digest evaluator asks one label per position (family 8, the part
  is the input's bit) and two finals per digit (family 9, sites `2o` and `2o + 1`);
* `replay_tagged`, `reachCM_tagged`: the full replay (conversion and body blocks, the key, all mask sites) and the
  reach on the curve (`Entry.reachCM`: the replay, then the digest);
* `reachOffCM_tagged`: the reach off the curve (`EntryReading.reachOffCM`: the conversion blocks, then the
  digest);
* `crtShadowOffCurve_tagged`, `crtShadow_offCurve_tagged`: the shadow's off-curve program (`Core/H8.lean`), the
  latter in the form of `crtThirdSwap_of_tagged`'s hypothesis.
-/

import Proof.Privacy.CRT.Paths.Refill
import Proof.Privacy.CRT.Core.H8

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy

/-! ### The digest evaluator -/

theorem coordBit_lt (u : AffineInput) (coord : Fin 2) (position : Nat) : coordBit u coord position < 2 := by
  unfold coordBit
  split <;> omega

/-- **The digest key**: one label per position of both coordinates, at the input's bit. -/
theorem digestKeyM_tagged (bits : Nat) (bitsLe : bits ≤ 65536) (labels : Fin 2 → Fin bits → Block)
    (u : AffineInput) : Tagged (digestLabelKeys bits) (digestKeyM bits labels u) := by
  unfold digestKeyM
  have coordTable : ∀ coord : Fin 2, Tagged {k | ∃ i < bits, k ∈ positionKeys coord.val i}
      (CRT.tableM bits fun position =>
        h128M (labels coord position) (digestLabelTag coord.val position.val (coordBit u coord position.val))) :=
    fun coord => Tagged.tableM (S := fun position => positionKeys coord.val position) bits
      (fun position => Tagged.h128M (positionKeys coord.val position.val) _ _
        ⟨8, coord.val, 0, 0, 0, position.val, coordBit u coord position.val⟩ rfl
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, coordBit_lt u coord position.val⟩
        ⟨by norm_num, coord.isLt, by norm_num, by norm_num, by norm_num, lt_of_lt_of_le position.isLt bitsLe,
          show coordBit u coord position.val < 64 by have := coordBit_lt u coord position.val; omega⟩)
      fun i j _ _ different => ⟨Set.disjoint_left.mpr fun k inI inJ => by
          simp only [positionKeys, Set.mem_setOf_eq] at inI inJ; omega,
        siteDisjoint_of_fam fun k inS => by
          simp only [positionKeys, Set.mem_setOf_eq] at inS; omega⟩
  refine Tagged.bind_pure ((Tagged.tableM (S := fun coord => {k | ∃ i < bits, k ∈ positionKeys coord i}) 2
    coordTable fun i j _ _ different => ⟨?_, ?_⟩).mono ?_) _
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    obtain ⟨_, _, inI⟩ := inI
    obtain ⟨_, _, inJ⟩ := inJ
    simp only [positionKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      obtain ⟨_, _, inS⟩ := inS
      simp only [positionKeys, Set.mem_setOf_eq] at inS
      omega
  · rintro k ⟨coord, coordLt, ⟨position, positionLt, inS⟩⟩
    simp only [positionKeys, digestLabelKeys, Set.mem_setOf_eq] at inS ⊢
    omega

/-- **The digest evaluator**: the key's labels, then both finals of every digit. -/
theorem digestEvalM_tagged (bits digits : Nat) (bitsLe : bits ≤ 65536) (digitsLe : digits ≤ 32768)
    (labels : Fin 2 → Fin bits → Block) (u : AffineInput) (entries : Fin digits → Exception.Entry) :
    Tagged (digestLabelKeys bits ∪ digestFinalKeys digits) (digestEvalM bits digits labels u entries) := by
  unfold digestEvalM
  refine Tagged.bind' (digestKeyM_tagged bits bitsLe labels u) (fun key => ?_) ?_ ?_ le_rfl
  · refine (Tagged.tableM (S := finalDigitKeys) digits (fun o => ?_)
      fun i j _ _ different => ⟨Set.disjoint_left.mpr fun k inI inJ => by
          simp only [finalDigitKeys, Set.mem_setOf_eq] at inI inJ; omega,
        siteDisjoint_of_fam fun k inS => by
          simp only [finalDigitKeys, Set.mem_setOf_eq] at inS; omega⟩).mono ?_
    · have key0 : (⟨9, 0, 0, 0, 0, 2 * o.val, 0⟩ : TagKey).InRange :=
        ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
          show 2 * o.val < 65536 by have := o.isLt; omega, by norm_num⟩
      have key1 : (⟨9, 0, 0, 0, 0, 2 * o.val + 1, 0⟩ : TagKey).InRange :=
        ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
          show 2 * o.val + 1 < 65536 by have := o.isLt; omega, by norm_num⟩
      unfold finalMaskM
      refine Tagged.bind' (Tagged.bind_pure (Tagged.h128M ({⟨9, 0, 0, 0, 0, 2 * o.val, 0⟩} : Set TagKey) _
          (digestFinalTag (2 * o.val)) ⟨9, 0, 0, 0, 0, 2 * o.val, 0⟩ rfl rfl key0) _)
        (S' := {⟨9, 0, 0, 0, 0, 2 * o.val + 1, 0⟩})
        (fun _ => Tagged.bind_pure (Tagged.bind_pure (Tagged.h128M
          ({⟨9, 0, 0, 0, 0, 2 * o.val + 1, 0⟩} : Set TagKey) _ (digestFinalTag (2 * o.val + 1))
          ⟨9, 0, 0, 0, 0, 2 * o.val + 1, 0⟩ rfl rfl key1) _) _)
        (Set.disjoint_singleton.mpr fun same => by simp only [TagKey.mk.injEq] at same; omega)
        (siteDisjoint_of_fam fun k inS => by
          rw [Set.mem_singleton_iff.mp inS]; exact ⟨by norm_num, by norm_num⟩) ?_
      rintro k (inS | inS) <;> rw [Set.mem_singleton_iff.mp inS]
      · exact ⟨rfl, rfl, rfl, rfl, rfl, show 2 * o.val / 2 = o.val by omega, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, show (2 * o.val + 1) / 2 = o.val by omega, rfl⟩
    · rintro k ⟨o, small, inS⟩
      simp only [finalDigitKeys, digestFinalKeys, Set.mem_setOf_eq] at inS ⊢
      omega
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [digestLabelKeys, digestFinalKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [digestLabelKeys, Set.mem_setOf_eq] at inS
      omega

/-- The entry's digest evaluator (254 positions, 91 digits). -/
theorem entryDigest_tagged (labels : Fin 2 → Fin coordinateBitCount → Block) (u : AffineInput)
    (entries : Fin digitCount → Exception.Entry) :
    Tagged digestKeys (digestEvalM coordinateBitCount digitCount labels u entries) :=
  digestEvalM_tagged coordinateBitCount digitCount (by decide) (by decide) labels u entries

/-! ### The reach -/

/-- The keys of the full replay: the conversion and body blocks, the key, every mask site. -/
def fullReplayKeys : Set TagKey := replayConvKeys ∪ ({keyKey} ∪ maskKeys digitCount)

/-- The keys of the reach on the curve: the full replay and the digest. -/
def reachKeys : Set TagKey := fullReplayKeys ∪ digestKeys

/-- The keys of the reach off the curve: the conversion blocks and the digest. -/
def reachOffKeys : Set TagKey := replayConvKeys ∪ digestKeys

theorem replayConvKeys_fam : ∀ k ∈ replayConvKeys, k.fam ≤ 6 := by
  intro k inside
  have := replayConvKeys_sub inside
  simp only [coordKeys, Set.mem_union, Set.mem_setOf_eq] at this
  omega

theorem digestKeys_fam : ∀ k ∈ digestKeys, k.fam = 8 ∨ k.fam = 9 := by
  intro k inside
  simp only [digestKeys, digestLabelKeys, digestFinalKeys, Set.mem_union, Set.mem_setOf_eq] at inside
  omega

theorem maskKeys_fam : ∀ k ∈ maskKeys digitCount, k.fam = 7 := by
  intro k inside
  simp only [maskKeys, nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inside
  omega

/-- Key sets whose pad keys and mask keys lie on one side only share no site. -/
theorem siteDisjoint_of_fams {S S' : Set TagKey} (fams : ∀ k ∈ S, ∀ k' ∈ S', k.fam = k'.fam → k.fam ≠ 6 ∧ k.fam ≠ 7) :
    SiteDisjoint S S' :=
  siteDisjoint_of_fields (fun k inS k' inS' six six' => absurd six (fams k inS k' inS' (six.trans six'.symm)).1)
    (fun k inS k' inS' seven seven' => absurd seven (fams k inS k' inS' (seven.trans seven'.symm)).2)

/-- **The full replay is `Tagged`.** -/
theorem replay_tagged (pub : Entry.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Tagged fullReplayKeys (Entry.replay pub input labels) := by
  unfold Entry.replay
  refine Tagged.bind (replayConv_tagged pub input labels) (fun conv => ?_) ?_ ?_
  · refine Tagged.bind (keyM_tagged _) (fun key => Tagged.bind_pure (maskAnswersM_tagged key digitCount (by decide)
      (by decide)) _) ?_ ?_
    · refine Set.disjoint_left.mpr fun k inK inM => ?_
      rw [Set.mem_singleton_iff.mp inK] at inM
      have := maskKeys_fam _ inM
      simp only [keyKey] at this
      omega
    · exact siteDisjoint_of_fam fun k inK => by
        rw [Set.mem_singleton_iff.mp inK]; exact ⟨by decide, by decide⟩
  · refine Set.disjoint_left.mpr fun k inC inR => ?_
    have := replayConvKeys_fam k inC
    rcases inR with inK | inM
    · rw [Set.mem_singleton_iff.mp inK] at this
      simp only [keyKey] at this
      omega
    · have := maskKeys_fam k inM
      omega
  · refine siteDisjoint_of_fams fun k inC k' inR same => ?_
    have := replayConvKeys_fam k inC
    rcases inR with inK | inM
    · rw [Set.mem_singleton_iff.mp inK] at same
      simp only [keyKey] at same
      omega
    · have := maskKeys_fam k' inM
      omega

/-- **The reach on the curve is `Tagged`** (`Entry.reachCM`: the full replay, then the digest). -/
theorem reachCM_tagged (pub : Entry.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Tagged reachKeys (Entry.reachCM pub input labels) := by
  unfold Entry.reachCM
  refine Tagged.bind (replay_tagged pub input labels) (fun out => Tagged.bind_pure (entryDigest_tagged _ _ _) _)
    ?_ ?_
  · refine Set.disjoint_left.mpr fun k inR inD => ?_
    have := digestKeys_fam k inD
    rcases inR with inC | inK | inM
    · have := replayConvKeys_fam k inC
      omega
    · rw [Set.mem_singleton_iff.mp inK] at this
      simp only [keyKey] at this
      omega
    · have := maskKeys_fam k inM
      omega
  · refine siteDisjoint_of_fams fun k inR k' inD same => ?_
    have := digestKeys_fam k' inD
    omega

/-- **The reach off the curve is `Tagged`** (the conversion blocks, then the digest). -/
theorem reachOffCM_tagged (pub : Entry.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Tagged reachOffKeys (EntryReading.reachOffCM pub input labels) := by
  unfold EntryReading.reachOffCM
  refine Tagged.bind (replayConv_tagged pub input labels) (fun conv => Tagged.bind_pure (entryDigest_tagged _ _ _) _)
    ?_ ?_
  · refine Set.disjoint_left.mpr fun k inC inD => ?_
    have := replayConvKeys_fam k inC
    have := digestKeys_fam k inD
    omega
  · refine siteDisjoint_of_fams fun k inC k' inD same => ?_
    have := digestKeys_fam k' inD
    omega

/-! ### The shadow off the curve -/

/-- **The shadow's off-curve program is `Tagged`.** -/
theorem crtShadowOffCurve_tagged [FieldCertificate] [GroupCertificate]
    (source : (Instance.view).Source) (u : AffineInput) :
    Tagged reachOffKeys (H8.crtShadowOffCurve source u) := by
  unfold H8.crtShadowOffCurve
  exact Tagged.bind_pure (reachOffCM_tagged _ u _) _

/-- **`crtThirdSwap_of_tagged`'s hypothesis for `crtEntry` and its shadow.** -/
theorem crtShadow_offCurve_tagged : ∀ [FieldCertificate] [GroupCertificate]
    (source : (PublicFirst.viewHere Instance.crtEntry).Source) (u : AffineInput) (coin : (H8.crtShadow).Coin),
    ∃ S : Set TagKey, Tagged S ((H8.crtShadow).offCurve source u coin) := by
  intro _ _ source u coin
  dsimp only [H8.crtShadow]
  exact ⟨reachOffKeys, crtShadowOffCurve_tagged source u⟩

end Kriterion.CRT.Paths
