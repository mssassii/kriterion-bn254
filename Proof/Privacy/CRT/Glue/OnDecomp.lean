/-
**`OnDecomp` for the CRT entry** (the first input of
`Laws.crtEntry_middleFactor`, `Proof/Privacy/CRT/Laws/MiddleCrt.lean`).

At an input `u` on the curve and a source, `ds` is the list of `u`'s 508 digest-label inputs (`Contain.dsOf`) and `P`
the set of their tags. The ten conjuncts of `Laws.OnDecomp`:

* the tags are family 8, so they lie away from every pad and mask site, are visible at `u` (the label at `u`'s bit),
  are pairwise distinct (a digest-label tag records its coordinate and position), and the collector programming (family
  7, stage 0) leaves them alone;
* route M's replay asks only conversion inputs (families 0 to 6), the key (family 10) and non-collector masks (family 7),
  so its value ignores `P`; the reveal reads only the conversion blocks (`Flags.replayWraps_congr`), so it ignores `P`;
* the view's entries are the full replay's, then `u`'s digest labels (`Contain.viewEntries_eq`); the entries off `ds`
  are the full replay's (`Contain.restEntries_eq`), which never ask a family-8 input, so they ignore `P`;
* the containment is `Contain.containment`.

**`crtEntry_decomp`** has exactly the type of `crtEntry_middleFactor`'s first argument.
-/

import Proof.Privacy.CRT.Glue.Containment

namespace Kriterion.CRT.Privacy.OnDecompCrt

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Align (asked hashInput_div)
open Kriterion.CRT.Privacy.Laws
open Kriterion.CRT.Privacy.H8 (visTag viewTable viewEntries programmedTable collectorTag tagHash CoreView crtRevealOn
  replayWraps rowsDoubling)
open Kriterion.CRT.Privacy.PublicFirst (viewHere)
open Kriterion.CRT.Privacy.Contain
open Kriterion.ArgoMAC.PlanB (digitCount)

set_option autoImplicit false

noncomputable section

/-! ### 1. Family-8 tags -/

theorem tagCode_small {f coord idx stage level slot part : ℕ} (hf : f < 16)
    (hin : TagInRange coord idx stage level slot part) : tagCode f coord idx stage level slot part < 2 ^ 40 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  unfold tagCode
  omega

/-- **A family-8 tag lies away from every pad and mask site.** -/
theorem family8_away {τ : ℕ} (small : τ < 2 ^ 40) (fam : tagFamily τ = 8) :
    ∀ site ∈ crtLayout.sites, tagPos τ ∉ (siteTags crtLayout site).map tagPos := by
  intro site mem hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  have fam' : tagFamily (tagPos t).val = 8 := by rw [heq, tagPos_val small]; exact fam
  have ne : ∀ {f coord idx stage level slot part : ℕ}, 5 < f → f < 8 →
      TagInRange coord idx stage level slot part →
      tagFamily (tagPos (tagCode f coord idx stage level slot part)).val ≠ 8 := by
    intro f coord idx stage level slot part h1 h2 hin
    simp only [tagPos]
    rw [Nat.mod_eq_of_lt (tagCode_small (by omega) hin), tagFamily_tagCode hin]
    omega
  rcases List.mem_append.mp mem with pad | mask
  · obtain ⟨κ', i, ρ, rfl, hκ', hi, hρ⟩ := Layout.mem_padSites pad
    obtain ⟨-, -, -, -, hm, hq⟩ := Layout.tableFacts κ' hκ' i hi
    simp only [siteTags, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have hj' : j < Layout.padCount κ' i := hj
    exact ne (by decide) (by decide) ⟨hκ', by omega, by omega, by omega, by omega, by omega⟩ fam'
  · rcases Layout.mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 2 := hj
      exact ne (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ fam'
    · simp only [siteTags, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      have hj' : j < 3 := by
        have : j < (if k = 227 then 2 else 3) := hj
        split at this <;> omega
      exact ne (by decide) (by decide) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ fam'

/-- The table position of a digest-label input. -/
theorem digest_tagOfInput {labels : LamportSignature} {u : AffineInput} {n : ℕ} (inside : n ∈ digestList labels u) :
    tagOfInput (n : BaseField) = tagPos (n / 2 ^ 128) :=
  tagOfInput_labelled (digestList_labelled inside).1

/-- **Distinct digest labels have distinct tags.** -/
theorem digest_tag_inj (labels : LamportSignature) (u : AffineInput) {c c' : Fin 2} {p p' : Fin coordinateBitCount}
    (same : tagOfInput ((hashInput (Kriterion.CRT.Entry.labelsOf labels c p)
        (digestLabelTag c.val p.val (coordBit u c p.val)) : ℕ) : BaseField) =
      tagOfInput ((hashInput (Kriterion.CRT.Entry.labelsOf labels c' p')
        (digestLabelTag c'.val p'.val (coordBit u c' p'.val)) : ℕ) : BaseField)) :
    c = c' ∧ p = p' := by
  have range := digestLabel_range u c p
  have range' := digestLabel_range u c' p'
  have lab : Paths.SameVisible.Labelled (hashInput (Kriterion.CRT.Entry.labelsOf labels c p)
      (digestLabelTag c.val p.val (coordBit u c p.val))) :=
    ⟨⟨8, c.val, 0, 0, 0, p.val, coordBit u c p.val⟩, ⟨by norm_num, range.coord, range.idx, range.stage,
      range.level, range.slot, range.part⟩, _, rfl⟩
  have lab' : Paths.SameVisible.Labelled (hashInput (Kriterion.CRT.Entry.labelsOf labels c' p')
      (digestLabelTag c'.val p'.val (coordBit u c' p'.val))) :=
    ⟨⟨8, c'.val, 0, 0, 0, p'.val, coordBit u c' p'.val⟩, ⟨by norm_num, range'.coord, range'.idx, range'.stage,
      range'.level, range'.slot, range'.part⟩, _, rfl⟩
  have vals := congrArg Fin.val same
  rw [tagOfInput_labelled lab, tagOfInput_labelled lab', tagPos_val (labelled_tag lab),
    tagPos_val (labelled_tag lab'), hashInput_div, hashInput_div] at vals
  have bit := Paths.coordBit_lt u c p.val
  have bit' := Paths.coordBit_lt u c' p'.val
  obtain ⟨_, hc, hs, _⟩ := Align.digestLabelTag_fields (b := coordBit u c p.val) c.isLt
    (lt_of_lt_of_le p.isLt (by decide)) (by omega)
  obtain ⟨_, hc', hs', _⟩ := Align.digestLabelTag_fields (b := coordBit u c' p'.val) c'.isLt
    (lt_of_lt_of_le p'.isLt (by decide)) (by omega)
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · rw [← hc, ← hc', vals]
  · rw [← hs, ← hs', vals]

/-! ### 2. `P` and `ds` -/

section Sets

variable [FieldCertificate] [GroupCertificate] (source : Kriterion.CRT.Entry.Source) (u : AffineInput)

/-- The tags of `u`'s digest labels. -/
def pOf : Finset (Fin (2 ^ 40)) := ((dsOf source u).map tagOfInput).toFinset

theorem mem_pOf {p : Fin (2 ^ 40)} (inside : p ∈ pOf source u) :
    ∃ n ∈ digestList (Kriterion.CRT.Entry.labels source u) u, p = tagPos (n / 2 ^ 128) := by
  unfold pOf dsOf at inside
  rw [List.mem_toFinset, List.map_map] at inside
  obtain ⟨n, member, rfl⟩ := List.mem_map.mp inside
  exact ⟨n, member, digest_tagOfInput member⟩

/-- **A labelled input off family 8 has a tag outside `P`.** -/
theorem tag_not_mem {n : ℕ} (labelled : Paths.SameVisible.Labelled n) (fam : tagFamily (n / 2 ^ 128) ≠ 8) :
    tagPos (n / 2 ^ 128) ∉ pOf source u := fun inside => by
  obtain ⟨d, member, same⟩ := mem_pOf source u inside
  obtain ⟨labelledD, famD, _⟩ := digestList_labelled member
  have vals := congrArg Fin.val same
  rw [tagPos_val (labelled_tag labelled), tagPos_val (labelled_tag labelledD)] at vals
  exact fam (vals ▸ famD)

theorem sites_away : ∀ p ∈ pOf source u, ∀ site ∈ Instance.crtEntry.layout.sites,
    p ∉ (siteTags Instance.crtEntry.layout site).map tagPos := by
  intro p inside
  obtain ⟨n, member, rfl⟩ := mem_pOf source u inside
  obtain ⟨labelled, fam, _⟩ := digestList_labelled member
  exact family8_away (labelled_tag labelled) fam

theorem visible_P : ∀ p ∈ pOf source u, visTag Kriterion.CRT.Entry.table u p.val = true := by
  intro p inside
  obtain ⟨n, member, rfl⟩ := mem_pOf source u inside
  obtain ⟨labelled, _, visible⟩ := digestList_labelled member
  rw [tagPos_val (labelled_tag labelled)]
  exact visible

theorem ds_nodup : ((dsOf source u).map tagOfInput).Nodup := by
  unfold dsOf digestList
  simp only [List.map_map, List.map_flatMap, List.map_cons, List.map_nil]
  rw [List.nodup_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun p _ => List.nodup_singleton _, ?_⟩
    refine (List.nodup_finRange coordinateBitCount).imp fun {p p'} ne => ?_
    intro x one two
    rw [List.mem_singleton] at one two
    exact ne (digest_tag_inj _ u (one.symm.trans two)).2
  · refine (List.nodup_finRange 2).imp fun {c c'} ne => ?_
    intro x one two
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp one
    obtain ⟨p', _, hp'⟩ := List.mem_flatMap.mp two
    rw [List.mem_singleton] at hp hp'
    exact ne (digest_tag_inj _ u (hp.symm.trans hp')).1

theorem ds_mem_P : ∀ x ∈ dsOf source u, tagOfInput x ∈ pOf source u :=
  fun x inside => List.mem_toFinset.mpr (List.mem_map_of_mem inside)

theorem programmed_P : ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))),
    ∀ p ∈ pOf source u, programmedTable table drawn p = table p := by
  intro table drawn p inside
  obtain ⟨n, member, rfl⟩ := mem_pOf source u inside
  obtain ⟨labelled, fam, _⟩ := digestList_labelled member
  exact programmedTable_off _ drawn table (drawnTag_ne drawn (labelled_tag labelled) (Or.inl (by omega)))

end Sets

/-! ### 3. The replay and the reveal ignore `P` -/

section Ignore

variable [FieldCertificate] [GroupCertificate] (source : Kriterion.CRT.Entry.Source) (u : AffineInput)

/-- The inputs a program asks along its path are the ones `asked` lists. -/
theorem queriesAlong_eq (H : HashN) {α : Type} : ∀ R : CM α, Flags.queriesAlong H R = asked H R
  | .pure _ => rfl
  | .query n next => by
    show n :: Flags.queriesAlong H (next (H n)) = n :: asked H (next (H n))
    rw [queriesAlong_eq H (next (H n))]

/-- Route M's replay value on a table. -/
theorem outOf_eq (table : TagTable) :
    outOf Instance.crtEntry table source u =
      ((Instance.view).replayProgram (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u)).eval
        (tagHash table) := rfl

theorem replay_ignores (valid : validate u = true) : Ignores ↑(pOf source u) (fun table => outOf Instance.crtEntry table source u) := by
  intro T T' agree
  show outOf Instance.crtEntry T source u = outOf Instance.crtEntry T' source u
  rw [outOf_eq, outOf_eq]
  refine Flags.eval_congr (tagHash T) (tagHash T') _ fun n member => ?_
  rw [queriesAlong_eq] at member
  obtain ⟨labelled, _⟩ := viewReplay_off u (tagHash T) _ _ n member
  have fam := (viewReplay_visible u valid (tagHash T) _ _ n member).2
  exact agree _ (tag_not_mem source u labelled fam)

/-- **The reveal on the programmed table ignores `P`**: it reads only the conversion blocks. -/
theorem reveal_ignores :
    ∀ (targets : Fin 91 → FieldMacToECMac.HomogeneousValue)
      (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (t t' : TagTable),
      (∀ p, p ∉ pOf source u → t p = t' p) →
        (crtRevealOn source u targets (programmedTable t drawn) ↔
          crtRevealOn source u targets (programmedTable t' drawn)) := by
  intro targets drawn t t' agree
  have agreeP := programmedTable_agree (↑(pOf source u)) drawn t t' fun p hp => agree p (by simpa using hp)
  have wraps : replayWraps source u (programmedTable t drawn) ↔ replayWraps source u (programmedTable t' drawn) := by
    refine Flags.replayWraps_congr source u _ _ fun n member => ?_
    rw [queriesAlong_eq] at member
    obtain ⟨labelled, family, _⟩ := replayConv_facts _ u _ _ n member
    have h := agreeP (tagPos (n / 2 ^ 128)) (by rw [Finset.mem_coe]; exact tag_not_mem source u labelled (by omega))
    exact h
  show rowsDoubling targets ∨ replayWraps source u (programmedTable t drawn) ↔
    rowsDoubling targets ∨ replayWraps source u (programmedTable t' drawn)
  rw [wraps]

end Ignore

/-! ### 4. The view's entries -/

section Entries

variable [FieldCertificate] [GroupCertificate] (source : Kriterion.CRT.Entry.Source) (u : AffineInput)

theorem hashEntries (valid : validate u = true) :
    ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))),
      HashEntries (viewEntries Instance.crtEntry Kriterion.CRT.Entry.table u
        (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn)) := by
  intro table drawn
  rw [viewEntries_eq source u valid, replayEntries_eq]
  intro e member
  rcases List.mem_append.mp member with inRep | inDig
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp inRep
    exact ⟨_, rfl⟩
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp inDig
    exact ⟨_, rfl⟩

theorem entries_split (valid : validate u = true) :
    ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))),
      viewEntries Instance.crtEntry Kriterion.CRT.Entry.table u
          (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn) =
        restEntries Instance.crtEntry Kriterion.CRT.Entry.table u (dsOf source u)
            (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn) ++
          tableEntries (viewTable Instance.crtEntry Kriterion.CRT.Entry.table u
            (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn)) (dsOf source u) := by
  intro table drawn
  rw [viewEntries_eq source u valid, restEntries_eq source u valid, tableEntries_eq]

/-- Two tables that agree off `P` give view tables that agree off `P`. -/
theorem vt_agree (T T' : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (agree : ∀ p, p ∉ (↑(pOf source u) : Set (Fin (2 ^ 40))) → T p = T' p) :
    ∀ p, p ∉ pOf source u → vtOf source u T drawn p = vtOf source u T' drawn p := by
  intro p hp
  rw [vtOf_apply, vtOf_apply]
  split_ifs
  · exact programmedTable_agree _ drawn T T' agree p (by simpa using hp)
  · rfl

theorem rest_ignores (valid : validate u = true) :
    ∀ drawn : List (BMR.Collector × ((Block × Block × Block) × Block)),
      Ignores ↑(pOf source u) fun table => restEntries Instance.crtEntry Kriterion.CRT.Entry.table u (dsOf source u)
        (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn) := by
  intro drawn T T' agree
  show restEntries Instance.crtEntry Kriterion.CRT.Entry.table u (dsOf source u)
      (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u T drawn) =
    restEntries Instance.crtEntry Kriterion.CRT.Entry.table u (dsOf source u)
      (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u T' drawn)
  rw [restEntries_eq source u valid, restEntries_eq source u valid, replayEntries_eq, replayEntries_eq]
  have vtAgree := vt_agree source u T T' drawn agree
  have agreeAt : ∀ n ∈ asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u T drawn)))
      (Kriterion.CRT.Entry.replay (Kriterion.CRT.Entry.publish source) u (Kriterion.CRT.Entry.labels source u)),
      schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u T drawn)) n =
        schemeHash (tableOracle (FI := Empty) (EI := Empty) (vtOf source u T' drawn)) n := by
    intro n member
    obtain ⟨labelled, _, fam⟩ := entryReplay_facts _ u _ valid _ n member
    show vtOf source u T drawn (tagOfInput (n : BaseField)) = vtOf source u T' drawn (tagOfInput (n : BaseField))
    exact vtAgree _ (by rw [tagOfInput_labelled labelled]; exact tag_not_mem source u labelled fam)
  obtain ⟨askedEq, _⟩ := Paths.SameVisible.asked_congr _ _ _ agreeAt
  rw [askedEq]
  refine List.map_congr_left fun x member => ?_
  obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
  obtain ⟨labelled, _, fam⟩ := entryReplay_facts _ u _ valid _ n inside
  rw [vtAgree _ (by rw [tagOfInput_labelled labelled]; exact tag_not_mem source u labelled fam)]

theorem contain (valid : validate u = true) :
    ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
      (installed : LazyOracle.State Empty Empty), drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (outOf Instance.crtEntry table source u).key drawn)
          (finOf Instance.crtEntry table source u) = some installed →
        ∀ x, installed.hash.lookup x =
          (Privacy.installEntries (restEntries Instance.crtEntry Kriterion.CRT.Entry.table u (dsOf source u)
            (viewOf Instance.crtEntry Kriterion.CRT.Entry.table source u table drawn)) LazyOracle.empty).hash.lookup x := by
  intro table drawn installed complete done x
  rw [restEntries_eq source u valid]
  exact containment source u valid table drawn installed complete done x

/-- **`OnDecomp` at one source on the curve.** -/
theorem onDecomp_at (valid : validate u = true) :
    OnDecomp Instance.crtEntry Kriterion.CRT.Entry.table crtRevealOn source u (pOf source u) (dsOf source u) :=
  ⟨sites_away source u, visible_P source u, ds_nodup source u, ds_mem_P source u, programmed_P source u,
    replay_ignores source u valid, reveal_ignores source u, hashEntries source u valid, entries_split source u valid,
    rest_ignores source u valid, contain source u valid⟩

end Entries

/-- The scheme's function is defined only on the curve, where `validate` holds. -/
theorem valid_of_function [FieldCertificate] [GroupCertificate] {scalar : NonZeroScalar} {u : AffineInput}
    {Q : Point} (defined : (Instance.crtEntry.scheme inferInstance inferInstance).function scalar u = some Q) :
    validate u = true := by
  refine (validate_eq_true_iff u).mpr ((decodePoint_defined u).mp fun none => ?_)
  have : (Instance.crtEntry.scheme inferInstance inferInstance).function scalar u = (decodePoint u).map _ := rfl
  rw [this, none] at defined
  exact absurd defined (by simp)

/-- **The on-curve decomposition of the CRT entry**, exactly the first argument of
`Laws.crtEntry_middleFactor`. -/
theorem crtEntry_decomp : ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput)
    (Q : Point), (Instance.crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
      ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField),
        OnDecomp Instance.crtEntry Kriterion.CRT.Entry.table crtRevealOn source u P ds := by
  intro _ _ scalar u Q defined source
  exact ⟨pOf source u, dsOf source u, onDecomp_at source u (valid_of_function defined)⟩

end

end Kriterion.CRT.Privacy.OnDecompCrt
