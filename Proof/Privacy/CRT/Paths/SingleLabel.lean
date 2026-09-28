/-
**`ReplaySingleLabel crtEntry`** (P10's obligation, `Refill/SingleLabel.lean`).

A tag run (`KeyRun`, `Paths/Tags.lean`) records every query's key and label, and asks the keys of one site at one
label. `SingleLabelFrom` instead records, for each site, the label its first query used (`recordSite`), and asks every
query of a site to be a site of the layout, not a collector-mask position, and at that label (`SiteQueryOK`). The
translation (`singleLabelFrom_of_keyRun`) carries an invariant between the two records along the path; here the
invariant is `Compatible` (a site's recorded label is the label of a key of that site in the run's history) and
`Unread` (the sites of a later program are still unrecorded).

* a labelled key's input decodes to the key's site and label (`siteOf_code`, `hashInput_label`);
* `replayConv`'s keys are the chunk, conversion and body keys of both coordinates (`replayConvKeys`), whose sites are
  pad sites of the layout (`replayConvKeys_sites`); the non-collector replay's keys are mask keys of stage 1 below
  site 228 (`nonCollectorKeys_sites`); the two share no site;
* `crtEntry_replaySingleLabel : ReplaySingleLabel Instance.crtEntry`, with `answers_le` from `crtLayout_answers_le`.
-/

import Proof.Privacy.CRT.Paths.EvalCoord
import Proof.Privacy.CRT.Paths.Entry
import Proof.Privacy.CRT.Refill.SingleLabel
import Proof.Privacy.CRT.Refill.Hop
import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy

/-! ### A labelled key's input -/

theorem tagInRange_of {k : TagKey} (range : k.InRange) :
    TagInRange k.coord k.idx k.stage k.level k.slot k.part :=
  ⟨range.2.1, range.2.2.1, range.2.2.2.1, range.2.2.2.2.1, range.2.2.2.2.2.1, range.2.2.2.2.2.2⟩

/-- A labelled hash input's low 128 bits are its label. -/
theorem hashInput_label (label : Block) (tag : Nat) : hashInput label tag % 2 ^ 128 = label.toNat := by
  unfold hashInput
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt label.isLt]

/-- **A key in range decodes to its site.** -/
theorem siteOf_code {k : TagKey} (range : k.InRange) : siteOf k.code = k.site := by
  have inRange := tagInRange_of range
  unfold siteOf
  rw [TagKey.code, tagFamily_tagCode inRange, tagCoord_tagCode inRange, tagIdx_tagCode inRange,
    tagSlot_tagCode inRange, tagStage_tagCode inRange]
  unfold TagKey.site
  obtain ⟨fam, coord, idx, stage, level, slot, part⟩ := k
  dsimp only
  split <;> split <;> simp_all

/-- A key in range is a collector-mask position only at family 7, stage 0. -/
theorem notCollector_of {k : TagKey} (range : k.InRange) (away : k.fam ≠ 7 ∨ k.stage ≠ 0) :
    isCollectorMaskTag k.code = false := by
  have inRange := tagInRange_of range
  unfold isCollectorMaskTag
  rw [TagKey.code, tagFamily_tagCode inRange, tagStage_tagCode inRange]
  rcases away with away | away <;> simp [away]

theorem recordSite_key_none {k : TagKey} (range : k.InRange) (noSite : k.site = none)
    (seen : SiteId → Option ℕ) (label : Block) : recordSite seen (hashInput label k.code) = seen := by
  unfold recordSite
  rw [hashInput_tag, siteOf_code range, noSite]

theorem recordSite_key_some {k : TagKey} (range : k.InRange) {site : SiteId} (isSite : k.site = some site)
    (seen : SiteId → Option ℕ) (label : Block) :
    recordSite seen (hashInput label k.code) = Function.update seen site (some label.toNat) := by
  unfold recordSite
  rw [hashInput_tag, siteOf_code range, isSite, hashInput_label]

theorem siteQueryOK_none {layout : SiteLayout} {k : TagKey} (range : k.InRange) (noSite : k.site = none)
    (seen : SiteId → Option ℕ) (label : Block) : SiteQueryOK layout seen (hashInput label k.code) := by
  unfold SiteQueryOK
  rw [hashInput_tag, siteOf_code range, noSite]
  exact trivial

theorem siteQueryOK_some {layout : SiteLayout} {k : TagKey} (range : k.InRange) {site : SiteId}
    (isSite : k.site = some site) (member : site ∈ layout.sites) (notCollector : isCollectorMaskTag k.code = false)
    (seen : SiteId → Option ℕ) (label : Block) (labelOK : seen site = none ∨ seen site = some label.toNat) :
    SiteQueryOK layout seen (hashInput label k.code) := by
  unfold SiteQueryOK
  rw [hashInput_tag, siteOf_code range, isSite, hashInput_label]
  exact ⟨member, notCollector, labelOK⟩

/-! ### From a tag run to `SingleLabelFrom` -/

/-- **The translation**: a tag run is single-label along an invariant between the two records that every query
keeps and that gives the leaf predicate. -/
theorem singleLabelFrom_of_keyRun {α : Type} {layout : SiteLayout} {S : Set TagKey}
    {Q : α → List (TagKey × Block) → Prop} {leaf : (SiteId → Option ℕ) → α → Prop}
    (Inv : (SiteId → Option ℕ) → List (TagKey × Block) → Prop)
    (step : ∀ seenSL seenKR key label, key ∈ S → key.InRange → key ∉ keysOf seenKR → SiteLabel seenKR key label →
      Inv seenSL seenKR → SiteQueryOK layout seenSL (hashInput label key.code) ∧
        Inv (recordSite seenSL (hashInput label key.code)) ((key, label) :: seenKR))
    (atLeaf : ∀ seenSL seenKR value, Q value seenKR → Inv seenSL seenKR → leaf seenSL value) :
    ∀ {seenKR : List (TagKey × Block)} {program : CM α}, KeyRun S Q seenKR program →
      ∀ seenSL, Inv seenSL seenKR → SingleLabelFrom layout leaf seenSL program := by
  intro seenKR program run
  induction run with
  | pure seen value post => exact fun seenSL inv => atLeaf seenSL seen value post inv
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
      intro seenSL inv
      subst coded
      obtain ⟨ok, inv'⟩ := step seenSL seen key label member range fresh sameLabel inv
      exact And.intro ok fun answer => ih answer _ inv'

/-- The recorded label of every site of a key of `S` is unset or the label of a key of that site in the history. -/
def Compatible (S : Set TagKey) (seenSL : SiteId → Option ℕ) (seenKR : List (TagKey × Block)) : Prop :=
  ∀ k ∈ S, ∀ site, k.site = some site →
    seenSL site = none ∨ ∃ p ∈ seenKR, p.1.site = some site ∧ seenSL site = some p.2.toNat

/-- No site of a key of `S` has a recorded label. -/
def Unread (S : Set TagKey) (seenSL : SiteId → Option ℕ) : Prop :=
  ∀ k ∈ S, ∀ site, k.site = some site → seenSL site = none

/-- The sites of the keys of `S` are sites of the layout, and no key of `S` is a collector-mask position. -/
def SitesOK (layout : SiteLayout) (S : Set TagKey) : Prop :=
  ∀ k ∈ S, k.InRange → ∀ site, k.site = some site → site ∈ layout.sites ∧ isCollectorMaskTag k.code = false

theorem compatible_nil {S : Set TagKey} {seenSL : SiteId → Option ℕ} (unread : Unread S seenSL) :
    Compatible S seenSL [] :=
  fun k inS site isSite => Or.inl (unread k inS site isSite)

theorem compatible_label {S : Set TagKey} {seenSL : SiteId → Option ℕ} {seenKR : List (TagKey × Block)}
    {key : TagKey} {label : Block} (member : key ∈ S) (sameLabel : SiteLabel seenKR key label)
    (compatible : Compatible S seenSL seenKR) {site : SiteId} (isSite : key.site = some site) :
    seenSL site = none ∨ seenSL site = some label.toNat := by
  rcases compatible key member site isSite with unset | ⟨p, inside, pSite, value⟩
  · exact Or.inl unset
  · right
    rw [value, sameLabel p inside (pSite.trans isSite.symm) (by rw [isSite]; exact Option.some_ne_none _)]

theorem compatible_record {S : Set TagKey} {seenSL : SiteId → Option ℕ} {seenKR : List (TagKey × Block)}
    {key : TagKey} (range : key.InRange) (label : Block) (compatible : Compatible S seenSL seenKR) :
    Compatible S (recordSite seenSL (hashInput label key.code)) ((key, label) :: seenKR) := by
  intro k inS site isSite
  cases keySite : key.site with
  | none =>
      rw [recordSite_key_none range keySite]
      rcases compatible k inS site isSite with unset | ⟨p, inside, pSite, value⟩
      · exact Or.inl unset
      · exact Or.inr ⟨p, List.mem_cons.mpr (Or.inr inside), pSite, value⟩
  | some site' =>
      rw [recordSite_key_some range keySite]
      by_cases same : site = site'
      · subst same
        exact Or.inr ⟨(key, label), List.mem_cons.mpr (Or.inl rfl), keySite, Function.update_self _ _ _⟩
      · rw [Function.update_of_ne same]
        rcases compatible k inS site isSite with unset | ⟨p, inside, pSite, value⟩
        · exact Or.inl unset
        · exact Or.inr ⟨p, List.mem_cons.mpr (Or.inr inside), pSite, value⟩

theorem unread_record {S M : Set TagKey} {seenSL : SiteId → Option ℕ} {key : TagKey} (range : key.InRange)
    (member : key ∈ S) (sites : SiteDisjoint S M) (label : Block) (unread : Unread M seenSL) :
    Unread M (recordSite seenSL (hashInput label key.code)) := by
  intro k inM site isSite
  cases keySite : key.site with
  | none =>
      rw [recordSite_key_none range keySite]
      exact unread k inM site isSite
  | some site' =>
      rw [recordSite_key_some range keySite, Function.update_of_ne]
      · exact unread k inM site isSite
      · intro same
        subst same
        have noSite := sites key member k inM (keySite.trans isSite.symm)
        rw [keySite] at noSite
        exact Option.some_ne_none _ noSite

/-- **A `Tagged` program is single-label** from any record in which its sites and a later program's sites
(`M`, site-disjoint from its own) are unread; at its leaves the later program's sites are still unread. -/
theorem singleLabelFrom_of_tagged {α : Type} {layout : SiteLayout} {S M : Set TagKey}
    {leaf : (SiteId → Option ℕ) → α → Prop} {program : CM α} (tagged : Tagged S program)
    (sitesOK : SitesOK layout S) (disjoint : SiteDisjoint S M)
    (atLeaf : ∀ seenSL value, Unread M seenSL → leaf seenSL value) (seenSL : SiteId → Option ℕ)
    (unreadS : Unread S seenSL) (unreadM : Unread M seenSL) : SingleLabelFrom layout leaf seenSL program := by
  refine singleLabelFrom_of_keyRun (fun seenSL seenKR => Compatible S seenSL seenKR ∧ Unread M seenSL)
    (fun seenSL seenKR key label member range _ sameLabel inv => ⟨?_, compatible_record range label inv.1,
      unread_record range member disjoint label inv.2⟩)
    (fun seenSL _ value _ inv => atLeaf seenSL value inv.2) tagged seenSL ⟨compatible_nil unreadS, unreadM⟩
  cases keySite : key.site with
  | none => exact siteQueryOK_none range keySite _ _
  | some site =>
      obtain ⟨inLayout, notCollector⟩ := sitesOK key member range site keySite
      exact siteQueryOK_some range keySite inLayout notCollector _ _
        (compatible_label member sameLabel inv.1 keySite)

/-! ### The keys of the replay and their sites -/

/-- A pad key of a coordinate's evaluator is a pad of a modulus index, residue below the modulus, part below the
pad count. -/
theorem coordEvalKeys_pad {T : CrtTable} {S coord : Nat} {k : TagKey} (inK : k ∈ coordEvalKeys T S coord)
    (six : k.fam = 6) :
    ∃ i : Fin T.count, k.coord = coord ∧ k.idx = i.val ∧ k.stage = 0 ∧ k.level = 0 ∧ k.slot < T.modulus i ∧
      k.part < T.padAnswers S i := by
  rcases inK with ⟨c, _, inC⟩ | ⟨i, inC | inB⟩
  · simp only [pairKeys, Set.mem_setOf_eq] at inC
    exfalso
    omega
  · simp only [convKeys, Set.mem_setOf_eq] at inC
    exfalso
    omega
  · simp only [bodyKeys, Set.mem_setOf_eq] at inB
    exact ⟨i, inB.2.1, inB.2.2.1, inB.2.2.2.1, inB.2.2.2.2.1, inB.2.2.2.2.2.1, inB.2.2.2.2.2.2⟩

theorem padModulus_fin (i : Fin bn254Table.count) : Layout.padModulus i.val = bn254Table.modulus i := by
  unfold Layout.padModulus
  rw [dif_pos i.isLt]

theorem pad_mem_sites {κ i ρ : Nat} (κLt : κ < 2) (iLt : i < 84) (ρLt : ρ < Layout.padModulus i) :
    SiteId.pad κ i ρ ∈ crtLayout.sites := by
  refine List.mem_append.mpr (Or.inl ?_)
  simp only [Layout.padSites, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨κ, κLt, i, iLt, ρ, ρLt, rfl⟩

theorem mask_mem_sites {k : Nat} (kLt : k < 182) : SiteId.mask 1 k ∈ crtLayout.sites :=
  List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨k, List.mem_range.mpr kLt, rfl⟩))))

theorem coordEvalKeys_sites (S coord : Nat) (coordLt : coord < 2) :
    SitesOK crtLayout (coordEvalKeys Entry.table S coord) := by
  intro k inK range site isSite
  rcases site_cases k with ⟨six, hk⟩ | ⟨seven, hk⟩ | ⟨_, _, noSite⟩
  · obtain ⟨i, kCoord, kIdx, _, _, kSlot, _⟩ := coordEvalKeys_pad inK six
    rw [hk] at isSite
    obtain rfl := Option.some.inj isSite
    refine ⟨pad_mem_sites (by omega) ?_ ?_, notCollector_of range (Or.inl (by omega))⟩
    · have count : Entry.table.count = 84 := bn254_count
      have := i.isLt
      omega
    · rw [kIdx, padModulus_fin i]
      exact kSlot
  · have := coordEvalKeys_sub _ _ _ inK
    simp only [coordKeys, Set.mem_setOf_eq] at this
    exfalso
    omega
  · rw [noSite] at isSite
    exact absurd isSite (Option.some_ne_none _).symm

/-- The keys of `replayConv` are at pad sites of the layout, never at collector masks. -/
theorem replayConvKeys_sites : SitesOK crtLayout replayConvKeys := by
  rintro k (inX | inY)
  · exact coordEvalKeys_sites _ 0 (by norm_num) k inX
  · exact coordEvalKeys_sites _ 1 (by norm_num) k inY

theorem pairSites_digitCount : pairSites digitCount = 182 := by decide

theorem singleSites_digitCount : singleSites digitCount = 0 := by decide

/-- The non-collector replay's keys are at stage-1 mask sites of the layout. -/
theorem nonCollectorKeys_sites : SitesOK crtLayout (nonCollectorKeys digitCount) := by
  intro k inK range site isSite
  have pairs := pairSites_digitCount
  have single := singleSites_digitCount
  have facts : k.fam = 7 ∧ k.stage = 1 ∧ k.slot < 182 := by
    rcases inK with inP | inS
    · simp only [maskStageKeys, Set.mem_setOf_eq] at inP
      omega
    · simp only [maskSiteKeys, Set.mem_setOf_eq] at inS
      omega
  rw [site_mask facts.1] at isSite
  obtain rfl := Option.some.inj isSite
  rw [facts.2.1]
  exact ⟨mask_mem_sites facts.2.2, notCollector_of range (Or.inr (by omega))⟩

theorem replayConv_nonCollector_siteDisjoint : SiteDisjoint replayConvKeys (nonCollectorKeys digitCount) := by
  refine siteDisjoint_of_fields (fun k _ k' inM _ six' => ?_) (fun k inC k' _ seven _ => ?_)
  · simp only [nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inM
    omega
  · have := replayConvKeys_sub inC
    simp only [coordKeys, Set.mem_union, Set.mem_setOf_eq] at this
    omega

/-- The view's non-collector replay (the entry's, read in the tier-2 index) is `Tagged`. -/
theorem viewNonCollectorReplay_tagged (key : Block) :
    Tagged (nonCollectorKeys digitCount)
      (EntryReading.nonCollectorReplay key >>= fun masks => pure (Instance.toMasks masks)) := by
  unfold EntryReading.nonCollectorReplay
  exact Tagged.bind_pure (Tagged.bind_pure (nonCollectorMasksM_tagged key digitCount (by decide)) _) _

/-! ### The obligation -/

/-- **The two programs of the replay are single-label** whenever the first is `Tagged` by `replayConvKeys` and the
second, at every key, by the non-collector keys (programs kept abstract, so no program is ever unfolded). -/
theorem singleLabel_of_parts {β γ : Type} (conv : CM β) (rest : Block → CM γ)
    (convTagged : Tagged replayConvKeys conv)
    (restTagged : ∀ key, Tagged (nonCollectorKeys digitCount) (rest key)) :
    SingleLabelFrom crtLayout
      (fun seen _ => ∀ key : Block, SingleLabelFrom crtLayout (fun _ _ => True) seen (rest key))
      (fun _ => none) conv := by
  have inner : ∀ seenSL, Unread (nonCollectorKeys digitCount) seenSL → ∀ key : Block,
      SingleLabelFrom crtLayout (fun _ _ => True) seenSL (rest key) := by
    intro seenSL unread key
    exact singleLabelFrom_of_tagged (M := ∅) (restTagged key) nonCollectorKeys_sites
      (fun _ _ _ inside => absurd inside id) (fun _ _ _ => trivial) seenSL unread (fun _ inside => absurd inside id)
  have unreadConv : Unread replayConvKeys (fun _ => none) := fun _ _ _ _ => rfl
  have unreadMask : Unread (nonCollectorKeys digitCount) (fun _ => none) := fun _ _ _ _ => rfl
  exact singleLabelFrom_of_tagged convTagged replayConvKeys_sites replayConv_nonCollector_siteDisjoint
    (fun seenSL _ unread => inner seenSL unread) _ unreadConv unreadMask

/-- **`ReplaySingleLabel` from the parts' tag runs**, for any entry on the real layout (the entry kept abstract:
`SingleLabelFrom` is a recursive predicate, and a goal of it at a concrete program is unfolded by `whnf` into the
program's evaluation). -/
theorem replaySingleLabel_of_parts {FI EI : Type} (E : CrtEntry FI EI) (layoutEq : E.layout = crtLayout)
    (convTagged : ∀ [field : BN254.FieldCertificate] (group : @BN254.GroupCertificate field) (published : E.Public)
      (u : BN254.AffineInput) (labels : GarbledCircuit.LamportSignature),
      Tagged replayConvKeys ((E.view field group).replayConv published u labels))
    (restTagged : ∀ [field : BN254.FieldCertificate] (group : @BN254.GroupCertificate field) (key : Block),
      Tagged (nonCollectorKeys digitCount) ((E.view field group).nonCollectorReplay key)) :
    ReplaySingleLabel E := by
  refine ⟨?_, ?_⟩
  · rw [layoutEq]
    exact crtLayout_answers_le
  · intro field group published u labels
    rw [layoutEq]
    exact singleLabel_of_parts _ _ (convTagged group published u labels) (restTagged group)

/-- **P10's obligation holds for the concrete entry.** -/
theorem crtEntry_replaySingleLabel : ReplaySingleLabel Instance.crtEntry :=
  replaySingleLabel_of_parts Instance.crtEntry rfl
    (fun group published u labels => by
      dsimp only [Instance.crtEntry, Instance.view]
      exact replayConv_tagged published u labels)
    (fun group key => by
      dsimp only [Instance.crtEntry, Instance.view]
      exact viewNonCollectorReplay_tagged key)

end Kriterion.CRT.Paths
