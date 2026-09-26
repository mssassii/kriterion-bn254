/-
**The replay's refill path and canonical queries on the concrete entry** (for `routeMReplay_pure`, `Laws/TableRun.lean`): route M's replay program (`(Instance.view).replayProgram`) is `Tagged`
(`viewReplay_tagged`), and a tag run whose site keys are at their sites' own tags gives

* `refillPath_of_keyRun`: the refill path conditions (`RefillPath`, `Laws/ReplayOn.lean`) from every lazy state. The
  invariant (`PathInv`) says that every site of a key in the history is touched in the current state, and that
  every table position read so far is a history key's tag position (off the sites) or a position of a history key's
  site. A non-site query is stored or fresh: fresh, its position is unread because the keys are distinct and away from
  every site because its family is not 6 or 7. A site query is at a touched site, or at a clean one: clean, no earlier
  key has its site (one label per site, so that site would be touched), and distinct sites have disjoint positions.
  After the query the queried point is stored, so the site is touched;
* `canonical_of_keyRun`: every query is below `p` and at one of its site's own tags (`Canonical`);
* `replay_refillPath`, `replay_canonical`, `replay_keyNonSite` for the concrete entry.
-/

import Proof.Privacy.CRT.Paths.SingleLabel
import Proof.Privacy.CRT.Paths.TableFacts
import Proof.Privacy.CRT.Laws.TableRun
import Proof.Privacy.CRT.Laws.RefillFacts

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT.Privacy Kriterion.CRT.Privacy.Laws

/-! ### Stored points only accumulate -/

/-- Every point stored in `σ` is stored in `σ'`. -/
def Keeps (σ σ' : LazyOracle.State Empty Empty) : Prop :=
  ∀ y, (σ.hash.lookup y).isSome → (σ'.hash.lookup y).isSome

theorem Keeps.trans {σ σ' σ'' : LazyOracle.State Empty Empty} (first : Keeps σ σ') (second : Keeps σ' σ'') :
    Keeps σ σ'' :=
  fun y found => second y (first y found)

theorem keeps_plantHash (σ : LazyOracle.State Empty Empty) (x : BaseField) (a : Block × Block) :
    Keeps σ (plantHash x a σ) := by
  intro y found
  rw [plantHash_lookup]
  split
  · rfl
  · exact found

theorem keeps_installPoints : ∀ (pairs : List (BaseField × (Block × Block))) (σ : LazyOracle.State Empty Empty),
    Keeps σ (installPoints pairs σ)
  | [], _ => fun _ found => found
  | pair :: rest, σ => by
      have step : installPoints (pair :: rest) σ = installPoints rest (installOne σ ⟨.hash pair.1, pair.2⟩) := rfl
      rw [step, installOne_hash]
      split
      · exact (keeps_plantHash σ pair.1 pair.2).trans (keeps_installPoints rest _)
      · exact keeps_installPoints rest σ

/-- After a lazy query the queried point is stored, and every stored point stays. -/
theorem lazyReader_keeps (n : ℕ) (σ : LazyOracle.State Empty Empty) :
    ∀ b ∈ (lazyReader n σ).support, Keeps σ b.2 ∧ (b.2.hash.lookup (n : BaseField)).isSome := by
  intro b member
  cases found : σ.hash.lookup (n : BaseField) with
  | none =>
      rw [lazyReader_fresh n σ found, PMF.support_map] at member
      obtain ⟨a, _, rfl⟩ := member
      refine ⟨keeps_plantHash σ _ a, ?_⟩
      rw [plantHash_lookup, if_pos rfl]
      rfl
  | some v =>
      rw [lazyReader_stored n σ v found, PMF.support_pure] at member
      rw [Set.mem_singleton_iff.mp member]
      refine ⟨fun _ stored => stored, ?_⟩
      rw [found]
      rfl

/-- A site is touched exactly when one of its points is stored. -/
theorem untouched_eq_false_iff {points : List BaseField} {σ : LazyOracle.State Empty Empty} :
    untouched points σ = false ↔ ∃ x ∈ points, (σ.hash.lookup x).isSome := by
  unfold untouched
  rw [List.all_eq_false]
  constructor
  · rintro ⟨x, mem, notNone⟩
    refine ⟨x, mem, ?_⟩
    rw [lookupHash_isNone] at notNone
    cases h : σ.hash.lookup x with
    | none =>
        rw [h] at notNone
        exact absurd rfl notNone
    | some _ => rfl
  · rintro ⟨x, mem, found⟩
    refine ⟨x, mem, ?_⟩
    rw [lookupHash_isNone]
    cases h : σ.hash.lookup x with
    | none =>
        rw [h] at found
        exact absurd found (by simp)
    | some _ => simp

theorem untouched_false_mono {points : List BaseField} {σ σ' : LazyOracle.State Empty Empty}
    (dirty : untouched points σ = false) (keeps : Keeps σ σ') : untouched points σ' = false := by
  obtain ⟨x, mem, found⟩ := untouched_eq_false_iff.mp dirty
  exact untouched_eq_false_iff.mpr ⟨x, mem, keeps x found⟩

/-! ### Keys at their sites' tags -/

/-- The site keys of `S` are at sites of the layout, at one of the site's own tags. -/
def SiteTagsOK (layout : SiteLayout) (S : Set TagKey) : Prop :=
  ∀ k ∈ S, k.InRange → ∀ site, k.site = some site → site ∈ layout.sites ∧ k.code ∈ siteTags layout site

theorem tagPos_injective {t t' : ℕ} (small : t < 2 ^ 40) (small' : t' < 2 ^ 40) (same : tagPos t = tagPos t') :
    t = t' := by
  have values := congrArg Fin.val same
  simp only [tagPos] at values
  rwa [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt small'] at values

/-- **A non-site key is away from every site's positions.** -/
theorem away_of_nonSite {layout : SiteLayout} (points : PointFacts layout) {k : TagKey} (range : k.InRange)
    (noSite : k.site = none) : ∀ site ∈ layout.sites, tagPos k.code ∉ (siteTags layout site).map tagPos := by
  intro site member inside
  obtain ⟨tag, hit, same⟩ := List.mem_map.mp inside
  have equal := tagPos_injective (points.bound site member tag hit) (TagKey.code_lt range) same
  have decode := points.decode site member tag hit
  rw [equal, siteOf_code range, noSite] at decode
  cases decode

/-- A labelled input at a site key is one of the site's points at its label. -/
theorem mem_sitePoints {layout : SiteLayout} {k : TagKey} {site : SiteId} (hit : k.code ∈ siteTags layout site)
    (label : Block) : ((hashInput label k.code : ℕ) : BaseField) ∈ sitePoints layout site label.toNat :=
  List.mem_map.mpr ⟨k.code, hit, rfl⟩

/-! ### The path invariant -/

/-- **The refill path invariant** along a tag run: the history's keys are in `S` and in range, the site of every
history key is touched, and every position read is a history key's tag position (off the sites) or a position of a
history key's site. -/
structure PathInv (layout : SiteLayout) (S : Set TagKey) (read : Set (Fin (2 ^ 40))) (σ : LazyOracle.State Empty Empty)
    (seen : List (TagKey × Block)) : Prop where
  keys : ∀ q ∈ seen, q.1 ∈ S ∧ q.1.InRange
  touched : ∀ q ∈ seen, ∀ site, q.1.site = some site → untouched (sitePoints layout site q.2.toNat) σ = false
  reads : ∀ p ∈ read, (∃ q ∈ seen, q.1.site = none ∧ p = tagPos q.1.code) ∨
    (∃ q ∈ seen, ∃ site, q.1.site = some site ∧ p ∈ sitePos layout site)

theorem PathInv.start (layout : SiteLayout) (S : Set TagKey) (σ : LazyOracle.State Empty Empty) :
    PathInv layout S ∅ σ [] :=
  ⟨fun _ inside => absurd inside List.not_mem_nil, fun _ inside => absurd inside List.not_mem_nil,
    fun _ inside => absurd inside id⟩

/-- One query keeps the invariant. -/
theorem PathInv.step {layout : SiteLayout} {S : Set TagKey} {read read' : Set (Fin (2 ^ 40))}
    {σ σ' : LazyOracle.State Empty Empty} {seen : List (TagKey × Block)} (inv : PathInv layout S read σ seen)
    (keeps : Keeps σ σ') {key : TagKey} {label : Block} (member : key ∈ S) (range : key.InRange)
    (newTouched : ∀ site, key.site = some site → untouched (sitePoints layout site label.toNat) σ' = false)
    (readSub : ∀ p ∈ read', p ∈ read ∨ (key.site = none ∧ p = tagPos key.code) ∨
      (∃ site, key.site = some site ∧ p ∈ sitePos layout site)) :
    PathInv layout S read' σ' ((key, label) :: seen) := by
  refine ⟨fun q inside => ?_, fun q inside site isSite => ?_, fun p inside => ?_⟩
  · rcases List.mem_cons.mp inside with first | old
    · rw [first]
      exact ⟨member, range⟩
    · exact inv.keys q old
  · rcases List.mem_cons.mp inside with first | old
    · rw [first] at isSite ⊢
      exact newTouched site isSite
    · exact untouched_false_mono (inv.touched q old site isSite) keeps
  · rcases readSub p inside with old | ⟨noSite, same⟩ | ⟨site, isSite, inSite⟩
    · rcases inv.reads p old with ⟨q, inSeen, noSite, same⟩ | ⟨q, inSeen, site, isSite, inSite⟩
      · exact Or.inl ⟨q, List.mem_cons.mpr (Or.inr inSeen), noSite, same⟩
      · exact Or.inr ⟨q, List.mem_cons.mpr (Or.inr inSeen), site, isSite, inSite⟩
    · exact Or.inl ⟨(key, label), List.mem_cons.mpr (Or.inl rfl), noSite, same⟩
    · exact Or.inr ⟨(key, label), List.mem_cons.mpr (Or.inl rfl), site, isSite, inSite⟩

/-! ### From a tag run to the refill path -/

/-- **The translation**: a tag run whose site keys are at their sites' own tags satisfies the refill path conditions
from every state satisfying the invariant. -/
theorem refillPath_of_keyRun {α : Type} {layout : SiteLayout} {S : Set TagKey}
    {Q : α → List (TagKey × Block) → Prop} (points : PointFacts layout) (facts : RefillLayoutFacts layout)
    (sitesOK : SiteTagsOK layout S) :
    ∀ {seen : List (TagKey × Block)} {program : CM α}, KeyRun S Q seen program →
      ∀ (read : Set (Fin (2 ^ 40))) (σ : LazyOracle.State Empty Empty), PathInv layout S read σ seen →
        RefillPath layout read σ program := by
  intro seen program run
  induction run with
  | pure seen value post => exact fun read σ _ => .pure read σ value
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
      intro read σ inv
      subst coded
      have decodeEq : siteOf (hashInput label key.code / 2 ^ 128) = key.site := by
        rw [hashInput_tag, siteOf_code range]
      have labelEq : hashInput label key.code % 2 ^ 128 = label.toNat := hashInput_label label key.code
      cases keySite : key.site with
      | none =>
          have noSite : siteOf (hashInput label key.code / 2 ^ 128) = none := by rw [decodeEq, keySite]
          cases found : σ.hash.lookup ((hashInput label key.code : ℕ) : BaseField) with
          | some v =>
              refine .stored read σ _ next v found (fun site decode => ?_) (ih _ read σ ?_)
              · rw [noSite] at decode
                cases decode
              · exact inv.step (fun _ stored => stored) member range (fun site isSite => by
                  rw [keySite] at isSite
                  cases isSite) fun p inside => Or.inl inside
          | none =>
              refine .fresh read σ _ next noSite found ?_ ?_ fun a => ih a _ _ ?_
              · rw [hashInput_tag]
                intro inRead
                rcases inv.reads _ inRead with ⟨q, inSeen, _, same⟩ | ⟨q, inSeen, site, isSite, inSite⟩
                · obtain ⟨_, qRange⟩ := inv.keys q inSeen
                  have codes := tagPos_injective (TagKey.code_lt range) (TagKey.code_lt qRange) same
                  exact fresh (List.mem_map.mpr ⟨q, inSeen, (TagKey.code_injective range qRange codes).symm⟩)
                · obtain ⟨qS, qRange⟩ := inv.keys q inSeen
                  exact away_of_nonSite points range keySite site (sitesOK q.1 qS qRange site isSite).1 inSite
              · rw [hashInput_tag]
                exact away_of_nonSite points range keySite
              · refine inv.step (keeps_plantHash σ _ a) member range (fun site isSite => by
                  rw [keySite] at isSite
                  cases isSite) fun p inside => ?_
                rcases Set.mem_insert_iff.mp inside with new | old
                · rw [hashInput_tag] at new
                  exact Or.inr (Or.inl ⟨keySite, new⟩)
                · exact Or.inl old
      | some site =>
          obtain ⟨inLayout, hit⟩ := sitesOK key member range site keySite
          have decode : siteOf (hashInput label key.code / 2 ^ 128) = some site := by rw [decodeEq, keySite]
          have point := mem_sitePoints hit label
          cases clean : untouched (sitePoints layout site (hashInput label key.code % 2 ^ 128)) σ with
          | false =>
              refine .touched read σ _ next site decode clean fun b inside => ih b.1 read b.2 ?_
              obtain ⟨keeps, stored⟩ := lazyReader_keeps _ σ b inside
              refine inv.step keeps member range (fun site' isSite => ?_) fun p inside => Or.inl inside
              rw [keySite] at isSite
              cases isSite
              exact untouched_eq_false_iff.mpr ⟨_, point, stored⟩
          | true =>
              refine .site read σ _ next site decode inLayout clean ?_ fun answers _ b inside => ih b.1 _ b.2 ?_
              · intro p inSite inRead
                rcases inv.reads p inRead with ⟨q, inSeen, qNoSite, same⟩ | ⟨q, inSeen, site', isSite, inSite'⟩
                · obtain ⟨_, qRange⟩ := inv.keys q inSeen
                  rw [same] at inSite
                  exact away_of_nonSite points qRange qNoSite site inLayout inSite
                · obtain ⟨qS, qRange⟩ := inv.keys q inSeen
                  by_cases sameSite : site' = site
                  · subst sameSite
                    have sameLabelQ := sameLabel q inSeen (isSite.trans keySite.symm) (by
                      rw [keySite]
                      exact Option.some_ne_none _)
                    have dirty := inv.touched q inSeen site' isSite
                    rw [sameLabelQ, ← labelEq, clean] at dirty
                    cases dirty
                  · exact facts.disjoint site inLayout site' (sitesOK q.1 qS qRange site' isSite).1
                      (Ne.symm sameSite) p inSite inSite'
              · obtain ⟨keeps, stored⟩ := lazyReader_keeps _ _ b inside
                refine inv.step ((keeps_installPoints _ σ).trans keeps) member range (fun site' isSite => ?_)
                  fun p inside' => ?_
                · rw [keySite] at isSite
                  cases isSite
                  exact untouched_eq_false_iff.mpr ⟨_, point, stored⟩
                · rcases inside' with old | new
                  · exact Or.inl old
                  · exact Or.inr (Or.inr ⟨site, keySite, new⟩)

/-- **A `Tagged` program satisfies the refill path conditions from every state.** -/
theorem refillPath_of_tagged {α : Type} {layout : SiteLayout} {S : Set TagKey} {program : CM α}
    (points : PointFacts layout) (facts : RefillLayoutFacts layout) (sitesOK : SiteTagsOK layout S)
    (tagged : Tagged S program) (σ : LazyOracle.State Empty Empty) : RefillPath layout ∅ σ program :=
  refillPath_of_keyRun points facts sitesOK tagged ∅ σ (PathInv.start layout S σ)

/-- **A tag run's queries are canonical.** -/
theorem canonical_of_keyRun {α : Type} {layout : SiteLayout} {S : Set TagKey}
    {Q : α → List (TagKey × Block) → Prop} (sitesOK : SiteTagsOK layout S) :
    ∀ {seen : List (TagKey × Block)} {program : CM α}, KeyRun S Q seen program → Canonical layout program := by
  intro seen program run
  induction run with
  | pure seen value post => exact .pure value
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
      subst coded
      refine .query _ next ?_ (fun site decode => ?_) fun answer => ih answer
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hashInput_lt range)]
      · rw [hashInput_tag, siteOf_code range] at decode
        rw [hashInput_tag]
        exact sitesOK key member range site decode

/-! ### The concrete replay -/

/-- The keys of route M's replay: the conversion and body blocks, the key, the non-collector masks. -/
def replayKeys : Set TagKey := replayConvKeys ∪ ({keyKey} ∪ nonCollectorKeys digitCount)

/-- The key query at `t'`. -/
theorem keyField_tagged (t : BaseField) : Tagged ({keyKey} : Set TagKey) (askN (EntryReading.keyField t).val) := by
  rw [EntryReading.keyField_val]
  unfold maskKeyInput
  exact Tagged.askN ({keyKey} : Set TagKey) _ maskKeyTag keyKey rfl rfl keyKey_range

/-- **Route M's replay program is `Tagged`.** -/
theorem viewReplay_tagged [FieldCertificate] [GroupCertificate] (published : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Tagged replayKeys ((Instance.view).replayProgram published u labels) := by
  unfold RouteMView.replayProgram
  dsimp only [Instance.view]
  refine Tagged.bind (replayConv_tagged published u labels) (fun conv => ?_) ?_ ?_
  · refine Tagged.bind (keyField_tagged _) (fun answer => Tagged.bind_pure (viewNonCollectorReplay_tagged _) _) ?_
      (siteDisjoint_of_fam fun k inK => by rw [Set.mem_singleton_iff.mp inK]; exact ⟨by decide, by decide⟩)
    refine Set.disjoint_left.mpr fun k inK inM => ?_
    rw [Set.mem_singleton_iff.mp inK] at inM
    simp only [keyKey, nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inM
    omega
  · refine Set.disjoint_left.mpr fun k inC inR => ?_
    have := replayConvKeys_sub inC
    simp only [coordKeys, Set.mem_union, Set.mem_setOf_eq] at this
    rcases inR with inK | inM
    · rw [Set.mem_singleton_iff.mp inK] at this
      simp only [keyKey] at this
      omega
    · simp only [nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inM
      omega
  · refine siteDisjoint_of_fields (fun k _ k' inR _ six' => ?_) (fun k inC k' _ seven _ => ?_)
    · rcases inR with inK | inM
      · rw [Set.mem_singleton_iff.mp inK] at six'
        simp only [keyKey] at six'
        omega
      · simp only [nonCollectorKeys, maskStageKeys, maskSiteKeys, Set.mem_union, Set.mem_setOf_eq] at inM
        omega
    · have := replayConvKeys_sub inC
      simp only [coordKeys, Set.mem_union, Set.mem_setOf_eq] at this
      omega

theorem padCount_fin (κ : ℕ) (i : Fin bn254Table.count) :
    Layout.padCount κ i.val = bn254Table.padAnswers (Layout.padS κ) i := by
  unfold Layout.padCount
  rw [dif_pos i.isLt]

theorem coordEvalKeys_siteTags (S coord : Nat) (coordLt : coord < 2) (count : Layout.padS coord = S) :
    SiteTagsOK crtLayout (coordEvalKeys Entry.table S coord) := by
  intro k inK range site isSite
  obtain ⟨inLayout, _⟩ := coordEvalKeys_sites S coord coordLt k inK range site isSite
  refine ⟨inLayout, ?_⟩
  rcases site_cases k with ⟨six, hk⟩ | ⟨seven, hk⟩ | ⟨_, _, noSite⟩
  · obtain ⟨i, kCoord, kIdx, kStage, kLevel, _, kPart⟩ := coordEvalKeys_pad inK six
    rw [hk] at isSite
    obtain rfl := Option.some.inj isSite
    show k.code ∈ (List.range (Layout.layoutAnswers (.pad k.coord k.idx k.slot))).map
      fun j => tagCode Family.body k.coord k.idx 0 0 k.slot j
    refine List.mem_map.mpr ⟨k.part, List.mem_range.mpr ?_, ?_⟩
    · show k.part < Layout.padCount k.coord k.idx
      rw [kIdx, padCount_fin, kCoord, count]
      exact kPart
    · unfold TagKey.code
      rw [six, kStage, kLevel]
      rfl
  · have := coordEvalKeys_sub _ _ _ inK
    simp only [coordKeys, Set.mem_setOf_eq] at this
    exfalso
    omega
  · rw [noSite] at isSite
    cases isSite

theorem replayKeys_siteTags : SiteTagsOK crtLayout replayKeys := by
  rintro k ((inX | inY) | inK | inM) range site isSite
  · exact coordEvalKeys_siteTags _ 0 (by norm_num) rfl k inX range site isSite
  · exact coordEvalKeys_siteTags _ 1 (by norm_num) rfl k inY range site isSite
  · rw [Set.mem_singleton_iff.mp inK] at isSite
    cases isSite
  · obtain ⟨inLayout, _⟩ := nonCollectorKeys_sites k inM range site isSite
    refine ⟨inLayout, ?_⟩
    have pairs := pairSites_digitCount
    have facts : k.fam = 7 ∧ k.coord = 0 ∧ k.idx = 0 ∧ k.stage = 1 ∧ k.level = 0 ∧
        ((k.slot < 227 ∧ k.part < 3) ∨ (k.slot = 227 ∧ k.part < 2)) := by
      rcases inM with inP | inS
      · simp only [maskStageKeys, Set.mem_setOf_eq] at inP
        omega
      · simp only [maskSiteKeys, Set.mem_setOf_eq] at inS
        omega
    obtain ⟨seven, kCoord, kIdx, kStage, kLevel, slots⟩ := facts
    rw [site_mask seven] at isSite
    obtain rfl := Option.some.inj isSite
    rw [kStage]
    show k.code ∈ (List.range (Layout.layoutAnswers (.mask 1 k.slot))).map
      fun j => tagCode Family.mask 0 0 1 0 k.slot j
    refine List.mem_map.mpr ⟨k.part, List.mem_range.mpr ?_, ?_⟩
    · show k.part < if k.slot = 227 then 2 else 3
      split <;> omega
    · unfold TagKey.code
      rw [seven, kCoord, kIdx, kStage, kLevel]
      rfl

/-- **P6b1's path conditions for route M's replay on the concrete entry**, from every lazy state. -/
theorem replay_refillPath [FieldCertificate] [GroupCertificate] (published : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    ∀ σ : LazyOracle.State Empty Empty, RefillPath crtLayout ∅ σ ((Instance.view).replayProgram published u labels) :=
  refillPath_of_tagged crtLayout_points crtLayout_refill replayKeys_siteTags (viewReplay_tagged published u labels)

/-- **Route M's replay asks canonical queries on the concrete entry.** -/
theorem replay_canonical [FieldCertificate] [GroupCertificate] (published : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Canonical crtLayout ((Instance.view).replayProgram published u labels) :=
  canonical_of_keyRun replayKeys_siteTags (viewReplay_tagged published u labels)

/-- **The key query is outside every site** (family 10). -/
theorem replay_keyNonSite [FieldCertificate] [GroupCertificate] (published : Kriterion.CRT.Entry.Public)
    (u : AffineInput) :
    ∀ conv, siteOf (((Instance.view).keyInput published u conv).val / 2 ^ 128) = none := by
  intro conv
  show siteOf ((EntryReading.keyField (Kriterion.CRT.Entry.curveOutput published u conv)).val / 2 ^ 128) = none
  rw [EntryReading.keyField_val]
  unfold maskKeyInput
  rw [hashInput_tag, show maskKeyTag = keyKey.code from rfl, siteOf_code keyKey_range]
  rfl

end Kriterion.CRT.Paths
