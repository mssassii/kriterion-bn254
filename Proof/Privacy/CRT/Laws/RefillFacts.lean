/-
**P6b1, the layout side: the merged refill reader and the real layout satisfy the refill law's hypotheses**.

* `refillReader_like`: `Sites.refillReader` satisfies `RefillLike`, by unfolding;
* `crtLayout_refill : RefillLayoutFacts crtLayout`: the real layout's sites are pairwise distinct, each site's tags are
  distinct table positions (`Layout.crtLayout_nodup`), two distinct sites share no position (their tags are
  `tagCode` of distinct fields below `2^40`, `tagCode_injective`), and every answer list a site law can draw has the
  site's number of answers (a fibre law is a map of `List.ofFn`).
-/

import Proof.Privacy.CRT.Laws.ReplayOn
import Proof.Privacy.CRT.Swap.Layout

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Layout

noncomputable section

/-! ### The merged refill reader -/

theorem refillReader_like {FI EI : Type} [DecidableEq FI] [DecidableEq EI] (layout : SiteLayout) :
    RefillLike layout (refillReader (FI := FI) (EI := EI) layout) where
  nonSite n σ decode := by
    unfold refillReader
    rw [decode]
  fresh n σ site decode clean := by
    unfold refillReader
    rw [decode]
    show (if untouched (sitePoints layout site (n % 2 ^ 128)) σ then _ else _) = _
    rw [if_pos clean]
  touched n σ site decode dirty := by
    unfold refillReader
    rw [decode]
    show (if untouched (sitePoints layout site (n % 2 ^ 128)) σ then _ else _) = _
    rw [dirty]
    rfl

/-! ### Running a composed program through a reader -/

/-- **A reader runs a composed program in sequence.** -/
theorem runReader_bind {FI EI : Type} (rd : Reader FI EI) {α β : Type} (P : CM α) (f : α → CM β)
    (σ : LazyOracle.State FI EI) :
    runReader rd (P >>= f) σ = (runReader rd P σ).bind fun r => runReader rd (f r.1) r.2 := by
  induction P generalizing σ with
  | pure value =>
      show runReader rd (f value) σ = (PMF.pure (value, σ)).bind _
      rw [PMF.pure_bind]
  | query n next ih =>
      show (rd n σ).bind (fun answered => runReader rd (FreeQuery.bind (next answered.1) f) answered.2) =
        ((rd n σ).bind fun answered => runReader rd (next answered.1) answered.2).bind _
      rw [PMF.bind_bind]
      exact congrArg _ (funext fun answered => ih answered.1 answered.2)

/-- A non-site query through a refill-like reader is the plain lazy query (so a labelled key query outside every
site may be run through the reader or asked directly). -/
theorem refill_nonSite_query {FI EI : Type} [DecidableEq FI] [DecidableEq EI] (layout : SiteLayout)
    {rd : Reader FI EI} (like : RefillLike layout rd) (n : ℕ) (decode : siteOf (n / 2 ^ 128) = none)
    (σ : LazyOracle.State FI EI) :
    runReader rd (askN n) σ = LazyOracle.query (.hash (n : BaseField)) σ := by
  show (rd n σ).bind (fun answered => PMF.pure (answered.1, answered.2)) = _
  rw [like.nonSite n σ decode]
  exact PMF.bind_pure _

/-! ### The real layout -/

namespace RefillLayout

/-- A tag with in-range fields is its own table position. -/
theorem tagPos_tagCode {fam coord idx stage level slot part : ℕ} (hfam : fam < 16)
    (h : TagInRange coord idx stage level slot part) :
    (tagPos (tagCode fam coord idx stage level slot part)).val = tagCode fam coord idx stage level slot part := by
  have := h.coord; have := h.idx; have := h.stage; have := h.level; have := h.slot; have := h.part
  show tagCode fam coord idx stage level slot part % 2 ^ 40 = _
  apply Nat.mod_eq_of_lt
  unfold tagCode
  omega

/-- The fields of a site's tags: family, coordinate, index, stage, slot, and the answer count. -/
def siteFields : SiteId → ℕ × ℕ × ℕ × ℕ × ℕ
  | .pad κ i ρ => (Family.body, κ, i, 0, ρ)
  | .mask st k => (Family.mask, 0, 0, st, k)

theorem siteTags_eq (layout : SiteLayout) (site : SiteId) :
    siteTags layout site = (List.range (layout.answers site)).map fun j =>
      tagCode (siteFields site).1 (siteFields site).2.1 (siteFields site).2.2.1 (siteFields site).2.2.2.1 0
        (siteFields site).2.2.2.2 j := by
  cases site <;> rfl

/-- The fields of a site of the real layout are in range. -/
theorem fields_inRange {site : SiteId} (member : site ∈ crtLayout.sites) :
    (siteFields site).1 < 16 ∧ ∀ j < crtLayout.answers site,
      TagInRange (siteFields site).2.1 (siteFields site).2.2.1 (siteFields site).2.2.2.1 0
        (siteFields site).2.2.2.2 j := by
  rcases List.mem_append.mp member with pad | mask
  · obtain ⟨κ, i, ρ, rfl, hκ, hi, hρ⟩ := mem_padSites pad
    obtain ⟨-, -, -, -, hm, hq⟩ := tableFacts κ hκ i hi
    simp only [siteFields, Family.body]
    refine ⟨by norm_num, fun j hj => ⟨hκ, by omega, by norm_num, by norm_num, by omega, ?_⟩⟩
    have : j < padCount κ i := hj
    omega
  · rcases mem_maskSites mask with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp only [siteFields, Family.mask]
      refine ⟨by norm_num, fun j hj => ⟨by norm_num, by norm_num, by norm_num, by norm_num, by omega, ?_⟩⟩
      have : j < 2 := hj
      omega
    · simp only [siteFields, Family.mask]
      refine ⟨by norm_num, fun j hj => ⟨by norm_num, by norm_num, by norm_num, by norm_num, by omega, ?_⟩⟩
      have : j < 3 := hj
      omega

/-- The sites of the real layout are determined by their fields. -/
theorem siteFields_injective {site site' : SiteId} (same : siteFields site = siteFields site') : site = site' := by
  cases site <;> cases site' <;> simp_all [siteFields, Family.body, Family.mask]

theorem sitesNodup : crtLayout.sites.Nodup := by
  show (padSites ++ maskSites).Nodup
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · unfold padSites
    refine List.nodup_flatMap.mpr ⟨fun κ _ => List.nodup_flatMap.mpr ⟨fun i _ => ?_, ?_⟩, ?_⟩
    · exact List.nodup_range.map fun ρ ρ' same => by injection same
    · refine List.nodup_range.pairwise_of_forall_ne fun i _ i' _ ne => ?_
      rw [Function.onFun, List.disjoint_left]
      intro site hit hit'
      simp only [List.mem_map, List.mem_range] at hit hit'
      obtain ⟨ρ, -, rfl⟩ := hit
      obtain ⟨ρ', -, same⟩ := hit'
      injection same with _ e _
      exact ne e.symm
    · refine List.nodup_range.pairwise_of_forall_ne fun κ _ κ' _ ne => ?_
      rw [Function.onFun, List.disjoint_left]
      intro site hit hit'
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hit hit'
      obtain ⟨i, -, ρ, -, rfl⟩ := hit
      obtain ⟨i', -, ρ', -, same⟩ := hit'
      injection same with e _ _
      exact ne e.symm
  · unfold maskSites
    refine List.nodup_append.mpr ⟨List.nodup_range.map fun k k' same => by injection same,
      List.nodup_range.map fun k k' same => by injection same, ?_⟩
    intro site hit site' hit'
    simp only [List.mem_map, List.mem_range] at hit hit'
    obtain ⟨k, -, rfl⟩ := hit
    obtain ⟨k', -, rfl⟩ := hit'
    intro same
    injection same with e _
    exact absurd e (by decide)
  · intro site hit site' hit' same
    subst same
    obtain ⟨κ, i, ρ, rfl, -⟩ := mem_padSites hit
    rcases mem_maskSites hit' with ⟨k, e, -⟩ | ⟨k, e, -⟩ <;> cases e

theorem disjoint : ∀ site ∈ crtLayout.sites, ∀ site' ∈ crtLayout.sites, site ≠ site' →
    ∀ p ∈ (siteTags crtLayout site).map tagPos, p ∉ (siteTags crtLayout site').map tagPos := by
  intro site member site' member' ne p hp hp'
  obtain ⟨fam, inRange⟩ := fields_inRange member
  obtain ⟨fam', inRange'⟩ := fields_inRange member'
  rw [siteTags_eq, List.map_map] at hp hp'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  obtain ⟨j', hj', same⟩ := List.mem_map.mp hp'
  rw [List.mem_range] at hj hj'
  have vals := congrArg Fin.val same
  simp only [Function.comp_apply] at vals
  rw [tagPos_tagCode fam' (inRange' j' hj'), tagPos_tagCode fam (inRange j hj)] at vals
  obtain ⟨e1, e2, e3, e4, -, e6, -⟩ := tagCode_injective (inRange' j' hj') (inRange j hj) vals
  exact ne (siteFields_injective (Prod.ext e1.symm (Prod.ext e2.symm (Prod.ext e3.symm
    (Prod.ext e4.symm e6.symm)))))

theorem length_of_ofFn {n : ℕ} (μ : PMF (Fin n → Block × Block)) {answers : List (Block × Block)}
    (member : answers ∈ (μ.map List.ofFn).support) : answers.length = n := by
  rw [PMF.support_map] at member
  obtain ⟨f, -, rfl⟩ := member
  exact List.length_ofFn

theorem lengths : ∀ site ∈ crtLayout.sites, ∀ answers ∈ (crtLayout.law site).support,
    answers.length = crtLayout.answers site := by
  intro site member answers support
  rcases List.mem_append.mp member with pad | mask
  · obtain ⟨κ, i, ρ, rfl, -⟩ := mem_padSites pad
    change answers ∈ (padSiteLaw (padS κ) (padModulus i) (padCount κ i)).support at support
    show answers.length = padCount κ i
    unfold padSiteLaw at support
    split at support
    · exact length_of_ofFn _ support
    · exact length_of_ofFn _ support
  · rcases mem_maskSites mask with ⟨k, rfl, -⟩ | ⟨k, rfl, -⟩
    · exact length_of_ofFn _ support
    · change answers ∈ pairSiteLaw.support at support
      show answers.length = 3
      exact length_of_ofFn _ support

end RefillLayout

/-- **The real layout satisfies the refill law's layout facts.** -/
theorem crtLayout_refill : RefillLayoutFacts crtLayout where
  sitesNodup := RefillLayout.sitesNodup
  posNodup := crtLayout_nodup
  disjoint := RefillLayout.disjoint
  lengths := RefillLayout.lengths

end

end Kriterion.CRT.Privacy.Laws
