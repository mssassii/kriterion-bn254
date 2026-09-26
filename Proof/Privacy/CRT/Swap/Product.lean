/-
**The swapped table in product form**.

`swappedTableLaw` redraws the layout's sites one after the other on a uniform table. Because a step only
overwrites its own site's positions, the steps commute with the draws: the law is a uniform base table and one
independent draw per site, written in at the end (`swappedTableLaw_product`). On a layout whose sites are distinct,
with distinct positions and pairwise disjoint (`Laws.RefillLayoutFacts`):

* a site reads back its drawn answers (`siteAnswersOf_overwriteSites`);
* a position of no site keeps the base table's value (`overwriteSites_outside`);
* the draws lie in their laws' supports (`siteDraws_support`) and are independent: events on distinct sites
  multiply (`siteDraws_pi`).
-/

import Proof.Privacy.CRT.Laws.ReplayOn

namespace Kriterion.CRT.Privacy

open BN254 Cryptography Kriterion.CRT
open scoped ENNReal

noncomputable section

/-- **Independent draws of the listed sites' answers** (a site outside the list draws `[]`). -/
def siteDraws (layout : SiteLayout) : List SiteId → PMF (SiteId → List (Block × Block))
  | [] => PMF.pure fun _ => []
  | site :: rest => (layout.law site).bind fun answers =>
      (siteDraws layout rest).map fun A => Function.update A site answers

/-- **Overwrite every listed site** of a table with its drawn answers. -/
def overwriteSites (layout : SiteLayout) (sites : List SiteId) (A : SiteId → List (Block × Block))
    (T : TagTable) : TagTable :=
  sites.foldl (fun T site => overwrite T (siteTags layout site) (A site)) T

namespace Product

theorem overwriteSites_nil (layout : SiteLayout) (A : SiteId → List (Block × Block)) (T : TagTable) :
    overwriteSites layout [] A T = T := rfl

theorem overwriteSites_cons (layout : SiteLayout) (site : SiteId) (rest : List SiteId)
    (A : SiteId → List (Block × Block)) (T : TagTable) :
    overwriteSites layout (site :: rest) A T =
      overwriteSites layout rest A (overwrite T (siteTags layout site) (A site)) := rfl

/-- Changing the draws off the listed sites changes nothing. -/
theorem overwriteSites_congr (layout : SiteLayout) :
    ∀ (sites : List SiteId) (A A' : SiteId → List (Block × Block)), (∀ s ∈ sites, A s = A' s) →
      ∀ T, overwriteSites layout sites A T = overwriteSites layout sites A' T
  | [], _, _, _, _ => rfl
  | site :: rest, A, A', same, T => by
      rw [overwriteSites_cons, overwriteSites_cons, same site List.mem_cons_self]
      exact overwriteSites_congr layout rest A A' (fun s member => same s (List.mem_cons_of_mem _ member)) _

/-- The fold of swap steps from any base law, in product form. -/
theorem foldl_swapStep (layout : SiteLayout) :
    ∀ (sites : List SiteId), sites.Nodup → ∀ μ : PMF TagTable,
      sites.foldl (Laws.swapStep layout) μ =
        μ.bind fun T0 => (siteDraws layout sites).map fun A => overwriteSites layout sites A T0
  | [], _, μ => by
      simp only [List.foldl_nil, siteDraws, PMF.pure_map, overwriteSites_nil]
      exact (PMF.bind_pure μ).symm
  | site :: rest, nodup, μ => by
      have fresh := (List.nodup_cons.mp nodup).1
      rw [List.foldl_cons, foldl_swapStep layout rest (List.nodup_cons.mp nodup).2]
      unfold Laws.swapStep
      rw [PMF.bind_bind]
      refine congrArg _ (funext fun T0 => ?_)
      simp only [siteDraws, PMF.bind_map, PMF.map_bind, PMF.map_comp]
      refine congrArg _ (funext fun answers => ?_)
      simp only [Function.comp_def]
      refine congrArg (fun f => PMF.map f _) (funext fun A => ?_)
      rw [overwriteSites_cons, Function.update_self]
      exact overwriteSites_congr layout rest A (Function.update A site answers)
        (fun s member => (Function.update_of_ne (fun (same : s = site) => fresh (same ▸ member)) _ _).symm) _

/-- A position outside every listed site keeps its value. -/
theorem overwriteSites_apply_of_away (layout : SiteLayout) :
    ∀ (sites : List SiteId) (A : SiteId → List (Block × Block)) (T : TagTable) (p : Fin (2 ^ 40)),
      (∀ s ∈ sites, p ∉ Laws.sitePos layout s) → overwriteSites layout sites A T p = T p
  | [], _, _, _, _ => rfl
  | site :: rest, A, T, p, away => by
      rw [overwriteSites_cons, overwriteSites_apply_of_away layout rest A _ p
        (fun s member => away s (List.mem_cons_of_mem _ member))]
      exact Swap.overwrite_apply_of_not_mem _ _ T p (away site List.mem_cons_self)

/-- A listed site reads back its drawn answers, when the listed sites are distinct and pairwise disjoint. -/
theorem siteAnswersOf_overwriteSites_of_mem (layout : SiteLayout) (facts : Laws.RefillLayoutFacts layout)
    (A : SiteId → List (Block × Block)) (lengths : ∀ s ∈ layout.sites, (A s).length = layout.answers s) :
    ∀ (sites : List SiteId), sites.Nodup → (∀ s ∈ sites, s ∈ layout.sites) → ∀ (T : TagTable) (site : SiteId),
      site ∈ sites → Laws.siteAnswersOf layout (overwriteSites layout sites A T) site = A site
  | [], _, _, _, _, member => absurd member List.not_mem_nil
  | s :: rest, nodup, inLayout, T, site, member => by
      rw [overwriteSites_cons]
      by_cases same : s = site
      · subst same
        have fresh := (List.nodup_cons.mp nodup).1
        have siteIn := inLayout s List.mem_cons_self
        -- the later sites do not touch this site's positions
        have keep : ∀ p ∈ Laws.sitePos layout s,
            overwriteSites layout rest A (overwrite T (siteTags layout s) (A s)) p =
              overwrite T (siteTags layout s) (A s) p := by
          intro p inSite
          refine overwriteSites_apply_of_away layout rest A _ p fun s' member' => ?_
          exact facts.disjoint s siteIn s' (inLayout s' (List.mem_cons_of_mem _ member'))
            (fun eq => fresh (eq ▸ member')) p inSite
        have length := lengths s siteIn
        refine List.ext_getElem ?_ fun j hj hj' => ?_
        · simp [Laws.siteAnswersOf, siteTags_length, length]
        · have jTags : j < (siteTags layout s).length := by simpa [Laws.siteAnswersOf] using hj
          simp only [Laws.siteAnswersOf, List.getElem_map]
          rw [keep _ (by
            show tagPos (siteTags layout s)[j] ∈ (siteTags layout s).map tagPos
            exact List.mem_map_of_mem (List.getElem_mem jTags))]
          exact Swap.overwrite_apply_mem _ _ T (facts.posNodup s siteIn) j jTags
            (by rw [length, ← siteTags_length]; exact jTags)
      · have member' : site ∈ rest := by
          rcases List.mem_cons.mp member with h | h
          · exact absurd h.symm same
          · exact h
        exact siteAnswersOf_overwriteSites_of_mem layout facts A lengths rest (List.nodup_cons.mp nodup).2
          (fun s' m => inLayout s' (List.mem_cons_of_mem _ m)) _ site member'

end Product

open Product

/-- **(1) The product form of the swapped table law.** -/
theorem swappedTableLaw_product (layout : SiteLayout) (nodup : layout.sites.Nodup) :
    swappedTableLaw layout = (PMF.uniformOfFintype TagTable).bind fun T0 =>
      (siteDraws layout layout.sites).map fun A => overwriteSites layout layout.sites A T0 := by
  rw [Laws.swappedTableLaw_eq]
  exact foldl_swapStep layout layout.sites nodup _

/-- **(2) A site reads back its drawn answers.** -/
theorem siteAnswersOf_overwriteSites (layout : SiteLayout) (facts : Laws.RefillLayoutFacts layout)
    (A : SiteId → List (Block × Block)) (lengths : ∀ s ∈ layout.sites, (A s).length = layout.answers s)
    (T0 : TagTable) (site : SiteId) (member : site ∈ layout.sites) :
    Laws.siteAnswersOf layout (overwriteSites layout layout.sites A T0) site = A site :=
  siteAnswersOf_overwriteSites_of_mem layout facts A lengths layout.sites facts.sitesNodup (fun _ m => m) T0 site
    member

/-- **(3) A position of no site keeps the base table's value.** -/
theorem overwriteSites_outside (layout : SiteLayout) (A : SiteId → List (Block × Block)) (T0 : TagTable)
    (p : Fin (2 ^ 40)) (away : ∀ s ∈ layout.sites, p ∉ Laws.sitePos layout s) :
    overwriteSites layout layout.sites A T0 p = T0 p :=
  overwriteSites_apply_of_away layout layout.sites A T0 p away

/-- **(4) Drawn answers lie in their laws' supports.** -/
theorem siteDraws_support (layout : SiteLayout) :
    ∀ (L : List SiteId) (A : SiteId → List (Block × Block)), A ∈ (siteDraws layout L).support →
      ∀ s ∈ L, A s ∈ (layout.law s).support
  | [], _, _, s, member => absurd member List.not_mem_nil
  | site :: rest, A, drawn, s, member => by
      simp only [siteDraws, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at drawn
      obtain ⟨answers, inLaw, A', inRest, rfl⟩ := drawn
      by_cases same : s = site
      · subst same
        rw [Function.update_self]
        exact inLaw
      · rw [Function.update_of_ne same]
        rcases List.mem_cons.mp member with h | h
        · exact absurd h same
        · exact siteDraws_support layout rest A' inRest s h

/-- **(5) Independence: events on distinct sites multiply.** -/
theorem siteDraws_pi (layout : SiteLayout) :
    ∀ (L : List SiteId), L.Nodup → ∀ (E : SiteId → Set (List (Block × Block))),
      (siteDraws layout L).toOuterMeasure {A | ∀ s ∈ L, A s ∈ E s} =
        (L.map fun s => (layout.law s).toOuterMeasure (E s)).prod
  | [], _, E => by
      simp [siteDraws, PMF.toOuterMeasure_pure_apply]
  | site :: rest, nodup, E => by
      have fresh := (List.nodup_cons.mp nodup).1
      have ih := siteDraws_pi layout rest (List.nodup_cons.mp nodup).2 E
      rw [siteDraws, PMF.toOuterMeasure_bind_apply, List.map_cons, List.prod_cons, ← ih,
        PMF.toOuterMeasure_apply (layout.law site), ← ENNReal.tsum_mul_right]
      refine tsum_congr fun answers => ?_
      rw [PMF.toOuterMeasure_map_apply]
      by_cases inside : answers ∈ E site
      · have pre : (fun A => Function.update A site answers) ⁻¹' {A | ∀ s ∈ site :: rest, A s ∈ E s} =
            {A | ∀ s ∈ rest, A s ∈ E s} := by
          ext A
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, List.mem_cons, forall_eq_or_imp, Function.update_self]
          constructor
          · rintro ⟨_, rest'⟩ s member
            have := rest' s member
            rwa [Function.update_of_ne (fun (eq : s = site) => fresh (eq ▸ member))] at this
          · intro rest'
            refine ⟨inside, fun s member => ?_⟩
            rw [Function.update_of_ne (fun (eq : s = site) => fresh (eq ▸ member))]
            exact rest' s member
        rw [pre, Set.indicator_of_mem inside]
      · have pre : (fun A => Function.update A site answers) ⁻¹' {A | ∀ s ∈ site :: rest, A s ∈ E s} = ∅ := by
          ext A
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, List.mem_cons, forall_eq_or_imp, Function.update_self,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro inE
          exact absurd inE inside
        rw [pre, Set.indicator_of_notMem inside, zero_mul, PMF.toOuterMeasure_apply]
        simp

end

end Kriterion.CRT.Privacy
