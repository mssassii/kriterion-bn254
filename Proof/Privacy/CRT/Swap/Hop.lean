/-
**the pad swap `G0T → G0U`** (row H3).

`G0T` and `G0U` are the same planted game on two tape laws (`plantedGame`): the uniform table tape and the swapped
table tape, which differ only in the tag table, uniform against `swappedTableLaw`, the uniform table with every site
redrawn from its law. The hop is bounded by data processing:

* the advantage is at most the distance of the tape laws (`PMF.etvDist_bind_right_le`, `advantage_eq_etvDist`);
* the tape laws are at most the table laws apart (`etvDist_tapes_le`);
* the table laws are at most the sum of the sites' biases apart (`etvDist_swappedTableLaw_le`), by a hybrid over the
  sites: overwriting a site's positions of a uniform table with uniform answers keeps it uniform
  (`Swap.uniform_bind_overwrite`, a bijection of `(table, answers)` pairs), so each site costs the distance of its law
  to uniform answers (`Swap.etvDist_step_le`).

The statement assumes `SwapLayoutFacts`: every site's tags are distinct positions of the table, and the sites' biases
sum to at most `padSwapError`. Cross-site disjointness is not needed. `Swap/Layout.lean` proves the facts for the real
layout from `Swap/Reading.lean` and `Glue/BudgetRows.lean`.
-/

import Proof.Privacy.CRT.Hybrids
import Proof.Privacy.Phase3.GameSwap

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le_const productPMF uniformOfFintype_productPMF
  advantage_eq_etvDist etvDist_map_le')
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv uniformOfFintype_map_fst)
open scoped ENNReal

noncomputable section

/-- Uniform answers of a site with `n` answers, as the list the site laws produce. -/
def uniformAnswers (n : ℕ) : PMF (List (Block × Block)) :=
  (PMF.uniformOfFintype (Fin n → Block × Block)).map List.ofFn

/-- The table position of a tag. -/
def tagPos (tag : ℕ) : Fin (2 ^ 40) := ⟨tag % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- **The facts of a site layout that the pad swap needs.** -/
structure SwapLayoutFacts (layout : SiteLayout) where
  /-- Each site's tags are distinct table positions. -/
  nodup : ∀ site ∈ layout.sites, ((siteTags layout site).map tagPos).Nodup
  /-- A bias for each site. -/
  bias : SiteId → ℝ≥0∞
  /-- Each site's law is within its bias of uniform answers. -/
  close : ∀ site ∈ layout.sites, (layout.law site).etvDist (uniformAnswers (layout.answers site)) ≤ bias site
  /-- The biases sum to at most `padSwapError`. -/
  total : (layout.sites.map bias).sum ≤ ENNReal.ofReal padSwapError

theorem siteTags_length (layout : SiteLayout) (site : SiteId) :
    (siteTags layout site).length = layout.answers site := by
  cases site <;> simp [siteTags]

namespace Swap

/-! ### Overwriting a table -/

theorem overwrite_cons (table : TagTable) (tag : ℕ) (tags : List ℕ) (a : Block × Block)
    (answers : List (Block × Block)) :
    overwrite table (tag :: tags) (a :: answers) = overwrite (Function.update table (tagPos tag) a) tags answers :=
  rfl

theorem overwrite_apply_of_not_mem : ∀ (tags : List ℕ) (answers : List (Block × Block)) (table : TagTable)
    (p : Fin (2 ^ 40)), p ∉ tags.map tagPos → overwrite table tags answers p = table p
  | [], _, table, p, _ => by simp [overwrite]
  | _ :: _, [], table, p, _ => by simp [overwrite]
  | tag :: tags, a :: answers, table, p, miss => by
      simp only [List.map_cons, List.mem_cons, not_or] at miss
      rw [overwrite_cons, overwrite_apply_of_not_mem tags answers _ p miss.2, Function.update_of_ne miss.1]

theorem overwrite_apply_mem : ∀ (tags : List ℕ) (answers : List (Block × Block)) (table : TagTable),
    (tags.map tagPos).Nodup → ∀ (j : ℕ) (hj : j < tags.length) (ha : j < answers.length),
      overwrite table tags answers (tagPos tags[j]) = answers[j]
  | [], _, _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], _, _, j, _, ha => absurd ha (Nat.not_lt_zero _)
  | tag :: tags, a :: answers, table, nodup, 0, _, _ => by
      have fresh : tagPos tag ∉ tags.map tagPos := (List.nodup_cons.mp nodup).1
      rw [List.getElem_cons_zero, List.getElem_cons_zero, overwrite_cons,
        overwrite_apply_of_not_mem tags answers _ _ fresh, Function.update_self]
  | tag :: tags, a :: answers, table, nodup, j + 1, hj, ha => by
      rw [List.getElem_cons_succ, List.getElem_cons_succ, overwrite_cons]
      exact overwrite_apply_mem tags answers _ (List.nodup_cons.mp nodup).2 j (by simpa using hj)
        (by simpa using ha)

/-- Write fresh answers at a site, return the old ones: an involution of `(table, answers)` pairs. -/
def swapPair (tags : List ℕ) (pair : TagTable × (Fin tags.length → Block × Block)) :
    TagTable × (Fin tags.length → Block × Block) :=
  (overwrite pair.1 tags (List.ofFn pair.2), fun j => pair.1 (tagPos tags[j.val]))

theorem swapPair_involutive (tags : List ℕ) (nodup : (tags.map tagPos).Nodup) :
    Function.Involutive (swapPair tags) := by
  rintro ⟨table, answers⟩
  have inner : ∀ j : Fin tags.length,
      overwrite table tags (List.ofFn answers) (tagPos tags[j.val]) = answers j := by
    intro j
    rw [overwrite_apply_mem tags _ table nodup j.val j.isLt (by simp)]
    simp [List.getElem_ofFn]
  show (overwrite (overwrite table tags (List.ofFn answers)) tags (List.ofFn fun j => table (tagPos tags[j.val])),
      fun j => overwrite table tags (List.ofFn answers) (tagPos tags[j.val])) = (table, answers)
  refine Prod.ext (funext fun p => ?_) (funext fun j => inner j)
  show overwrite (overwrite table tags (List.ofFn answers)) tags (List.ofFn fun j => table (tagPos tags[j.val])) p
    = table p
  by_cases hit : p ∈ tags.map tagPos
  · obtain ⟨j, hj, same⟩ := List.getElem_of_mem hit
    have hj' : j < tags.length := by simpa using hj
    rw [List.getElem_map] at same
    subst same
    rw [overwrite_apply_mem tags _ _ nodup j hj' (by simpa using hj')]
    simp only [List.getElem_ofFn]
  · rw [overwrite_apply_of_not_mem tags _ _ p hit, overwrite_apply_of_not_mem tags _ _ p hit]

/-- **Overwriting a uniform table at distinct positions with uniform answers keeps it uniform.** -/
theorem uniform_bind_overwrite (tags : List ℕ) (nodup : (tags.map tagPos).Nodup) :
    (PMF.uniformOfFintype TagTable).bind (fun table => (uniformAnswers tags.length).map (overwrite table tags))
      = PMF.uniformOfFintype TagTable := by
  let e : (TagTable × (Fin tags.length → Block × Block)) ≃ (TagTable × (Fin tags.length → Block × Block)) :=
    Function.Involutive.toPerm _ (swapPair_involutive tags nodup)
  have lhs : (PMF.uniformOfFintype TagTable).bind
        (fun table => (uniformAnswers tags.length).map (overwrite table tags))
      = ((PMF.uniformOfFintype (TagTable × (Fin tags.length → Block × Block))).map e).map Prod.fst := by
    rw [PMF.map_comp, uniformOfFintype_productPMF]
    unfold productPMF uniformAnswers
    rw [PMF.map_bind]
    refine congrArg _ (funext fun table => ?_)
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  rw [lhs, uniformOfFintype_map_equiv e, uniformOfFintype_map_fst]

/-- One site of the hybrid: the same prior, two answer laws. -/
theorem etvDist_step_le (μ : PMF TagTable) (tags : List ℕ) (law law' : PMF (List (Block × Block))) :
    (μ.bind fun table => law.map (overwrite table tags)).etvDist (μ.bind fun table => law'.map (overwrite table tags))
      ≤ law.etvDist law' :=
  etvDist_bind_left_le_const μ _ _ _ fun _ => etvDist_map_le' _ _ _

/-- The hybrid over a list of sites, from any prior. -/
theorem etvDist_foldl_le (layout : SiteLayout) (bias : SiteId → ℝ≥0∞) :
    ∀ (sites : List SiteId), (∀ site ∈ sites, ((siteTags layout site).map tagPos).Nodup) →
      (∀ site ∈ sites, (layout.law site).etvDist (uniformAnswers (layout.answers site)) ≤ bias site) →
      ∀ μ : PMF TagTable,
        (sites.foldl (fun law site => law.bind fun table =>
            (layout.law site).map fun answers => overwrite table (siteTags layout site) answers) μ).etvDist
          (PMF.uniformOfFintype TagTable)
          ≤ μ.etvDist (PMF.uniformOfFintype TagTable) + (sites.map bias).sum
  | [], _, _, μ => by simp
  | site :: rest, nodup, close, μ => by
      rw [List.foldl_cons]
      set tags := siteTags layout site with htags
      have fresh : (tags.map tagPos).Nodup := nodup site List.mem_cons_self
      have near : (layout.law site).etvDist (uniformAnswers tags.length) ≤ bias site := by
        rw [htags, siteTags_length]
        exact close site List.mem_cons_self
      have step : (μ.bind fun table => (layout.law site).map fun answers => overwrite table tags answers).etvDist
          (PMF.uniformOfFintype TagTable) ≤ bias site + μ.etvDist (PMF.uniformOfFintype TagTable) := by
        refine le_trans (PMF.etvDist_triangle _
          (μ.bind fun table => (uniformAnswers tags.length).map (overwrite table tags)) _) (add_le_add ?_ ?_)
        · exact le_trans (etvDist_step_le μ tags _ _) near
        · conv_lhs => rw [← uniform_bind_overwrite tags fresh]
          exact PMF.etvDist_bind_right_le _ _ _
      refine le_trans (etvDist_foldl_le layout bias rest (fun s mem => nodup s (List.mem_cons_of_mem _ mem))
        (fun s mem => close s (List.mem_cons_of_mem _ mem)) _) ?_
      rw [List.map_cons, List.sum_cons]
      calc _ ≤ bias site + μ.etvDist (PMF.uniformOfFintype TagTable) + (rest.map bias).sum :=
            add_le_add step le_rfl
        _ = μ.etvDist (PMF.uniformOfFintype TagTable) + (bias site + (rest.map bias).sum) := by ring

end Swap

/-! ### The table laws, the tapes, the games -/

/-- **The swapped table law is within the sum of the sites' biases of the uniform table.** -/
theorem etvDist_swappedTableLaw_le (layout : SiteLayout) (facts : SwapLayoutFacts layout) :
    (PMF.uniformOfFintype TagTable).etvDist (swappedTableLaw layout) ≤ (layout.sites.map facts.bias).sum := by
  rw [PMF.etvDist_comm]
  have chain := Swap.etvDist_foldl_le layout facts.bias layout.sites facts.nodup facts.close
    (PMF.uniformOfFintype TagTable)
  simpa [swappedTableLaw] using chain

variable {FI EI : Type} (E : CrtEntry FI EI)

/-- The uniform and the swapped table tapes are at most the table laws apart. -/
theorem etvDist_tapes_le :
    (uniformTableTape E).etvDist (swappedTableTape E)
      ≤ (PMF.uniformOfFintype TagTable).etvDist (swappedTableLaw E.layout) := by
  let _ : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
  have _ : Nonempty E.Coins := ⟨E.coinWitness⟩
  have uniformSplit : uniformTableTape E = (PMF.uniformOfFintype E.Coins).bind fun coins =>
      (PMF.uniformOfFintype TagTable).map fun table => (coins, table) := by
    change PMF.uniformOfFintype (E.Coins × TagTable) = _
    rw [uniformOfFintype_productPMF]
    rfl
  have swappedSplit : swappedTableTape E = (PMF.uniformOfFintype E.Coins).bind fun coins =>
      (swappedTableLaw E.layout).map fun table => (coins, table) := rfl
  rw [uniformSplit, swappedSplit]
  exact etvDist_bind_left_le_const _ _ _ _ fun _ => etvDist_map_le' _ _ _

theorem padSwapError_nonneg : 0 ≤ padSwapError := frac_nonneg _ _

/-- **Ledger row H3 (P1): the pad swap `G0T → G0U` costs at most `padSwapError`**, for any entry whose site layout
satisfies `SwapLayoutFacts`. -/
theorem crt_swap_of_layout [Finite FI] [Finite EI] (facts : SwapLayoutFacts E.layout) :
    HopBound (crtChain E).tablePlanted (crtChain E).padSwapped fun _ _ => padSwapError := by
  intro field group adversary parameter scalar _
  simp only [atSolution, crtChain, tablePlantedHybrid, padSwappedHybrid]
  rw [advantage_eq_etvDist]
  refine ENNReal.toReal_le_of_le_ofReal padSwapError_nonneg ?_
  unfold plantedGame
  exact le_trans (PMF.etvDist_bind_right_le _ _ _)
    (le_trans (etvDist_tapes_le E) (le_trans (etvDist_swappedTableLaw_le E.layout facts) facts.total))

end

end Kriterion.CRT.Privacy
