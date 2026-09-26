/-
**P10, step 3: the coupling of the two replays** (row H10).

`H` runs a replay program through the refill reader, `I` through the lazy reader, both on views (`Readers.lean`).
The coupling keeps a list `S` of the sites `H` has refilled, with their labels; `H`'s view is `I`'s view with the
points of those sites (`pending S`) filled by uniform values (`fillK`). One query keeps the invariant:

* a query outside every site, at a site `H` sees touched, or at a site already refilled (whose points are all
  pending, or which has none) is lazy in both, and a lazy query commutes with the fill (`lazy_step`);
* a query at a site `H` sees untouched and has not refilled draws it from the layout's law: at the cost of the law's
  distance to uniform answers (at most the site's bias), the draw is uniform, and installing uniform answers
  extends the fill to the site's points (`install_fill`), after which the query is lazy again.

Each site is refilled at most once (`SingleLabelFrom`), so the costs sum to at most the biases of the layout's
sites not yet refilled (`cost`). `couple` states this for any program with any continuations whose own distance is
bounded the same way at every leaf.
-/

import Proof.Privacy.CRT.Refill.Readers
import Proof.Privacy.CRT.Refill.SingleLabel

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Refill

open BN254 Cryptography Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC (FreeQuery)
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le_const)
open scoped ENNReal

noncomputable section

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]
variable (layout : SiteLayout)

/-! ### The refilled sites -/

/-- The points of the refilled sites. -/
def pending (S : List (SiteId × ℕ)) : Finset BaseField :=
  (S.flatMap fun e => sitePoints layout e.1 e.2).toFinset

/-- The biases of the layout's sites not yet refilled. -/
def cost (bias : SiteId → ℝ≥0∞) (S : List (SiteId × ℕ)) : ℝ≥0∞ :=
  ((layout.sites.filter fun site => site ∉ S.map Prod.fst).map bias).sum

/-- A site the refill can draw: it decodes from a tag that is not a collector-mask position. -/
def Drawable (site : SiteId) : Prop := ∃ tag, siteOf tag = some site ∧ isCollectorMaskTag tag = false

/-- The coupling's invariant: each refilled site's label is fixed at its refill label, and each refilled site is a
drawable site of the layout at a label below `2^128`. -/
structure Inv (seen : SiteId → Option ℕ) (S : List (SiteId × ℕ)) : Prop where
  label : ∀ e ∈ S, seen e.1 = some e.2
  site : ∀ e ∈ S, e.1 ∈ layout.sites ∧ Drawable e.1 ∧ e.2 < 2 ^ 128

theorem pending_nil : pending layout [] = ∅ := rfl

theorem pending_cons (site : SiteId) (label : ℕ) (S : List (SiteId × ℕ)) :
    pending layout ((site, label) :: S) = pending layout S ∪ (sitePoints layout site label).toFinset := by
  unfold pending
  rw [List.flatMap_cons, List.toFinset_append, Finset.union_comm]

theorem sum_filter_mono (bias : SiteId → ℝ≥0∞) (site : SiteId) (T : List SiteId) (L : List SiteId) :
    ((L.filter fun t => t ∉ site :: T).map bias).sum ≤ ((L.filter fun t => t ∉ T).map bias).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
      by_cases inT : t ∈ T
      · have : t ∈ site :: T := List.mem_cons_of_mem _ inT
        simp only [List.filter_cons, inT, this, not_true_eq_false, decide_false]
        exact ih
      · by_cases same : t = site
        · subst same
          simp only [List.filter_cons, List.mem_cons_self, not_true_eq_false, decide_false, inT,
            not_false_eq_true, decide_true, if_true, Bool.false_eq_true, if_false, List.map_cons, List.sum_cons]
          exact le_trans ih le_add_self
        · have : t ∉ site :: T := by simp [same, inT]
          simp only [List.filter_cons, this, inT, not_false_eq_true, decide_true, if_true, List.map_cons,
            List.sum_cons]
          exact add_le_add le_rfl ih

theorem sum_filter_cons (bias : SiteId → ℝ≥0∞) (site : SiteId) (T : List SiteId) (outside : site ∉ T) :
    ∀ L : List SiteId, site ∈ L →
      bias site + ((L.filter fun t => t ∉ site :: T).map bias).sum ≤ ((L.filter fun t => t ∉ T).map bias).sum
  | [], member => absurd member List.not_mem_nil
  | t :: L, member => by
      by_cases same : t = site
      · subst same
        simp only [List.filter_cons, List.mem_cons_self, not_true_eq_false, decide_false, outside,
          not_false_eq_true, decide_true, if_true, Bool.false_eq_true, if_false, List.map_cons, List.sum_cons]
        exact add_le_add le_rfl (sum_filter_mono bias t T L)
      · have rest : site ∈ L := by
          rcases List.mem_cons.mp member with h | h
          · exact absurd h.symm same
          · exact h
        have ih := sum_filter_cons bias site T outside L rest
        by_cases inT : t ∈ T
        · have : t ∈ site :: T := List.mem_cons_of_mem _ inT
          simp only [List.filter_cons, inT, this, not_true_eq_false, decide_false]
          exact ih
        · have : t ∉ site :: T := by simp [same, inT]
          simp only [List.filter_cons, this, inT, not_false_eq_true, decide_true, if_true, List.map_cons,
            List.sum_cons]
          calc bias site + (bias t + ((L.filter fun t => t ∉ site :: T).map bias).sum)
              = bias t + (bias site + ((L.filter fun t => t ∉ site :: T).map bias).sum) := add_left_comm _ _ _
            _ ≤ bias t + ((L.filter fun t => t ∉ T).map bias).sum := add_le_add le_rfl ih

/-- **Refilling a new site of the layout spends its bias.** -/
theorem cost_cons (bias : SiteId → ℝ≥0∞) {site : SiteId} (member : site ∈ layout.sites) (label : ℕ)
    {S : List (SiteId × ℕ)} (fresh : site ∉ S.map Prod.fst) :
    bias site + cost layout bias ((site, label) :: S) ≤ cost layout bias S := by
  unfold cost
  rw [List.map_cons]
  exact sum_filter_cons bias site (S.map Prod.fst) fresh layout.sites member

theorem inv_record {seen : SiteId → Option ℕ} {S : List (SiteId × ℕ)} (inv : Inv layout seen S) {input : ℕ}
    (ok : SiteQueryOK layout seen input) : Inv layout (recordSite seen input) S := by
  refine ⟨fun e member => ?_, inv.site⟩
  unfold SiteQueryOK at ok
  cases decode : siteOf (input / 2 ^ 128) with
  | none =>
      simp only [recordSite, decode]
      exact inv.label e member
  | some site =>
      rw [decode] at ok
      simp only [recordSite, decode]
      by_cases same : e.1 = site
      · have fixed := inv.label e member
        rw [same] at fixed ⊢
        rw [Function.update_self]
        rcases ok.2.2 with none | some
        · rw [fixed] at none
          cases none
        · rw [fixed] at some
          exact some.symm
      · rw [Function.update_of_ne same]
        exact inv.label e member

theorem inv_cons {seen : SiteId → Option ℕ} {S : List (SiteId × ℕ)} (inv : Inv layout seen S) {input : ℕ}
    {site : SiteId} (decode : siteOf (input / 2 ^ 128) = some site) (ok : SiteQueryOK layout seen input) :
    Inv layout (recordSite seen input) ((site, input % 2 ^ 128) :: S) := by
  have okSite := ok
  unfold SiteQueryOK at okSite
  rw [decode] at okSite
  have recorded := inv_record layout inv ok
  refine ⟨fun e member => ?_, fun e member => ?_⟩
  · rcases List.mem_cons.mp member with head | tail
    · subst head
      simp only [recordSite, decode, Function.update_self]
    · exact recorded.label e tail
  · rcases List.mem_cons.mp member with head | tail
    · subst head
      exact ⟨okSite.1, ⟨_, decode, okSite.2.1⟩, Nat.mod_lt _ (Nat.two_pow_pos 128)⟩
    · exact inv.site e tail

/-! ### Fill facts for one query -/

/-- A site is untouched on a filled view exactly when its points are neither pending nor defined; the filled
values do not matter. -/
theorem untouched_fill (points : List BaseField) (w : View FI EI) (P : Finset BaseField)
    (v : BaseField → Block × Block) :
    untouchedView points (fill w P v) = points.all fun x => decide (x ∉ P) && (w.2.2 x).isNone := by
  unfold untouchedView
  congr 1
  funext x
  by_cases inside : x ∈ P
  · cases known : w.2.2 x <;> simp [fill, fillHash, inside, known]
  · simp [fill, fillHash, inside]

/-- Two kernels that agree on every filled view agree after the fill kernel. -/
theorem fillK_bind_congr {β : Type} (w : View FI EI) (P : Finset BaseField) (f g : View FI EI → PMF β)
    (same : ∀ v, f (fill w P v) = g (fill w P v)) : (fillK w P).bind f = (fillK w P).bind g := by
  unfold fillK
  rw [PMF.bind_map, PMF.bind_map]
  exact congrArg _ (funext same)

/-- **A hash query commutes with the fill**, in distance: the two sides differ by at most the continuations'
distance at every answer. -/
theorem hash_step {β : Type} (x : BaseField) (w : View FI EI) (P : Finset BaseField)
    (G G' : (Block × Block) × View FI EI → PMF β) (c : ℝ≥0∞)
    (each : ∀ r, ((fillK r.2 P).bind fun w2 => G (r.1, w2)).etvDist (G' r) ≤ c) :
    ((fillK w P).bind fun w1 => (queryView.hashQueryView w1 x).bind G).etvDist
      ((queryView.hashQueryView w x).bind G') ≤ c := by
  have commute : (fillK w P).bind (fun w1 => (queryView.hashQueryView w1 x).bind G)
      = (queryView.hashQueryView w x).bind fun r => (fillK r.2 P).bind fun w2 => G (r.1, w2) := by
    rw [← PMF.bind_bind, fill_hashQuery, PMF.bind_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [PMF.bind_map]
    rfl
  rw [commute]
  exact etvDist_bind_left_le_const _ _ _ _ each

/-- **A lazy query commutes with the fill**, in distance. -/
theorem lazy_step {β : Type} (input : ℕ) (w : View FI EI) (P : Finset BaseField)
    (G G' : (Block × Block) × View FI EI → PMF β) (c : ℝ≥0∞)
    (each : ∀ r, ((fillK r.2 P).bind fun w2 => G (r.1, w2)).etvDist (G' r) ≤ c) :
    ((fillK w P).bind fun w1 => (lazyView input w1).bind G).etvDist ((lazyView input w).bind G') ≤ c :=
  hash_step (input : BaseField) w P G G' c each

/-- The fill on no pending point is the view itself. -/
theorem fillK_empty (w : View FI EI) : fillK w ∅ = PMF.pure w := by
  unfold fillK
  have : fill w ∅ = fun _ => w := by
    funext v
    have empty : fillHash w.2.2 ∅ v = w.2.2 := by
      funext x
      simp [fillHash]
    simp only [fill, empty]
  rw [this]
  exact PMF.map_const _ _

/-! ### The coupling -/

/-- **The coupling of the replays.** Started from `I`'s view and `H`'s view filled at the pending points of the
refilled sites `S`, a program run through the refill reader and through the lazy reader, followed by continuations
bounded the same way at every leaf, differ by at most the biases of the sites not yet refilled. -/
theorem couple (bias : SiteId → ℝ≥0∞)
    (close : ∀ site ∈ layout.sites, (layout.law site).etvDist (uniformAnswers (layout.answers site)) ≤ bias site)
    {α β : Type} (leaf : (SiteId → Option ℕ) → α → Prop) (KH KI : α → View FI EI → PMF β)
    (cont : ∀ seen S a w, Inv layout seen S → leaf seen a →
      ((fillK w (pending layout S)).bind (KH a)).etvDist (KI a w) ≤ cost layout bias S)
    (R : CM α) : ∀ (seen : SiteId → Option ℕ) (S : List (SiteId × ℕ)) (w : View FI EI), Inv layout seen S →
      SingleLabelFrom layout leaf seen R →
      ((fillK w (pending layout S)).bind fun w1 =>
          (runView (refillView layout layout.law) R w1).bind fun r => KH r.1 r.2).etvDist
        ((runView lazyView R w).bind fun r => KI r.1 r.2) ≤ cost layout bias S := by
  induction R with
  | pure value =>
      intro seen S w inv path
      simp only [runView, PMF.pure_bind]
      exact cont seen S value w inv path
  | query input next ih =>
      intro seen S w inv path
      obtain ⟨ok, rest⟩ := path
      simp only [runView, PMF.bind_bind]
      set P := pending layout S with hP
      set G : (Block × Block) × View FI EI → PMF β := fun r =>
        (runView (refillView layout layout.law) (next r.1) r.2).bind fun r' => KH r'.1 r'.2 with hG
      set G' : (Block × Block) × View FI EI → PMF β := fun r =>
        (runView lazyView (next r.1) r.2).bind fun r' => KI r'.1 r'.2 with hG'
      have inv' := inv_record layout inv ok
      have lazy : (∀ v, refillView layout layout.law input (fill w P v) = lazyView input (fill w P v)) →
          ((fillK w P).bind fun w1 => (refillView layout layout.law input w1).bind G).etvDist
            ((lazyView input w).bind G') ≤ cost layout bias S := by
        intro same
        rw [fillK_bind_congr w P _ (fun w1 => (lazyView input w1).bind G) fun v => by rw [same v]]
        exact lazy_step input w P G G' _ fun r => ih r.1 (recordSite seen input) S r.2 inv' (rest r.1)
      show ((fillK w P).bind fun w1 => (refillView layout layout.law input w1).bind G).etvDist
        ((lazyView input w).bind G') ≤ cost layout bias S
      cases decode : siteOf (input / 2 ^ 128) with
      | none =>
          refine lazy fun v => ?_
          unfold refillView
          rw [decode]
      | some site =>
          have okSite := ok
          unfold SiteQueryOK at okSite
          rw [decode] at okSite
          set points := sitePoints layout site (input % 2 ^ 128) with hpoints
          have shape : ∀ w1 : View FI EI, refillView layout layout.law input w1 =
              if untouchedView points w1 then
                (layout.law site).bind fun answers => lazyView input (installView (points.zip answers) w1)
              else lazyView input w1 := by
            intro w1
            unfold refillView
            rw [decode]
          by_cases U : (points.all fun x => decide (x ∉ P) && (w.2.2 x).isNone) = true
          · by_cases old : site ∈ S.map Prod.fst
            · -- a refilled site: its points are pending, so it has none
              obtain ⟨e, member, first⟩ := List.mem_map.mp old
              have fixed := inv.label e member
              rw [first] at fixed
              have sameLabel : e.2 = input % 2 ^ 128 := by
                rcases okSite.2.2 with none | some
                · rw [fixed] at none
                  cases none
                · rw [fixed] at some
                  exact Option.some.inj some
              have empty : points = [] := by
                rw [List.eq_nil_iff_forall_not_mem]
                intro x xMember
                have inside : x ∈ P := by
                  rw [hP]
                  unfold pending
                  rw [List.mem_toFinset, List.mem_flatMap]
                  refine ⟨e, member, ?_⟩
                  rw [first, sameLabel]
                  exact xMember
                have := List.all_eq_true.mp U x xMember
                simp [inside] at this
              refine lazy fun v => ?_
              rw [shape]
              split
              · simp only [empty, List.zip_nil_left]
                exact PMF.bind_const _ _
              · rfl
            · -- a new site: draw it, at the cost of its bias
              have U' : ∀ v, untouchedView points (fill w P v) = true := fun v => by rw [untouched_fill]; exact U
              have draw : (fillK w P).bind (fun w1 => (refillView layout layout.law input w1).bind G)
                  = (layout.law site).bind fun answers => (fillK w P).bind fun w1 =>
                      (lazyView input (installView (points.zip answers) w1)).bind G := by
                rw [fillK_bind_congr w P _ (fun w1 => (layout.law site).bind fun answers =>
                    (lazyView input (installView (points.zip answers) w1)).bind G) fun v => by
                  rw [shape, if_pos (U' v), PMF.bind_bind]]
                exact PMF.bind_comm _ _ _
              have length : points.length = layout.answers site := by
                rw [hpoints]
                unfold sitePoints
                rw [List.length_map, siteTags_length]
              set S' := (site, input % 2 ^ 128) :: S with hS'
              have middle : ((uniformAnswers (layout.answers site)).bind fun answers => (fillK w P).bind fun w1 =>
                    (lazyView input (installView (points.zip answers) w1)).bind G)
                  = (fillK w (pending layout S')).bind fun w2 => (lazyView input w2).bind G := by
                rw [PMF.bind_comm, ← length]
                calc (fillK w P).bind (fun w1 => (uniformAnswers points.length).bind fun answers =>
                        (lazyView input (installView (points.zip answers) w1)).bind G)
                    = ((fillK w P).bind fun w1 => (uniformAnswers points.length).map fun answers =>
                        installView (points.zip answers) w1).bind fun w2 => (lazyView input w2).bind G := by
                      rw [PMF.bind_bind]
                      refine congrArg _ (funext fun w1 => ?_)
                      rw [PMF.bind_map]
                      rfl
                  _ = _ := by rw [install_fill, hS', pending_cons]
              have invS' := inv_cons layout inv decode ok
              have step1 : ((fillK w P).bind fun w1 => (refillView layout layout.law input w1).bind G).etvDist
                  ((fillK w (pending layout S')).bind fun w2 => (lazyView input w2).bind G) ≤ bias site := by
                rw [draw, ← middle]
                exact le_trans (PMF.etvDist_bind_right_le _ _ _) (close site okSite.1)
              have step2 : ((fillK w (pending layout S')).bind fun w2 => (lazyView input w2).bind G).etvDist
                  ((lazyView input w).bind G') ≤ cost layout bias S' :=
                lazy_step input w _ G G' _ fun r => ih r.1 (recordSite seen input) S' r.2 invS' (rest r.1)
              calc _ ≤ _ := PMF.etvDist_triangle _ _ _
                _ ≤ bias site + cost layout bias S' := add_le_add step1 step2
                _ ≤ cost layout bias S := cost_cons layout bias okSite.1 _ old
          · -- touched in `H`: lazy
            refine lazy fun v => ?_
            rw [shape, if_neg (by rw [untouched_fill]; exact U)]

end

end Kriterion.CRT.Privacy.Refill
