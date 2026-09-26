/-
**Independence of several parts of the swapped table** (for `CrtRestSplit` and
`CrtBmrSplit`).

`ReplayOn.lean` proves that one position outside every site (`indep_swapped_pos`) and one whole site
(`indep_swapped_site`) of the swapped table have their laws and are independent of the rest of the table. This file
combines them: a list of distinct positions outside every site and a list of distinct sites of the layout, read
together, are distributed as independent uniform answers times the sites' own laws, independently of the table
outside those positions.

* `IndepS`: `Indep` with the side condition "in the support of the law"; `Indep.toS` converts every `Indep`;
* `indep_pair`: two independent reads on disjoint parts combine into the product law;
* `IndepS.map`, `IndepS.joint` (the joint law of the read and any function of the rest is the product);
* **`indep_swapped_set`**: positions and sites together.
-/

import Proof.Privacy.CRT.Laws.ReplayOn

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT

noncomputable section

/-! ### 1. The support form, pairs and maps -/

/-- `Indep` with the side condition "in the support of `ν`". -/
abbrev IndepS {V : Type} (μ : PMF TagTable) (P : Set (Fin (2 ^ 40))) (ν : PMF V) (read : TagTable → V) : Prop :=
  Indep μ P ν read (· ∈ ν.support)

/-- A function that ignores a larger set of positions ignores a smaller one. -/
theorem Ignores.mono {X : Type} {P P' : Set (Fin (2 ^ 40))} {G : TagTable → X} (ignores : Ignores P' G)
    (sub : P ⊆ P') : Ignores P G :=
  fun T T' agree => ignores T T' fun p off => agree p fun hp => off (sub hp)

/-- The product of two laws. -/
def prodLaw {A B : Type} (ν₁ : PMF A) (ν₂ : PMF B) : PMF (A × B) :=
  ν₁.bind fun a => ν₂.map fun b => (a, b)

theorem mem_support_prodLaw {A B : Type} {ν₁ : PMF A} {ν₂ : PMF B} {a : A} {b : B} (ha : a ∈ ν₁.support)
    (hb : b ∈ ν₂.support) : (a, b) ∈ (prodLaw ν₁ ν₂).support := by
  unfold prodLaw
  rw [PMF.mem_support_bind_iff]
  exact ⟨a, ha, by rw [PMF.support_map]; exact ⟨b, hb, rfl⟩⟩

section Indep

variable {V : Type} {μ : PMF TagTable} {P : Set (Fin (2 ^ 40))} {ν : PMF V} {read : TagTable → V}

/-- The read's law is `ν`. -/
theorem Indep.map_read {ok : V → Prop} (indep : Indep μ P ν read ok) : μ.map read = ν := by
  have law := indep V (fun v _ => PMF.pure v) fun _ _ _ _ _ => rfl
  simp only [PMF.bind_const, PMF.bind_pure] at law
  rw [← law]
  exact (PMF.bind_pure_comp read μ).symm

theorem Indep.read_mem {ok : V → Prop} (indep : Indep μ P ν read ok) {T : TagTable} (hT : T ∈ μ.support) :
    read T ∈ ν.support := by
  rw [← indep.map_read, PMF.support_map]
  exact ⟨T, hT, rfl⟩

/-- **Every `Indep` holds in the support form.** -/
theorem Indep.toS {ok : V → Prop} (indep : Indep μ P ν read ok) : IndepS μ P ν read := by
  intro β G ignores
  classical
  let G' : V → TagTable → PMF β := fun v T => if v ∈ ν.support then G v T else μ.bind (G v)
  have ignores' : ∀ v, ok v → Ignores P (G' v) := by
    intro v _ T T' agree
    by_cases hv : v ∈ ν.support
    · simp only [G', if_pos hv]
      exact ignores v hv T T' agree
    · simp only [G', if_neg hv]
  have lhs : μ.bind (fun T => G (read T) T) = μ.bind (fun T => G' (read T) T) :=
    PMF.bind_congr _ _ _ fun T hT => by simp only [G', if_pos (indep.read_mem hT)]
  rw [lhs, indep β G' ignores']
  exact PMF.bind_congr _ _ _ fun v hv => by
    have hv' : v ∈ ν.support := hv
    simp only [G', if_pos hv']

/-- **A function of the read is independent in the same way.** -/
theorem IndepS.map {W : Type} (indep : IndepS μ P ν read) (f : V → W) : IndepS μ P (ν.map f) (f ∘ read) := by
  intro β G ignores
  have ig : ∀ v ∈ ν.support, Ignores P (G (f v)) := fun v hv =>
    ignores (f v) (by rw [PMF.support_map]; exact ⟨v, hv, rfl⟩)
  show μ.bind (fun T => G (f (read T)) T) = _
  rw [indep β (fun v => G (f v)) ig, PMF.bind_map]
  rfl

/-- **The joint law of the read and a function of the rest of the table is the product.** -/
theorem IndepS.joint {X : Type} (indep : IndepS μ P ν read) (g : TagTable → X) (ignores : Ignores P g) :
    μ.map (fun T => (read T, g T)) = prodLaw ν (μ.map g) := by
  have law := indep (V × X) (fun v T => PMF.pure (v, g T)) fun v _ T T' agree => by
    show PMF.pure (v, g T) = PMF.pure (v, g T')
    rw [ignores T T' agree]
  rw [← PMF.bind_pure_comp]
  refine law.trans ?_
  unfold prodLaw
  refine congrArg _ (funext fun v => ?_)
  rw [PMF.map_comp]
  rfl

end Indep

/-- **Two independent reads on disjoint parts combine into the product law.** The second read ignores the first's
positions. -/
theorem indep_pair {A B : Type} {μ : PMF TagTable} {P₁ P₂ : Set (Fin (2 ^ 40))} {ν₁ : PMF A} {ν₂ : PMF B}
    {read₁ : TagTable → A} {read₂ : TagTable → B} (h₁ : IndepS μ P₁ ν₁ read₁) (h₂ : IndepS μ P₂ ν₂ read₂)
    (apart : Ignores P₁ read₂) :
    IndepS μ (P₁ ∪ P₂) (prodLaw ν₁ ν₂) fun T => (read₁ T, read₂ T) := by
  intro β G ignores
  classical
  have ig : ∀ a ∈ ν₁.support, ∀ b ∈ ν₂.support, Ignores (P₁ ∪ P₂) (G (a, b)) := fun a ha b hb =>
    ignores (a, b) (mem_support_prodLaw ha hb)
  let G₁ : A → TagTable → PMF β := fun a T =>
    if read₂ T ∈ ν₂.support then G (a, read₂ T) T else μ.bind (G (a, read₂ T))
  have ig₁ : ∀ a ∈ ν₁.support, Ignores P₁ (G₁ a) := by
    intro a ha T T' agree
    have same : read₂ T = read₂ T' := apart T T' agree
    by_cases hb : read₂ T ∈ ν₂.support
    · have hb' : read₂ T' ∈ ν₂.support := same ▸ hb
      simp only [G₁, if_pos hb, if_pos hb', same]
      exact ((ig a ha _ hb').mono Set.subset_union_left) T T' agree
    · have hb' : read₂ T' ∉ ν₂.support := same ▸ hb
      simp only [G₁, if_neg hb, if_neg hb', same]
  have onSupport : ∀ a, μ.bind (G₁ a) = μ.bind fun T => G (a, read₂ T) T := fun a =>
    PMF.bind_congr _ _ _ fun T hT => by simp only [G₁, if_pos (h₂.read_mem hT)]
  calc μ.bind (fun T => G (read₁ T, read₂ T) T) = μ.bind (fun T => G₁ (read₁ T) T) :=
        PMF.bind_congr _ _ _ fun T hT => by simp only [G₁, if_pos (h₂.read_mem hT)]
    _ = ν₁.bind fun a => μ.bind (G₁ a) := h₁ β G₁ ig₁
    _ = ν₁.bind fun a => ν₂.bind fun b => μ.bind (G (a, b)) := PMF.bind_congr _ _ _ fun a ha => by
        rw [onSupport a]
        exact h₂ β (fun b => G (a, b)) fun b hb => (ig a ha b hb).mono Set.subset_union_right
    _ = (prodLaw ν₁ ν₂).bind fun v => μ.bind (G v) := by
        unfold prodLaw
        rw [PMF.bind_bind]
        refine congrArg _ (funext fun a => ?_)
        rw [PMF.bind_map]
        rfl

/-! ### 2. Positions and sites of the swapped table -/

/-- The law of a list of independent draws. -/
def listLaw {X : Type} : List (PMF X) → PMF (List X)
  | [] => PMF.pure []
  | ν :: rest => (prodLaw ν (listLaw rest)).map fun v => v.1 :: v.2

theorem indep_nil {X : Type} (μ : PMF TagTable) (read : TagTable → List X) (empty : ∀ T, read T = []) :
    IndepS μ {p | p ∈ ([] : List (Fin (2 ^ 40)))} (listLaw []) read := by
  intro β G _
  simp only [empty]
  show _ = (PMF.pure []).bind _
  rw [PMF.pure_bind]

/-- **Distinct positions outside every site are independent uniform answers, independent of the rest.** -/
theorem indep_swapped_positions (layout : SiteLayout) :
    ∀ (ps : List (Fin (2 ^ 40))), ps.Nodup → (∀ p ∈ ps, ∀ site ∈ layout.sites, p ∉ (siteTags layout site).map tagPos) →
      IndepS (swappedTableLaw layout) {p | p ∈ ps} (listLaw (ps.map fun _ => PMF.uniformOfFintype (Block × Block)))
        (fun T => ps.map T)
  | [], _, _ => indep_nil _ _ fun _ => rfl
  | p :: ps, nodup, away => by
      have head := (indep_swapped_pos layout p fun site member => away p List.mem_cons_self site member).toS
      have tail := indep_swapped_positions layout ps (List.nodup_cons.mp nodup).2
        fun q hq => away q (List.mem_cons_of_mem _ hq)
      have apart : Ignores {p} (fun T => ps.map T) := fun T T' agree =>
        List.map_congr_left fun q hq => agree q fun hp => (List.nodup_cons.mp nodup).1 (by
          rw [Set.mem_singleton_iff] at hp
          rw [← hp]
          exact hq)
      have pair := (indep_pair head tail apart).map fun v => v.1 :: v.2
      have eqSet : ({p} ∪ {q | q ∈ ps} : Set (Fin (2 ^ 40))) = {q | q ∈ p :: ps} := by
        ext q
        simp
      rw [eqSet] at pair
      exact pair

/-- **Distinct sites of the layout have their laws, independent of each other and of the rest.** -/
theorem indep_swapped_sites (layout : SiteLayout) (facts : RefillLayoutFacts layout) :
    ∀ (S : List SiteId), S.Nodup → (∀ s ∈ S, s ∈ layout.sites) →
      IndepS (swappedTableLaw layout) {p | ∃ s ∈ S, p ∈ sitePos layout s} (listLaw (S.map layout.law))
        (fun T => S.map (siteAnswersOf layout T))
  | [], _, _ => by
      have eqSet : {p | ∃ s ∈ ([] : List SiteId), p ∈ sitePos layout s} = {p | p ∈ ([] : List (Fin (2 ^ 40)))} := by
        ext p
        simp
      rw [eqSet]
      exact indep_nil _ _ fun _ => rfl
  | s :: S, nodup, sub => by
      have sIn : s ∈ layout.sites := sub s List.mem_cons_self
      have head := (indep_swapped_site layout facts s sIn).toS
      have tail := indep_swapped_sites layout facts S (List.nodup_cons.mp nodup).2
        fun t ht => sub t (List.mem_cons_of_mem _ ht)
      have apart : Ignores (sitePos layout s) (fun T => S.map (siteAnswersOf layout T)) := by
        intro T T' agree
        refine List.map_congr_left fun t ht => List.map_congr_left fun tag hit => agree _ fun inS => ?_
        have ne : s ≠ t := fun same => (List.nodup_cons.mp nodup).1 (same ▸ ht)
        exact facts.disjoint s sIn t (sub t (List.mem_cons_of_mem _ ht)) ne _ inS (List.mem_map_of_mem hit)
      have pair := (indep_pair head tail apart).map fun v => v.1 :: v.2
      have eqSet : (sitePos layout s ∪ {p | ∃ t ∈ S, p ∈ sitePos layout t}) =
          {p | ∃ t ∈ s :: S, p ∈ sitePos layout t} := by
        ext p
        simp
      rw [eqSet] at pair
      exact pair

/-- **Positions and sites together**: distinct positions outside every site and distinct sites of the layout are
distributed as independent uniform answers times the sites' laws, independently of the table outside them. -/
theorem indep_swapped_set (layout : SiteLayout) (facts : RefillLayoutFacts layout) (ps : List (Fin (2 ^ 40)))
    (psNodup : ps.Nodup) (away : ∀ p ∈ ps, ∀ site ∈ layout.sites, p ∉ (siteTags layout site).map tagPos)
    (S : List SiteId) (sNodup : S.Nodup) (sub : ∀ s ∈ S, s ∈ layout.sites) :
    IndepS (swappedTableLaw layout) ({p | p ∈ ps} ∪ {p | ∃ s ∈ S, p ∈ sitePos layout s})
      (prodLaw (listLaw (ps.map fun _ => PMF.uniformOfFintype (Block × Block))) (listLaw (S.map layout.law)))
      (fun T => (ps.map T, S.map (siteAnswersOf layout T))) :=
  indep_pair (indep_swapped_positions layout ps psNodup away) (indep_swapped_sites layout facts S sNodup sub)
    fun _ _ agree => List.map_congr_left fun s hs => List.map_congr_left fun _ hit =>
      agree _ fun hp => away _ hp s (sub s hs) (List.mem_map_of_mem hit)

/-- **Any read of finitely many positions outside every site is independent of the rest**, with its own law. -/
theorem indep_swapped_read {V : Type} (layout : SiteLayout) (Ps : Finset (Fin (2 ^ 40)))
    (away : ∀ p ∈ Ps, ∀ site ∈ layout.sites, p ∉ (siteTags layout site).map tagPos) (read : TagTable → V)
    (dep : ∀ T T' : TagTable, (∀ p ∈ Ps, T p = T' p) → read T = read T') :
    IndepS (swappedTableLaw layout) ↑Ps ((swappedTableLaw layout).map read) read := by
  classical
  have list := indep_swapped_positions layout Ps.toList (Finset.nodup_toList Ps)
    fun p hp => away p (Finset.mem_toList.mp hp)
  let rebuild : List (Block × Block) → TagTable := fun l p => l.getD (Ps.toList.idxOf p) (0, 0)
  have rebuilt : ∀ T, ∀ p ∈ Ps, rebuild (Ps.toList.map T) p = T p := by
    intro T p hp
    have mem : p ∈ Ps.toList := Finset.mem_toList.mpr hp
    have lt := List.idxOf_lt_length_of_mem mem
    simp only [rebuild, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem lt,
      List.getElem_idxOf lt, Option.map_some, Option.getD_some]
  have mapped := list.map fun l => read (rebuild l)
  have readEq : ((fun l => read (rebuild l)) ∘ fun T => Ps.toList.map T) = read :=
    funext fun T => dep _ _ fun p hp => rebuilt T p hp
  have setEq : {p | p ∈ Ps.toList} = (↑Ps : Set (Fin (2 ^ 40))) := by
    ext p
    simp
  rw [readEq, setEq] at mapped
  rw [mapped.map_read]
  exact mapped

end

end Kriterion.CRT.Privacy.Laws
