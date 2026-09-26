/-
**Step 3 of the on-curve comparison: `HW`'s table run is deterministic**.

`routeMReplay_table` (P6b1) writes `HW`'s replay as the table run of route M's replay program on a table `T` drawn
from the swapped law. This file shows that the table run itself draws nothing. On a program whose queries are field
elements (`n < p`) and whose site queries name one of the site's own tags (`Canonical`), started from a state that
is consistent with `T` and closed under sites (every site of the layout, at every label, is stored whole or not at
all), every query is answered by `T` at its tag. A fresh non-site query is read from `T`. A clean site is installed
from `T` and the query reads its own point back. A stored query holds `T`'s answer by consistency. A query at a
touched site is stored, by closure.

* `tableReader_step`: one query, with the next state `stepState`;
* **`tableRun_eq_pure`**: the run is `PMF.pure (R.eval (tagHash T), tableFinal layout T R σ)`, and the final state
  is consistent with `T`, closed, and stores exactly the old inputs and the run's points (`runPoints`: a non-site
  input itself, a site's whole point list);
* `tableRun_empty`: from the empty state the final state is `SeenState tagOfInput empty (runPoints …) T`;
* **`routeMReplay_pure`**: `HW`'s replay from the empty state is `T ← swappedTableLaw; pure (eval, tableFinal)`;
* `crtLayout_points`: the layout facts for the real layout.
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Laws.ReplayRouteM
import Proof.Privacy.CRT.Laws.ReplayOff

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT

noncomputable section

variable {FI EI : Type}

/-! ### 1. Site points -/

/-- **The layout facts of the pure table run**: every tag of a site of the layout decodes to that site and is a
table position. -/
structure PointFacts (layout : SiteLayout) : Prop where
  decode : ∀ site ∈ layout.sites, ∀ tag ∈ siteTags layout site, siteOf tag = some site
  bound : ∀ site ∈ layout.sites, ∀ tag ∈ siteTags layout site, tag < 2 ^ 40

theorem val_natCast_small {m : ℕ} (small : m < 2 ^ 168) : ((m : BaseField)).val = m := by
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  exact lt_trans small (by unfold baseFieldModulus; norm_num)

theorem point_val {layout : SiteLayout} (facts : PointFacts layout) {site : SiteId} (member : site ∈ layout.sites)
    {label : ℕ} (small : label < 2 ^ 128) {tag : ℕ} (hit : tag ∈ siteTags layout site) :
    (((label + 2 ^ 128 * tag : ℕ) : BaseField)).val = label + 2 ^ 128 * tag := by
  apply val_natCast_small
  have bound := facts.bound site member tag hit
  have le : 2 ^ 128 * tag ≤ 2 ^ 128 * (2 ^ 40 - 1) := Nat.mul_le_mul_left _ (by omega)
  norm_num at le ⊢
  omega

theorem point_div {label tag : ℕ} (small : label < 2 ^ 128) : (label + 2 ^ 128 * tag) / 2 ^ 128 = tag := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.div_eq_of_lt small, zero_add]

theorem point_mod {label tag : ℕ} (small : label < 2 ^ 128) : (label + 2 ^ 128 * tag) % 2 ^ 128 = label := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt small]

/-- **A site point decodes**: its tag is one of the site's tags and decodes to the site, its label is its low part,
and its table position is its tag's. -/
theorem sitePoint_decode {layout : SiteLayout} (facts : PointFacts layout) {site : SiteId}
    (member : site ∈ layout.sites) {label : ℕ} (small : label < 2 ^ 128) {x : BaseField}
    (hx : x ∈ sitePoints layout site label) :
    x.val / 2 ^ 128 ∈ siteTags layout site ∧ siteOf (x.val / 2 ^ 128) = some site ∧ x.val % 2 ^ 128 = label ∧
      tagOfInput x = tagPos (x.val / 2 ^ 128) := by
  unfold sitePoints at hx
  obtain ⟨tag, hit, rfl⟩ := List.mem_map.mp hx
  rw [point_val facts member small hit, point_div small, point_mod small]
  refine ⟨hit, facts.decode site member tag hit, rfl, Fin.ext ?_⟩
  show (((label + 2 ^ 128 * tag : ℕ) : BaseField)).val / 2 ^ 128 % 2 ^ 40 = tag % 2 ^ 40
  rw [point_val facts member small hit, point_div small]

/-- **The point lists of two sites at two labels are equal or disjoint.** -/
theorem sitePoints_disjoint {layout : SiteLayout} (facts : PointFacts layout) {site site' : SiteId}
    (member : site ∈ layout.sites) (member' : site' ∈ layout.sites) {label label' : ℕ} (small : label < 2 ^ 128)
    (small' : label' < 2 ^ 128) {x : BaseField} (hx : x ∈ sitePoints layout site label)
    (hx' : x ∈ sitePoints layout site' label') : site = site' ∧ label = label' := by
  obtain ⟨-, d, m, -⟩ := sitePoint_decode facts member small hx
  obtain ⟨-, d', m', -⟩ := sitePoint_decode facts member' small' hx'
  exact ⟨Option.some_injective _ (d.symm.trans d'), m.symm.trans m'⟩

/-- A query at one of a site's tags is one of the site's points at its own label. -/
theorem self_mem_sitePoints (layout : SiteLayout) (site : SiteId) (n : ℕ) (hit : n / 2 ^ 128 ∈ siteTags layout site) :
    (n : BaseField) ∈ sitePoints layout site (n % 2 ^ 128) := by
  unfold sitePoints
  refine List.mem_map.mpr ⟨n / 2 ^ 128, hit, ?_⟩
  rw [Nat.mod_add_div]

/-- A non-site input is no site's point. -/
theorem nonSite_not_mem {layout : SiteLayout} (facts : PointFacts layout) {n : ℕ} (small : ((n : BaseField)).val = n)
    (notSite : siteOf (n / 2 ^ 128) = none) {site : SiteId} (member : site ∈ layout.sites) {label : ℕ}
    (smallLabel : label < 2 ^ 128) : (n : BaseField) ∉ sitePoints layout site label := by
  intro hit
  have decode := (sitePoint_decode facts member smallLabel hit).2.1
  rw [small, notSite] at decode
  cases decode

theorem zip_map_same {β γ δ : Type} (f : β → γ) (g : β → δ) :
    ∀ l : List β, (l.map f).zip (l.map g) = l.map fun b => (f b, g b)
  | [] => rfl
  | b :: l => by simp [zip_map_same f g l]

theorem tagOfInput_small {n : ℕ} (small : ((n : BaseField)).val = n) :
    tagOfInput (n : BaseField) = tagPos (n / 2 ^ 128) := by
  refine Fin.ext ?_
  show (n : BaseField).val / 2 ^ 128 % 2 ^ 40 = n / 2 ^ 128 % 2 ^ 40
  rw [small]

/-! ### 2. States consistent with a table -/

/-- **A state consistent with `T`**: every stored hash input holds `T`'s answer at its tag. -/
def TableConsistent (T : TagTable) (σ : LazyOracle.State FI EI) : Prop :=
  ∀ x v, σ.hash.lookup x = some v → v = Fintype.equivFin (Block × Block) (T (tagOfInput x))

/-- **A state closed under sites**: at every site of the layout and every label, its points are stored all or none. -/
def SiteClosed (layout : SiteLayout) (σ : LazyOracle.State FI EI) : Prop :=
  ∀ site ∈ layout.sites, ∀ label, label < 2 ^ 128 → ∀ x ∈ sitePoints layout site label,
    (σ.hash.lookup x).isSome → ∀ y ∈ sitePoints layout site label, (σ.hash.lookup y).isSome

theorem lookupHash_isNone (σ : LazyOracle.State FI EI) (x : BaseField) :
    (LazyOracle.lookup (.hash x) σ).isNone = (σ.hash.lookup x).isNone := by
  show (Option.map _ (σ.hash.lookup x)).isNone = _
  cases σ.hash.lookup x <;> rfl

theorem plantHash_lookup (σ : LazyOracle.State FI EI) (x y : BaseField) (a : Block × Block) :
    (plantHash x a σ).hash.lookup y = if y = x then some (Fintype.equivFin (Block × Block) a) else σ.hash.lookup y :=
  lookup_cons _ _ _ _

theorem plant_consistent (T : TagTable) {σ : LazyOracle.State FI EI} (cons : TableConsistent T σ) (x : BaseField)
    (a : Block × Block) (agree : a = T (tagOfInput x)) : TableConsistent T (plantHash x a σ) := by
  intro y v hv
  rw [plantHash_lookup] at hv
  by_cases same : y = x
  · rw [if_pos same] at hv
    subst same
    rw [← Option.some_injective _ hv, agree]
  · rw [if_neg same] at hv
    exact cons y v hv

theorem plant_isSome (σ : LazyOracle.State FI EI) (x y : BaseField) (a : Block × Block) :
    ((plantHash x a σ).hash.lookup y).isSome ↔ ((σ.hash.lookup y).isSome ∨ y = x) := by
  rw [plantHash_lookup]
  by_cases same : y = x
  · rw [if_pos same]
    simp [same]
  · rw [if_neg same]
    simp [same]

theorem stored_value (T : TagTable) {σ : LazyOracle.State FI EI} (cons : TableConsistent T σ) {x : BaseField}
    {v : Fin (Fintype.card (Block × Block))} (found : σ.hash.lookup x = some v) :
    hashValue v = T (tagOfInput x) := by
  rw [cons x v found]
  simp [hashValue]

section Install

variable [DecidableEq FI] [DecidableEq EI]

/-- **Installing pairs that agree with `T`** keeps the state consistent and stores exactly the old inputs and the
pairs' inputs. -/
theorem installPoints_spec (T : TagTable) :
    ∀ (pairs : List (BaseField × (Block × Block))), (∀ pair ∈ pairs, pair.2 = T (tagOfInput pair.1)) →
      ∀ σ : LazyOracle.State FI EI, TableConsistent T σ →
        TableConsistent T (installPoints pairs σ) ∧ (installPoints pairs σ).fixed = σ.fixed ∧
          (installPoints pairs σ).enc = σ.enc ∧
          ∀ x, ((installPoints pairs σ).hash.lookup x).isSome ↔ ((σ.hash.lookup x).isSome ∨ x ∈ pairs.map Prod.fst)
  | [], _, σ, cons => ⟨cons, rfl, rfl, fun x => by simp [installPoints]⟩
  | pair :: rest, agree, σ, cons => by
      have one : TableConsistent T ((LazyOracle.program (.hash pair.1) pair.2 σ).getD σ) ∧
          ((LazyOracle.program (.hash pair.1) pair.2 σ).getD σ).fixed = σ.fixed ∧
          ((LazyOracle.program (.hash pair.1) pair.2 σ).getD σ).enc = σ.enc ∧
          ∀ x, (((LazyOracle.program (.hash pair.1) pair.2 σ).getD σ).hash.lookup x).isSome ↔
            ((σ.hash.lookup x).isSome ∨ x = pair.1) := by
        by_cases fresh : σ.hash.lookup pair.1 = none
        · rw [program_hash_fresh σ pair.1 pair.2 fresh, Option.getD_some]
          exact ⟨plant_consistent T cons _ _ (agree pair (List.mem_cons_self ..)), rfl, rfl,
            fun x => plant_isSome σ pair.1 x pair.2⟩
        · have none : LazyOracle.program (.hash pair.1) pair.2 σ = none := by
            rw [program_hash, if_neg fresh]
          rw [none, Option.getD_none]
          refine ⟨cons, rfl, rfl, fun x => ⟨Or.inl, ?_⟩⟩
          rintro (stored | rfl)
          · exact stored
          · exact Option.ne_none_iff_isSome.mp fresh
      obtain ⟨c2, f2, e2, s2⟩ := installPoints_spec T rest (fun p hp => agree p (List.mem_cons_of_mem _ hp))
        _ one.1
      refine ⟨c2, f2.trans one.2.1, e2.trans one.2.2.1, fun x => ?_⟩
      show ((installPoints rest ((LazyOracle.program (.hash pair.1) pair.2 σ).getD σ)).hash.lookup x).isSome ↔ _
      rw [s2 x, one.2.2.2 x]
      simp only [List.map_cons, List.mem_cons]
      tauto

end Install

/-! ### 3. One query, and the run -/

/-- **Canonical queries**: every query is a field element, and a query whose tag decodes to a site is a site of the
layout at one of its own tags. -/
inductive Canonical (layout : SiteLayout) {α : Type} : CM α → Prop
  | pure (value : α) : Canonical layout (FreeQuery.pure value)
  | query (n : ℕ) (next : Block × Block → CM α) (small : ((n : BaseField)).val = n)
      (onSite : ∀ site, siteOf (n / 2 ^ 128) = some site → site ∈ layout.sites ∧ n / 2 ^ 128 ∈ siteTags layout site)
      (rest : ∀ a, Canonical layout (next a)) :
      Canonical layout (FreeQuery.query n next)

/-- The points one query stores: the input itself off the sites, the site's whole point list on a site. -/
def pointsOf (layout : SiteLayout) (n : ℕ) : List BaseField :=
  match siteOf (n / 2 ^ 128) with
  | none => [(n : BaseField)]
  | some site => sitePoints layout site (n % 2 ^ 128)

/-- **The points of a table run**, along the path of the table's answers. -/
def runPoints (layout : SiteLayout) (T : TagTable) {α : Type} : CM α → List BaseField
  | .pure _ => []
  | .query n next => pointsOf layout n ++ runPoints layout T (next (H8.tagHash T n))

section Run

variable [DecidableEq FI] [DecidableEq EI]

/-- The state after one query of the table reader (deterministic on a consistent, closed state). -/
def stepState (layout : SiteLayout) (T : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI) : LazyOracle.State FI EI :=
  match siteOf (n / 2 ^ 128) with
  | none => if σ.hash.lookup (n : BaseField) = none then
      plantHash (n : BaseField) (T (tagPos (n / 2 ^ 128))) σ else σ
  | some site => if untouched (sitePoints layout site (n % 2 ^ 128)) σ then
      installPoints ((sitePoints layout site (n % 2 ^ 128)).zip (siteAnswersOf layout T site)) σ else σ

/-- **The final state of a table run.** -/
def tableFinal (layout : SiteLayout) (T : TagTable) {α : Type} :
    CM α → LazyOracle.State FI EI → LazyOracle.State FI EI
  | .pure _, σ => σ
  | .query n next, σ => tableFinal layout T (next (H8.tagHash T n)) (stepState layout T n σ)

theorem stepState_none (layout : SiteLayout) (T : TagTable) {n : ℕ} (σ : LazyOracle.State FI EI)
    (decode : siteOf (n / 2 ^ 128) = none) :
    stepState layout T n σ = if σ.hash.lookup (n : BaseField) = none then
      plantHash (n : BaseField) (T (tagPos (n / 2 ^ 128))) σ else σ := by
  unfold stepState
  rw [decode]

theorem stepState_site (layout : SiteLayout) (T : TagTable) {n : ℕ} (σ : LazyOracle.State FI EI) {site : SiteId}
    (decode : siteOf (n / 2 ^ 128) = some site) :
    stepState layout T n σ = if untouched (sitePoints layout site (n % 2 ^ 128)) σ then
      installPoints ((sitePoints layout site (n % 2 ^ 128)).zip (siteAnswersOf layout T site)) σ else σ := by
  unfold stepState
  rw [decode]

theorem pointsOf_none (layout : SiteLayout) {n : ℕ} (decode : siteOf (n / 2 ^ 128) = none) :
    pointsOf layout n = [(n : BaseField)] := by
  unfold pointsOf
  rw [decode]

theorem pointsOf_site (layout : SiteLayout) {n : ℕ} {site : SiteId} (decode : siteOf (n / 2 ^ 128) = some site) :
    pointsOf layout n = sitePoints layout site (n % 2 ^ 128) := by
  unfold pointsOf
  rw [decode]

/-- **One query of the table reader** on a consistent, closed state: `T`'s answer at the query's tag, and the next
state is consistent, closed, and stores the old inputs and the query's points. -/
theorem tableReader_step (layout : SiteLayout) (facts : PointFacts layout) (T : TagTable) (n : ℕ)
    (small : ((n : BaseField)).val = n)
    (onSite : ∀ site, siteOf (n / 2 ^ 128) = some site → site ∈ layout.sites ∧ n / 2 ^ 128 ∈ siteTags layout site)
    (σ : LazyOracle.State FI EI) (cons : TableConsistent T σ) (closed : SiteClosed layout σ) :
    tableReader layout T n σ = PMF.pure (H8.tagHash T n, stepState layout T n σ) ∧
      TableConsistent T (stepState layout T n σ) ∧ SiteClosed layout (stepState layout T n σ) ∧
      (stepState layout T n σ).fixed = σ.fixed ∧ (stepState layout T n σ).enc = σ.enc ∧
      ∀ x, ((stepState layout T n σ).hash.lookup x).isSome ↔ ((σ.hash.lookup x).isSome ∨ x ∈ pointsOf layout n) := by
  have answer : H8.tagHash T n = T (tagPos (n / 2 ^ 128)) := rfl
  cases decode : siteOf (n / 2 ^ 128) with
  | none =>
      rw [stepState_none layout T σ decode, pointsOf_none layout decode]
      by_cases missing : σ.hash.lookup (n : BaseField) = none
      · rw [if_pos missing, tableReader_fresh layout T n σ decode missing, answer]
        refine ⟨rfl, plant_consistent T cons _ _ (by rw [tagOfInput_small small]), ?_, rfl, rfl, fun x => ?_⟩
        · intro site member label smallLabel x hx stored y hy
          rw [plant_isSome] at stored ⊢
          rcases stored with stored | rfl
          · exact Or.inl (closed site member label smallLabel x hx stored y hy)
          · exact absurd hx (nonSite_not_mem facts small decode member smallLabel)
        · rw [plant_isSome, List.mem_singleton]
      · rw [if_neg missing]
        obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp missing
        rw [tableReader_stored layout T n σ v found (fun site hit => by rw [decode] at hit; cases hit),
          lazyReader_stored n σ v found, stored_value T cons found, tagOfInput_small small, answer]
        refine ⟨rfl, cons, closed, rfl, rfl, fun x => ⟨Or.inl, ?_⟩⟩
        rintro (stored | hit)
        · exact stored
        · rw [List.mem_singleton] at hit
          rw [hit, found]
          rfl
  | some site =>
      obtain ⟨member, tagHit⟩ := onSite site decode
      have smallLabel : n % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (Nat.two_pow_pos 128)
      have self := self_mem_sitePoints layout site n tagHit
      rw [stepState_site layout T σ decode, pointsOf_site layout decode]
      by_cases clean : untouched (sitePoints layout site (n % 2 ^ 128)) σ = true
      · rw [if_pos clean, tableReader_site layout T n σ site decode clean]
        have pairsEq : (sitePoints layout site (n % 2 ^ 128)).zip (siteAnswersOf layout T site) =
            (siteTags layout site).map fun tag =>
              (((n % 2 ^ 128 + 2 ^ 128 * tag : ℕ) : BaseField), T (tagPos tag)) :=
          zip_map_same _ _ _
        have agree : ∀ pair ∈ (sitePoints layout site (n % 2 ^ 128)).zip (siteAnswersOf layout T site),
            pair.2 = T (tagOfInput pair.1) := by
          rw [pairsEq]
          intro pair hit
          obtain ⟨tag, tagMem, rfl⟩ := List.mem_map.mp hit
          show T (tagPos tag) = T (tagOfInput _)
          congr 1
          refine Fin.ext ?_
          show tag % 2 ^ 40 = ((n % 2 ^ 128 + 2 ^ 128 * tag : ℕ) : BaseField).val / 2 ^ 128 % 2 ^ 40
          rw [point_val facts member smallLabel tagMem, point_div smallLabel]
        have firsts : ((sitePoints layout site (n % 2 ^ 128)).zip (siteAnswersOf layout T site)).map Prod.fst =
            sitePoints layout site (n % 2 ^ 128) := by
          rw [pairsEq, List.map_map]
          rfl
        obtain ⟨cons₂, fixed₂, enc₂, stored₂⟩ := installPoints_spec T _ agree σ cons
        rw [firsts] at stored₂
        obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp ((stored₂ (n : BaseField)).mpr (Or.inr self))
        rw [lazyReader_stored n _ v found, stored_value T cons₂ found, tagOfInput_small small, answer]
        refine ⟨rfl, cons₂, ?_, fixed₂, enc₂, stored₂⟩
        intro site' member' label' smallLabel' x hx stored y hy
        rw [stored₂] at stored ⊢
        rcases stored with stored | inSite
        · exact Or.inl (closed site' member' label' smallLabel' x hx stored y hy)
        · obtain ⟨rfl, rfl⟩ := sitePoints_disjoint facts member member' smallLabel smallLabel' inSite hx
          exact Or.inr hy
      · have dirty : untouched (sitePoints layout site (n % 2 ^ 128)) σ = false := by simpa using clean
        rw [if_neg clean, tableReader_touched layout T n σ site decode dirty]
        have allStored : ∀ y ∈ sitePoints layout site (n % 2 ^ 128), (σ.hash.lookup y).isSome := by
          unfold untouched at dirty
          obtain ⟨x, hx, notNone⟩ := List.all_eq_false.mp dirty
          rw [lookupHash_isNone] at notNone
          exact closed site member _ smallLabel x hx (by simpa using notNone)
        obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp (allStored _ self)
        rw [lazyReader_stored n σ v found, stored_value T cons found, tagOfInput_small small, answer]
        refine ⟨rfl, cons, closed, rfl, rfl, fun x => ⟨Or.inl, ?_⟩⟩
        rintro (stored | hit)
        · exact stored
        · exact allStored x hit

/-- **Step 3: the table run is deterministic.** On a canonical program, from a state consistent with `T` and closed
under sites, the table run answers every query by `T` at its tag; the final state is consistent, closed, and stores
exactly the old inputs and the run's points. -/
theorem tableRun_eq_pure (layout : SiteLayout) (facts : PointFacts layout) (T : TagTable) {α : Type} {R : CM α}
    (canon : Canonical layout R) :
    ∀ σ : LazyOracle.State FI EI, TableConsistent T σ → SiteClosed layout σ →
      runReader (tableReader layout T) R σ = PMF.pure (R.eval (H8.tagHash T), tableFinal layout T R σ) ∧
        TableConsistent T (tableFinal layout T R σ) ∧ SiteClosed layout (tableFinal layout T R σ) ∧
        (tableFinal layout T R σ).fixed = σ.fixed ∧ (tableFinal layout T R σ).enc = σ.enc ∧
        ∀ x, ((tableFinal layout T R σ).hash.lookup x).isSome ↔
          ((σ.hash.lookup x).isSome ∨ x ∈ runPoints layout T R) := by
  induction canon with
  | pure value =>
      intro σ cons closed
      exact ⟨rfl, cons, closed, rfl, rfl, fun x => by simp [runPoints, tableFinal]⟩
  | query n next small onSite rest ih =>
      intro σ cons closed
      obtain ⟨read, cons₁, closed₁, fixed₁, enc₁, stored₁⟩ :=
        tableReader_step layout facts T n small onSite σ cons closed
      obtain ⟨run, cons₂, closed₂, fixed₂, enc₂, stored₂⟩ := ih (H8.tagHash T n) _ cons₁ closed₁
      refine ⟨?_, cons₂, closed₂, fixed₂.trans fixed₁, enc₂.trans enc₁, fun x => ?_⟩
      · rw [runReader_query, read, PMF.pure_bind]
        exact run
      · show ((tableFinal layout T (next (H8.tagHash T n)) (stepState layout T n σ)).hash.lookup x).isSome ↔
          _ ∨ x ∈ pointsOf layout n ++ runPoints layout T (next (H8.tagHash T n))
        rw [stored₂ x, stored₁ x, List.mem_append]
        tauto

/-- **From the empty state**, the final state holds `T`'s answers exactly at the run's points. -/
theorem tableRun_empty (layout : SiteLayout) (facts : PointFacts layout) (T : TagTable) {α : Type} {R : CM α}
    (canon : Canonical layout R) :
    runReader (tableReader layout T) R (LazyOracle.empty : LazyOracle.State FI EI) =
        PMF.pure (R.eval (H8.tagHash T), tableFinal layout T R LazyOracle.empty) ∧
      SeenState tagOfInput LazyOracle.empty (runPoints layout T R) T
        (tableFinal layout T R (LazyOracle.empty : LazyOracle.State FI EI)) := by
  have emptyLookup : ∀ x, (LazyOracle.empty : LazyOracle.State FI EI).hash.lookup x = none := fun _ => rfl
  obtain ⟨run, cons, -, fixed, enc, stored⟩ := tableRun_eq_pure layout facts T canon LazyOracle.empty
    (fun x v hv => by rw [emptyLookup] at hv; cases hv)
    (fun site _ label _ x _ hx => by rw [emptyLookup] at hx; cases hx)
  refine ⟨run, fixed, enc, fun y => ?_⟩
  by_cases hit : y ∈ runPoints layout T R
  · rw [if_pos hit]
    obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp ((stored y).mpr (Or.inr hit))
    rw [found, cons y v found]
  · rw [if_neg hit, emptyLookup]
    have notStored : ¬ ((tableFinal layout T R (LazyOracle.empty : LazyOracle.State FI EI)).hash.lookup y).isSome :=
      fun h => by
        rcases (stored y).mp h with h | h
        · rw [emptyLookup] at h; cases h
        · exact hit h
    exact Option.not_isSome_iff_eq_none.mp notStored

end Run

/-! ### 4. `HW`'s replay -/

theorem replayProgram_eq [FieldCertificate] {Public : Type} (view : RouteMView Public) (published : Public)
    (u : AffineInput) (labels : LamportSignature) :
    replayProgram view published u labels = view.replayProgram published u labels := rfl

/-- **`HW`'s replay from the empty state draws a swapped table and returns the program's value on it**, with the
table's answers stored at the run's points. -/
theorem routeMReplay_pure [FieldCertificate] [DecidableEq FI] [DecidableEq EI] {Public : Type}
    (view : RouteMView Public) (layout : SiteLayout) (facts : RefillLayoutFacts layout) (points : PointFacts layout)
    (published : Public) (u : AffineInput) (labels : LamportSignature)
    (keyNonSite : ∀ conv, siteOf ((view.keyInput published u conv).val / 2 ^ 128) = none)
    (path : RefillPath layout ∅ (LazyOracle.empty : LazyOracle.State FI EI) (view.replayProgram published u labels))
    (canon : Canonical layout (view.replayProgram published u labels)) :
    routeMReplay view (refillReader layout) published u labels (LazyOracle.empty : LazyOracle.State FI EI) =
      (swappedTableLaw layout).bind fun T =>
        PMF.pure ((view.replayProgram published u labels).eval (H8.tagHash T),
          tableFinal layout T (view.replayProgram published u labels) LazyOracle.empty) := by
  rw [routeMReplay_table view layout facts published u labels keyNonSite _ path]
  exact congrArg _ (funext fun T => (tableRun_empty layout points T canon).1)

/-! ### 5. The real layout -/

open RefillLayout Kriterion.CRT.Privacy.Layout in
/-- **The real layout satisfies the point facts.** -/
theorem crtLayout_points : PointFacts crtLayout where
  decode := by
    intro site member tag hit
    obtain ⟨fam, inRange⟩ := fields_inRange member
    rw [siteTags_eq] at hit
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hit
    rw [List.mem_range] at hj
    have h := inRange j hj
    unfold siteOf
    rw [tagFamily_tagCode h]
    rcases List.mem_append.mp member with pad | mask
    · obtain ⟨κ, i, ρ, rfl, -⟩ := mem_padSites pad
      simp only [siteFields, Family.body] at h ⊢
      rw [tagCoord_tagCode h, tagIdx_tagCode h, tagSlot_tagCode h]
    · rcases mem_maskSites mask with ⟨k, rfl, -⟩ | ⟨k, rfl, -⟩ <;>
      · simp only [siteFields, Family.mask] at h ⊢
        rw [tagStage_tagCode h, tagSlot_tagCode h]
  bound := by
    intro site member tag hit
    obtain ⟨fam, inRange⟩ := fields_inRange member
    rw [siteTags_eq] at hit
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hit
    rw [List.mem_range] at hj
    have value := tagPos_tagCode fam (inRange j hj)
    have lt := (tagPos (tagCode (siteFields site).1 (siteFields site).2.1 (siteFields site).2.2.1
      (siteFields site).2.2.2.1 0 (siteFields site).2.2.2.2 j)).isLt
    rw [value] at lt
    exact lt

end

end Kriterion.CRT.Privacy.Laws
