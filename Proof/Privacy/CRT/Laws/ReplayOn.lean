/-
**P6b1: `HW`'s replay reads a swapped table**.

`HW` (and `H`) run the evaluator's replay on the shared lazy oracle through the refill reader: the first query at a pad
or mask site whose points are all untouched draws the whole site from its swapped law and installs it, and every other
query is answered lazily. This file shows that such a run is a run on a table drawn up front from `G0U`'s swapped table
law, read deterministically by coordinate (`runReader_refill_table`):

* `Ignores P G`: `G` reads a table only outside the positions `P`; `Indep μ P ν read ok`: under the table law `μ`, the
  values `read T` at the positions `P` have the law `ν` and are independent of the rest;
* `indep_uniform` (one position of a uniform table), `indep_site` (a site right after its swap step), `indep_step`
  (a swap step at other positions keeps the independence), hence `indep_swapped_pos` (a non-site position of the
  swapped table is uniform and independent) and `indep_swapped_site` (a site of the swapped table has its law and is
  independent) under `RefillLayoutFacts` (sites distinct, each site's positions distinct, distinct sites disjoint, the
  site laws' answer counts);
* `RefillLike layout rd`: the three defining equations of `Sites.refillReader`, so the law holds for the
  merged reader by unfolding;
* `tableReader layout T`: the same reader with every fresh non-site answer read from `T` at its tag and every site
  read from `T` at its tags; `RefillPath`: the path conditions (a stored input is answered from the state; a fresh
  non-site input reads an unread non-site position; a site is read at one label while all its points are untouched,
  at unread positions); `tableRun_congr`: a table run reads the table only at the positions it reads freshly;
* `runReader_refill_table`: along a refill path, the refill run is the table run on a swapped table.
-/

import Proof.Privacy.CRT.Laws.Plant
import Proof.Privacy.CRT.Swap.Hop

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (uniform_equiv)

noncomputable section

variable {FI EI : Type}

/-! ### 1. Independence of table positions -/

/-- `G` reads a table only outside the positions `P`. -/
def Ignores {X : Type} (P : Set (Fin (2 ^ 40))) (G : TagTable → X) : Prop :=
  ∀ T T' : TagTable, (∀ p, p ∉ P → T p = T' p) → G T = G T'

/-- Under the table law `μ`, the values `read T` at the positions `P` have the law `ν` and are independent of the
table outside `P` (for the values `ok` holds on, which carry `ν`). -/
def Indep {V : Type} (μ : PMF TagTable) (P : Set (Fin (2 ^ 40))) (ν : PMF V) (read : TagTable → V)
    (ok : V → Prop) : Prop :=
  ∀ (β : Type) (G : V → TagTable → PMF β), (∀ v, ok v → Ignores P (G v)) →
    μ.bind (fun T => G (read T) T) = ν.bind fun v => μ.bind (G v)

/-- The positions of a site's tags. -/
def sitePos (layout : SiteLayout) (site : SiteId) : Set (Fin (2 ^ 40)) :=
  {p | p ∈ (siteTags layout site).map tagPos}

/-- A site's answers as a table holds them. -/
def siteAnswersOf (layout : SiteLayout) (T : TagTable) (site : SiteId) : List (Block × Block) :=
  (siteTags layout site).map fun tag => T (tagPos tag)

/-- One swap step of `swappedTableLaw`. -/
def swapStep (layout : SiteLayout) (μ : PMF TagTable) (site : SiteId) : PMF TagTable :=
  μ.bind fun table => (layout.law site).map fun answers => overwrite table (siteTags layout site) answers

theorem swappedTableLaw_eq (layout : SiteLayout) :
    swappedTableLaw layout = layout.sites.foldl (swapStep layout) (PMF.uniformOfFintype TagTable) := rfl

theorem overwrite_congr_at : ∀ (tags : List ℕ) (answers : List (Block × Block)) (T T' : TagTable)
    (p : Fin (2 ^ 40)), T p = T' p → overwrite T tags answers p = overwrite T' tags answers p
  | [], _, _, _, _, same => by simpa [overwrite] using same
  | _ :: _, [], _, _, _, same => by simpa [overwrite] using same
  | tag :: tags, a :: answers, T, T', p, same => by
      rw [Swap.overwrite_cons, Swap.overwrite_cons]
      refine overwrite_congr_at tags answers _ _ p ?_
      by_cases at_p : p = tagPos tag
      · subst at_p
        simp
      · rw [Function.update_of_ne at_p, Function.update_of_ne at_p]
        exact same

/-- A uniform table: one position is uniform and independent of the rest. -/
theorem indep_uniform (pos : Fin (2 ^ 40)) :
    Indep (PMF.uniformOfFintype TagTable) {pos} (PMF.uniformOfFintype (Block × Block)) (fun T => T pos)
      (fun _ => True) := by
  intro β G ignores
  have ignoresUpdate : ∀ a T, G a (Function.update T pos a) = G a T := fun a T =>
    ignores a trivial _ _ fun p off => by
      rw [Function.update_of_ne (fun same => off (by simp [same]))]
  have law := uniform_update_bind pos G ignoresUpdate
  calc (PMF.uniformOfFintype TagTable).bind (fun T => G (T pos) T)
      = ((PMF.uniformOfFintype TagTable).map fun T => G (T pos) T).bind id := by rw [PMF.bind_map]; rfl
    _ = ((PMF.uniformOfFintype (Block × Block)).bind fun a => (PMF.uniformOfFintype TagTable).map (G a)).bind id := by
        rw [law]
    _ = (PMF.uniformOfFintype (Block × Block)).bind fun a => (PMF.uniformOfFintype TagTable).bind (G a) := by
        rw [PMF.bind_bind]
        refine congrArg _ (funext fun a => ?_)
        rw [PMF.bind_map]
        rfl

/-- **A site right after its swap step** has the site's law and is independent of the rest. -/
theorem indep_site (layout : SiteLayout) (μ : PMF TagTable) (site : SiteId)
    (nodup : ((siteTags layout site).map tagPos).Nodup)
    (lengths : ∀ answers ∈ (layout.law site).support, answers.length = layout.answers site) :
    Indep (swapStep layout μ site) (sitePos layout site) (layout.law site) (fun T => siteAnswersOf layout T site)
      (fun answers => answers ∈ (layout.law site).support) := by
  intro β G ignores
  have readBack : ∀ T, ∀ answers ∈ (layout.law site).support,
      siteAnswersOf layout (overwrite T (siteTags layout site) answers) site = answers := by
    intro T answers member
    have length := lengths answers member
    refine List.ext_getElem (by simp [siteAnswersOf, siteTags_length, length]) fun j hj hj' => ?_
    have jTags : j < (siteTags layout site).length := by simpa [siteAnswersOf] using hj
    simp only [siteAnswersOf, List.getElem_map]
    exact Swap.overwrite_apply_mem _ _ T nodup j jTags (by rw [length, ← siteTags_length]; exact jTags)
  unfold swapStep
  rw [PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  calc μ.bind (fun T => (layout.law site).bind fun answers =>
        G (siteAnswersOf layout (overwrite T (siteTags layout site) answers) site)
          (overwrite T (siteTags layout site) answers))
      = μ.bind (fun T => (layout.law site).bind fun answers =>
          G answers (overwrite T (siteTags layout site) answers)) := by
        refine congrArg _ (funext fun T => ?_)
        exact PMF.bind_congr _ _ _ fun answers member => by rw [readBack T answers member]
    _ = (layout.law site).bind fun answers => μ.bind fun T => G answers (overwrite T (siteTags layout site) answers) :=
        PMF.bind_comm _ _ _
    _ = (layout.law site).bind fun answers => μ.bind fun T => (layout.law site).bind fun other =>
          G answers (overwrite T (siteTags layout site) other) := by
        refine PMF.bind_congr _ _ _ fun answers member => congrArg _ (funext fun T => ?_)
        have same : ∀ other, G answers (overwrite T (siteTags layout site) other) =
            G answers (overwrite T (siteTags layout site) answers) := fun other =>
          ignores answers member _ _ fun p off => by
            rw [Swap.overwrite_apply_of_not_mem _ _ _ p off, Swap.overwrite_apply_of_not_mem _ _ _ p off]
        simp only [same, PMF.bind_const]
    _ = (layout.law site).bind fun answers => (μ.bind fun table =>
          (layout.law site).map fun other => overwrite table (siteTags layout site) other).bind (G answers) := by
        refine congrArg _ (funext fun answers => ?_)
        rw [PMF.bind_bind]
        simp only [PMF.bind_map, Function.comp_def]

/-- **A swap step at other positions keeps the independence.** -/
theorem indep_step {V : Type} (layout : SiteLayout) (μ : PMF TagTable) (P : Set (Fin (2 ^ 40))) (ν : PMF V)
    (read : TagTable → V) (ok : V → Prop) (indep : Indep μ P ν read ok)
    (readCongr : ∀ T T' : TagTable, (∀ p ∈ P, T p = T' p) → read T = read T') (site : SiteId)
    (apart : ∀ p ∈ P, p ∉ (siteTags layout site).map tagPos) :
    Indep (swapStep layout μ site) P ν read ok := by
  intro β G ignores
  have readSame : ∀ T answers, read (overwrite T (siteTags layout site) answers) = read T := fun T answers =>
    readCongr _ _ fun p hp => Swap.overwrite_apply_of_not_mem _ _ _ p (apart p hp)
  let G' : V → TagTable → PMF β := fun v T =>
    (layout.law site).bind fun answers => G v (overwrite T (siteTags layout site) answers)
  have ignores' : ∀ v, ok v → Ignores P (G' v) := fun v hv T T' agree =>
    congrArg (PMF.bind (layout.law site)) (funext fun answers => ignores v hv _ _ fun p off =>
      overwrite_congr_at _ _ _ _ p (agree p off))
  unfold swapStep
  rw [PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, readSame]
  rw [indep β G' ignores']
  refine congrArg _ (funext fun v => ?_)
  rw [PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  rfl

/-- **The facts of a site layout that the refill law needs.** -/
structure RefillLayoutFacts (layout : SiteLayout) : Prop where
  sitesNodup : layout.sites.Nodup
  posNodup : ∀ site ∈ layout.sites, ((siteTags layout site).map tagPos).Nodup
  disjoint : ∀ site ∈ layout.sites, ∀ site' ∈ layout.sites, site ≠ site' →
    ∀ p ∈ (siteTags layout site).map tagPos, p ∉ (siteTags layout site').map tagPos
  lengths : ∀ site ∈ layout.sites, ∀ answers ∈ (layout.law site).support, answers.length = layout.answers site

theorem indep_foldl {V : Type} (layout : SiteLayout) (P : Set (Fin (2 ^ 40))) (ν : PMF V) (read : TagTable → V)
    (ok : V → Prop) (readCongr : ∀ T T' : TagTable, (∀ p ∈ P, T p = T' p) → read T = read T') :
    ∀ (sites : List SiteId) (μ : PMF TagTable), Indep μ P ν read ok →
      (∀ site ∈ sites, ∀ p ∈ P, p ∉ (siteTags layout site).map tagPos) →
      Indep (sites.foldl (swapStep layout) μ) P ν read ok
  | [], _, indep, _ => indep
  | site :: sites, μ, indep, apart => by
      rw [List.foldl_cons]
      exact indep_foldl layout P ν read ok readCongr sites _
        (indep_step layout μ P ν read ok indep readCongr site (apart site List.mem_cons_self))
        fun site' member => apart site' (List.mem_cons_of_mem _ member)

/-- **A position outside every site of the swapped table is uniform and independent of the rest.** -/
theorem indep_swapped_pos (layout : SiteLayout) (pos : Fin (2 ^ 40))
    (away : ∀ site ∈ layout.sites, pos ∉ (siteTags layout site).map tagPos) :
    Indep (swappedTableLaw layout) {pos} (PMF.uniformOfFintype (Block × Block)) (fun T => T pos)
      (fun _ => True) := by
  rw [swappedTableLaw_eq]
  refine indep_foldl layout {pos} _ _ _ (fun T T' agree => agree pos rfl) _ _ (indep_uniform pos) ?_
  intro site member p hp
  rw [Set.mem_singleton_iff] at hp
  subst hp
  exact away site member

/-- **A site of the swapped table has its law and is independent of the rest.** -/
theorem indep_swapped_site (layout : SiteLayout) (facts : RefillLayoutFacts layout) (site : SiteId)
    (member : site ∈ layout.sites) :
    Indep (swappedTableLaw layout) (sitePos layout site) (layout.law site) (fun T => siteAnswersOf layout T site)
      (fun answers => answers ∈ (layout.law site).support) := by
  obtain ⟨pre, post, split⟩ := List.append_of_mem member
  have nodup := facts.sitesNodup
  rw [split] at nodup
  have notPost : site ∉ post := (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
  rw [swappedTableLaw_eq, split, List.foldl_append, List.foldl_cons]
  refine indep_foldl layout _ _ _ _ ?_ post _
    (indep_site layout _ site (facts.posNodup site member) (facts.lengths site member)) ?_
  · intro T T' agree
    exact List.map_congr_left fun tag hit => agree _ (List.mem_map_of_mem hit)
  · intro site' member' p hp
    have inSites : site' ∈ layout.sites := by
      rw [split]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ member')
    exact facts.disjoint site member site' inSites (fun same => notPost (same ▸ member')) p hp

/-! ### 2. The refill reader and the table reader -/

theorem runReader_query (rd : Reader FI EI) {α : Type} (n : ℕ) (next : Block × Block → CM α)
    (σ : LazyOracle.State FI EI) :
    runReader rd (FreeQuery.query n next) σ = (rd n σ).bind fun answered => runReader rd (next answered.1) answered.2 :=
  rfl

section Readers

variable [DecidableEq FI] [DecidableEq EI]

/-- **The three defining equations of the refill reader**: a non-site
input is read lazily; the first query at a site whose points are all untouched draws the site from its law, installs
it, and reads lazily; a query at a touched site is read lazily. -/
structure RefillLike (layout : SiteLayout) (rd : Reader FI EI) : Prop where
  nonSite : ∀ n σ, siteOf (n / 2 ^ 128) = none → rd n σ = lazyReader n σ
  fresh : ∀ n σ site, siteOf (n / 2 ^ 128) = some site →
    untouched (sitePoints layout site (n % 2 ^ 128)) σ = true →
    rd n σ = (layout.law site).bind fun answers =>
      lazyReader n (installPoints ((sitePoints layout site (n % 2 ^ 128)).zip answers) σ)
  touched : ∀ n σ site, siteOf (n / 2 ^ 128) = some site →
    untouched (sitePoints layout site (n % 2 ^ 128)) σ = false → rd n σ = lazyReader n σ

/-- A non-site read of a table: a stored input from the state, a fresh one from the table at its tag (and stored). -/
def tableRead (T : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI) :
    PMF ((Block × Block) × LazyOracle.State FI EI) :=
  if σ.hash.lookup (n : BaseField) = none then
    PMF.pure (T (tagPos (n / 2 ^ 128)), plantHash (n : BaseField) (T (tagPos (n / 2 ^ 128))) σ)
  else lazyReader n σ

/-- **The table reader**: the refill reader with every fresh non-site answer and every refilled site read from the
table `T` at its tags. -/
def tableReader (layout : SiteLayout) (T : TagTable) : Reader FI EI := fun n σ =>
  match siteOf (n / 2 ^ 128) with
  | none => tableRead T n σ
  | some site =>
    if untouched (sitePoints layout site (n % 2 ^ 128)) σ then
      lazyReader n (installPoints ((sitePoints layout site (n % 2 ^ 128)).zip (siteAnswersOf layout T site)) σ)
    else lazyReader n σ

theorem lazyReader_stored (n : ℕ) (σ : LazyOracle.State FI EI) (v : Fin (Fintype.card (Block × Block)))
    (found : σ.hash.lookup (n : BaseField) = some v) : lazyReader n σ = PMF.pure (hashValue v, σ) :=
  query_hash_stored σ _ v found

theorem lazyReader_fresh (n : ℕ) (σ : LazyOracle.State FI EI) (missing : σ.hash.lookup (n : BaseField) = none) :
    lazyReader n σ = (PMF.uniformOfFintype (Block × Block)).map fun b => (b, plantHash (n : BaseField) b σ) :=
  query_hash_fresh σ _ missing

/-- **The path conditions of a refill run**, relative to the table positions `read` already read: a stored input
is answered from the state (and, if its tag decodes to a site, that site is touched); a fresh non-site input reads
an unread position outside every site; a site is read at one label while all its points are untouched, at unread
positions, and the run continues from each installed state; a query at a site already touched (by stage 1, F4) is
answered lazily on both sides and reads no table position. -/
inductive RefillPath (layout : SiteLayout) {α : Type} :
    Set (Fin (2 ^ 40)) → LazyOracle.State FI EI → CM α → Prop
  | pure (read : Set (Fin (2 ^ 40))) (σ : LazyOracle.State FI EI) (value : α) :
      RefillPath layout read σ (FreeQuery.pure value)
  | stored (read : Set (Fin (2 ^ 40))) (σ : LazyOracle.State FI EI) (n : ℕ) (next : Block × Block → CM α)
      (v : Fin (Fintype.card (Block × Block))) (found : σ.hash.lookup (n : BaseField) = some v)
      (onSite : ∀ site, siteOf (n / 2 ^ 128) = some site →
        untouched (sitePoints layout site (n % 2 ^ 128)) σ = false)
      (rest : RefillPath layout read σ (next (hashValue v))) :
      RefillPath layout read σ (FreeQuery.query n next)
  | fresh (read : Set (Fin (2 ^ 40))) (σ : LazyOracle.State FI EI) (n : ℕ) (next : Block × Block → CM α)
      (notSite : siteOf (n / 2 ^ 128) = none) (missing : σ.hash.lookup (n : BaseField) = none)
      (unread : tagPos (n / 2 ^ 128) ∉ read)
      (away : ∀ site ∈ layout.sites, tagPos (n / 2 ^ 128) ∉ (siteTags layout site).map tagPos)
      (rest : ∀ a, RefillPath layout (insert (tagPos (n / 2 ^ 128)) read) (plantHash (n : BaseField) a σ) (next a)) :
      RefillPath layout read σ (FreeQuery.query n next)
  | site (read : Set (Fin (2 ^ 40))) (σ : LazyOracle.State FI EI) (n : ℕ) (next : Block × Block → CM α)
      (site : SiteId) (decode : siteOf (n / 2 ^ 128) = some site) (member : site ∈ layout.sites)
      (clean : untouched (sitePoints layout site (n % 2 ^ 128)) σ = true)
      (unread : ∀ p ∈ (siteTags layout site).map tagPos, p ∉ read)
      (rest : ∀ answers : List (Block × Block), answers.length = layout.answers site →
        ∀ b ∈ (lazyReader n (installPoints ((sitePoints layout site (n % 2 ^ 128)).zip answers) σ)).support,
          RefillPath layout (read ∪ sitePos layout site) b.2 (next b.1)) :
      RefillPath layout read σ (FreeQuery.query n next)
  | touched (read : Set (Fin (2 ^ 40))) (σ : LazyOracle.State FI EI) (n : ℕ) (next : Block × Block → CM α)
      (site : SiteId) (decode : siteOf (n / 2 ^ 128) = some site)
      (dirty : untouched (sitePoints layout site (n % 2 ^ 128)) σ = false)
      (rest : ∀ b ∈ (lazyReader n σ).support, RefillPath layout read b.2 (next b.1)) :
      RefillPath layout read σ (FreeQuery.query n next)

theorem tableReader_stored (layout : SiteLayout) (T : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI)
    (v : Fin (Fintype.card (Block × Block))) (found : σ.hash.lookup (n : BaseField) = some v)
    (onSite : ∀ site, siteOf (n / 2 ^ 128) = some site →
      untouched (sitePoints layout site (n % 2 ^ 128)) σ = false) :
    tableReader layout T n σ = lazyReader n σ := by
  unfold tableReader
  cases decode : siteOf (n / 2 ^ 128) with
  | none =>
      show tableRead T n σ = _
      unfold tableRead
      rw [if_neg (by rw [found]; exact Option.some_ne_none v)]
  | some site =>
      show (if untouched (sitePoints layout site (n % 2 ^ 128)) σ then _ else _) = _
      rw [onSite site decode]
      rfl

theorem refill_stored (layout : SiteLayout) {rd : Reader FI EI} (like : RefillLike layout rd) (n : ℕ)
    (σ : LazyOracle.State FI EI)
    (onSite : ∀ site, siteOf (n / 2 ^ 128) = some site →
      untouched (sitePoints layout site (n % 2 ^ 128)) σ = false) :
    rd n σ = lazyReader n σ := by
  cases decode : siteOf (n / 2 ^ 128) with
  | none => exact like.nonSite n σ decode
  | some site => exact like.touched n σ site decode (onSite site decode)

theorem tableReader_fresh (layout : SiteLayout) (T : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI)
    (notSite : siteOf (n / 2 ^ 128) = none) (missing : σ.hash.lookup (n : BaseField) = none) :
    tableReader layout T n σ =
      PMF.pure (T (tagPos (n / 2 ^ 128)), plantHash (n : BaseField) (T (tagPos (n / 2 ^ 128))) σ) := by
  unfold tableReader
  rw [notSite]
  show tableRead T n σ = _
  unfold tableRead
  rw [if_pos missing]

theorem tableReader_site (layout : SiteLayout) (T : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI)
    (site : SiteId) (decode : siteOf (n / 2 ^ 128) = some site)
    (clean : untouched (sitePoints layout site (n % 2 ^ 128)) σ = true) :
    tableReader layout T n σ =
      lazyReader n (installPoints ((sitePoints layout site (n % 2 ^ 128)).zip (siteAnswersOf layout T site)) σ) := by
  unfold tableReader
  rw [decode]
  show (if untouched (sitePoints layout site (n % 2 ^ 128)) σ then _ else _) = _
  rw [if_pos clean]

theorem tableReader_touched (layout : SiteLayout) (T : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI)
    (site : SiteId) (decode : siteOf (n / 2 ^ 128) = some site)
    (dirty : untouched (sitePoints layout site (n % 2 ^ 128)) σ = false) :
    tableReader layout T n σ = lazyReader n σ := by
  unfold tableReader
  rw [decode]
  show (if untouched (sitePoints layout site (n % 2 ^ 128)) σ then _ else _) = _
  rw [dirty]
  rfl

/-- **A table run reads the table only at the positions it reads freshly.** -/
theorem tableRun_congr (layout : SiteLayout) {α : Type} {read : Set (Fin (2 ^ 40))} {σ : LazyOracle.State FI EI}
    {R : CM α} (path : RefillPath layout read σ R) :
    ∀ T T' : TagTable, (∀ p, p ∉ read → T p = T' p) →
      runReader (tableReader layout T) R σ = runReader (tableReader layout T') R σ := by
  induction path with
  | pure read σ value => intro T T' _; rfl
  | stored read σ n next v found onSite rest ih =>
      intro T T' agree
      rw [runReader_query, runReader_query, tableReader_stored layout T n σ v found onSite,
        tableReader_stored layout T' n σ v found onSite, lazyReader_stored n σ v found, PMF.pure_bind,
        PMF.pure_bind]
      exact ih T T' agree
  | fresh read σ n next notSite missing unread away rest ih =>
      intro T T' agree
      rw [runReader_query, runReader_query, tableReader_fresh layout T n σ notSite missing,
        tableReader_fresh layout T' n σ notSite missing, PMF.pure_bind, PMF.pure_bind,
        agree _ unread]
      exact ih _ T T' fun p off => agree p fun inRead => off (Set.mem_insert_of_mem _ inRead)
  | site read σ n next site decode member clean unread rest ih =>
      intro T T' agree
      have same : siteAnswersOf layout T site = siteAnswersOf layout T' site :=
        List.map_congr_left fun tag hit => agree _ (unread _ (List.mem_map_of_mem hit))
      rw [runReader_query, runReader_query, tableReader_site layout T n σ site decode clean,
        tableReader_site layout T' n σ site decode clean, same]
      refine PMF.bind_congr _ _ _ fun b hb => ih _ (by simp [siteAnswersOf, siteTags_length]) b hb T T' ?_
      intro p off
      exact agree p fun inRead => off (Or.inl inRead)
  | touched read σ n next site decode dirty rest ih =>
      intro T T' agree
      rw [runReader_query, runReader_query, tableReader_touched layout T n σ site decode dirty,
        tableReader_touched layout T' n σ site decode dirty]
      exact PMF.bind_congr _ _ _ fun b hb => ih b hb T T' agree

/-- **Along a refill path, the refill run is the table run on a swapped table.** -/
theorem runReader_refill_table (layout : SiteLayout) (facts : RefillLayoutFacts layout) {rd : Reader FI EI}
    (like : RefillLike layout rd) {α : Type} {read : Set (Fin (2 ^ 40))} {σ : LazyOracle.State FI EI} {R : CM α}
    (path : RefillPath layout read σ R) :
    runReader rd R σ = (swappedTableLaw layout).bind fun T => runReader (tableReader layout T) R σ := by
  induction path with
  | pure read σ value =>
      show PMF.pure (value, σ) = (swappedTableLaw layout).bind fun _ => PMF.pure (value, σ)
      rw [PMF.bind_const]
  | stored read σ n next v found onSite rest ih =>
      rw [runReader_query, refill_stored layout like n σ onSite, lazyReader_stored n σ v found, PMF.pure_bind, ih]
      refine congrArg _ (funext fun T => ?_)
      rw [runReader_query, tableReader_stored layout T n σ v found onSite, lazyReader_stored n σ v found,
        PMF.pure_bind]
  | fresh read σ n next notSite missing unread away rest ih =>
      rw [runReader_query, like.nonSite n σ notSite, lazyReader_fresh n σ missing, PMF.bind_map]
      simp only [Function.comp_def]
      simp only [ih]
      have law := indep_swapped_pos layout (tagPos (n / 2 ^ 128)) away _
        (fun a T => runReader (tableReader layout T) (next a) (plantHash (n : BaseField) a σ))
        fun a _ T T' agree => tableRun_congr layout (rest a) T T' fun p off => agree p fun hit => off (by
          rw [Set.mem_singleton_iff] at hit
          rw [hit]
          exact Set.mem_insert _ _)
      rw [← law]
      refine congrArg _ (funext fun T => ?_)
      rw [runReader_query, tableReader_fresh layout T n σ notSite missing, PMF.pure_bind]
  | site read σ n next site decode member clean unread rest ih =>
      rw [runReader_query, like.fresh n σ site decode clean, PMF.bind_bind]
      have step : ∀ answers ∈ (layout.law site).support,
          (lazyReader n (installPoints ((sitePoints layout site (n % 2 ^ 128)).zip answers) σ)).bind
              (fun b => runReader rd (next b.1) b.2) =
            (swappedTableLaw layout).bind fun T =>
              (lazyReader n (installPoints ((sitePoints layout site (n % 2 ^ 128)).zip answers) σ)).bind
                fun b => runReader (tableReader layout T) (next b.1) b.2 := by
        intro answers support
        rw [PMF.bind_comm]
        refine PMF.bind_congr _ _ _ fun b hb => ?_
        exact ih answers (facts.lengths site member answers support) b hb
      rw [PMF.bind_congr _ _ _ step]
      have law := indep_swapped_site layout facts site member _
        (fun answers T => (lazyReader n (installPoints ((sitePoints layout site (n % 2 ^ 128)).zip answers) σ)).bind
          fun b => runReader (tableReader layout T) (next b.1) b.2)
        fun answers support T T' agree => PMF.bind_congr _ _ _ fun b hb =>
          tableRun_congr layout (rest answers (facts.lengths site member answers support) b hb) T T'
            fun p off => agree p fun hit => off (Or.inr hit)
      rw [← law]
      refine congrArg _ (funext fun T => ?_)
      rw [runReader_query, tableReader_site layout T n σ site decode clean]
  | touched read σ n next site decode dirty rest ih =>
      rw [runReader_query, like.touched n σ site decode dirty]
      rw [PMF.bind_congr _ _ _ fun b hb => ih b hb, PMF.bind_comm]
      refine congrArg _ (funext fun T => ?_)
      rw [runReader_query, tableReader_touched layout T n σ site decode dirty]

end Readers

end

end Kriterion.CRT.Privacy.Laws
