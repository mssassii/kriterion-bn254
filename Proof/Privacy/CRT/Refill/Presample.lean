/-
**P10, step 1: what a lazy state shows, and the fill of pending points** (row H10, `crt_refill_of_layout`).

The refill hop `H → I` compares two runs of the stage-2 replay on the shared lazy oracle: `H` refills an untouched
site as a unit, `I` answers every point lazily. The lazy oracle's state is a list, but every operation depends on it
only through its lookups, so the runs are compared through the **view** of a state: its permutation parts and its
hash lookups (`view`). A hash query factors through the view (`query_hash_view`).
-/

import Proof.Privacy.CRT.Hybrids
import Proof.Privacy.PGS.DaviesMeyerUniform
import Proof.Privacy.Phase3.Basic

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Refill

open BN254 Cryptography Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- The library's (private) coding of hash answers, `Fintype.equivFin`. -/
abbrev hashCode : (Block × Block) ≃ Fin (Fintype.card (Block × Block)) := Fintype.equivFin _

theorem lookup_hash_eq (σ : LazyOracle.State FI EI) (x : BaseField) :
    LazyOracle.lookup (.hash x) σ = (σ.hash.lookup x).map hashCode.symm := rfl

/-- A hash query, typed with its answer type unfolded (as the readers use it). -/
def hashQuery (σ : LazyOracle.State FI EI) (x : BaseField) : PMF ((Block × Block) × LazyOracle.State FI EI) :=
  LazyOracle.query (.hash x) σ

theorem hashQuery_eq (σ : LazyOracle.State FI EI) (x : BaseField) :
    hashQuery σ x = (σ.hash.query Fintype.card_pos x).distribution.map
      (fun a => (hashCode.symm a.1, { σ with hash := a.2 })) := rfl

theorem lazyReader_eq (input : ℕ) (σ : LazyOracle.State FI EI) :
    lazyReader input σ = hashQuery σ (input : BaseField) := rfl

/-! ### Views -/

/-- The hash lookups of a state. -/
def hashView (σ : LazyOracle.State FI EI) : BaseField → Option (Block × Block) :=
  fun x => (σ.hash.lookup x).map hashCode.symm

theorem hashView_eq (σ : LazyOracle.State FI EI) (x : BaseField) :
    hashView σ x = LazyOracle.lookup (.hash x) σ := rfl

/-- What the runs depend on: the permutation parts and the hash lookups. -/
abbrev View (FI EI : Type) :=
  (FI → SparsePermutation (2 ^ 128)) × (EI → SparsePermutation (2 ^ 128)) × (BaseField → Option (Block × Block))

/-- The view of a state. -/
def view (σ : LazyOracle.State FI EI) : View FI EI := (σ.fixed, σ.enc, hashView σ)

theorem hashView_eq_none (σ : LazyOracle.State FI EI) (x : BaseField) :
    hashView σ x = none ↔ σ.hash.lookup x = none := by
  unfold hashView
  cases σ.hash.lookup x <;> simp

/-- The view after storing a fresh hash answer. -/
theorem hashView_cons (σ : LazyOracle.State FI EI) (x : BaseField) (u : Fin (Fintype.card (Block × Block))) :
    hashView { σ with hash := (x, u) :: σ.hash } = Function.update (hashView σ) x (some (hashCode.symm u)) := by
  funext y
  unfold hashView
  by_cases same : y = x
  · subst same
    simp [List.lookup]
  · have ne : (y == x) = false := by simp [same]
    simp [List.lookup, ne, same]

/-- **A hash query through the view**: a known point returns its value and keeps the view; a fresh point returns a
uniform value, which the view then stores. -/
theorem query_hash_view (σ : LazyOracle.State FI EI) (x : BaseField) :
    (hashQuery σ x).map (fun a => (a.1, view a.2)) =
      match hashView σ x with
      | some w => PMF.pure (w, view σ)
      | none => (PMF.uniformOfFintype (Block × Block)).map fun w =>
          (w, (σ.fixed, σ.enc, Function.update (hashView σ) x (some w))) := by
  rw [hashQuery_eq]
  cases found : σ.hash.lookup x with
  | some u =>
      have seen : hashView σ x = some (hashCode.symm u) := by simp [hashView, found]
      rw [seen]
      simp only [HashTable.query, found, Draw.distribution, PMF.pure_map]
  | none =>
      have fresh : hashView σ x = none := (hashView_eq_none σ x).mpr found
      rw [fresh]
      simp only [HashTable.query, found, Draw.distribution, PMF.map_comp]
      rw [← uniformOfFintype_map_equiv hashCode.symm, PMF.map_comp]
      congr 1
      funext u
      simp only [Function.comp, view, hashView_cons]

/-! ### Every public query through the view -/

/-- The view-level semantics of a public query. -/
def queryView : (request : PublicQuery FI EI) → View FI EI → PMF (request.Answer × View FI EI)
  | .fixedForward index input, w => ((w.1 index).forward input.toFin).distribution.map
      fun a => (BitVec.ofFin a.1, (Function.update w.1 index a.2, w.2.1, w.2.2))
  | .fixedInverse index output, w => ((w.1 index).inverse output.toFin).distribution.map
      fun a => (BitVec.ofFin a.1, (Function.update w.1 index a.2, w.2.1, w.2.2))
  | .encForward index input, w => ((w.2.1 index).forward input.toFin).distribution.map
      fun a => (BitVec.ofFin a.1, (w.1, Function.update w.2.1 index a.2, w.2.2))
  | .encInverse index output, w => ((w.2.1 index).inverse output.toFin).distribution.map
      fun a => (BitVec.ofFin a.1, (w.1, Function.update w.2.1 index a.2, w.2.2))
  | .hash x, w => hashQueryView w x
where
  /-- A hash query on a view. -/
  hashQueryView (w : View FI EI) (x : BaseField) : PMF ((Block × Block) × View FI EI) :=
    match w.2.2 x with
    | some v => PMF.pure (v, w)
    | none => (PMF.uniformOfFintype (Block × Block)).map fun v => (v, (w.1, w.2.1, Function.update w.2.2 x (some v)))

theorem hashQuery_view (σ : LazyOracle.State FI EI) (x : BaseField) :
    (hashQuery σ x).map (fun a => (a.1, view a.2)) = queryView.hashQueryView (view σ) x := by
  rw [query_hash_view]
  rfl

/-- **Every public query factors through the view.** -/
theorem query_view (request : PublicQuery FI EI) (σ : LazyOracle.State FI EI) :
    (LazyOracle.query request σ).map (fun a => (a.1, view a.2)) = queryView request (view σ) := by
  cases request with
  | hash x => exact hashQuery_view σ x
  | fixedForward index input =>
      simp only [LazyOracle.query, PMF.map_comp]; rfl
  | fixedInverse index output =>
      simp only [LazyOracle.query, PMF.map_comp]; rfl
  | encForward index input =>
      simp only [LazyOracle.query, PMF.map_comp]; rfl
  | encInverse index output =>
      simp only [LazyOracle.query, PMF.map_comp]; rfl

/-- **An oracle program's lazy run factors through the view.** -/
theorem run_view {Result : Type} {budget : ℕ} (program : OracleProgram (publicOracleSpec FI EI) Result budget)
    (σ : LazyOracle.State FI EI) :
    (LazyOracle.run program σ).map (fun r => (r.1, view r.2)) = runSampled queryView program (view σ) := by
  unfold LazyOracle.run
  induction program generalizing σ with
  | pure distribution =>
      simp only [runSampled, PMF.map_comp]; rfl
  | query request next ih =>
      simp only [runSampled, PMF.map_bind, ih]
      rw [← query_view, PMF.bind_map]
      rfl
  | sample distribution next ih =>
      simp only [runSampled, PMF.map_bind, ih]

/-! ### The fill of pending points -/

/-- The hash lookups with the pending points `P` filled from `v` where the view has no value. -/
def fillHash (h : BaseField → Option (Block × Block)) (P : Finset BaseField) (v : BaseField → Block × Block) :
    BaseField → Option (Block × Block) :=
  fun x => if x ∈ P ∧ h x = none then some (v x) else h x

/-- A filled view. -/
def fill (w : View FI EI) (P : Finset BaseField) (v : BaseField → Block × Block) : View FI EI :=
  (w.1, w.2.1, fillHash w.2.2 P v)

/-- The fill kernel: the pending values uniform. -/
def fillK (w : View FI EI) (P : Finset BaseField) : PMF (View FI EI) :=
  (PMF.uniformOfFintype (BaseField → Block × Block)).map (fill w P)

/-- **Resampling one coordinate of a uniform function.** -/
theorem uniform_resample {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β] (x : α)
    (g : (α → β) → γ) :
    (PMF.uniformOfFintype (α → β)).map (fun v => (v x, g v))
      = (PMF.uniformOfFintype β).bind fun u => (PMF.uniformOfFintype (α → β)).map fun v => (u, g (Function.update v x u)) := by
  let e : β × (α → β) ≃ (α → β) × β :=
    { toFun := fun p => (Function.update p.2 x p.1, p.2 x)
      invFun := fun q => (q.1 x, Function.update q.1 x q.2)
      left_inv := fun p => by
        obtain ⟨u, v⟩ := p
        simp
      right_inv := fun q => by
        obtain ⟨f, b⟩ := q
        simp }
  have product : PMF.uniformOfFintype (β × (α → β))
      = (PMF.uniformOfFintype β).bind fun u => (PMF.uniformOfFintype (α → β)).map (Prod.mk u) :=
    Kriterion.ArgoMAC.Security.Phase3.uniformOfFintype_productPMF
  have pushed : (PMF.uniformOfFintype (β × (α → β))).map (fun p => (Function.update p.2 x p.1 x, g (Function.update p.2 x p.1)))
      = (PMF.uniformOfFintype (α → β)).map (fun v => (v x, g v)) := by
    have : (fun p : β × (α → β) => (Function.update p.2 x p.1 x, g (Function.update p.2 x p.1)))
        = (fun v : α → β => (v x, g v)) ∘ Prod.fst ∘ e := rfl
    rw [this, ← PMF.map_comp, ← PMF.map_comp, uniformOfFintype_map_equiv,
      Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_fst]
  rw [← pushed, product, PMF.map_bind]
  refine congrArg _ (funext fun u => ?_)
  rw [PMF.map_comp]
  simp [Function.comp_def]

/-- Two independent draws, one of them a map, commute. -/
theorem bind_map_comm {α β γ : Type} (p : PMF α) (q : PMF β) (f : α → β → γ) :
    p.bind (fun a => q.map (f a)) = q.bind (fun b => p.map fun a => f a b) := by
  simp only [PMF.map]
  exact PMF.bind_comm p q _

/-- A uniform function updated at one point by a uniform value is uniform. -/
theorem uniform_update {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β] (x : α) :
    (PMF.uniformOfFintype (α → β)).bind (fun v => (PMF.uniformOfFintype β).map fun u => Function.update v x u)
      = PMF.uniformOfFintype (α → β) := by
  have key := congrArg (fun law => law.map Prod.snd) (uniform_resample (β := β) x (fun v => v))
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at key
  rw [bind_map_comm]
  exact key.symm.trans (PMF.map_id _)

theorem fillHash_update_of_not_mem (h : BaseField → Option (Block × Block)) (P : Finset BaseField)
    (v : BaseField → Block × Block) {x : BaseField} (outside : x ∉ P) (a : Block × Block) :
    Function.update (fillHash h P v) x (some a) = fillHash (Function.update h x (some a)) P v := by
  funext y
  by_cases same : y = x
  · subst same
    simp [fillHash, outside]
  · simp [fillHash, Function.update_of_ne same]

theorem fillHash_resample (h : BaseField → Option (Block × Block)) (P : Finset BaseField)
    (v : BaseField → Block × Block) {x : BaseField} (inside : x ∈ P) (fresh : h x = none) (a : Block × Block) :
    fillHash h P (Function.update v x a) = fillHash (Function.update h x (some a)) P v := by
  funext y
  by_cases same : y = x
  · subst same
    simp [fillHash, inside, fresh]
  · simp [fillHash, Function.update_of_ne same]

theorem fillHash_of_some (h : BaseField → Option (Block × Block)) (P : Finset BaseField)
    (v : BaseField → Block × Block) {x : BaseField} {a : Block × Block} (known : h x = some a) :
    fillHash h P v x = some a := by
  simp [fillHash, known]

theorem hashQueryView_some {w : View FI EI} {x : BaseField} {a : Block × Block} (known : w.2.2 x = some a) :
    queryView.hashQueryView w x = PMF.pure (a, w) := by
  unfold queryView.hashQueryView
  rw [known]

theorem hashQueryView_none {w : View FI EI} {x : BaseField} (fresh : w.2.2 x = none) :
    queryView.hashQueryView w x = (PMF.uniformOfFintype (Block × Block)).map
      fun v => (v, (w.1, w.2.1, Function.update w.2.2 x (some v))) := by
  unfold queryView.hashQueryView
  rw [fresh]

/-- A query that commutes with each fill commutes with the fill kernel. -/
theorem fill_query_of_each (request : PublicQuery FI EI) (w : View FI EI) (P : Finset BaseField)
    (each : ∀ v, queryView request (fill w P v) = (queryView request w).map fun a => (a.1, fill a.2 P v)) :
    (fillK w P).bind (queryView request)
      = (queryView request w).bind fun a => (fillK a.2 P).map fun w' => (a.1, w') := by
  unfold fillK
  rw [PMF.bind_map, Function.comp_def]
  simp only [each, PMF.map_comp]
  exact bind_map_comm _ _ _

/-- A hash query that commutes with each fill commutes with the fill kernel. -/
theorem fill_hashQuery_of_each (w : View FI EI) (P : Finset BaseField) (x : BaseField)
    (each : ∀ v, queryView.hashQueryView (fill w P v) x
      = (queryView.hashQueryView w x).map fun a => (a.1, fill a.2 P v)) :
    (fillK w P).bind (fun w1 => queryView.hashQueryView w1 x)
      = (queryView.hashQueryView w x).bind fun a => (fillK a.2 P).map fun w' => (a.1, w') := by
  unfold fillK
  rw [PMF.bind_map, Function.comp_def]
  simp only [each, PMF.map_comp]
  exact bind_map_comm _ _ _

/-- **A hash query commutes with the fill of pending points.** -/
theorem fill_hashQuery (w : View FI EI) (P : Finset BaseField) (x : BaseField) :
    (fillK w P).bind (fun w1 => queryView.hashQueryView w1 x)
      = (queryView.hashQueryView w x).bind fun a => (fillK a.2 P).map fun w' => (a.1, w') := by
  cases known : w.2.2 x with
  | some a =>
      refine fill_hashQuery_of_each w P x fun v => ?_
      have filled : (fill w P v).2.2 x = some a := fillHash_of_some _ _ _ known
      rw [hashQueryView_some filled, hashQueryView_some known, PMF.pure_map]
  | none =>
      by_cases inside : x ∈ P
      · have filled : ∀ v, (fill w P v).2.2 x = some (v x) := fun v => by
          simp [fill, fillHash, inside, known]
        rw [hashQueryView_none known, PMF.bind_map]
        calc (fillK w P).bind (fun w1 => queryView.hashQueryView w1 x)
            = (PMF.uniformOfFintype (BaseField → Block × Block)).bind
                (fun v => queryView.hashQueryView (fill w P v) x) := by
              unfold fillK
              rw [PMF.bind_map]
              rfl
          _ = (PMF.uniformOfFintype (BaseField → Block × Block)).bind
                (fun v => PMF.pure (v x, fill w P v)) :=
              congrArg _ (funext fun v => hashQueryView_some (filled v))
          _ = (PMF.uniformOfFintype (BaseField → Block × Block)).map (fun v => (v x, fill w P v)) := rfl
          _ = _ := uniform_resample x (fun v => fill w P v)
          _ = _ := by
            refine congrArg _ (funext fun u => ?_)
            unfold fillK
            rw [Function.comp_apply, PMF.map_comp]
            congr 1
            funext v
            simp only [Function.comp_def, fill, fillHash_resample w.2.2 P v inside known u]
      · refine fill_hashQuery_of_each w P x fun v => ?_
        have filled : (fill w P v).2.2 x = none := by simp [fill, fillHash, inside, known]
        rw [hashQueryView_none filled, hashQueryView_none known, PMF.map_comp]
        congr 1
        funext u
        simp only [Function.comp_def, fill, fillHash_update_of_not_mem w.2.2 P v inside u]

/-- **A query commutes with the fill of pending points.** Querying a filled view is querying the view and filling
after: a pending point returns its filled value in the one and a fresh uniform value in the other, equal in law after
resampling that value (`uniform_resample`). -/
theorem fill_query (request : PublicQuery FI EI) (w : View FI EI) (P : Finset BaseField) :
    (fillK w P).bind (queryView request)
      = (queryView request w).bind fun a => (fillK a.2 P).map fun w' => (a.1, w') := by
  cases request with
  | fixedForward index input =>
      refine fill_query_of_each _ w P fun v => ?_
      simp only [queryView, PMF.map_comp]
      rfl
  | fixedInverse index output =>
      refine fill_query_of_each _ w P fun v => ?_
      simp only [queryView, PMF.map_comp]
      rfl
  | encForward index input =>
      refine fill_query_of_each _ w P fun v => ?_
      simp only [queryView, PMF.map_comp]
      rfl
  | encInverse index output =>
      refine fill_query_of_each _ w P fun v => ?_
      simp only [queryView, PMF.map_comp]
      rfl
  | hash x => exact fill_hashQuery w P x

/-- **A lazy run commutes with the fill of pending points** (joint law of the result and the final view). -/
theorem run_fill {Result : Type} {budget : ℕ} (program : OracleProgram (publicOracleSpec FI EI) Result budget)
    (w : View FI EI) (P : Finset BaseField) :
    (fillK w P).bind (runSampled queryView program)
      = (runSampled queryView program w).bind fun r => (fillK r.2 P).map fun w' => (r.1, w') := by
  induction program generalizing w with
  | pure distribution =>
      simp only [runSampled, PMF.bind_map, Function.comp_def]
      unfold fillK
      rw [PMF.bind_map, Function.comp_def, bind_map_comm]
      refine congrArg _ (funext fun r => ?_)
      rw [PMF.map_comp]
      rfl
  | query request next ih =>
      simp only [runSampled]
      rw [← PMF.bind_bind, fill_query, PMF.bind_bind, PMF.bind_bind]
      refine congrArg _ (funext fun a => ?_)
      rw [PMF.bind_map, Function.comp_def]
      exact ih a.1 a.2
  | sample distribution next ih =>
      simp only [runSampled]
      rw [PMF.bind_comm, PMF.bind_bind]
      refine congrArg _ (funext fun x => ?_)
      exact ih x w

end

end Kriterion.CRT.Privacy.Refill
