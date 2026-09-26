/-
**P10, step 2: the readers and the route-M programming through the view** (row H10).

The refill reader, the lazy reader, route M's interception of the collector masks, the installation of a refilled
site and route M's programming of the collector points all depend on a lazy state only through its view
(`Presample.lean`); this file restates each on views (`refillView`, `lazyView`, `installView`, `programHashAllView`) and proves the factorisations. Two fill facts close the file: programming at points outside
the pending set commutes with the fill (`programHashAllView_fill`), and installing uniform answers at fresh points
outside the pending set extends the fill to them (`install_fill`).
-/

import Proof.Privacy.CRT.Refill.Presample
import Proof.Privacy.CRT.Swap.Hop

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Refill

open BN254 Cryptography Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC (FreeQuery)
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-! ### Programming a hash point -/

/-- Programming a hash point, typed with its answer type unfolded. -/
def programHash (σ : LazyOracle.State FI EI) (x : BaseField) (a : Block × Block) :
    Option (LazyOracle.State FI EI) :=
  LazyOracle.program (.hash x) a σ

theorem programHash_eq (σ : LazyOracle.State FI EI) (x : BaseField) (a : Block × Block) :
    programHash σ x a =
      if σ.hash.lookup x = none then some { σ with hash := (x, hashCode a) :: σ.hash } else none := rfl

/-- Programming a hash point on a view. -/
def programHashView (w : View FI EI) (x : BaseField) (a : Block × Block) : Option (View FI EI) :=
  if w.2.2 x = none then some (w.1, w.2.1, Function.update w.2.2 x (some a)) else none

theorem programHash_view (σ : LazyOracle.State FI EI) (x : BaseField) (a : Block × Block) :
    (programHash σ x a).map view = programHashView (view σ) x a := by
  rw [programHash_eq]
  unfold programHashView
  have same : (view σ).2.2 x = none ↔ σ.hash.lookup x = none := hashView_eq_none σ x
  by_cases fresh : σ.hash.lookup x = none
  · rw [if_pos fresh, if_pos (same.mpr fresh), Option.map_some]
    congr 1
    show (σ.fixed, σ.enc, hashView { σ with hash := (x, hashCode a) :: σ.hash }) = _
    rw [hashView_cons, Equiv.symm_apply_apply]
    rfl
  · rw [if_neg fresh, if_neg (fun h => fresh (same.mp h)), Option.map_none]

/-- Route M's programming on a view. -/
def programHashAllView : List (BaseField × (Block × Block)) → View FI EI → Option (View FI EI)
  | [], w => some w
  | (x, a) :: rest, w => (programHashView w x a).bind (programHashAllView rest)

theorem programHashAll_view (requests : List (BaseField × (Block × Block))) (σ : LazyOracle.State FI EI) :
    (programHashAll requests σ).map view = programHashAllView requests (view σ) := by
  induction requests generalizing σ with
  | nil => rfl
  | cons request rest ih =>
      obtain ⟨x, a⟩ := request
      have step := programHash_view σ x a
      show ((programHash σ x a).bind (programHashAll rest)).map view
        = (programHashView (view σ) x a).bind (programHashAllView rest)
      cases programmed : programHash σ x a with
      | none =>
          rw [programmed, Option.map_none] at step
          rw [← step]
          rfl
      | some next =>
          rw [programmed, Option.map_some] at step
          rw [← step, Option.bind_some, Option.bind_some, ih]

theorem programHashView_fill (w : View FI EI) (P : Finset BaseField) (v : BaseField → Block × Block)
    {x : BaseField} (outside : x ∉ P) (a : Block × Block) :
    programHashView (fill w P v) x a = (programHashView w x a).map fun w' => fill w' P v := by
  unfold programHashView
  have same : (fill w P v).2.2 x = w.2.2 x := by simp [fill, fillHash, outside]
  rw [same]
  by_cases fresh : w.2.2 x = none
  · rw [if_pos fresh, if_pos fresh, Option.map_some]
    simp only [fill, fillHash_update_of_not_mem w.2.2 P v outside a]
  · rw [if_neg fresh, if_neg fresh, Option.map_none]

/-- **Programming outside the pending points commutes with the fill.** -/
theorem programHashAllView_fill (requests : List (BaseField × (Block × Block))) (w : View FI EI)
    (P : Finset BaseField) (v : BaseField → Block × Block) (outside : ∀ request ∈ requests, request.1 ∉ P) :
    programHashAllView requests (fill w P v) = (programHashAllView requests w).map fun w' => fill w' P v := by
  induction requests generalizing w with
  | nil => rfl
  | cons request rest ih =>
      obtain ⟨x, a⟩ := request
      simp only [programHashAllView]
      rw [programHashView_fill w P v (outside (x, a) List.mem_cons_self) a]
      cases programHashView w x a with
      | none => rfl
      | some next =>
          rw [Option.map_some, Option.bind_some, Option.bind_some]
          exact ih next fun request member => outside request (List.mem_cons_of_mem _ member)

/-! ### Installing a refilled site -/

/-- The installation of a site on a view. -/
def installView (pairs : List (BaseField × (Block × Block))) (w : View FI EI) : View FI EI :=
  pairs.foldl (fun current pair => (programHashView current pair.1 pair.2).getD current) w

theorem installPoints_view (pairs : List (BaseField × (Block × Block))) (σ : LazyOracle.State FI EI) :
    view (installPoints pairs σ) = installView pairs (view σ) := by
  induction pairs generalizing σ with
  | nil => rfl
  | cons pair rest ih =>
      show view (installPoints rest ((LazyOracle.program (.hash pair.1) pair.2 σ).getD σ))
        = installView rest ((programHashView (view σ) pair.1 pair.2).getD (view σ))
      rw [ih]
      congr 1
      have step := programHash_view σ pair.1 pair.2
      show view ((programHash σ pair.1 pair.2).getD σ) = _
      cases programmed : programHash σ pair.1 pair.2 with
      | none =>
          rw [programmed, Option.map_none] at step
          rw [← step]
          rfl
      | some next =>
          rw [programmed, Option.map_some] at step
          rw [← step]
          rfl

/-- The uniform answers of `n + 1` points: a first uniform answer, then `n`. -/
theorem uniformAnswers_succ (n : ℕ) :
    uniformAnswers (n + 1) = (PMF.uniformOfFintype (Block × Block)).bind fun a =>
      (uniformAnswers n).map fun answers => a :: answers := by
  unfold uniformAnswers
  have product : PMF.uniformOfFintype ((Block × Block) × (Fin n → Block × Block))
      = (PMF.uniformOfFintype (Block × Block)).bind fun a =>
          (PMF.uniformOfFintype (Fin n → Block × Block)).map (Prod.mk a) :=
    Kriterion.ArgoMAC.Security.Phase3.uniformOfFintype_productPMF
  rw [← uniformOfFintype_map_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Block × Block), PMF.map_comp,
    product, PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext f
  simp [Function.comp_def, Fin.consEquiv, List.ofFn_succ]

theorem uniformAnswers_zero : uniformAnswers 0 = PMF.pure [] := by
  unfold uniformAnswers
  have : (List.ofFn : (Fin 0 → Block × Block) → List (Block × Block)) = fun _ => [] := by
    funext f
    simp
  rw [this]
  exact PMF.map_const _ _

theorem fillHash_install (h : BaseField → Option (Block × Block)) (P : Finset BaseField)
    (v : BaseField → Block × Block) {x : BaseField} (fresh : h x = none) (a : Block × Block) :
    Function.update (fillHash h P v) x (some a) = fillHash h (insert x P) (Function.update v x a) := by
  funext y
  by_cases same : y = x
  · subst same
    simp [fillHash, fresh]
  · simp [fillHash, same]

/-- Filling a point the view already defines, or a point already pending, changes nothing. -/
theorem fillK_insert_of_settled (w : View FI EI) (Q : Finset BaseField) {x : BaseField}
    (settled : x ∈ Q ∨ w.2.2 x ≠ none) : fillK w (insert x Q) = fillK w Q := by
  rcases settled with inside | known
  · rw [Finset.insert_eq_of_mem inside]
  · unfold fillK
    congr 1
    funext v
    simp only [fill]
    congr 2
    funext y
    by_cases same : y = x
    · subst same
      simp [fillHash, known]
    · simp [fillHash, same]

/-- **Installing uniform answers at a site's points extends the fill to them.** Fresh points outside the pending
set take the uniform answers; a point the view defines, or one already pending, rejects its program, and its
answer is never read. -/
theorem install_fill (w : View FI EI) (points : List BaseField) (P : Finset BaseField) :
    (fillK w P).bind (fun w1 => (uniformAnswers points.length).map fun answers => installView (points.zip answers) w1)
      = fillK w (P ∪ points.toFinset) := by
  induction points generalizing P with
  | nil =>
      simp only [List.length_nil, uniformAnswers_zero, PMF.pure_map, List.zip_nil_left, List.toFinset_nil,
        Finset.union_empty]
      exact PMF.bind_pure _
  | cons x rest ih =>
      have union : P ∪ (x :: rest).toFinset = insert x (P ∪ rest.toFinset) := by
        rw [List.toFinset_cons, Finset.union_insert]
      have shape : (fillK w P).bind (fun w1 => (uniformAnswers (x :: rest).length).map fun answers =>
            installView ((x :: rest).zip answers) w1)
          = (PMF.uniformOfFintype (BaseField → Block × Block)).bind (fun v =>
              (PMF.uniformOfFintype (Block × Block)).bind fun a => (uniformAnswers rest.length).map fun answers =>
                installView (rest.zip answers) ((programHashView (fill w P v) x a).getD (fill w P v))) := by
        unfold fillK
        rw [PMF.bind_map]
        refine congrArg _ (funext fun v => ?_)
        rw [Function.comp_apply, List.length_cons, uniformAnswers_succ, PMF.map_bind]
        refine congrArg _ (funext fun a => ?_)
        rw [PMF.map_comp]
        rfl
      rw [shape, union]
      by_cases fresh : x ∉ P ∧ w.2.2 x = none
      · have step : ∀ v a, (programHashView (fill w P v) x a).getD (fill w P v)
            = fill w (insert x P) (Function.update v x a) := by
          intro v a
          have filled : (fill w P v).2.2 x = none := by simp [fill, fillHash, fresh.1, fresh.2]
          unfold programHashView
          rw [if_pos filled, Option.getD_some]
          simp only [fill, fillHash_install w.2.2 P v fresh.2 a]
        simp only [step]
        calc (PMF.uniformOfFintype (BaseField → Block × Block)).bind (fun v =>
              (PMF.uniformOfFintype (Block × Block)).bind fun a => (uniformAnswers rest.length).map fun answers =>
                installView (rest.zip answers) (fill w (insert x P) (Function.update v x a)))
            = ((PMF.uniformOfFintype (BaseField → Block × Block)).bind fun v =>
                (PMF.uniformOfFintype (Block × Block)).map fun a => Function.update v x a).bind (fun v =>
                  (uniformAnswers rest.length).map fun answers => installView (rest.zip answers)
                    (fill w (insert x P) v)) := by
              rw [PMF.bind_bind]
              refine congrArg _ (funext fun v => ?_)
              rw [PMF.bind_map]
              rfl
          _ = (fillK w (insert x P)).bind (fun w1 =>
                (uniformAnswers rest.length).map fun answers => installView (rest.zip answers) w1) := by
              rw [uniform_update]
              unfold fillK
              rw [PMF.bind_map]
              rfl
          _ = fillK w (insert x P ∪ rest.toFinset) := ih (insert x P)
          _ = fillK w (insert x (P ∪ rest.toFinset)) := by rw [Finset.insert_union]
      · have stuck : ∀ v a, (programHashView (fill w P v) x a).getD (fill w P v) = fill w P v := by
          intro v a
          have defined : (fill w P v).2.2 x ≠ none := by
            by_cases inside : x ∈ P
            · by_cases known : w.2.2 x = none
              · simp [fill, fillHash, inside, known]
              · simp [fill, fillHash, inside, known]
            · have known : w.2.2 x ≠ none := fun h => fresh ⟨inside, h⟩
              simp [fill, fillHash, inside, known]
          unfold programHashView
          rw [if_neg defined, Option.getD_none]
        simp only [stuck, PMF.bind_const]
        have settled : x ∈ P ∪ rest.toFinset ∨ w.2.2 x ≠ none := by
          by_cases inside : x ∈ P
          · exact Or.inl (Finset.mem_union_left _ inside)
          · exact Or.inr fun h => fresh ⟨inside, h⟩
        rw [fillK_insert_of_settled w _ settled, ← ih P]
        unfold fillK
        rw [PMF.bind_map]
        rfl

/-! ### Readers on views -/

/-- `I`'s reader on a view. -/
def lazyView (input : ℕ) (w : View FI EI) : PMF ((Block × Block) × View FI EI) :=
  queryView.hashQueryView w (input : BaseField)

/-- A site is untouched on a view. -/
def untouchedView (points : List BaseField) (w : View FI EI) : Bool :=
  points.all fun point => (w.2.2 point).isNone

/-- The refill reader on a view, with the refill law a parameter (the layout's law, or uniform answers). -/
def refillView (layout : SiteLayout) (law : SiteId → PMF (List (Block × Block))) (input : ℕ) (w : View FI EI) :
    PMF ((Block × Block) × View FI EI) :=
  match siteOf (input / 2 ^ 128) with
  | none => lazyView input w
  | some site =>
    let points := sitePoints layout site (input % 2 ^ 128)
    if untouchedView points w then
      (law site).bind fun answers => lazyView input (installView (points.zip answers) w)
    else lazyView input w

/-- A `FreeQuery CrtSpec` program run on views through a reader. -/
def runView (reader : ℕ → View FI EI → PMF ((Block × Block) × View FI EI)) {α : Type} :
    FreeQuery CrtSpec α → View FI EI → PMF (α × View FI EI)
  | .pure value, w => PMF.pure (value, w)
  | .query input next, w => (reader input w).bind fun answered => runView reader (next answered.1) answered.2

theorem lazyReader_view (input : ℕ) (σ : LazyOracle.State FI EI) :
    (lazyReader input σ).map (fun a => (a.1, view a.2)) = lazyView input (view σ) :=
  hashQuery_view σ (input : BaseField)

theorem untouched_view (points : List BaseField) (σ : LazyOracle.State FI EI) :
    untouched points σ = untouchedView points (view σ) := rfl

theorem refillReader_view (layout : SiteLayout) (input : ℕ) (σ : LazyOracle.State FI EI) :
    (refillReader layout input σ).map (fun a => (a.1, view a.2)) = refillView layout layout.law input (view σ) := by
  unfold refillReader refillView
  cases siteOf (input / 2 ^ 128) with
  | none => exact lazyReader_view input σ
  | some site =>
      dsimp only
      by_cases fresh : untouched (sitePoints layout site (input % 2 ^ 128)) σ = true
      · have fresh' : untouchedView (sitePoints layout site (input % 2 ^ 128)) (view σ) = true := fresh
        rw [if_pos fresh, if_pos fresh', PMF.map_bind]
        congr 1
        funext answers
        rw [lazyReader_view, installPoints_view]
      · have fresh' : ¬ untouchedView (sitePoints layout site (input % 2 ^ 128)) (view σ) = true := fresh
        rw [if_neg fresh, if_neg fresh']
        exact lazyReader_view input σ

theorem runReader_view (reader : Reader FI EI) (readerView : ℕ → View FI EI → PMF ((Block × Block) × View FI EI))
    (factors : ∀ input σ, (reader input σ).map (fun a => (a.1, view a.2)) = readerView input (view σ))
    {α : Type} (program : FreeQuery CrtSpec α) (σ : LazyOracle.State FI EI) :
    (runReader reader program σ).map (fun r => (r.1, view r.2)) = runView readerView program (view σ) := by
  induction program generalizing σ with
  | pure value => simp only [runReader, runView, PMF.pure_map]
  | query input next ih =>
      simp only [runReader, runView, PMF.map_bind]
      rw [← factors, PMF.bind_map]
      refine congrArg _ (funext fun answered => ?_)
      exact ih answered.1 answered.2

end

end Kriterion.CRT.Privacy.Refill
