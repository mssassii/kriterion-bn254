/-
**(B): `CrtMiddleFactor`, the private stage 2 of `M'` against the ideal view**.

`M'`'s stage 2 on the curve replays route M privately from the empty oracle, flags a replay that meets the stage-1
state `σ₁`, draws the target rows and the collector answers, programs the collectors, runs the shadow's discarded
questions, and flags by the reveal. The ideal view law `idealCore` draws a swapped table, reads the replay's output on
it, draws the rows and the collector answers, and flags by the reveal on the programmed table. This file puts the two
side by side:

* `routeMReplay_bind`, **`middleStage2_on`**: on the curve, `M'`'s stage 2 is a swapped table, then
  the rest of the stage on the replay's value and the deterministic private state `tableFinal …`;
* **`tableRunOff_pure`**: off the curve `M'` answers fresh points from the table; from a state
  consistent with the table the run is deterministic;
* `installEntries_merge`, `merge_sameLookup`: installing hash entries into `σ₁` has the lookups of the merge of their
  private installation, when it does not meet `σ₁`;
* **`middleOn_le`**: at one source on the curve, `M'`'s weighted stage-2 mass is at most the ideal view law's, from two
  named inputs: containment (the private state after the collector programs has the lookups of the view's entries) and
  the flag (the ideal reveal on the programmed table implies the shadow's reveal on the final private state).
-/

import Proof.Privacy.CRT.Laws.TableRun
import Proof.Privacy.CRT.PublicFirst.Below

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.H8
open Kriterion.CRT.Privacy.PublicFirst (Meets mergeState finishPrivate stageTwoWeight middleStage2 collectorDraws OffRun
  viewHere contHW shadow_law_step shadow_law_meets weight_none tsum_bind_mul tsum_map_mul tsum_pure_mul_eq
  storedPoints mem_keys_of_lookup CrtShadow)
open scoped ENNReal

noncomputable section

variable {FI EI : Type}

/-! ### 1. Lookups of merges and installations -/

theorem lookup_append (l₁ l₂ : List (BaseField × Fin (Fintype.card (Block × Block)))) (x : BaseField) :
    (l₁ ++ l₂).lookup x = match l₁.lookup x with
      | some v => some v
      | none => l₂.lookup x := by
  induction l₁ with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨k, v⟩ := head
      rw [List.cons_append, lookup_cons, lookup_cons]
      by_cases same : x = k
      · rw [if_pos same, if_pos same]
      · rw [if_neg same, if_neg same]
        exact ih

theorem merge_lookup (planted state : LazyOracle.State FI EI) (x : BaseField) :
    (mergeState planted state).hash.lookup x = match state.hash.lookup x with
      | some v => some v
      | none => planted.hash.lookup x :=
  lookup_append _ _ x

theorem mergeState_plant (planted state : LazyOracle.State FI EI) (x : BaseField) (a : Block × Block) :
    mergeState planted (plantHash x a state) = plantHash x a (mergeState planted state) := rfl

section Install

variable [DecidableEq FI] [DecidableEq EI]

theorem installOne_mono (σ : LazyOracle.State FI EI) (y : BaseField) (a : Block × Block) (x : BaseField)
    (stored : (σ.hash.lookup x).isSome) : ((installOne σ ⟨.hash y, a⟩).hash.lookup x).isSome := by
  rw [installOne_hash]
  split
  · exact (plant_isSome σ y x a).mpr (Or.inl stored)
  · exact stored

theorem installOne_stores (σ : LazyOracle.State FI EI) (y : BaseField) (a : Block × Block) :
    ((installOne σ ⟨.hash y, a⟩).hash.lookup y).isSome := by
  rw [installOne_hash]
  split
  · exact (plant_isSome σ y y a).mpr (Or.inr rfl)
  · rename_i stored
    exact Option.ne_none_iff_isSome.mp stored

theorem installEntries_mono : ∀ (l : List (Entry FI EI)), HashEntries l → ∀ (σ : LazyOracle.State FI EI) x,
    (σ.hash.lookup x).isSome → ((Privacy.installEntries l σ).hash.lookup x).isSome
  | [], _, _, _, stored => stored
  | e :: rest, hashes, σ, x, stored => by
      obtain ⟨y, hy⟩ := hashes e List.mem_cons_self
      obtain ⟨q, a⟩ := e
      simp only at hy
      subst hy
      rw [installEntries_cons]
      exact installEntries_mono rest (fun e' member => hashes e' (List.mem_cons_of_mem _ member)) _ x
        (installOne_mono σ y a x stored)

theorem installEntries_stores : ∀ (l : List (Entry FI EI)), HashEntries l → ∀ (σ : LazyOracle.State FI EI),
    ∀ e ∈ l, ((Privacy.installEntries l σ).hash.lookup (entryInput e)).isSome
  | [], _, _, e, member => absurd member List.not_mem_nil
  | e :: rest, hashes, σ, e', member => by
      have restHashes : HashEntries rest := fun e'' m => hashes e'' (List.mem_cons_of_mem _ m)
      obtain ⟨y, hy⟩ := hashes e List.mem_cons_self
      obtain ⟨q, a⟩ := e
      simp only at hy
      subst hy
      rw [installEntries_cons]
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact installEntries_mono rest restHashes _ y (installOne_stores σ y a)
      · exact installEntries_stores rest restHashes _ e' later

/-- **Installing into `σ₁` against installing privately and merging**, at inputs `σ₁` does not store. -/
theorem installEntries_merge (planted : LazyOracle.State FI EI) :
    ∀ (l : List (Entry FI EI)) (A B : LazyOracle.State FI EI), HashEntries l →
      (∀ e ∈ l, planted.hash.lookup (entryInput e) = none) → SameLookup (mergeState planted A) B →
      SameLookup (mergeState planted (Privacy.installEntries l A)) (Privacy.installEntries l B)
  | [], _, _, _, _, same => same
  | e :: rest, A, B, hashes, apart, same => by
      have restHashes : HashEntries rest := fun e' m => hashes e' (List.mem_cons_of_mem _ m)
      have restApart : ∀ e' ∈ rest, planted.hash.lookup (entryInput e') = none := fun e' m =>
        apart e' (List.mem_cons_of_mem _ m)
      obtain ⟨y, hy⟩ := hashes e List.mem_cons_self
      obtain ⟨q, a⟩ := e
      simp only at hy
      subst hy
      have fresh : planted.hash.lookup y = none := apart _ List.mem_cons_self
      have iff : A.hash.lookup y = none ↔ B.hash.lookup y = none := by
        rw [← same.2.2 y, merge_lookup]
        cases A.hash.lookup y with
        | none => simp [fresh]
        | some v => simp
      rw [installEntries_cons, installEntries_cons, installOne_hash A y a, installOne_hash B y a]
      by_cases hA : A.hash.lookup y = none
      · rw [if_pos hA, if_pos (iff.mp hA)]
        exact installEntries_merge planted rest _ _ restHashes restApart (same.plant y a)
      · rw [if_neg hA, if_neg fun hB => hA (iff.mpr hB)]
        exact installEntries_merge planted rest A B restHashes restApart same

/-- **The merge of a private state with the lookups of some hash entries is their installation into `σ₁`**, when the
private state does not meet `σ₁`. -/
theorem merge_sameLookup (planted installed : LazyOracle.State FI EI) (l : List (Entry FI EI)) (hashes : HashEntries l)
    (same : ∀ x, installed.hash.lookup x = (Privacy.installEntries l LazyOracle.empty).hash.lookup x)
    (apart : ¬ Meets planted installed) :
    SameLookup (mergeState planted installed) (Privacy.installEntries l planted) := by
  have disjoint : ∀ e ∈ l, planted.hash.lookup (entryInput e) = none := by
    intro e he
    by_contra hit
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hit
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (installEntries_stores l hashes LazyOracle.empty e he)
    rw [← same] at hw
    exact apart ⟨entryInput e, mem_keys_of_lookup _ _ _ hw, mem_keys_of_lookup _ _ _ hv⟩
  have base := installEntries_merge planted l LazyOracle.empty planted hashes disjoint (SameLookup.refl planted)
  refine SameLookup.trans (σ' := mergeState planted (Privacy.installEntries l LazyOracle.empty))
    ⟨rfl, rfl, fun x => ?_⟩ base
  rw [merge_lookup, merge_lookup, same x]

end Install

/-! ### 2. Off the curve: the table reader is deterministic -/

section Off

variable [DecidableEq FI] [DecidableEq EI]

/-- `M'`'s off-curve answer at an input: the table at the input's tag. -/
def offAnswer (table : TagTable) (n : ℕ) : Block × Block := table (tagOfInput (n : BaseField))

/-- The state after one off-curve read. -/
def offStep (table : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI) : LazyOracle.State FI EI :=
  if σ.hash.lookup (n : BaseField) = none then plantHash (n : BaseField) (offAnswer table n) σ else σ

/-- **The final state of an off-curve run.** -/
def offFinal (table : TagTable) {α : Type} : CM α → LazyOracle.State FI EI → LazyOracle.State FI EI
  | .pure _, σ => σ
  | .query n next, σ => offFinal table (next (offAnswer table n)) (offStep table n σ)

/-- The inputs an off-curve run reads. -/
def offPoints (table : TagTable) {α : Type} : CM α → List BaseField
  | .pure _ => []
  | .query n next => (n : BaseField) :: offPoints table (next (offAnswer table n))

theorem tableReaderOff_step (table : TagTable) (n : ℕ) (σ : LazyOracle.State FI EI) (cons : TableConsistent table σ) :
    PublicFirst.tableReader table n σ = PMF.pure (offAnswer table n, offStep table n σ) ∧
      TableConsistent table (offStep table n σ) ∧ (offStep table n σ).fixed = σ.fixed ∧
      (offStep table n σ).enc = σ.enc ∧
      ∀ x, ((offStep table n σ).hash.lookup x).isSome ↔ ((σ.hash.lookup x).isSome ∨ x = (n : BaseField)) := by
  by_cases missing : σ.hash.lookup (n : BaseField) = none
  · have read : PublicFirst.tableReader table n σ =
        PMF.pure (offAnswer table n, plantHash (n : BaseField) (offAnswer table n) σ) := by
      unfold PublicFirst.tableReader
      rw [show (LazyOracle.lookup (.hash (n : BaseField)) σ : Option (Block × Block)) = none by
        show Option.map _ (σ.hash.lookup (n : BaseField)) = none
        rw [missing]
        rfl]
      rw [program_hash_fresh σ _ _ missing]
      rfl
    unfold offStep
    rw [if_pos missing]
    exact ⟨read, plant_consistent table cons _ _ rfl, rfl, rfl, fun x => plant_isSome σ _ x _⟩
  · obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp missing
    have read : PublicFirst.tableReader table n σ = PMF.pure (offAnswer table n, σ) := by
      unfold PublicFirst.tableReader
      rw [show (LazyOracle.lookup (.hash (n : BaseField)) σ : Option (Block × Block)) =
          some (offAnswer table n) by
        show Option.map _ (σ.hash.lookup (n : BaseField)) = _
        rw [found, cons _ v found]
        exact congrArg some ((Fintype.equivFin (Block × Block)).symm_apply_apply _)]
    unfold offStep
    rw [if_neg missing]
    refine ⟨read, cons, rfl, rfl, fun x => ⟨Or.inl, ?_⟩⟩
    rintro (stored | rfl)
    · exact stored
    · rw [found]
      rfl

/-- **(b): off the curve `M'`'s table run is deterministic.** From a state consistent with the table,
the run answers every input by the table at its tag; the final state is consistent and stores exactly the old inputs
and the inputs read. -/
theorem tableRunOff_pure (table : TagTable) {α : Type} :
    ∀ (P : CM α) (σ : LazyOracle.State FI EI), TableConsistent table σ →
      runReader (PublicFirst.tableReader table) P σ = PMF.pure (P.eval (offAnswer table), offFinal table P σ) ∧
        TableConsistent table (offFinal table P σ) ∧ (offFinal table P σ).fixed = σ.fixed ∧
        (offFinal table P σ).enc = σ.enc ∧
        ∀ x, ((offFinal table P σ).hash.lookup x).isSome ↔ ((σ.hash.lookup x).isSome ∨ x ∈ offPoints table P)
  | .pure value, σ, cons => ⟨rfl, cons, rfl, rfl, fun x => by simp [offPoints, offFinal]⟩
  | .query n next, σ, cons => by
      obtain ⟨read, cons₁, fixed₁, enc₁, stored₁⟩ := tableReaderOff_step table n σ cons
      obtain ⟨run, cons₂, fixed₂, enc₂, stored₂⟩ := tableRunOff_pure table (next (offAnswer table n)) _ cons₁
      refine ⟨?_, cons₂, fixed₂.trans fixed₁, enc₂.trans enc₁, fun x => ?_⟩
      · rw [runReader_query, read, PMF.pure_bind]
        exact run
      · show ((offFinal table (next (offAnswer table n)) (offStep table n σ)).hash.lookup x).isSome ↔
          _ ∨ x ∈ (n : BaseField) :: offPoints table (next (offAnswer table n))
        rw [stored₂ x, stored₁ x, List.mem_cons]
        tauto

/-- From the empty state. -/
theorem tableRunOff_empty (table : TagTable) {α : Type} (P : CM α) :
    runReader (PublicFirst.tableReader table) P (LazyOracle.empty : LazyOracle.State FI EI) =
        PMF.pure (P.eval (offAnswer table), offFinal table P LazyOracle.empty) ∧
      SeenState tagOfInput LazyOracle.empty (offPoints table P) table
        (offFinal table P (LazyOracle.empty : LazyOracle.State FI EI)) := by
  have emptyLookup : ∀ x, (LazyOracle.empty : LazyOracle.State FI EI).hash.lookup x = none := fun _ => rfl
  obtain ⟨run, cons, fixed, enc, stored⟩ := tableRunOff_pure table P LazyOracle.empty
    (fun x v hv => by rw [emptyLookup] at hv; cases hv)
  refine ⟨run, fixed, enc, fun y => ?_⟩
  by_cases hit : y ∈ offPoints table P
  · rw [if_pos hit]
    obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp ((stored y).mpr (Or.inr hit))
    rw [found, cons y v found]
  · rw [if_neg hit, emptyLookup]
    have notStored : ¬ ((offFinal table P (LazyOracle.empty : LazyOracle.State FI EI)).hash.lookup y).isSome :=
      fun h => by
        rcases (stored y).mp h with h | h
        · rw [emptyLookup] at h; cases h
        · exact hit h
    exact Option.not_isSome_iff_eq_none.mp notStored

end Off

/-! ### 3. On the curve: `M'`'s stage 2 as a table law -/

/-- **`HW`'s replay from the empty state, followed by any continuation.** -/
theorem routeMReplay_bind [FieldCertificate] [DecidableEq FI] [DecidableEq EI] {Public : Type}
    (view : RouteMView Public) (layout : SiteLayout) (facts : RefillLayoutFacts layout) (points : PointFacts layout)
    (published : Public) (u : AffineInput) (labels : LamportSignature)
    (keyNonSite : ∀ conv, siteOf ((view.keyInput published u conv).val / 2 ^ 128) = none)
    (path : RefillPath layout ∅ (LazyOracle.empty : LazyOracle.State FI EI) (view.replayProgram published u labels))
    (canon : Canonical layout (view.replayProgram published u labels)) {γ : Type}
    (K : ReplayOut × LazyOracle.State FI EI → PMF γ) :
    (routeMReplay view (refillReader layout) published u labels LazyOracle.empty).bind K =
      (swappedTableLaw layout).bind fun table =>
        K ((view.replayProgram published u labels).eval (tagHash table),
          tableFinal layout table (view.replayProgram published u labels) LazyOracle.empty) := by
  rw [routeMReplay_pure view layout facts points published u labels keyNonSite path canon, PMF.bind_bind]
  simp only [PMF.pure_bind]

variable (E : CrtEntry FI EI)

section On

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The replay program of a source at `u`. -/
abbrev replayOf (source : (viewHere E).Source) (u : AffineInput) : CM ReplayOut :=
  (viewHere E).replayProgram ((viewHere E).publish source) u ((viewHere E).labels source u)

open Classical in
/-- **`M'`'s stage 2 on the curve after the replay** (the continuation of `middleStage2`). -/
def middleContOn (shadow : CrtShadow (viewHere E).Source FI EI) (scalar : NonZeroScalar)
    (source : (viewHere E).Source) (u : AffineInput) (target : Point) (planted : LazyOracle.State FI EI)
    (ran : ReplayOut × LazyOracle.State FI EI) : PMF (Option (Option (LamportSignature × LazyOracle.State FI EI))) :=
  let labels := (viewHere E).labels source u
  let published := (viewHere E).publish source
  if Meets planted ran.2 then PMF.pure none else
  ((viewHere E).realRows scalar u target).bind fun drawnRows => match drawnRows with
    | none => PMF.pure none
    | some targets =>
      (collectorDraws E (collectorMasks u ran.1 ((viewHere E).gammaOf published) targets)).bind
        fun drawn => match drawn with
        | none => PMF.pure none
        | some drawn => match programHashAll (programRequests ran.1.key drawn) ran.2 with
          | none => PMF.pure none
          | some installed => shadow.law.bind fun coin =>
            (runReader lazyReader (shadow.onCurve source u coin) installed).map fun shadowed =>
              finishPrivate planted labels (shadow.revealOn source u targets coin shadowed.2) shadowed.2

omit [Fintype FI] [Fintype EI] in
theorem middleStage2_some (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (target : Point)
    (planted : LazyOracle.State FI EI) :
    middleStage2 E shadow offRun scalar source u (some target) planted =
      (routeMReplay (viewHere E) (refillReader E.layout) ((viewHere E).publish source) u ((viewHere E).labels source u)
        LazyOracle.empty).bind (middleContOn E shadow scalar source u target planted) := rfl

omit [Fintype FI] [Fintype EI] in
/-- **(a): on the curve, `M'`'s stage 2 is a swapped table, then the rest of the stage on the replay's
value and the deterministic private state.** -/
theorem middleStage2_on (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (target : Point)
    (planted : LazyOracle.State FI EI) (facts : RefillLayoutFacts E.layout) (points : PointFacts E.layout)
    (keyNonSite : ∀ conv, siteOf (((viewHere E).keyInput ((viewHere E).publish source) u conv).val / 2 ^ 128) = none)
    (path : RefillPath E.layout ∅ (LazyOracle.empty : LazyOracle.State FI EI) (replayOf E source u))
    (canon : Canonical E.layout (replayOf E source u)) :
    middleStage2 E shadow offRun scalar source u (some target) planted =
      (swappedTableLaw E.layout).bind fun table =>
        middleContOn E shadow scalar source u target planted
          ((replayOf E source u).eval (tagHash table), tableFinal E.layout table (replayOf E source u) LazyOracle.empty) := by
  rw [middleStage2_some]
  exact routeMReplay_bind (viewHere E) E.layout facts points _ u _ keyNonSite path canon _

end On

end

end Kriterion.CRT.Privacy.Laws
