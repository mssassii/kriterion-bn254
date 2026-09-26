/-
**P7, the public-first hop, part 5: private runs couple with shared runs** (the CRT, hash-only form of xinshu's
`PublicFirst/{Lookup, Sparse, SparseStep, FullRel, Private}.lean`).

A private run starts from the empty oracle; the shared run starts from the stage-1 state `σ₁`. The private run,
merged into `σ₁` (`mergeState`: its hash pairs on top), is the shared run whenever its final state does not meet
`σ₁`: every query is then fresh or cached on both sides at once, and a fresh answer is prepended on both sides. In the
expectation form used here (`Couples`): for every weight `h` on outcomes of the shared run,
`∑ private(p) · [p.2 does not meet σ₁] · h(p.1, merge σ₁ p.2) ≤ ∑ shared(p) · h(p)`.

* hash-table facts: `lookup_append_of_none`, `lookup_append_of_some`, `mem_keys_of_lookup`;
* `Extends` (pairs prepended, permutations unchanged), `Meets` monotone along it;
* the framework: `Couples`, `ExtendsRun`, `couples_bind`, `couples_map`, `couples_pure`;
* the lazy hash query (`couples_query_hash`, `extendsRun_query_hash`).
-/

import Proof.Privacy.CRT.PublicFirst.Middle

namespace Kriterion.CRT.Privacy.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### 1. Association lists -/

section Lookup

variable {K V : Type} [DecidableEq K]

theorem lookup_append_of_none (first second : List (K × V)) (x : K) (none : second.lookup x = none) :
    (first ++ second).lookup x = first.lookup x := by
  induction first with
  | nil => exact none
  | cons head tail ih =>
    obtain ⟨k, v⟩ := head
    show (((k, v) :: (tail ++ second)).lookup x) = ((k, v) :: tail).lookup x
    rw [List.lookup_cons, List.lookup_cons, ih]

theorem lookup_append_of_some (first second : List (K × V)) (x : K) (v : V) (found : first.lookup x = some v) :
    (first ++ second).lookup x = some v := by
  induction first with
  | nil => simp at found
  | cons head tail ih =>
    obtain ⟨k, w⟩ := head
    show (((k, w) :: (tail ++ second)).lookup x) = some v
    rw [List.lookup_cons]
    rw [List.lookup_cons] at found
    split
    · rename_i hit
      rw [hit] at found
      exact found
    · rename_i miss
      rw [miss] at found
      exact ih found

theorem mem_keys_of_lookup (table : List (K × V)) (x : K) (v : V) (found : table.lookup x = some v) :
    x ∈ table.map Prod.fst := by
  induction table with
  | nil => simp at found
  | cons head tail ih =>
    obtain ⟨k, w⟩ := head
    rw [List.lookup_cons] at found
    split at found
    · rename_i hit
      have : x = k := by simpa using hit
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih found)

theorem lookup_isSome_of_mem (table : List (K × V)) (x : K) (member : x ∈ table.map Prod.fst) :
    (table.lookup x).isSome := by
  induction table with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨k, w⟩ := head
    rw [List.lookup_cons]
    split
    · rfl
    · rename_i miss
      have different : x ≠ k := by simpa using miss
      rcases List.mem_cons.mp member with same | rest
      · exact (different same).elim
      · exact ih rest

end Lookup

/-! ### 2. Extensions, meetings and merges -/

variable {FI EI : Type}

/-- **A state extends another**: pairs prepended to its hash table, the permutations unchanged. -/
def Extends (state next : LazyOracle.State FI EI) : Prop :=
  ∃ extra : List (BaseField × Fin (Fintype.card (Block × Block))),
    next.hash = extra ++ state.hash ∧ next.fixed = state.fixed ∧ next.enc = state.enc

theorem Extends.refl (state : LazyOracle.State FI EI) : Extends state state := ⟨[], rfl, rfl, rfl⟩

theorem Extends.trans {first second third : LazyOracle.State FI EI} (one : Extends first second)
    (two : Extends second third) : Extends first third := by
  obtain ⟨extra, hash, fixed, enc⟩ := one
  obtain ⟨extra', hash', fixed', enc'⟩ := two
  exact ⟨extra' ++ extra, by rw [hash', hash, List.append_assoc], fixed'.trans fixed, enc'.trans enc⟩

theorem storedPoints_extends {state next : LazyOracle.State FI EI} (grow : Extends state next) {x : BaseField}
    (member : x ∈ storedPoints state) : x ∈ storedPoints next := by
  obtain ⟨extra, hash, -, -⟩ := grow
  unfold storedPoints at member ⊢
  rw [hash, List.map_append]
  exact List.mem_append_right _ member

theorem meets_extends {planted state next : LazyOracle.State FI EI} (grow : Extends state next)
    (meets : Meets planted state) : Meets planted next := by
  obtain ⟨x, inState, inPlanted⟩ := meets
  exact ⟨x, storedPoints_extends grow inState, inPlanted⟩

open Classical in
/-- **The private weight**: `0` when the private state meets `σ₁`, otherwise the shared weight at the merge. -/
def flagMerge {α : Type} (planted : LazyOracle.State FI EI) (h : α × LazyOracle.State FI EI → ℝ≥0∞)
    (p : α × LazyOracle.State FI EI) : ℝ≥0∞ :=
  if Meets planted p.2 then 0 else h (p.1, mergeState planted p.2)

theorem flagMerge_le {α : Type} (planted : LazyOracle.State FI EI) (h : α × LazyOracle.State FI EI → ℝ≥0∞)
    (p : α × LazyOracle.State FI EI) : flagMerge planted h p ≤ h (p.1, mergeState planted p.2) := by
  unfold flagMerge
  split
  · exact zero_le
  · exact le_rfl

theorem flagMerge_meets {α : Type} (planted : LazyOracle.State FI EI) (h : α × LazyOracle.State FI EI → ℝ≥0∞)
    (p : α × LazyOracle.State FI EI) (meets : Meets planted p.2) : flagMerge planted h p = 0 := by
  unfold flagMerge
  rw [if_pos meets]

/-! ### 3. The coupling framework -/

/-- **A runner couples** (private against shared): for every weight on the shared outcomes. -/
def Couples {α : Type} (run : LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI)) : Prop :=
  ∀ (planted state : LazyOracle.State FI EI) (h : α × LazyOracle.State FI EI → ℝ≥0∞),
    ∑' p, run state p * flagMerge planted h p ≤ ∑' p, run (mergeState planted state) p * h p

/-- **A runner only extends the state.** -/
def ExtendsRun {α : Type} (run : LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI)) : Prop :=
  ∀ state p, p ∈ (run state).support → Extends state p.2

theorem couples_pure {α : Type} (value : α) :
    Couples (FI := FI) (EI := EI) fun state => PMF.pure (value, state) := by
  intro planted state h
  rw [tsum_pure_mul', tsum_pure_mul']
  exact flagMerge_le planted h (value, state)
where
  tsum_pure_mul' {β : Type} (b : β) (f : β → ℝ≥0∞) : ∑' o, PMF.pure b o * f o = f b := by
    classical
    rw [tsum_eq_single b fun o different => by rw [PMF.pure_apply, if_neg different, zero_mul]]
    rw [PMF.pure_apply, if_pos rfl, one_mul]

theorem extendsRun_pure {α : Type} (value : α) :
    ExtendsRun (FI := FI) (EI := EI) fun state => PMF.pure (value, state) := by
  intro state p member
  rw [PMF.mem_support_pure_iff] at member
  subst member
  exact Extends.refl state

/-- A weight whose flagged form vanishes on every outcome of a run from a state meeting `σ₁`. -/
theorem tsum_flagMerge_of_meets {α : Type} (run : LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI))
    (grows : ExtendsRun run) (planted state : LazyOracle.State FI EI) (meets : Meets planted state)
    (h : α × LazyOracle.State FI EI → ℝ≥0∞) : ∑' p, run state p * flagMerge planted h p = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun p => ?_
  by_cases member : p ∈ (run state).support
  · rw [flagMerge_meets planted h p (meets_extends (grows state p member) meets), mul_zero]
  · rw [PMF.apply_eq_zero_iff _ _ |>.mpr member, zero_mul]

theorem couples_bind {α β : Type} (run : LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI))
    (next : α → LazyOracle.State FI EI → PMF (β × LazyOracle.State FI EI))
    (first : Couples run) (second : ∀ a, Couples (next a)) (secondGrows : ∀ a, ExtendsRun (next a)) :
    Couples fun state => (run state).bind fun p => next p.1 p.2 := by
  intro planted state h
  rw [tsum_bind_mul, tsum_bind_mul]
  have inner : ∀ q : α × LazyOracle.State FI EI,
      ∑' p, next q.1 q.2 p * flagMerge planted h p ≤
        flagMerge planted (fun r => ∑' p, next r.1 r.2 p * h p) q := by
    intro q
    by_cases meets : Meets planted q.2
    · rw [tsum_flagMerge_of_meets (next q.1) (secondGrows q.1) planted q.2 meets h]
      exact zero_le
    · unfold flagMerge
      rw [if_neg meets]
      exact second q.1 planted q.2 h
  calc ∑' q, run state q * ∑' p, next q.1 q.2 p * flagMerge planted h p
      ≤ ∑' q, run state q * flagMerge planted (fun r => ∑' p, next r.1 r.2 p * h p) q :=
        ENNReal.tsum_le_tsum fun q => mul_le_mul' le_rfl (inner q)
    _ ≤ ∑' q, run (mergeState planted state) q * ∑' p, next q.1 q.2 p * h p := first planted state _

theorem extendsRun_bind {α β : Type} (run : LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI))
    (next : α → LazyOracle.State FI EI → PMF (β × LazyOracle.State FI EI))
    (first : ExtendsRun run) (second : ∀ a, ExtendsRun (next a)) :
    ExtendsRun fun state => (run state).bind fun p => next p.1 p.2 := by
  intro state p member
  obtain ⟨q, inFirst, inSecond⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  exact (first state q inFirst).trans (second q.1 q.2 p inSecond)

theorem couples_map {α β : Type} (run : LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI)) (f : α → β)
    (first : Couples run) : Couples fun state => (run state).map fun p => (f p.1, p.2) := by
  intro planted state h
  rw [tsum_map_mul, tsum_map_mul]
  exact first planted state (fun p => h (f p.1, p.2))

theorem extendsRun_map {α β : Type} (run : LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI)) (f : α → β)
    (first : ExtendsRun run) : ExtendsRun fun state => (run state).map fun p => (f p.1, p.2) := by
  intro state p member
  obtain ⟨q, inFirst, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  rw [← same]
  exact first state q inFirst

/-! ### 4. The lazy hash query -/

section Query

variable [DecidableEq FI] [DecidableEq EI]

/-- **A lazy hash query on a merge** at a point `σ₁` does not store is the private query, merged. -/
theorem query_hash_merge (planted state : LazyOracle.State FI EI) (x : BaseField)
    (fresh : planted.hash.lookup x = none) :
    LazyOracle.query (.hash x) (mergeState planted state) =
      (LazyOracle.query (.hash x) state).map fun p => (p.1, mergeState planted p.2) := by
  unfold LazyOracle.query mergeState
  simp only
  unfold HashTable.query
  rw [lookup_append_of_none _ _ _ fresh]
  cases found : state.hash.lookup x with
  | some v =>
    simp only [Draw.distribution, PMF.pure_map]
  | none =>
    simp only [Draw.distribution, PMF.map_comp]
    rfl

/-- A hash-table query returns the table itself (the key stored) or the table with the key prepended. -/
theorem hashQuery_support (table : HashTable BaseField (Fintype.card (Block × Block))) (x : BaseField)
    (a : Fin (Fintype.card (Block × Block)) × HashTable BaseField (Fintype.card (Block × Block)))
    (member : a ∈ (table.query Fintype.card_pos x).distribution.support) :
    (a.2 = table ∧ x ∈ table.map Prod.fst) ∨ a.2 = (x, a.1) :: table := by
  unfold HashTable.query at member
  cases found : table.lookup x with
  | some v =>
    rw [found] at member
    simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact Or.inl ⟨rfl, mem_keys_of_lookup table x v found⟩
  | none =>
    rw [found] at member
    simp only [Draw.distribution, PMF.mem_support_map_iff] at member
    obtain ⟨value, -, same⟩ := member
    subst same
    exact Or.inr rfl

/-- The lazy hash query extends the state and stores its point. -/
theorem query_hash_support (state : LazyOracle.State FI EI) (x : BaseField)
    (p : (Block × Block) × LazyOracle.State FI EI)
    (member : p ∈ (LazyOracle.query (.hash x) state).support) :
    Extends state p.2 ∧ x ∈ storedPoints p.2 := by
  unfold LazyOracle.query at member
  simp only at member
  obtain ⟨a, inQuery, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  subst same
  rcases hashQuery_support state.hash x a inQuery with ⟨kept, stored⟩ | added
  · refine ⟨⟨[], by simpa using kept, rfl, rfl⟩, ?_⟩
    show x ∈ a.2.map Prod.fst
    rw [kept]
    exact stored
  · refine ⟨⟨[(x, a.1)], by simpa using added, rfl, rfl⟩, ?_⟩
    show x ∈ a.2.map Prod.fst
    rw [added]
    exact List.mem_cons_self

theorem extendsRun_query_hash (x : BaseField) :
    ExtendsRun (FI := FI) (EI := EI) fun state => LazyOracle.query (.hash x) state :=
  fun state p member => (query_hash_support state x p member).1

/-- **The lazy hash query couples.** -/
theorem couples_query_hash (x : BaseField) :
    Couples (FI := FI) (EI := EI) fun state => LazyOracle.query (.hash x) state := by
  intro planted state h
  show ∑' p, LazyOracle.query (.hash x) state p * flagMerge planted h p ≤
    ∑' p, LazyOracle.query (.hash x) (mergeState planted state) p * h p
  cases found : planted.hash.lookup x with
  | none =>
    rw [query_hash_merge planted state x found, tsum_map_mul]
    exact ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (flagMerge_le planted h p)
  | some v =>
    have zero : ∑' p, LazyOracle.query (.hash x) state p * flagMerge planted h p = 0 := by
      refine ENNReal.tsum_eq_zero.mpr fun p => ?_
      by_cases member : p ∈ (LazyOracle.query (.hash x) state).support
      · have stored := (query_hash_support state x p member).2
        rw [flagMerge_meets planted h p ⟨x, stored, mem_keys_of_lookup planted.hash x v found⟩, mul_zero]
      · rw [PMF.apply_eq_zero_iff _ _ |>.mpr member, zero_mul]
    rw [zero]
    exact zero_le

/-! ### 5. Runs through a reader -/

theorem runReader_pure (reader : Reader FI EI) {α : Type} (value : α) :
    runReader reader (.pure value) = fun state => PMF.pure (value, state) := rfl

theorem runReader_query (reader : Reader FI EI) {α : Type} (input : ℕ) (next : Block × Block → CM α) :
    runReader reader (.query input next) =
      fun state => (reader input state).bind fun answered => runReader reader (next answered.1) answered.2 := rfl

theorem extendsRun_runReader (reader : Reader FI EI) (grows : ∀ input, ExtendsRun (reader input)) {α : Type} :
    ∀ program : CM α, ExtendsRun (runReader reader program)
  | .pure value => by
    rw [runReader_pure]
    exact extendsRun_pure value
  | .query input next => by
    rw [runReader_query]
    exact extendsRun_bind _ _ (grows input) fun answer => extendsRun_runReader reader grows (next answer)

/-- **A run through a coupling reader couples.** -/
theorem couples_runReader (reader : Reader FI EI) (couples : ∀ input, Couples (reader input))
    (grows : ∀ input, ExtendsRun (reader input)) {α : Type} : ∀ program : CM α, Couples (runReader reader program)
  | .pure value => by
    rw [runReader_pure]
    exact couples_pure value
  | .query input next => by
    rw [runReader_query]
    exact couples_bind _ _ (couples input) (fun answer => couples_runReader reader couples grows (next answer))
      fun answer => extendsRun_runReader reader grows (next answer)

theorem couples_lazyReader (input : ℕ) : Couples (FI := FI) (EI := EI) (lazyReader input) :=
  couples_query_hash (input : BaseField)

theorem extendsRun_lazyReader (input : ℕ) : ExtendsRun (FI := FI) (EI := EI) (lazyReader input) :=
  extendsRun_query_hash (input : BaseField)

/-! ### 6. Installations and the refill reader -/

theorem lookup_hash_isNone (state : LazyOracle.State FI EI) (x : BaseField) :
    (LazyOracle.lookup (.hash x) state).isNone = (state.hash.lookup x).isNone := by
  show (Option.map _ (state.hash.lookup x)).isNone = _
  cases state.hash.lookup x <;> rfl

theorem merge_lookup_isNone (planted state : LazyOracle.State FI EI) (x : BaseField) :
    ((mergeState planted state).hash.lookup x).isNone =
      ((state.hash.lookup x).isNone && (planted.hash.lookup x).isNone) := by
  show ((state.hash ++ planted.hash).lookup x).isNone = _
  rw [List.lookup_append]
  cases state.hash.lookup x <;> cases planted.hash.lookup x <;> rfl

/-- One installation step on a merge, at a point `σ₁` does not store, is the private step merged. -/
theorem programStep_merge (planted state : LazyOracle.State FI EI) (pair : BaseField × (Block × Block))
    (fresh : planted.hash.lookup pair.1 = none) :
    (LazyOracle.program (.hash pair.1) pair.2 (mergeState planted state)).getD (mergeState planted state) =
      mergeState planted ((LazyOracle.program (.hash pair.1) pair.2 state).getD state) := by
  unfold LazyOracle.program mergeState
  simp only
  rw [lookup_append_of_none _ _ _ fresh]
  split
  · rfl
  · rfl

theorem installPoints_merge (planted : LazyOracle.State FI EI) :
    ∀ (pairs : List (BaseField × (Block × Block))) (state : LazyOracle.State FI EI),
      (∀ pair ∈ pairs, planted.hash.lookup pair.1 = none) →
        installPoints pairs (mergeState planted state) = mergeState planted (installPoints pairs state)
  | [], _, _ => rfl
  | pair :: rest, state, fresh => by
    unfold installPoints
    rw [List.foldl_cons, List.foldl_cons, programStep_merge planted state pair (fresh pair List.mem_cons_self)]
    exact installPoints_merge planted rest _ fun other member => fresh other (List.mem_cons_of_mem _ member)

theorem programStep_extends (state : LazyOracle.State FI EI) (pair : BaseField × (Block × Block)) :
    Extends state ((LazyOracle.program (.hash pair.1) pair.2 state).getD state) ∧
      pair.1 ∈ storedPoints ((LazyOracle.program (.hash pair.1) pair.2 state).getD state) := by
  unfold LazyOracle.program
  simp only
  split
  · refine ⟨⟨[(pair.1, _)], rfl, rfl, rfl⟩, ?_⟩
    exact List.mem_cons_self
  · rename_i known
    refine ⟨Extends.refl state, ?_⟩
    obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp known
    exact mem_keys_of_lookup state.hash pair.1 v found

theorem installPoints_extends :
    ∀ (pairs : List (BaseField × (Block × Block))) (state : LazyOracle.State FI EI),
      Extends state (installPoints pairs state) ∧ ∀ pair ∈ pairs, pair.1 ∈ storedPoints (installPoints pairs state)
  | [], state => ⟨Extends.refl state, fun _ member => by simp at member⟩
  | pair :: rest, state => by
    unfold installPoints
    rw [List.foldl_cons]
    obtain ⟨grow, stored⟩ := programStep_extends state pair
    obtain ⟨growRest, storedRest⟩ := installPoints_extends rest
      ((LazyOracle.program (.hash pair.1) pair.2 state).getD state)
    refine ⟨grow.trans growRest, fun other member => ?_⟩
    rcases List.mem_cons.mp member with same | inRest
    · subst same
      exact storedPoints_extends growRest stored
    · exact storedRest other inRest

/-- **A well-sized layout**: every answer list the swapped law draws at a site has at least as many answers as the
site has points, so a refill installs every point of the site. -/
def WellSized (layout : SiteLayout) : Prop :=
  ∀ site answers, answers ∈ (layout.law site).support → layout.answers site ≤ answers.length

theorem sitePoints_length (layout : SiteLayout) (site : SiteId) (label : ℕ) :
    (sitePoints layout site label).length = layout.answers site := by
  cases site <;> simp [sitePoints, siteTags]

theorem untouched_merge (points : List BaseField) (planted state : LazyOracle.State FI EI) :
    untouched points (mergeState planted state) = (untouched points state && untouched points planted) := by
  unfold untouched
  induction points with
  | nil => rfl
  | cons point rest ih =>
    rw [List.all_cons, List.all_cons, List.all_cons, ih, lookup_hash_isNone, lookup_hash_isNone,
      lookup_hash_isNone, merge_lookup_isNone]
    cases (state.hash.lookup point).isNone <;> cases (planted.hash.lookup point).isNone <;>
      cases (rest.all fun point => (LazyOracle.lookup (.hash point) state).isNone) <;>
      cases (rest.all fun point => (LazyOracle.lookup (.hash point) planted).isNone) <;> rfl

theorem extendsRun_refillReader (layout : SiteLayout) (input : ℕ) :
    ExtendsRun (FI := FI) (EI := EI) (refillReader layout input) := by
  intro state p member
  unfold refillReader at member
  cases hsite : siteOf (input / 2 ^ 128) with
  | none =>
    rw [hsite] at member
    exact extendsRun_lazyReader input state p member
  | some site =>
    rw [hsite] at member
    dsimp only at member
    split at member
    · obtain ⟨answers, -, inLazy⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      exact (installPoints_extends _ state).1.trans (extendsRun_lazyReader input _ p inLazy)
    · exact extendsRun_lazyReader input state p member

/-- **The refill reader couples** (on a well-sized layout). -/
theorem couples_refillReader (layout : SiteLayout) (sized : WellSized layout) (input : ℕ) :
    Couples (FI := FI) (EI := EI) (refillReader layout input) := by
  intro planted state h
  show ∑' p, refillReader layout input state p * flagMerge planted h p ≤
    ∑' p, refillReader layout input (mergeState planted state) p * h p
  unfold refillReader
  cases hsite : siteOf (input / 2 ^ 128) with
  | none =>
    dsimp only
    exact couples_lazyReader input planted state h
  | some site =>
    dsimp only
    rw [untouched_merge]
    cases hs : untouched (sitePoints layout site (input % 2 ^ 128)) state with
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact couples_lazyReader input planted state h
    | true =>
      cases hp : untouched (sitePoints layout site (input % 2 ^ 128)) planted with
      | true =>
        simp only [Bool.and_self, ↓reduceIte]
        rw [tsum_bind_mul, tsum_bind_mul]
        refine ENNReal.tsum_le_tsum fun answers => mul_le_mul' le_rfl ?_
        have fresh : ∀ pair ∈ (sitePoints layout site (input % 2 ^ 128)).zip answers,
            planted.hash.lookup pair.1 = none := by
          rintro ⟨k, v⟩ member
          have inPoints := (List.of_mem_zip member).1
          have all := List.all_eq_true.mp hp k inPoints
          rw [lookup_hash_isNone] at all
          exact Option.isNone_iff_eq_none.mp all
        rw [installPoints_merge planted _ state fresh]
        exact couples_lazyReader input planted _ h
      | false =>
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨y, inPoints, touched⟩ : ∃ y ∈ sitePoints layout site (input % 2 ^ 128),
            ¬ (LazyOracle.lookup (.hash y) planted).isNone = true := by
          by_contra none
          have all : untouched (sitePoints layout site (input % 2 ^ 128)) planted = true :=
            List.all_eq_true.mpr fun y inPoints => by
              by_contra touched
              exact none ⟨y, inPoints, touched⟩
          rw [hp] at all
          exact Bool.noConfusion all
        rw [lookup_hash_isNone] at touched
        have notNone : planted.hash.lookup y ≠ none := fun eq => touched (Option.isNone_iff_eq_none.mpr eq)
        obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp notNone
        have zero : ∑' p, ((layout.law site).bind fun answers =>
            lazyReader input (installPoints ((sitePoints layout site (input % 2 ^ 128)).zip answers) state)) p *
              flagMerge planted h p = 0 := by
          rw [tsum_bind_mul]
          refine ENNReal.tsum_eq_zero.mpr fun answers => ?_
          by_cases drawn : answers ∈ (layout.law site).support
          · have long : (sitePoints layout site (input % 2 ^ 128)).length ≤ answers.length := by
              rw [sitePoints_length]
              exact sized site answers drawn
            have keys : ((sitePoints layout site (input % 2 ^ 128)).zip answers).map Prod.fst =
                sitePoints layout site (input % 2 ^ 128) := List.map_fst_zip long
            obtain ⟨pair, inZip, pairKey⟩ : ∃ pair ∈ (sitePoints layout site (input % 2 ^ 128)).zip answers,
                pair.1 = y := by
              rw [← keys] at inPoints
              exact List.mem_map.mp inPoints
            have stored := (installPoints_extends _ state).2 pair inZip
            rw [pairKey] at stored
            have meets : Meets planted
                (installPoints ((sitePoints layout site (input % 2 ^ 128)).zip answers) state) :=
              ⟨y, stored, mem_keys_of_lookup planted.hash y v found⟩
            rw [tsum_flagMerge_of_meets (lazyReader input) (extendsRun_lazyReader input) planted _ meets h,
              mul_zero]
          · rw [PMF.apply_eq_zero_iff _ _ |>.mpr drawn, zero_mul]
        rw [zero]
        exact zero_le

end Query

end

end Kriterion.CRT.Privacy.PublicFirst
