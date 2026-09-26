/-
**P7, the public-first hop, part 6: `M` is below `HW`** (`CrtMiddleBelow`; the CRT, hash-only form of xinshu's
`PublicFirst/Middle.lean` sections 2 to 4 and `PublicFirst/Private.lean`'s `discard_run`, generalized to an `HW` that
aborts on a failed collector program, F5).

`M` runs its stage 2 privately from the empty oracle; `HW` runs it on the stage-1 state `σ₁`. Stage by stage:

* the route-M replay (the refill reader, a lazy key query, the refill reader again) couples
  (`couples_routeMReplay`, from `Coupling.lean`); `M` flags a private replay that meets `σ₁`, so every later step
  reads a private state whose merge into `σ₁` is `HW`'s state;
* the rows and the collector draws are the same kernels in both games; an abort, and a failed private collector
  program, is a flag of `M`;
* a successful private collector program is `HW`'s successful program on the merge, unless the installed state
  meets `σ₁` (`programHashAll_some_merge`), in which case `M` flags it (a failed private program is also a failed
  program of `HW` on the merge, `programHashAll_none_merge`);
* off the curve `M` reads the shadow's program lazily (`lazyRun`), and the shadow's extra lazy reads run privately and flagged are dominated by the same reads on the merge
  (`couples_runReader`), and on the shared state reads whose answers are discarded do not change the adversary's stage
  2 (`discard_runReader`, from P3's eager/lazy `public_step` and `public_run_result`);
* the reveal flag only lowers `M`.

The one hypothesis is `WellSized E.layout` (the refill installs every point of a site).
-/

import Proof.Privacy.CRT.PublicFirst.Coupling
import Proof.Privacy.CRT.PublicFirst.Obligation
import Proof.Privacy.Phase3.Glue.OracleLaw

namespace Kriterion.CRT.Privacy.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step public_run_result)
open scoped ENNReal

noncomputable section

variable {FI EI : Type}

/-! ### 1. Discarded lazy reads (xinshu's `discard_run`, for a reader run) -/

theorem tsum_pure_mul_eq {β : Type} (b : β) (f : β → ℝ≥0∞) : ∑' o, PMF.pure b o * f o = f b := by
  classical
  rw [tsum_eq_single b fun o different => by rw [PMF.pure_apply, if_neg different, zero_mul]]
  rw [PMF.pure_apply, if_pos rfl, one_mul]

section Discard

variable [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The completion law survives one lazy query whose answer is discarded. -/
theorem query_bind_completion (request : PublicQuery FI EI) (state : LazyOracle.State FI EI) :
    (LazyOracle.query request state).bind (fun answer => publicCompletion answer.2) = publicCompletion state := by
  have step := congrArg (PMF.map Prod.snd) (public_step request state)
  rw [PMF.map_comp, PMF.map_bind] at step
  have handler : (Prod.snd ∘ publicHandler id request) = id := by
    funext complete
    rfl
  rw [handler, PMF.map_id] at step
  rw [step]
  congr 1
  funext answer
  rw [PMF.map_comp]
  exact (PMF.map_id _).symm

theorem lazyReader_bind_completion (input : ℕ) (state : LazyOracle.State FI EI) :
    (lazyReader input state).bind (fun answer => publicCompletion answer.2) = publicCompletion state :=
  query_bind_completion (.hash (input : BaseField)) state

/-- **Discarded lazy reads leave every later run's law unchanged.** -/
theorem discard_runReader {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FI EI) Result budget) {α : Type} (computation : CM α) :
    ∀ state, (runReader lazyReader computation state).bind (fun r => (LazyOracle.run program r.2).map Prod.fst)
      = (LazyOracle.run program state).map Prod.fst := by
  induction computation with
  | pure value =>
    intro state
    simp only [runReader, PMF.pure_bind]
  | query input next ih =>
    intro state
    show ((lazyReader input state).bind fun answered => runReader lazyReader (next answered.1) answered.2).bind
      (fun r => (LazyOracle.run program r.2).map Prod.fst) = _
    rw [PMF.bind_bind]
    simp_rw [ih]
    simp_rw [← public_run_result]
    rw [← PMF.bind_bind, lazyReader_bind_completion]

end Discard

/-! ### 2. Collector programs on a merge -/

section Programs

variable [DecidableEq FI] [DecidableEq EI]

theorem mergeState_empty (planted : LazyOracle.State FI EI) : mergeState planted LazyOracle.empty = planted := rfl

/-- A program at a point `σ₁` does not store, on a merge, is the private program merged. -/
theorem program_hash_merge (planted state : LazyOracle.State FI EI) (point : BaseField) (answer : Block × Block)
    (fresh : planted.hash.lookup point = none) :
    LazyOracle.program (.hash point) answer (mergeState planted state) =
      (LazyOracle.program (.hash point) answer state).map (mergeState planted) := by
  unfold LazyOracle.program mergeState
  simp only
  rw [lookup_append_of_none _ _ _ fresh]
  by_cases known : state.hash.lookup point = none
  · rw [if_pos known, if_pos known]
    rfl
  · rw [if_neg known, if_neg known]
    rfl

/-- A program at a point `σ₁` stores fails on a merge. -/
theorem program_hash_planted (planted state : LazyOracle.State FI EI) (point : BaseField) (answer : Block × Block)
    (v : Fin (Fintype.card (Block × Block))) (found : planted.hash.lookup point = some v) :
    LazyOracle.program (.hash point) answer (mergeState planted state) = none := by
  unfold LazyOracle.program mergeState
  simp only
  have stored : (state.hash ++ planted.hash).lookup point ≠ none := by
    rw [List.lookup_append, found]
    cases state.hash.lookup point <;> simp
  rw [if_neg stored]

/-- A program that fails privately fails on a merge. -/
theorem program_hash_none_merge (planted state : LazyOracle.State FI EI) (point : BaseField) (answer : Block × Block)
    (fail : LazyOracle.program (.hash point) answer state = none) :
    LazyOracle.program (.hash point) answer (mergeState planted state) = none := by
  unfold LazyOracle.program at fail
  simp only at fail
  by_cases known : state.hash.lookup point = none
  · rw [if_pos known] at fail
    exact absurd fail (by simp)
  · obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp known
    unfold LazyOracle.program mergeState
    simp only
    rw [lookup_append_of_some _ _ _ v found, if_neg (by simp)]

/-- A successful program extends the state and stores its point. -/
theorem program_hash_some (state next : LazyOracle.State FI EI) (point : BaseField) (answer : Block × Block)
    (done : LazyOracle.program (.hash point) answer state = some next) :
    Extends state next ∧ point ∈ storedPoints next := by
  unfold LazyOracle.program at done
  simp only at done
  by_cases known : state.hash.lookup point = none
  · rw [if_pos known] at done
    obtain rfl := Option.some.inj done
    exact ⟨⟨[(point, _)], rfl, rfl, rfl⟩, List.mem_cons_self⟩
  · rw [if_neg known] at done
    exact absurd done (by simp)

theorem programHashAll_extends :
    ∀ (requests : List (BaseField × (Block × Block))) (state next : LazyOracle.State FI EI),
      programHashAll requests state = some next → Extends state next ∧ ∀ r ∈ requests, r.1 ∈ storedPoints next
  | [], state, next, done => by
    have same : state = next := Option.some.inj done
    subst same
    exact ⟨Extends.refl _, fun _ member => by simp at member⟩
  | (point, answer) :: rest, state, next, done => by
    cases step : LazyOracle.program (.hash point) answer state with
    | none =>
      have fail : programHashAll ((point, answer) :: rest) state = none := by
        show (LazyOracle.program (.hash point) answer state).bind (programHashAll rest) = none
        rw [step]
        rfl
      rw [fail] at done
      exact absurd done (by simp)
    | some middle =>
      have done' : programHashAll rest middle = some next := by
        have unfolded : programHashAll ((point, answer) :: rest) state =
            (LazyOracle.program (.hash point) answer state).bind (programHashAll rest) := rfl
        rw [unfolded, step] at done
        exact done
      obtain ⟨grow, stored⟩ := program_hash_some state middle point answer step
      obtain ⟨growRest, storedRest⟩ := programHashAll_extends rest middle next done'
      refine ⟨grow.trans growRest, fun r member => ?_⟩
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        exact storedPoints_extends growRest stored
      · exact storedRest r inRest

/-- **A failed private program list fails on the merge.** -/
theorem programHashAll_none_merge (planted : LazyOracle.State FI EI) :
    ∀ (requests : List (BaseField × (Block × Block))) (state : LazyOracle.State FI EI),
      programHashAll requests state = none → programHashAll requests (mergeState planted state) = none
  | [], state, fail => absurd fail (by simp [programHashAll])
  | (point, answer) :: rest, state, fail => by
    have unfolded : ∀ σ : LazyOracle.State FI EI, programHashAll ((point, answer) :: rest) σ =
        (LazyOracle.program (.hash point) answer σ).bind (programHashAll rest) := fun _ => rfl
    rw [unfolded] at fail ⊢
    cases step : LazyOracle.program (.hash point) answer state with
    | none =>
      rw [program_hash_none_merge planted state point answer step]
      rfl
    | some middle =>
      rw [step] at fail
      have fail' : programHashAll rest middle = none := fail
      cases fresh : planted.hash.lookup point with
      | none =>
        rw [program_hash_merge planted state point answer fresh, step]
        exact programHashAll_none_merge planted rest middle fail'
      | some v =>
        rw [program_hash_planted planted state point answer v fresh]
        rfl

/-- **A successful private program list is the merge's, unless its result meets `σ₁`.** -/
theorem programHashAll_some_merge (planted : LazyOracle.State FI EI) :
    ∀ (requests : List (BaseField × (Block × Block))) (state next : LazyOracle.State FI EI),
      programHashAll requests state = some next →
        programHashAll requests (mergeState planted state) = some (mergeState planted next) ∨ Meets planted next
  | [], state, next, done => by
    have same : state = next := Option.some.inj done
    subst same
    exact Or.inl rfl
  | (point, answer) :: rest, state, next, done => by
    have unfolded : ∀ σ : LazyOracle.State FI EI, programHashAll ((point, answer) :: rest) σ =
        (LazyOracle.program (.hash point) answer σ).bind (programHashAll rest) := fun _ => rfl
    rw [unfolded] at done ⊢
    cases step : LazyOracle.program (.hash point) answer state with
    | none =>
      rw [step] at done
      exact absurd done (by simp)
    | some middle =>
      rw [step] at done
      have done' : programHashAll rest middle = some next := done
      cases fresh : planted.hash.lookup point with
      | none =>
        rw [program_hash_merge planted state point answer fresh, step]
        exact programHashAll_some_merge planted rest middle next done'
      | some v =>
        right
        have stored := (program_hash_some state middle point answer step).2
        have grow := (programHashAll_extends rest middle next done').1
        exact ⟨point, storedPoints_extends grow stored, mem_keys_of_lookup planted.hash point v fresh⟩

end Programs

/-! ### 3. The route-M replay couples -/

section Replay

variable [DecidableEq FI] [DecidableEq EI]

/-- The key query of route M's replay, with its answer typed as a pair of blocks. -/
def keyQuery (x : BaseField) (state : LazyOracle.State FI EI) : PMF ((Block × Block) × LazyOracle.State FI EI) :=
  LazyOracle.query (.hash x) state

/-- Route M's replay after the key: the non-collector mask sites through the reader. -/
def replayKeyed [FieldCertificate] {Public : Type} (view : RouteMView Public) (reader : Reader FI EI)
    (conv : view.ConvOut) (keyed : Block × Block) (state : LazyOracle.State FI EI) :
    PMF (ReplayOut × LazyOracle.State FI EI) :=
  (runReader reader (view.nonCollectorReplay keyed.1) state).map fun masked =>
    ({ delivered := view.delivered conv, masks := masked.1, key := keyed.1 }, masked.2)

/-- Route M's replay after the conversion blocks: the key query, then the non-collector mask sites. -/
def replayTail [FieldCertificate] {Public : Type} (view : RouteMView Public) (reader : Reader FI EI)
    (published : Public) (u : AffineInput) (conv : view.ConvOut) (state : LazyOracle.State FI EI) :
    PMF (ReplayOut × LazyOracle.State FI EI) :=
  (keyQuery (view.keyInput published u conv) state).bind fun keyed => replayKeyed view reader conv keyed.1 keyed.2

theorem routeMReplay_eq [FieldCertificate] {Public : Type} (view : RouteMView Public) (reader : Reader FI EI)
    (published : Public) (u : AffineInput) (labels : LamportSignature) :
    (fun state => routeMReplay view reader published u labels state) = fun state =>
      (runReader reader (view.replayConv published u labels) state).bind fun conv =>
        replayTail view reader published u conv.1 conv.2 := rfl

theorem couples_keyQuery (x : BaseField) : Couples (FI := FI) (EI := EI) (keyQuery x) :=
  couples_query_hash x

theorem extendsRun_keyQuery (x : BaseField) : ExtendsRun (FI := FI) (EI := EI) (keyQuery x) :=
  extendsRun_query_hash x

theorem couples_replayKeyed [FieldCertificate] {Public : Type} (view : RouteMView Public) (reader : Reader FI EI)
    (couples : ∀ input, Couples (reader input)) (grows : ∀ input, ExtendsRun (reader input))
    (conv : view.ConvOut) (keyed : Block × Block) : Couples (replayKeyed view reader conv keyed) :=
  couples_map (runReader reader (view.nonCollectorReplay keyed.1))
    (fun masks => ({ delivered := view.delivered conv, masks := masks, key := keyed.1 } : ReplayOut))
    (couples_runReader reader couples grows _)

theorem extendsRun_replayKeyed [FieldCertificate] {Public : Type} (view : RouteMView Public)
    (reader : Reader FI EI) (grows : ∀ input, ExtendsRun (reader input)) (conv : view.ConvOut)
    (keyed : Block × Block) : ExtendsRun (replayKeyed view reader conv keyed) :=
  extendsRun_map (runReader reader (view.nonCollectorReplay keyed.1))
    (fun masks => ({ delivered := view.delivered conv, masks := masks, key := keyed.1 } : ReplayOut))
    (extendsRun_runReader reader grows _)

theorem couples_replayTail [FieldCertificate] {Public : Type} (view : RouteMView Public) (reader : Reader FI EI)
    (couples : ∀ input, Couples (reader input)) (grows : ∀ input, ExtendsRun (reader input))
    (published : Public) (u : AffineInput) (conv : view.ConvOut) :
    Couples (replayTail view reader published u conv) :=
  couples_bind (keyQuery (view.keyInput published u conv)) (replayKeyed view reader conv)
    (couples_keyQuery _) (couples_replayKeyed view reader couples grows conv)
    (extendsRun_replayKeyed view reader grows conv)

theorem extendsRun_replayTail [FieldCertificate] {Public : Type} (view : RouteMView Public)
    (reader : Reader FI EI) (grows : ∀ input, ExtendsRun (reader input)) (published : Public) (u : AffineInput)
    (conv : view.ConvOut) : ExtendsRun (replayTail view reader published u conv) :=
  extendsRun_bind (keyQuery (view.keyInput published u conv)) (replayKeyed view reader conv)
    (extendsRun_keyQuery _) (extendsRun_replayKeyed view reader grows conv)

/-- **Route M's replay couples** when its reader does. -/
theorem couples_routeMReplay [FieldCertificate] {Public : Type} (view : RouteMView Public) (reader : Reader FI EI)
    (couples : ∀ input, Couples (reader input)) (grows : ∀ input, ExtendsRun (reader input))
    (published : Public) (u : AffineInput) (labels : LamportSignature) :
    Couples fun state => routeMReplay view reader published u labels state := by
  rw [routeMReplay_eq]
  exact couples_bind (runReader reader (view.replayConv published u labels)) (replayTail view reader published u)
    (couples_runReader reader couples grows _) (couples_replayTail view reader couples grows published u)
    (extendsRun_replayTail view reader grows published u)

end Replay

/-! ### 4. Weights after a stage 2 -/

section Weights

variable [DecidableEq FI] [DecidableEq EI]

/-- The adversary's stage 2 after `HW`'s stage 2, at one bit (an abort is `false`). -/
def contHW {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) :
    Option (LamportSignature × LazyOracle.State FI EI) → ℝ≥0∞
  | none => PMF.pure false b
  | some (labels, state) => ((LazyOracle.run (decide labels) state).map Prod.fst) b

theorem map_some_apply {α : Type} (ν : PMF α) (b : α) : (ν.map some) (some b) = ν b := by
  rw [PMF.map_apply, tsum_eq_single b]
  · simp
  · intro a different
    simp [Ne.symm different]

theorem weight_none {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (b : Bool) : stageTwoWeight decide b none = 0 := by
  simp [stageTwoWeight, stageTwoCont, PMF.pure_apply]

theorem weight_abort {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (b : Bool) : stageTwoWeight decide b (some none) = contHW decide b none := by
  simp [stageTwoWeight, stageTwoCont, contHW, PMF.pure_apply]

theorem weight_some {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (b : Bool) (labels : LamportSignature) (state : LazyOracle.State FI EI) :
    stageTwoWeight decide b (some (some (labels, state))) = contHW decide b (some (labels, state)) := by
  show ((LazyOracle.run (decide labels) state).map fun result => some result.1) (some b) =
    ((LazyOracle.run (decide labels) state).map Prod.fst) b
  rw [show (fun result : Bool × LazyOracle.State FI EI => some result.1) = some ∘ Prod.fst from rfl,
    ← PMF.map_comp, map_some_apply]

/-- The flagged ending is below the flagged merge weight. -/
theorem finish_le (planted : LazyOracle.State FI EI) (labels : LamportSignature) (reveal : Prop) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) {α : Type}
    (p : α × LazyOracle.State FI EI) :
    stageTwoWeight decide b (finishPrivate planted labels reveal p.2) ≤
      flagMerge planted (fun q => contHW decide b (some (labels, q.2))) p := by
  unfold finishPrivate flagMerge
  by_cases meets : Meets planted p.2
  · rw [if_pos (Or.inl meets), weight_none]
    exact zero_le
  · by_cases revealed : reveal
    · rw [if_pos (Or.inr revealed), weight_none]
      exact zero_le
    · rw [if_neg (fun either => either.elim meets revealed), if_neg meets, weight_some]

end Weights

/-! ### 5. The shadow step -/

section Shadow

variable [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

theorem discard_weight (labels : LamportSignature) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool)
    (extra : CM Unit) (state : LazyOracle.State FI EI) :
    ∑' p, runReader lazyReader extra state p * contHW decide b (some (labels, p.2)) =
      contHW decide b (some (labels, state)) := by
  have law := congrArg (fun distribution : PMF Bool => distribution b) (discard_runReader (decide labels) extra state)
  simp only [PMF.bind_apply] at law
  exact law

/-- **The shadow step**: the private flagged shadow, the reveal flag and the merge are dominated by `HW`, which runs
nothing. -/
theorem shadow_step (planted state : LazyOracle.State FI EI) (labels : LamportSignature) (extra : CM Unit)
    (reveal : LazyOracle.State FI EI → Prop) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) :
    ∑' o, ((runReader lazyReader extra state).map fun ran => finishPrivate planted labels (reveal ran.2) ran.2) o *
        stageTwoWeight decide b o ≤ contHW decide b (some (labels, mergeState planted state)) := by
  rw [tsum_map_mul]
  calc ∑' p, runReader lazyReader extra state p *
        stageTwoWeight decide b (finishPrivate planted labels (reveal p.2) p.2)
      ≤ ∑' p, runReader lazyReader extra state p *
          flagMerge planted (fun q => contHW decide b (some (labels, q.2))) p :=
        ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (finish_le planted labels _ decide b p)
    _ ≤ ∑' p, runReader lazyReader extra (mergeState planted state) p * contHW decide b (some (labels, p.2)) :=
        couples_runReader lazyReader couples_lazyReader extendsRun_lazyReader extra planted state _
    _ = contHW decide b (some (labels, mergeState planted state)) := discard_weight labels decide b extra _

/-- A shadow run from a state that already meets `σ₁` weighs nothing. -/
theorem shadow_meets (planted state : LazyOracle.State FI EI) (meets : Meets planted state)
    (labels : LamportSignature) (extra : CM Unit) (reveal : LazyOracle.State FI EI → Prop) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) :
    ∑' o, ((runReader lazyReader extra state).map fun ran => finishPrivate planted labels (reveal ran.2) ran.2) o *
        stageTwoWeight decide b o = 0 := by
  rw [tsum_map_mul]
  refine ENNReal.tsum_eq_zero.mpr fun p => ?_
  by_cases member : p ∈ (runReader lazyReader extra state).support
  · have still := meets_extends (extendsRun_runReader lazyReader extendsRun_lazyReader extra state p member) meets
    unfold finishPrivate
    rw [if_pos (Or.inl still), weight_none, mul_zero]
  · rw [PMF.apply_eq_zero_iff _ _ |>.mpr member, zero_mul]

/-- The shadow step averaged over the shadow coins. -/
theorem shadow_law_step {Coin : Type} (law : PMF Coin) (planted state : LazyOracle.State FI EI)
    (labels : LamportSignature) (extra : Coin → CM Unit) (reveal : Coin → LazyOracle.State FI EI → Prop)
    {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) :
    ∑' o, (law.bind fun coin => (runReader lazyReader (extra coin) state).map fun ran =>
        finishPrivate planted labels (reveal coin ran.2) ran.2) o * stageTwoWeight decide b o
      ≤ contHW decide b (some (labels, mergeState planted state)) := by
  rw [tsum_bind_mul]
  calc ∑' coin, law coin * ∑' o, ((runReader lazyReader (extra coin) state).map fun ran =>
          finishPrivate planted labels (reveal coin ran.2) ran.2) o * stageTwoWeight decide b o
      ≤ ∑' coin, law coin * contHW decide b (some (labels, mergeState planted state)) :=
        ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl
          (shadow_step planted state labels (extra coin) (reveal coin) decide b)
    _ = contHW decide b (some (labels, mergeState planted state)) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem shadow_law_meets {Coin : Type} (law : PMF Coin) (planted state : LazyOracle.State FI EI)
    (meets : Meets planted state) (labels : LamportSignature) (extra : Coin → CM Unit)
    (reveal : Coin → LazyOracle.State FI EI → Prop)
    {budget : ℕ} (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) :
    ∑' o, (law.bind fun coin => (runReader lazyReader (extra coin) state).map fun ran =>
        finishPrivate planted labels (reveal coin ran.2) ran.2) o * stageTwoWeight decide b o = 0 := by
  rw [tsum_bind_mul]
  refine ENNReal.tsum_eq_zero.mpr fun coin => ?_
  rw [shadow_meets planted state meets labels (extra coin) (reveal coin) decide b, mul_zero]

end Shadow

/-! ### 6. Stage 2, and `M` below `HW` -/

variable (E : CrtEntry FI EI)

section Stage2

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **`M`'s stage 2 is dominated by `HW`'s**, at every source, input, output and stage-1 state. -/
theorem stage2_dominates (sized : WellSized E.layout) (shadow : CrtShadow (viewHere E).Source FI EI)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (output : Option Point)
    (planted : LazyOracle.State FI EI) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget) (b : Bool) :
    ∑' o, middleStage2 E shadow lazyRun scalar source u output planted o * stageTwoWeight decide b o ≤
      ∑' o, (routeMSimulator (viewHere E) ((viewHere E).realRows scalar) (refillReader E.layout)).stage2 source u
        output planted o * contHW decide b o := by
  cases output with
  | none =>
    simp only [middleStage2, routeMSimulator, lazyRun]
    rw [tsum_pure_mul_eq]
    exact shadow_law_step shadow.law planted LazyOracle.empty _ _ _ decide b
  | some target =>
    simp only [middleStage2, routeMSimulator, collectorDraws]
    rw [tsum_bind_mul, tsum_bind_mul]
    refine le_trans (ENNReal.tsum_le_tsum fun ran => mul_le_mul' le_rfl ?_)
      (couples_routeMReplay (viewHere E) (refillReader E.layout) (couples_refillReader E.layout sized)
        (extendsRun_refillReader E.layout) _ u _ planted LazyOracle.empty _)
    unfold flagMerge
    by_cases meets : Meets planted ran.2
    · rw [if_pos meets, if_pos meets, tsum_pure_mul_eq, weight_none]
    · rw [if_neg meets, if_neg meets]
      beta_reduce
      rw [tsum_bind_mul, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun drawnRows => mul_le_mul' le_rfl ?_
      rcases drawnRows with _ | targets
      · dsimp only
        rw [tsum_pure_mul_eq, weight_none]
        exact zero_le
      · dsimp only
        rw [tsum_bind_mul, tsum_map_mul]
        refine ENNReal.tsum_le_tsum fun drawn => mul_le_mul' le_rfl ?_
        rcases drawn with _ | drawn
        · dsimp only
          rw [tsum_pure_mul_eq, weight_none]
          exact zero_le
        · dsimp only
          cases privately : programHashAll (programRequests ran.1.key drawn) ran.2 with
          | none =>
            dsimp only
            rw [tsum_pure_mul_eq, weight_none]
            exact zero_le
          | some installed =>
            dsimp only
            rcases programHashAll_some_merge planted _ _ _ privately with same | met
            · rw [same]
              exact shadow_law_step shadow.law planted installed _ _ _ decide b
            · rw [shadow_law_meets shadow.law planted installed met _ _ _ decide b]
              exact zero_le

end Stage2

/-- The abstract ideal game, unfolded into `PMF` binds (xinshu's `stagedGame`). -/
def stagedGame [FieldCertificate] {FI EI Randomness Public Key Oracle Aux : Type}
    [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FI EI Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : ℕ) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  (simulator.stage1 parameter LazyOracle.empty).bind fun first => match first with
  | none => PMF.pure false
  | some (circuit, state, oracle) =>
    (LazyOracle.run (adversary.chooseInput parameter circuit auxiliary) oracle).bind fun selected =>
      (simulator.stage2 state selected.1.1 (scheme.function scalar selected.1.1) selected.2).bind
        fun second => match second with
        | none => PMF.pure false
        | some (labels, updated) =>
          (LazyOracle.run (adversary.decide parameter circuit labels auxiliary selected.1.2) updated).map Prod.fst

/-- `abstractIdealGame` is `stagedGame` (xinshu's proof). -/
theorem abstractIdealGame_eq_staged [FieldCertificate] {FI EI Randomness Public Key Oracle Aux : Type}
    [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FI EI Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : ℕ) (scalar : NonZeroScalar) (auxiliary : Aux) :
    abstractIdealGame scheme simulator adversary parameter scalar auxiliary =
      stagedGame scheme simulator adversary parameter scalar auxiliary := by
  unfold abstractIdealGame stagedGame
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, liftM, monadLift,
    MonadLift.monadLift, OptionT.lift, Option.elimM, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map_bind, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext first
  rcases first with _ | ⟨circuit, state, oracle⟩
  · simp [PMF.pure_map]
  · simp only [Option.elim, PMF.map_bind]
    congr 1
    funext selected
    congr 1
    funext second
    rcases second with _ | ⟨labels, updated⟩
    · simp [PMF.pure_map]
    · simp only [PMF.map_bind, PMF.pure_map, Option.getD_some]
      exact PMF.bind_pure_comp Prod.fst _

section Below

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **`M` is below `HW`** at one instance. -/
theorem middle_below (sized : WellSized E.layout) (shadow : CrtShadow (viewHere E).Source FI EI)
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) :
    Below (publicFirstHybrid E adversary parameter scalar)
      (middleGame E shadow lazyRun adversary parameter scalar) := by
  intro b
  rw [middleGame_some_eq]
  unfold publicFirstHybrid
  rw [abstractIdealGame_eq_staged]
  unfold stagedGame
  rw [PMF.bind_apply]
  have stage1 : (routeMSimulator (FI := FI) (EI := EI) (viewHere E) ((viewHere E).realRows scalar)
      (refillReader E.layout)).stage1
      parameter LazyOracle.empty =
        (letI := (viewHere E).sourceFintype
         haveI := (viewHere E).sourceNonempty
         (PMF.uniformOfFintype (viewHere E).Source).map fun source =>
           some ((viewHere E).publish source, source, LazyOracle.empty)) := rfl
  rw [stage1]
  erw [tsum_map_mul]
  refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
  dsimp only
  rw [PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun selected => mul_le_mul' le_rfl ?_
  rw [PMF.bind_apply]
  refine le_trans (stage2_dominates E sized shadow scalar source selected.1.1 _ selected.2
    (fun labels => adversary.decide parameter ((viewHere E).publish source) labels () selected.1.2) b)
    (le_of_eq (tsum_congr fun o => ?_))
  congr 1
  rcases o with _ | ⟨labels, state⟩ <;> rfl

end Below

/-- **`CrtMiddleBelow`** (P7) on a well-sized layout. -/
theorem crtMiddleBelow_of (sized : WellSized E.layout)
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI) :
    CrtMiddleBelow E shadow := by
  intro _ _ _ _ _ _ adversary parameter scalar
  exact middle_below E sized shadow adversary parameter scalar

end

end Kriterion.CRT.Privacy.PublicFirst
