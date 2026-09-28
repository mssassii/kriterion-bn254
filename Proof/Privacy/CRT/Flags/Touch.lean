/-
**P8, `CrtTouchGuess` at `crtEntry` and `crtShadow` by route (B)**.

* `lazy_new_asked`: a lazy run stores only the old points and the inputs its path asks (on the final state's answers).
* `digest_new`: the shadow's digest on the curve stores, beyond the old points, `u`'s digest-label inputs and
  family-9 finals.
* `touchTable_on_le`, `touchAt_on_le`: on the curve, `M'`'s touch below the ideal view law, per table and per source,
  against a bound on the lazy digest run.
* `touchAt_off_le`: off the curve, `M'`'s touch as a sum over the swapped table, flagged by the ideal reveal.
-/

import Proof.Privacy.CRT.Flags.TouchSplit
import Proof.Privacy.CRT.Paths.LabelsViewed

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.Instance Kriterion.CRT.Privacy.H8
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

namespace Touch

/-! ### 1. What a lazy run stores -/

section Lazy

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

theorem hashQuery_cases (table : HashTable BaseField (Fintype.card (Block × Block))) (x : BaseField)
    (a : Fin (Fintype.card (Block × Block)) × HashTable BaseField (Fintype.card (Block × Block)))
    (member : a ∈ (table.query Fintype.card_pos x).distribution.support) :
    (table.lookup x = some a.1 ∧ a.2 = table) ∨ (table.lookup x = none ∧ a.2 = (x, a.1) :: table) := by
  unfold HashTable.query at member
  cases found : table.lookup x with
  | some v =>
    rw [found] at member
    simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    rw [found] at member
    simp only [Draw.distribution, PMF.mem_support_map_iff] at member
    obtain ⟨value, -, same⟩ := member
    subst same
    exact Or.inr ⟨rfl, rfl⟩

/-- **The lazy hash query**: the answer is stored at the point, old lookups are kept, and only the point is new. -/
theorem query_hash_facts (σ : LazyOracle.State FI EI) (x : BaseField) (p : (Block × Block) × LazyOracle.State FI EI)
    (member : p ∈ (LazyOracle.query (.hash x) σ).support) :
    LazyOracle.lookup (.hash x) p.2 = some p.1 ∧
      (∀ y v, LazyOracle.lookup (.hash y) σ = some v → LazyOracle.lookup (.hash y) p.2 = some v) ∧
      ∀ y ∈ storedPoints p.2, y ∈ storedPoints σ ∨ y = x := by
  unfold LazyOracle.query at member
  simp only at member
  obtain ⟨a, inQuery, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  subst same
  rcases hashQuery_cases σ.hash x a inQuery with ⟨found, kept⟩ | ⟨fresh, added⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp only [LazyOracle.lookup, kept, found]
      rfl
    · intro y v hv
      simpa only [LazyOracle.lookup, kept] using hv
    · intro y hy
      left
      simpa only [storedPoints, kept] using hy
  · refine ⟨?_, ?_, ?_⟩
    · simp only [LazyOracle.lookup, added, List.lookup, beq_self_eq_true]
      rfl
    · intro y v hv
      have ne : y ≠ x := by
        rintro rfl
        simp only [LazyOracle.lookup, fresh, Option.map_none] at hv
        cases hv
      have hne : (y == x) = false := by simpa using ne
      simp only [LazyOracle.lookup, added, List.lookup, hne] at hv ⊢
      exact hv
    · intro y hy
      simp only [storedPoints, added, List.map_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Or.inr rfl
      · exact Or.inl hy

/-- A lazy run keeps every old lookup. -/
theorem lazy_keeps {α : Type} (P : CM α) : ∀ (σ : LazyOracle.State FI EI),
    ∀ p ∈ (runReader lazyReader P σ).support,
      ∀ y v, LazyOracle.lookup (.hash y) σ = some v → LazyOracle.lookup (.hash y) p.2 = some v := by
  induction P with
  | pure value =>
    intro σ p member
    have same : p = (value, σ) := (PMF.mem_support_pure_iff _ _).mp member
    subst same
    exact fun _ _ h => h
  | query n next ih =>
    intro σ p member y v hv
    obtain ⟨a, inA, inRest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    have facts := query_hash_facts σ (n : BaseField) a inA
    exact ih a.1 a.2 p inRest y v (facts.2.1 y v hv)

/-- The answers a state holds, as a hash of the layer. -/
def ansOf (s : LazyOracle.State FI EI) : HashN := fun n => (LazyOracle.lookup (.hash (n : BaseField)) s).getD (0, 0)

/-- **A lazy run stores only the old points and the inputs its path asks**, on the final state's answers. -/
theorem lazy_new_asked {α : Type} (P : CM α) : ∀ (σ : LazyOracle.State FI EI),
    ∀ p ∈ (runReader lazyReader P σ).support, ∀ x ∈ storedPoints p.2,
      x ∈ storedPoints σ ∨ ∃ n ∈ Align.asked (ansOf p.2) P, x = (n : BaseField) := by
  induction P with
  | pure value =>
    intro σ p member x hx
    have same : p = (value, σ) := (PMF.mem_support_pure_iff _ _).mp member
    subst same
    exact Or.inl hx
  | query n next ih =>
    intro σ p member x hx
    obtain ⟨a, inA, inRest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    have facts := query_hash_facts σ (n : BaseField) a inA
    have ans : ansOf p.2 n = a.1 := by
      unfold ansOf
      rw [lazy_keeps (next a.1) a.2 p inRest _ _ facts.1]
      rfl
    have askedEq : Align.asked (ansOf p.2) (FreeQuery.query n next) =
        n :: Align.asked (ansOf p.2) (next a.1) := by
      show n :: Align.asked (ansOf p.2) (next (ansOf p.2 n)) = _
      rw [ans]
    rw [askedEq]
    rcases ih a.1 a.2 p inRest x hx with old | ⟨m, hm, same⟩
    · rcases facts.2.2 x old with older | same
      · exact Or.inl older
      · exact Or.inr ⟨n, List.mem_cons_self, same⟩
    · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, same⟩

end Lazy

/-! ### 2. `M'`'s touch below the ideal view law, per source -/

section Middle

variable {FI EI : Type} (E : CrtEntry FI EI)
variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

omit [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem touchWeight_none (x : BaseField) : touchWeight x (none : Outcome FI EI) = 0 := by
  simp [touchWeight, storedOf]

omit [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- The touch of a finished private outcome at the empty stage-1 state is at most the point's storage. -/
theorem touchWeight_finish_le (labels : LamportSignature) (reveal : Prop) (state : LazyOracle.State FI EI)
    (x : BaseField) : touchWeight x (finishPrivate LazyOracle.empty labels reveal state) ≤ ind (x ∈ storedPoints state) := by
  unfold finishPrivate
  split_ifs
  · rw [touchWeight_none]
    exact zero_le
  · have same : storedPoints (mergeState (LazyOracle.empty : LazyOracle.State FI EI) state) = storedPoints state := by
      simp [storedPoints, mergeState, LazyOracle.empty]
    simp only [touchWeight, storedOf, ind, same]
    split_ifs <;> simp_all

/-- **On the curve, at one table**: `M'`'s touch, weighted by `w`, is below the ideal side against any `G` above `w`
times the digest's storage of the point after the collector programs. -/
theorem touchTable_on_le (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (Q : Point) (x : BaseField)
    (w : ℝ≥0∞) (G : List (BMR.Collector × ((Block × Block × Block) × Block)) → ℝ≥0∞)
    (flag : Laws.OnFlag E shadow reveal source u) (table : TagTable)
    (bound : ∀ (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
      (installed : LazyOracle.State FI EI) (coin : shadow.Coin), drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (Laws.outOf E table source u).key drawn) (Laws.finOf E table source u) =
        some installed →
      w * ∑' p, runReader lazyReader (shadow.onCurve source u coin) installed p * ind (x ∈ storedPoints p.2) ≤
        G drawn) :
    ∑' o, Laws.middleContOn E shadow scalar source u Q LazyOracle.empty
        (Laws.outOf E table source u, Laws.finOf E table source u) o * (w * touchWeight x o) ≤
      Laws.expOn E T reveal scalar u Q source table G := by
  unfold Laws.middleContOn Laws.expOn
  dsimp only
  have notMeets : ¬ Meets (LazyOracle.empty : LazyOracle.State FI EI) (Laws.finOf E table source u) := by
    rintro ⟨y, -, hy⟩
    simp [storedPoints, LazyOracle.empty] at hy
  rw [if_neg notMeets, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun drawnRows => mul_le_mul' le_rfl ?_
  rcases drawnRows with _ | targets
  · dsimp only
    rw [tsum_pure_mul_eq, touchWeight_none, mul_zero]
  · dsimp only
    rw [Laws.collectorDraws_eq, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun d => ?_
    rcases d with _ | drawn
    · dsimp only
      rw [tsum_pure_mul_eq, touchWeight_none, mul_zero, mul_zero]
    · dsimp only
      by_cases zero : collectorDrawsOf E (collectorMasks u (Laws.outOf E table source u)
          ((viewHere E).gammaOf ((viewHere E).publish source)) targets) (some drawn) = 0
      · rw [zero, zero_mul, zero_mul]
      refine mul_le_mul' le_rfl ?_
      have keys : drawn.map Prod.fst = collectorList :=
        Laws.drawAll_keys _ _ drawn ((PMF.mem_support_iff _ _).mpr zero)
      cases privately : programHashAll (programRequests (Laws.outOf E table source u).key drawn)
          (Laws.finOf E table source u) with
      | none =>
          dsimp only
          rw [tsum_pure_mul_eq, touchWeight_none, mul_zero]
          exact zero_le
      | some installed =>
          dsimp only
          by_cases rv : reveal source u targets (programmedTable table drawn)
          · rw [if_pos rv, tsum_bind_mul]
            refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun coin => ?_)
            rw [tsum_map_mul]
            refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun p => ?_)
            by_cases member : p ∈ (runReader lazyReader (shadow.onCurve source u coin) installed).support
            · unfold finishPrivate
              rw [if_pos (Or.inr (flag table targets drawn installed coin privately p member rv)),
                touchWeight_none, mul_zero, mul_zero]
            · rw [PMF.apply_eq_zero_iff _ _ |>.mpr member, zero_mul]
          · rw [if_neg rv, tsum_bind_mul]
            calc ∑' coin, shadow.law coin * ∑' o, ((runReader lazyReader (shadow.onCurve source u coin) installed).map
                  fun shadowed => finishPrivate LazyOracle.empty ((viewHere E).labels source u)
                    (shadow.revealOn source u targets coin shadowed.2) shadowed.2) o * (w * touchWeight x o)
                ≤ ∑' coin, shadow.law coin * G drawn := by
                  refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
                  rw [tsum_map_mul]
                  calc ∑' p, runReader lazyReader (shadow.onCurve source u coin) installed p *
                        (w * touchWeight x (finishPrivate LazyOracle.empty ((viewHere E).labels source u)
                          (shadow.revealOn source u targets coin p.2) p.2))
                      ≤ ∑' p, runReader lazyReader (shadow.onCurve source u coin) installed p *
                          (w * ind (x ∈ storedPoints p.2)) :=
                        ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl
                          (mul_le_mul' le_rfl (touchWeight_finish_le _ _ _ x))
                    _ = w * ∑' p, runReader lazyReader (shadow.onCurve source u coin) installed p *
                          ind (x ∈ storedPoints p.2) := by
                        rw [← ENNReal.tsum_mul_left]
                        exact tsum_congr fun p => by ring
                    _ ≤ G drawn := bound drawn installed coin keys privately
              _ = G drawn := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **On the curve, at one source**: `M'`'s touch, weighted by `w`, is below the ideal view law against `F'`, for any
`F'` whose value at the view of a table and draws is above `w` times the digest's storage of the point. -/
theorem touchAt_on_le (T : CrtTable) (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (Q : Point) (x : BaseField)
    (facts : Laws.RefillLayoutFacts E.layout) (points : Laws.PointFacts E.layout)
    (keyNonSite : ∀ conv, siteOf (((viewHere E).keyInput ((viewHere E).publish source) u conv).val / 2 ^ 128) = none)
    (path : Laws.RefillPath E.layout ∅ (LazyOracle.empty : LazyOracle.State FI EI) (Laws.replayOf E source u))
    (canon : Laws.Canonical E.layout (Laws.replayOf E source u))
    (flag : Laws.OnFlag E shadow reveal source u) (w : ℝ≥0∞) (F : CoreView E T u → ℝ≥0∞)
    (bound : ∀ (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
      (installed : LazyOracle.State FI EI) (coin : shadow.Coin), drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (Laws.outOf E table source u).key drawn) (Laws.finOf E table source u) =
        some installed →
      w * ∑' p, runReader lazyReader (shadow.onCurve source u coin) installed p * ind (x ∈ storedPoints p.2) ≤
        F (Laws.viewOf E T source u table drawn)) :
    ∑' o, middleStage2 E shadow offRun scalar source u (some Q) LazyOracle.empty o * (w * touchWeight x o) ≤
      ∑' o, Laws.idealOnAt E T reveal scalar u Q source o * Laws.optOf E T u F o := by
  rw [Laws.middleStage2_on E shadow offRun scalar source u Q LazyOracle.empty facts points keyNonSite path canon,
    tsum_bind_mul, Laws.idealOnAt_eq, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl ?_
  rw [Laws.idealBody_tsum]
  exact touchTable_on_le E T shadow reveal scalar source u Q x w
    (fun drawn => F (Laws.viewOf E T source u table drawn)) flag table
    fun drawn installed coin keys prog => bound table drawn installed coin keys prog

omit [Fintype FI] [Fintype EI] in
/-- **Off the curve, at one source**: `M'`'s touch, weighted by `w`, is a sum over the shadow's coin and the swapped
table of the point's storage in the final private state, off the ideal reveal. -/
theorem touchAt_off_le (shadow : CrtShadow (viewHere E).Source FI EI)
    (reveal : (viewHere E).Source → AffineInput → TagTable → Prop)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (x : BaseField) (w : ℝ≥0∞)
    (flag : Laws.OffFlag E shadow reveal source u) :
    ∑' o, middleStage2 E shadow (tableRun (swappedTableLaw E.layout)) scalar source u none LazyOracle.empty o *
        (w * touchWeight x o) ≤
      ∑' coin, shadow.law coin * ∑' t, swappedTableLaw E.layout t *
        (ind (¬ reveal source u t) * (w * ind (x ∈ storedPoints (Laws.offFinOf E shadow source u coin t)))) := by
  rw [Laws.middleStage2_none, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
  rw [tsum_map_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl ?_
  rw [tsum_pure_mul_eq]
  dsimp only
  by_cases rv : reveal source u t
  · unfold finishPrivate
    rw [if_pos (Or.inr (flag coin t rv)), touchWeight_none, mul_zero]
    exact zero_le
  · rw [show ind (¬ reveal source u t) = 1 from ind_of rv, one_mul]
    exact mul_le_mul' le_rfl (touchWeight_finish_le _ _ _ x)

end Middle

/-! ### 3. The ideal view law, summed over the source, and the real law -/

section Real

variable {FI EI : Type} (E : CrtEntry FI EI)
variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
theorem tsum_some_eq (T : CrtTable) (u : AffineInput) (μ : PMF (Option (CoreView E T u))) (F : CoreView E T u → ℝ≥0∞) :
    ∑' v, μ (some v) * F v = ∑' o, μ o * Laws.optOf E T u F o := by
  rw [tsum_option _ ENNReal.summable]
  simp [Laws.optOf]

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- **On the curve, the per-source ideal laws average to `idealAt`.** -/
theorem idealOn_sum (T : CrtTable) (revealOn : RevealOn E) (revealOff : RevealOff E) (scalar : NonZeroScalar)
    (u : AffineInput) (Q : Point) (onCurve : (E.scheme inferInstance inferInstance).function scalar u = some Q)
    (F : CoreView E T u → ℝ≥0∞) :
    (letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        ∑' o, Laws.idealOnAt E T revealOn scalar u Q source o * Laws.optOf E T u F o) =
      ∑' v, idealAt E T revealOn revealOff scalar u (some v) * F v := by
  rw [tsum_some_eq]
  unfold idealAt
  rw [onCurve]
  dsimp only
  rw [Laws.idealCore_eq, tsum_bind_mul]

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- **Off the curve, the per-source ideal laws average to `idealAt`.** -/
theorem idealOff_sum (T : CrtTable) (revealOn : RevealOn E) (revealOff : RevealOff E) (scalar : NonZeroScalar)
    (u : AffineInput) (offCurve : (E.scheme inferInstance inferInstance).function scalar u = none)
    (F : CoreView E T u → ℝ≥0∞) :
    (letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        ∑' o, Laws.idealOffAt E T revealOff u source o * Laws.optOf E T u F o) =
      ∑' v, idealAt E T revealOn revealOff scalar u (some v) * F v := by
  rw [tsum_some_eq]
  unfold idealAt
  rw [offCurve]
  dsimp only
  rw [Laws.idealCoreOff_eq, tsum_bind_mul]

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- The ideal law off the curve at one source, as a sum over the swapped table. -/
theorem idealOffAt_tsum (T : CrtTable) (reveal : (viewHere E).Source → AffineInput → TagTable → Prop)
    (u : AffineInput) (source : (viewHere E).Source) (F : CoreView E T u → ℝ≥0∞) :
    ∑' o, Laws.idealOffAt E T reveal u source o * Laws.optOf E T u F o =
      ∑' t, swappedTableLaw E.layout t * (ind (¬ reveal source u t) * F (Laws.offView E T source u t)) := by
  unfold Laws.idealOffAt
  rw [tsum_map_mul]
  refine tsum_congr fun t => congrArg _ ?_
  by_cases rv : reveal source u t
  · rw [if_pos rv]
    unfold ind
    rw [if_neg (not_not.mpr rv), zero_mul]
    rfl
  · rw [if_neg rv, ind_of rv, one_mul]
    rfl

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- **Through the core row to the real law**: the ideal law against `F` is below the swapped tape against any `G`
above `F` at the real view off the doubling. -/
theorem core_to_real (T : CrtTable) (revealOn : RevealOn E) (revealOff : RevealOff E)
    (core : CrtCoreBelow E T revealOn revealOff) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (F : CoreView E T u → ℝ≥0∞) (G : TableTape E → ℝ≥0∞)
    (above : ∀ tape, ¬ Doubling E scalar tape u → F (realView E T parameter scalar u tape) ≤ G tape) :
    ∑' v, idealAt E T revealOn revealOff scalar u (some v) * F v ≤ ∑' tape, swappedTableTape E tape * G tape := by
  calc ∑' v, idealAt E T revealOn revealOff scalar u (some v) * F v
      ≤ ∑' v, realCore E T parameter scalar u (some v) * F v :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul' (core parameter scalar u v) le_rfl
    _ = ∑' o, realCore E T parameter scalar u o * Laws.optOf E T u F o := tsum_some_eq E T u _ F
    _ ≤ ∑' tape, swappedTableTape E tape * G tape := by
        unfold realCore
        rw [tsum_map_mul]
        refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
        by_cases d : Doubling E scalar tape u
        · rw [if_pos d]
          exact zero_le
        · rw [if_neg d]
          exact above tape d

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
/-- The real view's published value is the stage-one view. -/
theorem realView_fst (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape E) :
    (realView E T parameter scalar u tape).1 = stageOneView E parameter scalar tape := rfl

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
open Classical in
theorem tsum_fiber {X V : Type} (f : X → V) (g : X → ℝ≥0∞) :
    ∑' x, g x = ∑' v, ∑' x, if f x = v then g x else 0 := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (f x) fun v different => if_neg (Ne.symm different), if_pos rfl]

omit [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI] in
open Classical in
/-- **The stage-one guess in the weight form.** -/
theorem stageOne_weight (ε : ℝ≥0∞) (one : CrtStageOneGuess E ε) (parameter : ℕ) (scalar : NonZeroScalar)
    (query : PublicQuery FI EI) (weight : E.Public → ℝ≥0∞) :
    ∑' tape, swappedTableTape E tape * (weight (stageOneView E parameter scalar tape) *
        ind (Touches (garblerEntries E parameter scalar tape) query)) ≤
      ε * ∑' tape, swappedTableTape E tape * weight (stageOneView E parameter scalar tape) := by
  set μ := swappedTableTape E
  set sv := stageOneView E parameter scalar
  have left : ∑' tape, μ tape * (weight (sv tape) * ind (Touches (garblerEntries E parameter scalar tape) query)) =
      ∑' view, weight view * μ.toOuterMeasure {tape | sv tape = view ∧
        Touches (garblerEntries E parameter scalar tape) query} := by
    rw [tsum_fiber sv]
    refine tsum_congr fun view => ?_
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun tape => ?_
    unfold ind
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases same : sv tape = view
    · subst same
      by_cases touch : Touches (garblerEntries E parameter scalar tape) query
      · simp [touch]
        ring
      · simp [touch]
    · simp [same]
  have right : ∑' tape, μ tape * weight (sv tape) = ∑' view, weight view * μ.toOuterMeasure {tape | sv tape = view} := by
    rw [tsum_fiber sv]
    refine tsum_congr fun view => ?_
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun tape => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases same : sv tape = view
    · subst same
      simp only [if_true]
      ring
    · simp [same]
  rw [left, right, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun view => ?_
  calc weight view * μ.toOuterMeasure {tape | sv tape = view ∧ Touches (garblerEntries E parameter scalar tape) query}
      ≤ weight view * (ε * μ.toOuterMeasure {tape | sv tape = view}) := mul_le_mul' le_rfl (one parameter scalar view query)
    _ = ε * (weight view * μ.toOuterMeasure {tape | sv tape = view}) := by ring

end Real

/-! ### 4. The touch guess at `crtEntry` -/

section Crt

variable [FieldCertificate] [GroupCertificate]

theorem ind_mono {P R : Prop} (imp : P → R) : ind P ≤ ind R := by
  unfold ind
  split_ifs <;> simp_all

theorem tsum_law_le {C : Type} (μ : PMF C) (X : C → ℝ≥0∞) (R : ℝ≥0∞) (bound : ∀ c, X c ≤ R) :
    ∑' c, μ c * X c ≤ R :=
  calc ∑' c, μ c * X c ≤ ∑' c, μ c * R := ENNReal.tsum_le_tsum fun c => mul_le_mul' le_rfl (bound c)
    _ = R := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [FieldCertificate] [GroupCertificate] in
/-- A view entry's input has a visible tag. -/
theorem viewEntries_input_visible [FieldCertificate] [GroupCertificate] {FI EI : Type} (E : CrtEntry FI EI)
    (T : CrtTable) (u : AffineInput) (v : CoreView E T u) (x : BaseField)
    (member : x ∈ (viewEntries E T u v).map Laws.entryInput) : visTag T u (x.val / 2 ^ 128) = true := by
  obtain ⟨⟨q, a⟩, he, rfl⟩ := List.mem_map.mp member
  have keep := (List.mem_filter.mp he).2
  cases q with
  | hash y => exact keep
  | _ => simp at keep

/-- A family-9 point is no view entry's input. -/
theorem final_not_viewed (u : AffineInput) (v : CoreView crtEntry Entry.table u) (x : BaseField)
    (fam : tagFamily (x.val / 2 ^ 128) = 9) : x ∉ (viewEntries crtEntry Entry.table u v).map Laws.entryInput :=
  fun member => by
    have visible := viewEntries_input_visible crtEntry Entry.table u v x member
    rw [OffDecomp.visTag_final Entry.table u fam] at visible
    cases visible

/-- The finals off the curve are family-9 points. -/
theorem xsOf_family (source : (viewHere crtEntry).Source) (u : AffineInput) (t : TagTable) (x : BaseField)
    (member : x ∈ OffDecomp.xsOf source u t) : tagFamily (x.val / 2 ^ 128) = 9 := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp member
  obtain ⟨small, fam⟩ := OffDecomp.final_small _ n hn
  rw [small.1]
  exact fam

/-- **What the shadow's digest stores on the curve**, beyond the old points: `u`'s digest-label inputs and
family-9 finals. -/
theorem digest_new (source : (viewHere crtEntry).Source) (u : AffineInput) (installed : LazyOracle.State Empty Empty) :
    ∀ p ∈ (runReader lazyReader (crtShadowOnCurve source u) installed).support, ∀ x ∈ storedPoints p.2,
      x ∈ storedPoints installed ∨
        (∃ (c : Fin 2) (q : Fin coordinateBitCount),
          x = ((hashInput (Entry.labelsOf ((viewHere crtEntry).labels source u) c q)
            (digestLabelTag c.val q.val (coordBit u c q.val)) : ℕ) : BaseField)) ∨
        tagFamily (x.val / 2 ^ 128) = 9 := by
  intro p member x hx
  rcases lazy_new_asked _ installed p member x hx with old | ⟨n, hn, same⟩
  · exact Or.inl old
  · have split : Align.asked (ansOf p.2) (crtShadowOnCurve source u) =
        Align.asked (ansOf p.2)
            (digestKeyM coordinateBitCount (Entry.labelsOf ((viewHere crtEntry).labels source u)) u) ++
          OffDecomp.finalsAt (digestKey (ansOf p.2) coordinateBitCount
            (Entry.labelsOf ((viewHere crtEntry).labels source u)) u) := by
      unfold crtShadowOnCurve
      rw [Align.asked_bind, Align.asked_pure, List.append_nil, Align.asked_digestEvalM]
      rfl
    rw [split, List.mem_append, Align.asked_digestKeyM] at hn
    rcases hn with label | final
    · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_singleton] at label
      obtain ⟨c, q, rfl⟩ := label
      exact Or.inr (Or.inl ⟨c, q, same⟩)
    · obtain ⟨small, fam⟩ := OffDecomp.final_small _ n final
      right
      right
      rw [same, small.1]
      exact fam

open Classical in
/-- The weight of a view against the touch of `x`: the view's entries for a point off family 9, `1/2^128` on it. -/
def Fx (x : BaseField) (u : AffineInput) (v : CoreView crtEntry Entry.table u) : ℝ≥0∞ :=
  if tagFamily (x.val / 2 ^ 128) = 9 then ENNReal.ofReal (1 / 2 ^ 128)
  else ind (x ∈ (viewEntries crtEntry Entry.table u v).map Laws.entryInput)

open Classical in
/-- The weight of a tape against the touch of `x`: a garbler entry at `x` off family 9, `1/2^128` on it. -/
def Gx (parameter : ℕ) (scalar : NonZeroScalar) (x : BaseField) (tape : TableTape crtEntry) : ℝ≥0∞ :=
  if tagFamily (x.val / 2 ^ 128) = 9 then ENNReal.ofReal (1 / 2 ^ 128)
  else ind (Touches (garblerEntries crtEntry parameter scalar tape) (.hash x))

/-- **A real view's entry is a garbler entry** (off the doubling, `crtEntry_viewEntriesPerm`). -/
theorem viewed_touches (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape crtEntry) (u : AffineInput)
    (x : BaseField) (nd : ¬ Doubling crtEntry scalar tape u)
    (member : x ∈ (viewEntries crtEntry Entry.table u (realView crtEntry Entry.table parameter scalar u tape)).map
      Laws.entryInput) :
    Touches (garblerEntries crtEntry parameter scalar tape) (.hash x) := by
  obtain ⟨perm, hashes, -⟩ := Paths.crtEntry_viewEntriesPerm parameter scalar tape u nd
  have designed : x ∈ (designedEntries crtEntry Entry.table parameter scalar tape u).map Laws.entryInput :=
    (perm.map Laws.entryInput).mem_iff.mpr member
  obtain ⟨e, he, same⟩ := List.mem_map.mp designed
  obtain ⟨y, hy⟩ := hashes e he
  have filtered : e ∈ (garblerEntries crtEntry parameter scalar tape).filter fun entry =>
      crtDesigned Entry.table ⟨fun scalar tape => crtEntry.exceptional scalar tape.1⟩ scalar
        (tape.1, tapeOracle crtEntry tape) u entry := he
  refine List.mem_map.mpr ⟨e, List.mem_of_mem_filter filtered, ?_⟩
  obtain ⟨q, a⟩ := e
  simp only at hy
  subst hy
  exact congrArg PublicQuery.hash same

omit [FieldCertificate] [GroupCertificate] in
/-- The touch charge `1/2^w + 1/(p − 1)` (`w = labelBits = 101`) covers the full-width tail guess `1/2^128`. -/
theorem inv_le_touchCharge : (1 : ℝ) / 2 ^ 128 ≤ stageOneTouchCharge := by
  rw [stageOneTouchCharge_eq]
  have hashBound : (1 : ℝ) / 2 ^ 128 ≤ 1 / 2 ^ Kriterion.CRT.Narrow.labelBits := by
    norm_num [Kriterion.CRT.Narrow.labelBits]
  have nonneg : 0 ≤ 1 / ((BN254.baseFieldModulus : ℝ) - 1) := by
    unfold BN254.baseFieldModulus
    norm_num
  linarith

/-- **The common tail**: the ideal law against `weight * Fx` is below the charge times the swapped tape's weight. -/
theorem tail_le (core : CrtCoreBelow crtEntry Entry.table crtRevealOn crtRevealOff)
    (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge)) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (x : BaseField) (weight : crtEntry.Public → ℝ≥0∞) :
    ∑' v, idealAt crtEntry Entry.table crtRevealOn crtRevealOff scalar u (some v) * (weight v.1 * Fx x u v) ≤
      ENNReal.ofReal stageOneTouchCharge *
        ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
  refine le_trans (core_to_real crtEntry Entry.table crtRevealOn crtRevealOff core parameter scalar u _
    (fun tape => weight (stageOneView crtEntry parameter scalar tape) * Gx parameter scalar x tape)
    fun tape nd => ?_) ?_
  · rw [realView_fst crtEntry Entry.table parameter scalar u tape]
    refine mul_le_mul' le_rfl ?_
    unfold Fx Gx
    split_ifs
    · exact le_rfl
    · exact ind_mono fun member => viewed_touches parameter scalar tape u x nd member
  · unfold Gx
    by_cases fam : tagFamily (x.val / 2 ^ 128) = 9
    · simp only [if_pos fam]
      rw [show ∑' tape, swappedTableTape crtEntry tape * (weight (stageOneView crtEntry parameter scalar tape) *
            ENNReal.ofReal (1 / 2 ^ 128)) =
          ENNReal.ofReal (1 / 2 ^ 128) * ∑' tape, swappedTableTape crtEntry tape *
            weight (stageOneView crtEntry parameter scalar tape) by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun tape => by ring]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact inv_le_touchCharge
    · simp only [if_neg fam]
      exact stageOne_weight crtEntry _ one parameter scalar (.hash x) weight

end Crt

/-! ### 5. The join at `crtEntry` -/

/-- The `Fintype Empty` instance of `CrtOnFinalFresh` and `CrtDigestLabelsViewed` (elaborated with no local
instance). -/
abbrev finiteEmpty : Fintype Empty := @Fintype.ofFinite Empty inferInstance

section Join

variable [FieldCertificate] [GroupCertificate]

omit [FieldCertificate] [GroupCertificate] in
/-- `CrtOnFinalFresh` at any instances of `Fintype Empty` and `DecidableEq Empty`. -/
theorem onFresh_at (onFresh : CrtOnFinalFresh) (fi : Fintype Empty) (di : DecidableEq Empty)
    [field : FieldCertificate] [group : GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput) (Q : Point)
    (onCurve : (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q)
    (source : (viewHere crtEntry).Source) (table : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    letI := fi
    letI := di
    ∀ installed : LazyOracle.State Empty Empty, drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (Laws.outOf crtEntry table source u).key drawn)
          (Laws.finOf crtEntry table source u) = some installed →
      ∀ x : BaseField, tagFamily (x.val / 2 ^ 128) = 9 →
        (runReader lazyReader (crtShadowOnCurve source u) installed).toOuterMeasure {p | x ∈ storedPoints p.2}
          ≤ ENNReal.ofReal (1 / 2 ^ 128) := by
  have e1 : fi = finiteEmpty := Subsingleton.elim _ _
  have e2 : di = Classical.decEq Empty := Subsingleton.elim _ _
  subst e1 e2
  exact onFresh field group scalar u Q onCurve source table drawn

omit [FieldCertificate] [GroupCertificate] in
/-- `crtEntry_digestLabelsViewed` at any instances of `Fintype Empty` and `DecidableEq Empty`. -/
theorem labelsViewed_at (fi : Fintype Empty) (di : DecidableEq Empty) [field : FieldCertificate]
    [group : GroupCertificate] (u : AffineInput) (v : CoreView crtEntry Entry.table u) (c : Fin 2)
    (p : Fin coordinateBitCount) :
    letI := fi
    letI := di
    ((hashInput (Entry.labelsOf v.2.1 c p) (digestLabelTag c.val p.val (coordBit u c p.val)) : ℕ) : BaseField) ∈
      (viewEntries crtEntry Entry.table u v).map Laws.entryInput := by
  have e1 : fi = finiteEmpty := Subsingleton.elim _ _
  have e2 : di = Classical.decEq Empty := Subsingleton.elim _ _
  subst e1 e2
  exact Paths.crtEntry_digestLabelsViewed field group u v c p

/-- **The on-curve containment** from `OnDecomp`: after the collector programs, every stored point is an input of
the view's entries. -/
theorem installed_viewed {source : (viewHere crtEntry).Source} {u : AffineInput} {P : Finset (Fin (2 ^ 40))}
    {ds : List BaseField} (decomp : Laws.OnDecomp crtEntry Entry.table crtRevealOn source u P ds)
    (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (installed : LazyOracle.State Empty Empty) (keys : drawn.map Prod.fst = collectorList)
    (prog : programHashAll (programRequests (Laws.outOf crtEntry table source u).key drawn)
      (Laws.finOf crtEntry table source u) = some installed)
    (x : BaseField) (stored : x ∈ storedPoints installed) :
    x ∈ (viewEntries crtEntry Entry.table u (Laws.viewOf crtEntry Entry.table source u table drawn)).map
      Laws.entryInput := by
  obtain ⟨-, -, -, -, -, -, -, hashes, -, -, lookups⟩ := decomp
  rw [Laws.mem_storedPoints_iff, lookups table drawn installed keys prog x] at stored
  have restHashes : Laws.HashEntries (Laws.restEntries crtEntry Entry.table u ds
      (Laws.viewOf crtEntry Entry.table source u table drawn)) :=
    fun e he => hashes table drawn e (List.mem_of_mem_filter he)
  rcases (Laws.installEntries_isSome _ restHashes LazyOracle.empty x).mp stored with none | member
  · simp [LazyOracle.empty] at none
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨e, List.mem_of_mem_filter he, rfl⟩

/-- **The on-curve bound at one table**: the digest's storage of `x` after the collector programs is below `Fx`. -/
theorem on_store_le (onFresh : CrtOnFinalFresh)
    (decomp : ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
      (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
        ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField),
          Laws.OnDecomp crtEntry Kriterion.CRT.Entry.table crtRevealOn source u P ds)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point)
    (onCurve : (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q)
    (source : (viewHere crtEntry).Source) (x : BaseField) (table : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State Empty Empty)
    (keys : drawn.map Prod.fst = collectorList)
    (prog : programHashAll (programRequests (Laws.outOf crtEntry table source u).key drawn)
      (Laws.finOf crtEntry table source u) = some installed) :
    ∑' p, runReader lazyReader (crtShadowOnCurve source u) installed p * ind (x ∈ storedPoints p.2) ≤
      Fx x u (Laws.viewOf crtEntry Entry.table source u table drawn) := by
  have mass : ∑' p, runReader lazyReader (crtShadowOnCurve source u) installed p * ind (x ∈ storedPoints p.2) =
      (runReader lazyReader (crtShadowOnCurve source u) installed).toOuterMeasure {p | x ∈ storedPoints p.2} := by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun p => ?_
    unfold ind
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  unfold Fx
  split_ifs with fam
  · rw [mass]
    have h1 := onFresh_at onFresh inferInstance inferInstance scalar u Q onCurve source table drawn
    have h2 := h1 installed keys
    have h3 := h2 prog x fam
    refine le_trans (le_of_eq ?_) h3
    congr 1
  · by_cases viewed : x ∈ (viewEntries crtEntry Entry.table u
        (Laws.viewOf crtEntry Entry.table source u table drawn)).map Laws.entryInput
    · rw [ind_of viewed]
      exact tsum_law_le _ _ 1 fun p => by
        unfold ind
        split_ifs <;> simp
    · have absent : ∀ p ∈ (runReader lazyReader (crtShadowOnCurve source u) installed).support,
          x ∉ storedPoints p.2 := by
        intro p member stored
        rcases digest_new source u installed p member x stored with old | ⟨c, q, same⟩ | fam9
        · obtain ⟨P, ds, d⟩ := decomp scalar u Q onCurve source
          exact viewed (installed_viewed d table drawn installed keys prog x old)
        · subst same
          exact viewed (labelsViewed_at inferInstance inferInstance u (Laws.viewOf crtEntry Entry.table source u table drawn) c q)
        · exact fam fam9
      have zero : ∑' p, runReader lazyReader (crtShadowOnCurve source u) installed p *
          ind (x ∈ storedPoints p.2) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun p => ?_
        by_cases member : p ∈ (runReader lazyReader (crtShadowOnCurve source u) installed).support
        · unfold ind
          rw [if_neg (absent p member), mul_zero]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul]
      rw [zero]
      exact zero_le

/-- **The off-curve storage**: the final private state stores the view's entries' inputs and the finals. -/
theorem off_stored (source : (viewHere crtEntry).Source) (u : AffineInput) (off : validate u = false)
    (t : TagTable) (x : BaseField)
    (stored : x ∈ storedPoints (Laws.offFinOf crtEntry crtShadow source u () t)) :
    x ∈ (viewEntries crtEntry Entry.table u (Laws.offView crtEntry Entry.table source u t)).map Laws.entryInput ∨
      x ∈ OffDecomp.xsOf source u t := by
  obtain ⟨-, -, -, -, -, -, hashes, -, lookups⟩ := OffDecomp.crtOffDecomp source u off
  rw [Laws.mem_storedPoints_iff, lookups t x] at stored
  have allHashes : Laws.HashEntries (viewEntries crtEntry Entry.table u (Laws.offView crtEntry Entry.table source u t) ++
      Laws.tableEntries t (OffDecomp.xsOf source u t)) := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hashes t e h
    · exact Laws.tableEntries_hash t _ e h
  rcases (Laws.installEntries_isSome _ allHashes LazyOracle.empty x).mp stored with none | member
  · simp [LazyOracle.empty] at none
  · rw [List.map_append, List.mem_append, Laws.tableEntries_inputs] at member
    exact member

/-- **The off-curve bound at one source**, against the ideal law off the curve. -/
theorem off_source_le (offFresh : CrtOffFinalFresh) (u : AffineInput)
    (off : validate u = false) (source : (viewHere crtEntry).Source) (x : BaseField)
    (weight : crtEntry.Public → ℝ≥0∞) :
    ∑' coin, (crtShadow : CrtShadow (viewHere crtEntry).Source Empty Empty).law coin *
        ∑' t, swappedTableLaw crtEntry.layout t * (ind (¬ crtRevealOff source u t) *
          (weight ((viewHere crtEntry).publish source) *
            ind (x ∈ storedPoints (Laws.offFinOf crtEntry crtShadow source u coin t)))) ≤
      ∑' t, swappedTableLaw crtEntry.layout t * (ind (¬ crtRevealOff source u t) *
        (weight (Laws.offView crtEntry Entry.table source u t).1 *
          Fx x u (Laws.offView crtEntry Entry.table source u t))) := by
  refine tsum_law_le _ _ _ fun coin => ?_
  cases coin
  set w := weight ((viewHere crtEntry).publish source) with hw
  simp only
  unfold Fx
  by_cases fam : tagFamily (x.val / 2 ^ 128) = 9
  · simp only [if_pos fam]
    have pointwise : ∀ t, ind (x ∈ storedPoints (Laws.offFinOf crtEntry crtShadow source u () t)) ≤
        ind (x ∈ OffDecomp.xsOf source u t) := fun t => ind_mono fun stored => by
      rcases off_stored source u off t x stored with viewed | final
      · exact absurd viewed (final_not_viewed u _ x fam)
      · exact final
    calc ∑' t, swappedTableLaw crtEntry.layout t * (ind (¬ crtRevealOff source u t) *
            (w * ind (x ∈ storedPoints (Laws.offFinOf crtEntry crtShadow source u () t))))
        ≤ ∑' t, swappedTableLaw crtEntry.layout t * (ind (¬ crtRevealOff source u t) *
            (w * ind (x ∈ OffDecomp.xsOf source u t))) :=
          ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (pointwise t)))
      _ = w * ∑' t, swappedTableLaw crtEntry.layout t *
            (ind (¬ crtRevealOff source u t) * ind (x ∈ OffDecomp.xsOf source u t)) := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun t => by ring
      _ ≤ w * (ENNReal.ofReal (1 / 2 ^ 128) *
            ∑' t, swappedTableLaw crtEntry.layout t * ind (¬ crtRevealOff source u t)) :=
          mul_le_mul' le_rfl (offFresh _ _ source u off x fam)
      _ = ∑' t, swappedTableLaw crtEntry.layout t * (ind (¬ crtRevealOff source u t) *
            (w * ENNReal.ofReal (1 / 2 ^ 128))) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun t => by ring
  · simp only [if_neg fam]
    refine ENNReal.tsum_le_tsum fun t => mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
    refine ind_mono fun stored => ?_
    rcases off_stored source u off t x stored with viewed | final
    · exact viewed
    · exact absurd (xsOf_family source u t x final) fam

/-- The shadow's on-curve program (a projection lemma, rule 15). -/
theorem crtShadow_onCurve (source : (viewHere crtEntry).Source) (u : AffineInput)
    (coin : (crtShadow : CrtShadow (viewHere crtEntry).Source Empty Empty).Coin) :
    (crtShadow : CrtShadow (viewHere crtEntry).Source Empty Empty).onCurve source u coin =
      crtShadowOnCurve source u := by
  dsimp only [crtShadow]

/-- **The touch guess at the global instances.** -/
theorem touch_main (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge))
    (core : CrtCoreBelow crtEntry Entry.table crtRevealOn crtRevealOff)
    (decomp : ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
      (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
        ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField),
          Laws.OnDecomp crtEntry Kriterion.CRT.Entry.table crtRevealOn source u P ds)
    (onFresh : CrtOnFinalFresh) (offFresh : CrtOffFinalFresh) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (x : BaseField) (weight : crtEntry.Public → ℝ≥0∞) :
    (letI := (viewHere crtEntry).sourceFintype
     haveI := (viewHere crtEntry).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere crtEntry).Source source *
        (weight ((viewHere crtEntry).publish source) *
          touchAt crtEntry crtShadow (tableRun (swappedTableLaw crtEntry.layout)) scalar source u x))
      ≤ ENNReal.ofReal stageOneTouchCharge *
        ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
  refine le_trans ?_ (tail_le core one parameter scalar u x weight)
  cases output : (crtEntry.scheme inferInstance inferInstance).function scalar u with
  | some Q =>
    refine le_trans ?_ (le_of_eq (idealOn_sum crtEntry Entry.table crtRevealOn crtRevealOff scalar u Q output
      (fun v => weight v.1 * Fx x u v)))
    refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
    unfold touchAt
    rw [output, ← ENNReal.tsum_mul_left]
    refine le_trans (le_of_eq (tsum_congr fun o => mul_left_comm _ _ _)) ?_
    refine touchAt_on_le crtEntry Entry.table crtShadow (tableRun (swappedTableLaw crtEntry.layout)) crtRevealOn
      scalar source u Q x Laws.crtLayout_refill Laws.crtLayout_points
      (fun conv => Paths.replay_keyNonSite ((viewHere crtEntry).publish source) u conv)
      (Paths.replay_refillPath ((viewHere crtEntry).publish source) u ((viewHere crtEntry).labels source u) _)
      (Paths.replay_canonical ((viewHere crtEntry).publish source) u ((viewHere crtEntry).labels source u))
      (crtOnFlag source u) _ _ fun table drawn installed coin keys prog => ?_
    rw [crtShadow_onCurve]
    have h := on_store_le onFresh decomp scalar u Q output source x table drawn installed keys prog
    have pub : (Laws.viewOf crtEntry Entry.table source u table drawn).1 = (viewHere crtEntry).publish source := rfl
    rw [pub]
    refine mul_le_mul' le_rfl (le_trans (le_of_eq ?_) (le_trans h (le_of_eq ?_)))
    · congr 1
    · congr 1
  | none =>
    have off : validate u = false := by
      have decoded : decodePoint u = none := Option.map_eq_none_iff.mp output
      cases valid : validate u
      · rfl
      · exfalso
        simp [decodePoint, valid] at decoded
    refine le_trans ?_ (le_of_eq (idealOff_sum crtEntry Entry.table crtRevealOn crtRevealOff scalar u output
      (fun v => weight v.1 * Fx x u v)))
    refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
    unfold touchAt
    rw [output, ← ENNReal.tsum_mul_left, idealOffAt_tsum]
    refine le_trans (le_of_eq (tsum_congr fun o => mul_left_comm _ _ _)) ?_
    refine le_trans (touchAt_off_le crtEntry crtShadow crtRevealOff scalar source u x _
      (Laws.crtOffFlag source u)) ?_
    exact off_source_le offFresh u off source x weight

end Join

/-- The global `Fintype Empty` instance. -/
abbrev fintypeEmpty : Fintype Empty := inferInstance

/-- The global `DecidableEq Empty` instance. -/
abbrev decEqEmpty : DecidableEq Empty := inferInstance

/-- **The touch guess at any instances** of `Fintype Empty` and `DecidableEq Empty`. -/
theorem touch_at (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge))
    (core : CrtCoreBelow crtEntry Entry.table crtRevealOn crtRevealOff)
    (decomp : ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
      (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
        ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField),
          Laws.OnDecomp crtEntry Kriterion.CRT.Entry.table crtRevealOn source u P ds)
    (onFresh : CrtOnFinalFresh) (offFresh : CrtOffFinalFresh) (fi : Fintype Empty) (di : DecidableEq Empty)
    [field : FieldCertificate] [group : GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (x : BaseField) (weight : crtEntry.Public → ℝ≥0∞) :
    (letI := fi
     letI := di
     letI := (viewHere crtEntry).sourceFintype
     haveI := (viewHere crtEntry).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere crtEntry).Source source *
        (weight ((viewHere crtEntry).publish source) *
          touchAt crtEntry crtShadow (tableRun (swappedTableLaw crtEntry.layout)) scalar source u x))
      ≤ ENNReal.ofReal stageOneTouchCharge *
        ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
  have e1 : fi = fintypeEmpty := Subsingleton.elim _ _
  have e2 : di = decEqEmpty := Subsingleton.elim _ _
  subst e1 e2
  exact touch_main one core decomp onFresh offFresh parameter scalar u x weight

end Touch

open Touch in
/-- **The touch guess at `crtEntry`**: from the stage-one guess, the core row, the on-curve decomposition
(exactly `Laws.crtEntry_middleFactor`'s first argument: its containment of the private state after the collector
programs), and the freshness of the finals on and off the curve. -/
theorem crtTouchGuess (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge))
    (core : CrtCoreBelow crtEntry Entry.table crtRevealOn crtRevealOff)
    (decomp : ∀ [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
      (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
        ∀ source, ∃ (P : Finset (Fin (2 ^ 40))) (ds : List BaseField),
          Laws.OnDecomp crtEntry Kriterion.CRT.Entry.table crtRevealOn source u P ds)
    (onFresh : CrtOnFinalFresh) (offFresh : CrtOffFinalFresh) :
    CrtTouchGuess crtEntry crtShadow (ENNReal.ofReal stageOneTouchCharge) := by
  intro field group parameter scalar u x weight
  exact touch_at one core decomp onFresh offFresh fintypeEmpty _ parameter scalar u x weight

end

end Kriterion.CRT.Privacy.Flags
