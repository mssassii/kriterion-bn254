/-
**The hidden hop `G0U → G1U`** (row T1, P2a). The index types are empty (`[IsEmpty FI] [IsEmpty EI]`),
since with permutation indices the reduction fails through answer touches of inverse queries.

### The proof (xinshu's `hidden_advantage_le`, `Hidden/Reduction.lean`, on the table tape)

For every tape, `G0U` (the whole garbler transcript planted before stage 1) and `G1U` (stage 1 on the empty oracle,
the reached garbler entries installed at the input choice) both dominate one flagged sub-law: stage 1 on the empty
oracle, the designed-visible entries planted at the input choice, killed at a stage-1 touch of the garbler's entries
or a stage-2 touch of the entries the designed rule hides (xinshu's generic `eagerPlanted_ge`, `lateInstalled_ge`).
Two games dominating one flagged law are within its missing mass (`advantage_le_of_dominated`), which is the two
touch masses, each bounded by the union bound (`touch_mass_le`, stage 2 through `guess_bind`).

Differences from xinshu's proof: `G0U` is planted by definition (no eager-lazy step); the stage-1 start is the empty
oracle (hash-only: no EncPRF entries), so the stage-1 relation is `rel_plantAll_of_avoid` at the empty state; the
obligations count query touches, which with empty index types are exactly xinshu's touches of `extraOf` and
`dropAll` (`touches_extraOf`, `touches_dropAll`); the designed entries are not a sub-list of the reached ones by
definition, and `DesignedReached` supplies that inclusion. `GarblerDistinct` is not used.
-/

import Proof.Privacy.CRT.Hidden.Obligations
import Proof.Privacy.Phase3.Hidden.Guess

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

noncomputable section

namespace HiddenReduction

open Kriterion.ArgoMAC.Security.Phase3.Hidden (Extra extraOf dropAll plantAll plant flaggedMass eagerPlanted
  lateInstalled atBool expect expect_mono expect_add expect_map expect_bind expect_one_sub expect_le_one
  cleanWeight cleanWeight_le_one touch_mass_le guess_bind advantage_le_of_dominated runLog runLog_length
  Consistent Within Avoid rel_plantAll_of_avoid eagerPlanted_ge lateInstalled_ge flagged_sum flagged_total_ge
  hashPair expect_const outer_eq_expect)

/-! ### Identical until bad from an advantage bound (xinshu's `UntilBadIff.lean`, for the CRT `UntilBad`) -/

/-- A law on `Bool × Bool` from its four masses. -/
def flaggedLaw (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun outcome => match outcome with
    | (true, false) => downTrue
    | (true, true) => upTrue
    | (false, false) => downFalse
    | (false, true) => upFalse) (by
      rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
      simpa [add_comm, add_left_comm, add_assoc] using total)

theorem flaggedLaw_fst (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) (outcome : Bool) :
    (flaggedLaw upTrue upFalse downTrue downFalse total).map Prod.fst outcome
      = if outcome then downTrue + upTrue else downFalse + upFalse := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]
  cases outcome <;> simp [flaggedLaw, add_comm]

theorem flaggedLaw_bad (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) :
    (flaggedLaw upTrue upFalse downTrue downFalse total).toOuterMeasure badSet = upTrue + upFalse := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  simp [flaggedLaw, badSet, Set.indicator]

theorem pmf_bool_false (law : PMF Bool) : law false = 1 - law true := by
  have total := law.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at total
  have swapped : (1 : ℝ≥0∞) = law false + law true := by
    rw [← total]; ring
  exact (ENNReal.sub_eq_of_eq_add (PMF.apply_ne_top law _) swapped).symm

/-- A `PMF Bool` is determined by its mass at `true`. -/
theorem pmf_bool_ext {first second : PMF Bool} (same : first true = second true) : first = second := by
  refine PMF.ext fun outcome => ?_
  cases outcome
  · rw [pmf_bool_false first, pmf_bool_false second, same]
  · exact same

/-- **Every advantage bound is an identical-until-bad pair** (the CRT `UntilBad`). -/
theorem untilBad_of_advantage_le {first second : PMF Bool} {error : ℝ}
    (bound : Assumptions.advantage first second ≤ error) : UntilBad first second error := by
  set a := first true
  set b := second true
  have aLe : a ≤ 1 := PMF.coe_le_one first true
  have bLe : b ≤ 1 := PMF.coe_le_one second true
  have aTop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top aLe
  have split (x y : ℝ≥0∞) (small : min x y ≤ x) : min x y + (x - min x y) = x :=
    add_tsub_cancel_of_le small
  have totalOf (x : ℝ≥0∞) (y z : ℝ≥0∞) (xLe : x ≤ 1) :
      min x y + (x - min x y) + (min (1 - x) z + ((1 - x) - min (1 - x) z)) = 1 := by
    rw [split _ _ (min_le_left _ _), split _ _ (min_le_left _ _)]
    exact add_tsub_cancel_of_le xLe
  refine ⟨flaggedLaw (a - min a b) ((1 - a) - min (1 - a) (1 - b)) (min a b) (min (1 - a) (1 - b))
      (totalOf a b (1 - b) aLe),
    flaggedLaw (b - min a b) ((1 - b) - min (1 - a) (1 - b)) (min a b) (min (1 - a) (1 - b))
      (by rw [min_comm a b, min_comm (1 - a) (1 - b)]; exact totalOf b a (1 - a) bLe),
    ?_, ?_, ?_, ?_⟩
  · refine pmf_bool_ext ?_
    rw [flaggedLaw_fst, if_pos rfl, split _ _ (min_le_left _ _)]
  · refine pmf_bool_ext ?_
    rw [flaggedLaw_fst, if_pos rfl, add_tsub_cancel_of_le (min_le_right _ _)]
  · intro outcome
    cases outcome <;> rfl
  · rw [flaggedLaw_bad]
    refine le_trans ?_ bound
    unfold Assumptions.advantage
    rcases le_total b a with ba | ab
    · have oneLe : 1 - a ≤ 1 - b := tsub_le_tsub_left ba 1
      rw [min_eq_right ba, min_eq_left oneLe, tsub_self, add_zero,
        ENNReal.toReal_sub_of_le ba aTop]
      exact le_abs_self _
    · have oneLe : 1 - b ≤ 1 - a := tsub_le_tsub_left ab 1
      rw [min_eq_left ab, min_eq_right oneLe, tsub_self, zero_add,
        ENNReal.toReal_sub_of_le oneLe (ENNReal.sub_ne_top ENNReal.one_ne_top),
        ENNReal.toReal_sub_of_le aLe ENNReal.one_ne_top,
        ENNReal.toReal_sub_of_le bLe ENNReal.one_ne_top]
      rw [abs_sub_comm]
      calc (1 : ℝ≥0∞).toReal - a.toReal - ((1 : ℝ≥0∞).toReal - b.toReal) = b.toReal - a.toReal := by
            ring
        _ ≤ |b.toReal - a.toReal| := le_abs_self _

/-! ### Transcripts, touches, and the empty start -/

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- A program's transcript is consistent with the oracle it ran on. -/
theorem programTranscript_consistent {α : Type} (O : PublicOracle FI EI) :
    ∀ {budget : ℕ} (P : QueryProgram (publicOracleSpec FI EI) α budget),
      Consistent O (programTranscript (publicAnswer O) P)
  | _, .pure _ => fun _ member => by cases member
  | _, .query request next => fun entry member => by
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact programTranscript_consistent O (next (publicAnswer O request)) entry member

/-- A hash entry of a list is a member at its hash query. -/
theorem hash_of_hashPair {entry : Entry FI EI} {key : BaseField} {value : Block × Block}
    (pair : hashPair entry = some (key, value)) : entry = ⟨.hash key, value⟩ := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | hash input =>
      simp only [hashPair, Option.some.injEq] at pair
      obtain ⟨rfl, rfl⟩ := pair
      rfl
  | _ => simp [hashPair] at pair

variable [IsEmpty FI] [IsEmpty EI]

/-- With empty index types, a touch of the garbler's extra entries is a query touch of the list. -/
theorem touches_extraOf {O : PublicOracle FI EI} {L : List (Entry FI EI)} {e : Entry FI EI}
    (touch : Kriterion.ArgoMAC.Security.Phase3.Hidden.Touches (extraOf O L) e) : Touches L e.1 := by
  classical
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward index _ => exact isEmptyElim index
  | fixedInverse index _ => exact isEmptyElim index
  | encForward index _ => exact isEmptyElim index
  | encInverse index _ => exact isEmptyElim index
  | hash key =>
      simp only [Kriterion.ArgoMAC.Security.Phase3.Hidden.Touches, extraOf] at touch
      split_ifs at touch with found
      · obtain ⟨entry, member, value, pair⟩ := found
        rw [hash_of_hashPair pair] at member
        exact List.mem_map.mpr ⟨_, member, rfl⟩
      · simp at touch

/-- With empty index types, a touch of the garbler's extra entries minus `D` is a query touch of the list
entries outside `D`. -/
theorem touches_dropAll {O : PublicOracle FI EI} {L D : List (Entry FI EI)} {e : Entry FI EI}
    (touch : Kriterion.ArgoMAC.Security.Phase3.Hidden.Touches (dropAll (extraOf O L) D) e) :
    ∃ entry ∈ L, entry ∉ D ∧ entry.1 = e.1 := by
  classical
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward index _ => exact isEmptyElim index
  | fixedInverse index _ => exact isEmptyElim index
  | encForward index _ => exact isEmptyElim index
  | encInverse index _ => exact isEmptyElim index
  | hash key =>
      simp only [Kriterion.ArgoMAC.Security.Phase3.Hidden.Touches, dropAll, extraOf] at touch
      split_ifs at touch with inD found
      · simp at touch
      · obtain ⟨entry, member, value, pair⟩ := found
        refine ⟨entry, member, fun inD' => inD ⟨entry, inD', value, pair⟩, ?_⟩
        rw [hash_of_hashPair pair]
      · simp at touch

/-- The empty oracle avoids every extra set (empty index types). -/
theorem avoid_empty (K : Extra FI EI) : Avoid (LazyOracle.empty : LazyOracle.State FI EI) K :=
  ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun _ _ _ => rfl⟩

theorem bind_apply_expect {α : Type} (μ : PMF α) (f : α → PMF Bool) (b : Bool) :
    (μ.bind f) b = expect μ (fun a => f a b) := by
  rw [PMF.bind_apply]
  rfl

theorem map_fst_apply (p : PMF (Bool × LazyOracle.State FI EI)) (b : Bool) :
    (p.map Prod.fst) b = atBool p b := by
  rw [PMF.map_apply]
  unfold atBool expect
  refine tsum_congr fun o => ?_
  beta_reduce
  by_cases h : o.1 = b
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/-! ### The empty extra set (the touches of a bad tape are not counted) -/

/-- The extra set with no entries. -/
def emptyExtra : Extra FI EI := ⟨fun _ _ _ => False, fun _ _ _ => False, fun _ => none⟩

theorem not_touches_emptyExtra (entry : Kriterion.ArgoMAC.Security.Phase3.Hidden.Asked FI EI) :
    ¬ Kriterion.ArgoMAC.Security.Phase3.Hidden.Touches (emptyExtra (FI := FI) (EI := EI)) entry := by
  obtain ⟨query, answer⟩ := entry
  cases query <;>
    simp [Kriterion.ArgoMAC.Security.Phase3.Hidden.Touches, emptyExtra,
      Kriterion.ArgoMAC.Security.Phase3.Hidden.ForwardTouch]

theorem cleanWeight_emptyExtra
    (log : List (Kriterion.ArgoMAC.Security.Phase3.Hidden.Asked FI EI)) :
    cleanWeight (emptyExtra (FI := FI) (EI := EI)) log = 1 := by
  unfold cleanWeight
  rw [if_pos fun entry _ => not_touches_emptyExtra entry]

/-! ### The reduction, per game -/

variable (E : CrtEntry FI EI)

theorem crt_hidden_advantage_le [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI]
    (T : CrtTable) (reached : DesignedReached E T) (ε δ : ℝ≥0∞) (finite : ε ≠ ⊤) (finiteδ : δ ≠ ⊤)
    (one : CrtStageOneGuess E ε) (two : CrtStageTwoGuess E T ε δ)
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) :
    Assumptions.advantage (padSwappedHybrid E adversary parameter scalar)
        (hiddenDeletedHybrid E adversary parameter scalar) ≤
      ((adversary.firstQueryBudget parameter : ℝ≥0∞) * ε +
        ((adversary.secondQueryBudget parameter : ℝ≥0∞) * ε + δ)).toReal := by
  classical
  obtain ⟨bad, badMass, twoOff⟩ := two parameter scalar
  let μ : PMF (TableTape E) := swappedTableTape E
  let O := fun tape : TableTape E => tapeOracle E tape
  let garbled := fun tape : TableTape E =>
    (E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, O tape)
  let first := fun tape : TableTape E => adversary.chooseInput parameter (garbled tape).1 ()
  let second := fun (tape : TableTape E) (r : AffineInput × adversary.State) =>
    adversary.decide parameter (garbled tape).1
      ((E.scheme inferInstance inferInstance).encode (garbled tape).2 r.1) () r.2
  let L := fun tape : TableTape E => garblerEntries E parameter scalar tape
  let vis := fun (tape : TableTape E) (r : AffineInput × adversary.State) =>
    (L tape).filter fun entry => decide (entry.1 ∈ (programTranscript (publicAnswer (O tape))
      (E.reachProgram inferInstance inferInstance (garbled tape).1 r.1
        ((E.scheme inferInstance inferInstance).encode (garbled tape).2 r.1))).map Sigma.fst)
  let vis'' := fun (tape : TableTape E) (r : AffineInput × adversary.State) =>
    designedEntries E T parameter scalar tape r.1
  let start : LazyOracle.State FI EI := LazyOracle.empty
  let A : Bool → ℝ≥0∞ := fun b => expect μ fun tape =>
    flaggedMass (first tape) (second tape) start (extraOf (O tape) (L tape)) (vis'' tape) b
  have consistent : ∀ tape, Consistent (O tape) (L tape) := fun tape =>
    programTranscript_consistent (O tape) _
  have visWithin : ∀ tape r, Within (vis tape r) (L tape) :=
    fun tape r e member => (List.mem_filter.mp member).1
  have designedWithin : ∀ tape r, Within (vis'' tape r) (vis tape r) := by
    intro tape r e member
    refine List.mem_filter.mpr ⟨(List.mem_filter.mp member).1, ?_⟩
    have reach := reached parameter scalar tape r.1 e member
    exact decide_eq_true (List.mem_map_of_mem (f := Sigma.fst) reach)
  have designedInL : ∀ tape r, Within (vis'' tape r) (L tape) :=
    fun tape r e member => visWithin tape r e (designedWithin tape r e member)
  -- the two games as averages over the tape
  have g0 : ∀ b, padSwappedHybrid E adversary parameter scalar b = expect μ fun tape =>
      eagerPlanted (first tape) (second tape) (plantAll (L tape) start) b := by
    intro b
    unfold padSwappedHybrid plantedGame
    rw [bind_apply_expect]
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [bind_apply_expect]
    unfold eagerPlanted
    refine congrArg (expect _) (funext fun r => ?_)
    exact map_fst_apply _ b
  have g1 : ∀ b, hiddenDeletedHybrid E adversary parameter scalar b = expect μ fun tape =>
      lateInstalled (first tape) (second tape) start (vis tape) b := by
    intro b
    unfold hiddenDeletedHybrid
    rw [bind_apply_expect]
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [bind_apply_expect]
    unfold lateInstalled
    refine congrArg (expect _) (funext fun r => ?_)
    exact map_fst_apply _ b
  have ge0 : ∀ b, A b ≤ padSwappedHybrid E adversary parameter scalar b := by
    intro b
    rw [g0]
    exact expect_mono _ fun tape => eagerPlanted_ge (first tape) (second tape) (O tape) (L tape)
      (consistent tape) (rel_plantAll_of_avoid (O tape) (L tape) (consistent tape) start (avoid_empty _))
      (vis'' tape) (designedInL tape) b
  have ge1 : ∀ b, A b ≤ hiddenDeletedHybrid E adversary parameter scalar b := by
    intro b
    rw [g1]
    exact expect_mono _ fun tape => lateInstalled_ge (first tape) (second tape) (O tape) (L tape)
      (consistent tape) (avoid_empty _) (vis tape) (vis'' tape) (visWithin tape) (designedWithin tape) b
  -- the two touch masses
  let run₁ := fun view : E.Public => runLog (adversary.chooseInput parameter view ()) start
  have touch₁ : expect μ (fun tape => expect (runLog (first tape) start)
      (fun o => 1 - cleanWeight (extraOf (O tape) (L tape)) o.2.2)) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) * ε := by
    have bound := touch_mass_le μ (stageOneView E parameter scalar) (fun tape => extraOf (O tape) (L tape))
      (fun view => (run₁ view).map fun o => ((o.1, o.2.1), o.2.2))
      (adversary.firstQueryBudget parameter)
      (fun view o member => by
        rw [PMF.support_map] at member
        obtain ⟨o', member', rfl⟩ := member
        exact runLog_length _ _ o' member')
      ε (fun v e => le_trans (μ.toOuterMeasure.mono fun tape hit => And.intro hit.1 (touches_extraOf hit.2))
        (one parameter scalar v e.1))
    refine le_trans (le_of_eq ?_) bound
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [expect_map]
    rfl
  let W := fun (z : (AffineInput × adversary.State) × LazyOracle.State FI EI × List (Entry FI EI))
      (tape : TableTape E) => stageTwoView E T parameter scalar z.1.1 tape
  let extra₂ := fun (z : (AffineInput × adversary.State) × LazyOracle.State FI EI × List (Entry FI EI))
      (tape : TableTape E) => dropAll (extraOf (O tape) (L tape)) (designedEntries E T parameter scalar tape z.1.1)
  let μ₂ := μ.bind fun tape => (run₁ (stageOneView E parameter scalar tape)).map fun z => (tape, z)
  let run₂ := fun (view : (E.Public × LamportSignature × List (Entry FI EI)) ×
      ((AffineInput × adversary.State) × LazyOracle.State FI EI × List (Entry FI EI))) =>
    (runLog (adversary.decide parameter view.1.1 view.1.2.1 () view.2.1.2)
      (plantAll view.1.2.2 view.2.2.1)).map fun o => ((o.1, o.2.1), o.2.2)
  let extra₂' := fun (z : (AffineInput × adversary.State) × LazyOracle.State FI EI × List (Entry FI EI))
      (tape : TableTape E) => if bad tape then emptyExtra else extra₂ z tape
  have touch₂' : expect μ (fun tape => expect (runLog (first tape) start) (fun o =>
      expect (runLog (second tape o.1) (plantAll (vis'' tape o.1) o.2.1))
        fun o₂ => 1 - cleanWeight (extra₂' o tape) o₂.2.2)) ≤
      (adversary.secondQueryBudget parameter : ℝ≥0∞) * ε := by
    have guess := guess_bind μ (stageOneView E parameter scalar) run₁ W Prod.fst (fun _ _ => rfl)
      extra₂' ε (fun z w e => le_trans (μ.toOuterMeasure.mono fun tape hit => by
          obtain ⟨hw, touch⟩ := hit
          by_cases hb : bad tape
          · simp only [extra₂', if_pos hb] at touch
            exact absurd touch (not_touches_emptyExtra e)
          · simp only [extra₂', if_neg hb] at touch
            refine ⟨hw, ?_, hb⟩
            obtain ⟨entry, member, notD, same⟩ := touches_dropAll touch
            exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨member, decide_eq_true notD⟩, same⟩)
        (twoOff z.1.1 w e.1))
    have bound := touch_mass_le μ₂ (fun p => (W p.2 p.1, p.2)) (fun p => extra₂' p.2 p.1) run₂
      (adversary.secondQueryBudget parameter)
      (fun view o member => by
        rw [PMF.support_map] at member
        obtain ⟨o', member', rfl⟩ := member
        exact runLog_length _ _ o' member')
      ε guess
    refine le_trans (le_of_eq ?_) bound
    rw [expect_bind]
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [expect_map]
    refine congrArg (expect _) (funext fun z => ?_)
    rw [expect_map]
    rfl
  have touch₂ : expect μ (fun tape => expect (runLog (first tape) start) (fun o =>
      expect (runLog (second tape o.1) (plantAll (vis'' tape o.1) o.2.1))
        fun o₂ => 1 - cleanWeight (dropAll (extraOf (O tape) (L tape)) (vis'' tape o.1)) o₂.2.2)) ≤
      (adversary.secondQueryBudget parameter : ℝ≥0∞) * ε + δ := by
    have split : ∀ tape, expect (runLog (first tape) start) (fun o =>
        expect (runLog (second tape o.1) (plantAll (vis'' tape o.1) o.2.1))
          fun o₂ => 1 - cleanWeight (dropAll (extraOf (O tape) (L tape)) (vis'' tape o.1)) o₂.2.2) ≤
        expect (runLog (first tape) start) (fun o =>
          expect (runLog (second tape o.1) (plantAll (vis'' tape o.1) o.2.1))
            fun o₂ => 1 - cleanWeight (extra₂' o tape) o₂.2.2) + (if bad tape then 1 else 0) := by
      intro tape
      by_cases hb : bad tape
      · rw [if_pos hb]
        refine le_trans (expect_le_one _ fun o => expect_le_one _ fun o₂ => tsub_le_self) le_add_self
      · rw [if_neg hb, add_zero]
        refine le_of_eq (congrArg (expect _) (funext fun o => congrArg (expect _) (funext fun o₂ => ?_)))
        simp only [extra₂', if_neg hb]
        rfl
    have badExpect : expect μ (fun tape => if bad tape then (1 : ℝ≥0∞) else 0) ≤ δ := by
      refine le_trans (le_of_eq ?_) badMass
      rw [outer_eq_expect]
      refine congrArg (expect μ) (funext fun tape => ?_)
      by_cases hb : bad tape
      · simp [hb]
      · simp [hb]
    calc _ ≤ expect μ (fun tape => expect (runLog (first tape) start) (fun o =>
            expect (runLog (second tape o.1) (plantAll (vis'' tape o.1) o.2.1))
              fun o₂ => 1 - cleanWeight (extra₂' o tape) o₂.2.2) + (if bad tape then 1 else 0)) :=
          expect_mono _ split
      _ = _ := expect_add _ _ _
      _ ≤ _ := add_le_add touch₂' badExpect
  -- the missing mass
  have sumLe : ∀ tape, flaggedMass (first tape) (second tape) start (extraOf (O tape) (L tape)) (vis'' tape) true +
      flaggedMass (first tape) (second tape) start (extraOf (O tape) (L tape)) (vis'' tape) false ≤ 1 := by
    intro tape
    rw [flagged_sum]
    exact expect_le_one _ fun o => le_trans (mul_le_mul' (cleanWeight_le_one _ _)
      (expect_le_one _ fun o₂ => cleanWeight_le_one _ _)) (le_of_eq (one_mul 1))
  have missing : 1 - (A true + A false) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) * ε +
        ((adversary.secondQueryBudget parameter : ℝ≥0∞) * ε + δ) := by
    have sumA : A true + A false = expect μ fun tape =>
        flaggedMass (first tape) (second tape) start (extraOf (O tape) (L tape)) (vis'' tape) true +
          flaggedMass (first tape) (second tape) start (extraOf (O tape) (L tape)) (vis'' tape) false :=
      (expect_add _ _ _).symm
    rw [sumA, ← expect_one_sub _ sumLe]
    refine le_trans (expect_mono _ fun tape => flagged_total_ge (first tape) (second tape) start
      (extraOf (O tape) (L tape)) (vis'' tape)) ?_
    rw [expect_add]
    exact add_le_add touch₁ touch₂
  exact advantage_le_of_dominated _ _ A ge0 ge1 _ missing
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) finite,
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) finite, finiteδ⟩⟩)

theorem crtHiddenCharge_nonneg : 0 ≤ crtHiddenCharge := by
  rw [crtHiddenCharge_eq]
  unfold BN254.baseFieldModulus
  norm_num

end HiddenReduction

variable {FI EI : Type} (E : CrtEntry FI EI)

/-- **The hidden hop from the guesses** (P2a: xinshu's `hidden_of_guess`, `Hidden/Reduction.lean:885`, ported to
the table tape and hash-only entries; the stage-2 guess holds off a tape event of mass `δ`, charged once). -/
theorem crt_hidden_of_guess [Finite FI] [Finite EI] [IsEmpty FI] [IsEmpty EI] (T : CrtTable) (δ : ℝ) (hδ : 0 ≤ δ)
    (reached : DesignedReached E T) (one : CrtStageOneGuess E (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess E T (ENNReal.ofReal crtHiddenCharge) (ENNReal.ofReal δ)) :
    GameUntilBad (crtChain E).padSwapped (crtChain E).hiddenDeleted fun first second =>
      hiddenPointError (first + second) + δ := by
  intro field group adversary parameter scalar _
  apply HiddenReduction.untilBad_of_advantage_le
  have bound := @HiddenReduction.crt_hidden_advantage_le FI EI (Classical.decEq _) (Classical.decEq _) _ _ E
    field group (Fintype.ofFinite _) (Fintype.ofFinite _) T reached (ENNReal.ofReal crtHiddenCharge)
    (ENNReal.ofReal δ) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top one two adversary parameter scalar
  refine le_trans bound (le_of_eq ?_)
  rw [← add_assoc, ← add_mul, ← Nat.cast_add, ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal HiddenReduction.crtHiddenCharge_nonneg, ENNReal.toReal_ofReal hδ]
  unfold hiddenPointError
  push_cast
  ring

end

end Kriterion.CRT.Privacy
