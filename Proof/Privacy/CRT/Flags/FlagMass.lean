/-
**P8, the flag mass of `M'`: the reduction to two per-input guessing bounds** (`CrtFlagMass`; the CRT, hash-only
form of xinshu's `FlagMass.lean`, `FlagBound.lean` and `Count.lean`'s `run_touch_mass_le`).

`M'`'s stage 2 at a stage-1 state `σ₁` flags when the private replay or the private final state **meets** `σ₁`, on an
abort, or on a reveal. The private run itself does not read `σ₁`, so its law is that of the stage 2 at the empty
stage-1 state, `middleStage2 … LazyOracle.empty`, which flags only on an abort or a reveal. So
(`middleStage2_none_le`): the flag mass at `σ₁` is at most the mass at the empty state of **a flag, or an
unflagged outcome whose final state meets `σ₁`** (`flagWeight`), and a meeting is a stored point of `σ₁` that the
final state stores (`flagWeight_le`, a union bound over `σ₁`'s points).

Averaged over the uniform source and the adversary's stage 1, the input is the adversary's, chosen after the view.
As in `Coincidence.lean`, it suffices to bound each part **for every fixed input and point, against every weight on
the published value** (the adaptive choice is absorbed exactly):

* `CrtFlagGuess ε`: the mass of a flag at the empty state (an abort or a reveal: the wrap window, the doubling);
* `CrtTouchGuess c`: the mass with which the unflagged final state stores a given point, bounded by `c` times the
  weight's mass under the swapped tape (`swappedTableTape`, read through `stageOneView`): route (B) reaches the real
  law through `CrtCoreBelow` (`adaptive_le₂` absorbs the adaptive choice against a second law);

and the stage-1 state stores at most `q₁` points (xinshu's `run_entryCount_le`). **`crtFlagMass_of`**:
`CrtFlagMass E shadow` from `CrtFlagGuess (smudgeError + exceptionalError)` and `CrtTouchGuess
stageOneTouchCharge`.
-/

import Proof.Privacy.CRT.PublicFirst.Below
import Proof.Privacy.CRT.Hidden.Obligations
import Proof.Privacy.Phase3.PublicFirst.Count

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### 1. Weights on stage-2 outcomes -/

section Weights

variable {FI EI : Type}

/-- The outcome of a flagged stage 2. -/
abbrev Outcome (FI EI : Type) := Option (Option (LamportSignature × LazyOracle.State FI EI))

/-- `1` on a flag (`none`, and the unused abort `some none`), `0` on labels and a state. -/
def flagDown : Outcome FI EI → ℝ≥0∞
  | some (some _) => 0
  | _ => 1

/-- `1` exactly on the flag. -/
def noneWeight : Outcome FI EI → ℝ≥0∞
  | none => 1
  | _ => 0

open Classical in
/-- **The flag weight at `σ₁` of an outcome at the empty state**: `1` on a flag, and on labels and a state that meets
`σ₁`. -/
def flagWeight (planted : LazyOracle.State FI EI) : Outcome FI EI → ℝ≥0∞
  | some (some (_, state)) => if Meets planted state then 1 else 0
  | _ => 1

/-- The points an outcome's state stores (none on a flag). -/
def storedOf : Outcome FI EI → List BaseField
  | some (some (_, state)) => storedPoints state
  | _ => []

open Classical in
/-- `1` when the outcome's state stores the point. -/
def touchWeight (x : BaseField) (o : Outcome FI EI) : ℝ≥0∞ := if x ∈ storedOf o then 1 else 0

/-- **A meeting is a stored point of `σ₁`** (the union bound over `σ₁`'s points). -/
theorem flagWeight_le (planted : LazyOracle.State FI EI) (o : Outcome FI EI) :
    flagWeight planted o ≤ flagDown o + ((storedPoints planted).map fun x => touchWeight x o).sum := by
  rcases o with _ | _ | ⟨labels, state⟩
  · exact le_add_right le_rfl
  · exact le_add_right le_rfl
  · simp only [flagWeight, flagDown, zero_add]
    split
    · rename_i meets
      obtain ⟨x, inState, inPlanted⟩ := meets
      have term : touchWeight x (some (some (labels, state))) = 1 := by
        unfold touchWeight storedOf
        rw [if_pos inState]
      calc (1 : ℝ≥0∞) = touchWeight x (some (some (labels, state))) := term.symm
        _ ≤ _ := List.single_le_sum (fun _ _ => zero_le) _
            (List.mem_map_of_mem (f := fun x => touchWeight x (some (some (labels, state)))) inPlanted)
    · exact zero_le

theorem noneWeight_eq (μ : PMF (Outcome FI EI)) : ∑' o, μ o * noneWeight o = μ none := by
  rw [tsum_eq_single none fun o different => by
    rcases o with _ | _ | _
    · exact absurd rfl different
    · simp [noneWeight]
    · simp [noneWeight]]
  simp [noneWeight]

end Weights

/-! ### 2. The empty stage-1 state -/

section Empty

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

theorem not_meets_empty (state : LazyOracle.State FI EI) : ¬ Meets LazyOracle.empty state := by
  rintro ⟨x, -, inEmpty⟩
  simp [storedPoints, LazyOracle.empty] at inEmpty

theorem storedPoints_merge_empty (state : LazyOracle.State FI EI) :
    storedPoints (mergeState LazyOracle.empty state) = storedPoints state := by
  simp [storedPoints, mergeState, LazyOracle.empty]

/-- **The flagged ending at `σ₁` is below the flag weight of the ending at the empty state.** -/
theorem finish_flag_le (planted : LazyOracle.State FI EI) (labels : LamportSignature) (reveal : Prop)
    (state : LazyOracle.State FI EI) :
    noneWeight (finishPrivate planted labels reveal state) ≤
      flagWeight planted (finishPrivate LazyOracle.empty labels reveal state) := by
  unfold finishPrivate
  by_cases revealed : reveal
  · rw [if_pos (show Meets planted state ∨ reveal from Or.inr revealed),
      if_pos (show Meets LazyOracle.empty state ∨ reveal from Or.inr revealed)]
    exact le_rfl
  · rw [if_neg (show ¬ (Meets LazyOracle.empty state ∨ reveal) from
      fun either => either.elim (not_meets_empty state) revealed)]
    by_cases meets : Meets planted state
    · rw [if_pos (show Meets planted state ∨ reveal from Or.inl meets)]
      have meets' : Meets planted (mergeState LazyOracle.empty state) := by
        obtain ⟨x, inState, inPlanted⟩ := meets
        exact ⟨x, by rw [storedPoints_merge_empty]; exact inState, inPlanted⟩
      simp only [flagWeight, if_pos meets', noneWeight]
      exact le_rfl
    · rw [if_neg (show ¬ (Meets planted state ∨ reveal) from fun either => either.elim meets revealed)]
      simp [noneWeight]

/-- The flag weight at `σ₁` of an ending from a state that already meets `σ₁` is `1`. -/
theorem finish_flag_one (planted : LazyOracle.State FI EI) (labels : LamportSignature) (reveal : Prop)
    (state : LazyOracle.State FI EI) (meets : Meets planted state) :
    flagWeight planted (finishPrivate LazyOracle.empty labels reveal state) = 1 := by
  unfold finishPrivate
  split
  · rfl
  · have meets' : Meets planted (mergeState LazyOracle.empty state) := by
      obtain ⟨x, inState, inPlanted⟩ := meets
      exact ⟨x, by rw [storedPoints_merge_empty]; exact inState, inPlanted⟩
    simp only [flagWeight, if_pos meets']

theorem tsum_mul_one {α : Type} (μ : PMF α) (g : α → ℝ≥0∞) (one : ∀ a ∈ μ.support, g a = 1) :
    ∑' a, μ a * g a = 1 := by
  calc ∑' a, μ a * g a = ∑' a, μ a * 1 := tsum_congr fun a => by
        by_cases member : a ∈ μ.support
        · rw [one a member]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
    _ = 1 := by simp only [mul_one, PMF.tsum_coe]

/-- The shadow step from a state that meets `σ₁` has flag weight `1`. -/
theorem shadow_flag_one {Coin : Type} (law : PMF Coin) (planted state : LazyOracle.State FI EI)
    (meets : Meets planted state) (labels : LamportSignature) (extra : Coin → CM Unit)
    (reveal : Coin → LazyOracle.State FI EI → Prop) :
    ∑' o, (law.bind fun coin => (runReader lazyReader (extra coin) state).map fun ran =>
        finishPrivate LazyOracle.empty labels (reveal coin ran.2) ran.2) o * flagWeight planted o = 1 := by
  rw [tsum_bind_mul]
  refine tsum_mul_one law _ fun coin _ => ?_
  rw [tsum_map_mul]
  refine tsum_mul_one _ _ fun p member => ?_
  exact finish_flag_one planted labels _ p.2
    (meets_extends (extendsRun_runReader lazyReader extendsRun_lazyReader (extra coin) state p member) meets)

/-- The shadow step at `σ₁` against the one at the empty state. -/
theorem shadow_flag_le {Coin : Type} (law : PMF Coin) (planted state : LazyOracle.State FI EI)
    (labels : LamportSignature) (extra : Coin → CM Unit) (reveal : Coin → LazyOracle.State FI EI → Prop) :
    ∑' o, (law.bind fun coin => (runReader lazyReader (extra coin) state).map fun ran =>
        finishPrivate planted labels (reveal coin ran.2) ran.2) o * noneWeight o ≤
      ∑' o, (law.bind fun coin => (runReader lazyReader (extra coin) state).map fun ran =>
        finishPrivate LazyOracle.empty labels (reveal coin ran.2) ran.2) o * flagWeight planted o := by
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
  rw [tsum_map_mul, tsum_map_mul]
  exact ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (finish_flag_le planted labels _ p.2)

end Empty

/-! ### 3. Stage 2 at `σ₁` against stage 2 at the empty state -/

variable {FI EI : Type} (E : CrtEntry FI EI)

section Stage2

variable [FieldCertificate] [GroupCertificate] [DecidableEq FI] [DecidableEq EI]

/-- **The flag at `σ₁` is below the flag weight at the empty state.** -/
theorem middleStage2_none_le (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput) (output : Option Point)
    (planted : LazyOracle.State FI EI) :
    middleStage2 E shadow offRun scalar source u output planted none ≤
      ∑' o, middleStage2 E shadow offRun scalar source u output LazyOracle.empty o * flagWeight planted o := by
  rw [← noneWeight_eq]
  cases output with
  | none =>
    simp only [middleStage2]
    rw [tsum_bind_mul, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
    rw [tsum_map_mul, tsum_map_mul]
    exact ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (finish_flag_le planted _ _ p.2)
  | some target =>
    simp only [middleStage2]
    rw [tsum_bind_mul, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun ran => mul_le_mul' le_rfl ?_
    rw [if_neg (not_meets_empty ran.2)]
    by_cases meets : Meets planted ran.2
    · rw [if_pos meets, tsum_pure_mul_eq]
      show (1 : ℝ≥0∞) ≤ _
      rw [tsum_bind_mul]
      refine le_of_eq (tsum_mul_one _ _ fun drawnRows _ => ?_).symm
      rcases drawnRows with _ | targets
      · dsimp only
        rw [tsum_pure_mul_eq]
        rfl
      · dsimp only
        rw [tsum_bind_mul]
        refine tsum_mul_one _ _ fun drawn _ => ?_
        rcases drawn with _ | drawn
        · dsimp only
          rw [tsum_pure_mul_eq]
          rfl
        · dsimp only
          cases privately : programHashAll (programRequests ran.1.key drawn) ran.2 with
          | none =>
            dsimp only
            rw [tsum_pure_mul_eq]
            rfl
          | some installed =>
            dsimp only
            exact shadow_flag_one shadow.law planted installed
              (meets_extends (programHashAll_extends _ _ _ privately).1 meets) _ _ _
    · rw [if_neg meets]
      rw [tsum_bind_mul, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun drawnRows => mul_le_mul' le_rfl ?_
      rcases drawnRows with _ | targets
      · dsimp only
        rw [tsum_pure_mul_eq, tsum_pure_mul_eq]
        exact le_rfl
      · dsimp only
        rw [tsum_bind_mul, tsum_bind_mul]
        refine ENNReal.tsum_le_tsum fun drawn => mul_le_mul' le_rfl ?_
        rcases drawn with _ | drawn
        · dsimp only
          rw [tsum_pure_mul_eq, tsum_pure_mul_eq]
          exact le_rfl
        · dsimp only
          cases privately : programHashAll (programRequests ran.1.key drawn) ran.2 with
          | none =>
            dsimp only
            rw [tsum_pure_mul_eq, tsum_pure_mul_eq]
            exact le_rfl
          | some installed =>
            dsimp only
            exact shadow_flag_le shadow.law planted installed _ _ _

end Stage2

/-! ### 4. The two guessing bounds and the flag mass -/

section Mass

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The flag mass of the stage 2 at the empty state (an abort or a reveal), at a source and an input. -/
def flagAt (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI) (scalar : NonZeroScalar)
    (source : (viewHere E).Source) (u : AffineInput) : ℝ≥0∞ :=
  ∑' o, middleStage2 E shadow offRun scalar source u ((E.scheme inferInstance inferInstance).function scalar u)
    LazyOracle.empty o * flagDown o

/-- The mass with which the unflagged final state stores a point, at a source and an input. -/
def touchAt (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI) (scalar : NonZeroScalar)
    (source : (viewHere E).Source) (u : AffineInput) (x : BaseField) : ℝ≥0∞ :=
  ∑' o, middleStage2 E shadow offRun scalar source u ((E.scheme inferInstance inferInstance).function scalar u)
    LazyOracle.empty o * touchWeight x o

/-- `M'`'s flag mass as a sum over the stage-1 outcomes. -/
theorem middleGame_none_eq (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) :
    middleGame E shadow offRun adversary parameter scalar none =
      (letI := (viewHere E).sourceFintype
       haveI := (viewHere E).sourceNonempty
       ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter ((viewHere E).publish source) ())
            LazyOracle.empty selected *
          middleStage2 E shadow offRun scalar source selected.1.1
            ((E.scheme inferInstance inferInstance).function scalar selected.1.1) selected.2 none) := by
  unfold middleGame
  rw [PMF.bind_apply]
  refine tsum_congr fun source => ?_
  rw [PMF.bind_apply]
  refine congrArg _ (tsum_congr fun selected => ?_)
  rw [PMF.bind_apply]
  refine congrArg _ ?_
  rw [← noneWeight_eq]
  refine tsum_congr fun o => congrArg _ ?_
  rcases o with _ | _ | ⟨labels, state⟩
  · simp [stageTwoCont, noneWeight]
  · simp [stageTwoCont, noneWeight]
  · simp only [stageTwoCont, noneWeight, PMF.map_apply]
    simp

/-- A finite sum of weights inside a sum over a law. -/
theorem tsum_mul_listSum {α : Type} (μ : α → ℝ≥0∞) (list : List BaseField) (g : BaseField → α → ℝ≥0∞) :
    ∑' a, μ a * (list.map fun x => g x a).sum = (list.map fun x => ∑' a, μ a * g x a).sum := by
  induction list with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    rw [ENNReal.tsum_add, ih]

/-- The stage-1 state of a run of budget `q₁` stores at most `q₁` points. -/
theorem stored_length_le {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FI EI) Result budget) (outcome : Result × LazyOracle.State FI EI)
    (member : outcome ∈ (LazyOracle.run program LazyOracle.empty).support) :
    (storedPoints outcome.2).length ≤ budget := by
  have count := Kriterion.ArgoMAC.Security.Phase3.PublicFirst.run_entryCount_le program LazyOracle.empty
    outcome member
  rw [Kriterion.ArgoMAC.Security.Phase3.PublicFirst.entryCount_empty, zero_add] at count
  unfold Kriterion.ArgoMAC.Security.Phase3.PublicFirst.entryCount at count
  simp only [storedPoints, List.length_map]
  omega

/-- **An adaptive choice after the view**: a per-outcome bound against every weight on the view bounds the average. -/
theorem adaptive_le {S V T : Type} (μ : PMF S) (pub : S → V) (run : V → PMF T) (f : S → T → ℝ≥0∞) (B : ℝ≥0∞)
    (guess : ∀ t, ∑' s, μ s * (run (pub s) t * f s t) ≤ B * ∑' s, μ s * run (pub s) t) :
    ∑' s, μ s * ∑' t, run (pub s) t * f s t ≤ B := by
  calc ∑' s, μ s * ∑' t, run (pub s) t * f s t = ∑' t, ∑' s, μ s * (run (pub s) t * f s t) := by
        simp_rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_comm
    _ ≤ ∑' t, B * ∑' s, μ s * run (pub s) t := ENNReal.tsum_le_tsum guess
    _ = B := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
        rw [PMF.tsum_coe, mul_one]

/-- **An adaptive choice after the view, against a second law**: a per-outcome bound by the mass of a second law of
views bounds the average. -/
theorem adaptive_le₂ {S S' V T : Type} (μ : PMF S) (pub : S → V) (ν : PMF S') (pub' : S' → V) (run : V → PMF T)
    (f : S → T → ℝ≥0∞) (B : ℝ≥0∞)
    (guess : ∀ t, ∑' s, μ s * (run (pub s) t * f s t) ≤ B * ∑' s', ν s' * run (pub' s') t) :
    ∑' s, μ s * ∑' t, run (pub s) t * f s t ≤ B := by
  calc ∑' s, μ s * ∑' t, run (pub s) t * f s t = ∑' t, ∑' s, μ s * (run (pub s) t * f s t) := by
        simp_rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_comm
    _ ≤ ∑' t, B * ∑' s', ν s' * run (pub' s') t := ENNReal.tsum_le_tsum guess
    _ = B := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
        rw [PMF.tsum_coe, mul_one]

/-- **The flag mass from the two per-input bounds**, at one instance. -/
theorem middleGame_none_le (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) (ε c : ℝ≥0∞)
    {S' : Type} (ν : PMF S') (pub' : S' → E.Public)
    (flagGuess : ∀ (u : AffineInput) (weight : E.Public → ℝ≥0∞),
      (letI := (viewHere E).sourceFintype
       haveI := (viewHere E).sourceNonempty
       ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
          (weight ((viewHere E).publish source) * flagAt E shadow offRun scalar source u))
        ≤ ε * (letI := (viewHere E).sourceFintype
               haveI := (viewHere E).sourceNonempty
               ∑' source, PMF.uniformOfFintype (viewHere E).Source source * weight ((viewHere E).publish source)))
    (touchGuess : ∀ (u : AffineInput) (x : BaseField) (weight : E.Public → ℝ≥0∞),
      (letI := (viewHere E).sourceFintype
       haveI := (viewHere E).sourceNonempty
       ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
          (weight ((viewHere E).publish source) * touchAt E shadow offRun scalar source u x))
        ≤ c * ∑' s', ν s' * weight (pub' s')) :
    middleGame E shadow offRun adversary parameter scalar none ≤
      ε + (adversary.firstQueryBudget parameter : ℝ≥0∞) * c := by
  letI := (viewHere E).sourceFintype
  haveI := (viewHere E).sourceNonempty
  rw [middleGame_none_eq]
  have step : ∀ source (selected : (AffineInput × adversary.State) × LazyOracle.State FI EI),
      middleStage2 E shadow offRun scalar source selected.1.1
          ((E.scheme inferInstance inferInstance).function scalar selected.1.1) selected.2 none ≤
        flagAt E shadow offRun scalar source selected.1.1 +
          ((storedPoints selected.2).map fun x => touchAt E shadow offRun scalar source selected.1.1 x).sum := by
    intro source selected
    refine le_trans (middleStage2_none_le E shadow offRun scalar source _ _ selected.2) ?_
    calc _ ≤ ∑' o, middleStage2 E shadow offRun scalar source selected.1.1
            ((E.scheme inferInstance inferInstance).function scalar selected.1.1) LazyOracle.empty o *
          (flagDown o + ((storedPoints selected.2).map fun x => touchWeight x o).sum) :=
          ENNReal.tsum_le_tsum fun o => mul_le_mul' le_rfl (flagWeight_le selected.2 o)
      _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, tsum_mul_listSum]
          rfl
  refine le_trans (ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun selected => mul_le_mul' le_rfl (step source selected))) ?_
  simp only [mul_add, ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · exact adaptive_le (PMF.uniformOfFintype (viewHere E).Source) (viewHere E).publish
      (fun view => LazyOracle.run (adversary.chooseInput parameter view ()) LazyOracle.empty)
      (fun source selected => flagAt E shadow offRun scalar source selected.1.1) ε
      fun selected => flagGuess selected.1.1 fun view =>
        LazyOracle.run (adversary.chooseInput parameter view ()) LazyOracle.empty selected
  · refine adaptive_le₂ (PMF.uniformOfFintype (viewHere E).Source) (viewHere E).publish ν pub'
      (fun view => LazyOracle.run (adversary.chooseInput parameter view ()) LazyOracle.empty)
      (fun source selected =>
        ((storedPoints selected.2).map fun x => touchAt E shadow offRun scalar source selected.1.1 x).sum) _
      fun selected => ?_
    set W := ∑' s', ν s' *
      LazyOracle.run (adversary.chooseInput parameter (pub' s') ()) LazyOracle.empty selected
      with hW
    calc ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
          (LazyOracle.run (adversary.chooseInput parameter ((viewHere E).publish source) ()) LazyOracle.empty
              selected *
            ((storedPoints selected.2).map fun x => touchAt E shadow offRun scalar source selected.1.1 x).sum)
        = ((storedPoints selected.2).map fun x => ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
            (LazyOracle.run (adversary.chooseInput parameter ((viewHere E).publish source) ()) LazyOracle.empty
              selected * touchAt E shadow offRun scalar source selected.1.1 x)).sum := by
          rw [← tsum_mul_listSum]
          refine tsum_congr fun source => ?_
          rw [List.sum_map_mul_left]
      _ ≤ ((storedPoints selected.2).map fun _ => c * W).sum :=
          List.sum_le_sum fun x _ => touchGuess selected.1.1 x fun view =>
            LazyOracle.run (adversary.chooseInput parameter view ()) LazyOracle.empty selected
      _ = ((storedPoints selected.2).length : ℝ≥0∞) * (c * W) := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ ≤ (adversary.firstQueryBudget parameter : ℝ≥0∞) * c * W := by
          rw [mul_assoc]
          by_cases zero : W = 0
          · rw [zero, mul_zero, mul_zero, mul_zero]
          · obtain ⟨s', positive⟩ : ∃ s', ν s' *
                LazyOracle.run (adversary.chooseInput parameter (pub' s') ())
                  LazyOracle.empty selected ≠ 0 := by
              by_contra none
              push Not at none
              exact zero (ENNReal.tsum_eq_zero.mpr none)
            have member : selected ∈ (LazyOracle.run (adversary.chooseInput parameter
                (pub' s') ()) LazyOracle.empty).support :=
              (PMF.mem_support_iff _ _).mpr (right_ne_zero_of_mul positive)
            have length := stored_length_le _ selected member
            exact mul_le_mul' (by exact_mod_cast length) le_rfl

end Mass

/-! ### 5. `CrtFlagMass` -/

/-- **The flag guess** (P8): at every input, against every weight on the published value, the stage 2 at the empty
stage-1 state flags (an abort, a reveal) with mass at most `ε`. -/
def CrtFlagGuess [fixedFinite : Finite FI] [encFinite : Finite EI]
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI) (ε : ℝ≥0∞) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar) (u : AffineInput),
    (letI := field
     letI := group
     letI := @Fintype.ofFinite FI fixedFinite
     letI := @Fintype.ofFinite EI encFinite
     letI := Classical.decEq FI
     letI := Classical.decEq EI
     letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∀ weight : E.Public → ℝ≥0∞,
       ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
          (weight ((viewHere E).publish source) *
            flagAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u)
        ≤ ε * ∑' source, PMF.uniformOfFintype (viewHere E).Source source * weight ((viewHere E).publish source))

/-- **The touch guess** (P8): at every input and point, against every weight on the published value, the unflagged
final state of the stage 2 stores the point with mass at most `c` times the weight's mass under the swapped tape
(the real published value, `stageOneView`). -/
def CrtTouchGuess [fixedFinite : Finite FI] [encFinite : Finite EI]
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI) (c : ℝ≥0∞) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (x : BaseField),
    (letI := field
     letI := group
     letI := @Fintype.ofFinite FI fixedFinite
     letI := @Fintype.ofFinite EI encFinite
     letI := Classical.decEq FI
     letI := Classical.decEq EI
     letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∀ weight : E.Public → ℝ≥0∞,
       ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
          (weight ((viewHere E).publish source) *
            touchAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u x)
        ≤ c * ∑' tape, swappedTableTape E tape * weight (stageOneView E parameter scalar tape))

/-- **`CrtFlagMass`** (P8) from the flag guess at `smudgeError + exceptionalError` and the touch guess at
`stageOneTouchCharge`. -/
theorem crtFlagMass_of [fixedFinite : Finite FI] [encFinite : Finite EI]
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI)
    (flag : CrtFlagGuess E shadow (ENNReal.ofReal (smudgeError + exceptionalError)))
    (touch : CrtTouchGuess E shadow (ENNReal.ofReal stageOneTouchCharge)) :
    CrtFlagMass E shadow := by
  intro field group adversary parameter scalar _
  letI := field
  letI := group
  letI := @Fintype.ofFinite FI fixedFinite
  letI := @Fintype.ofFinite EI encFinite
  letI := Classical.decEq FI
  letI := Classical.decEq EI
  have bound := middleGame_none_le E shadow (tableRun (swappedTableLaw E.layout)) adversary parameter scalar
    _ _ (swappedTableTape E) (stageOneView E parameter scalar) (fun u weight => flag field group scalar u weight)
    (fun u x weight => touch field group parameter scalar u x weight)
  have smudgeNonneg : 0 ≤ smudgeError + exceptionalError := by
    unfold smudgeError exceptionalError
    exact add_nonneg (frac_nonneg _ _) (frac_nonneg _ _)
  have chargeNonneg : 0 ≤ stageOneTouchCharge := by
    unfold stageOneTouchCharge
    first
      | exact frac_nonneg _ _
      | (unfold crtHiddenCharge; exact frac_nonneg _ _)
  calc (middleGame E shadow (tableRun (swappedTableLaw E.layout)) adversary parameter scalar none).toReal
      ≤ (ENNReal.ofReal (smudgeError + exceptionalError) +
          (adversary.firstQueryBudget parameter : ℝ≥0∞) * ENNReal.ofReal stageOneTouchCharge).toReal :=
        ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) bound
    _ = smudgeError + exceptionalError + (adversary.firstQueryBudget parameter : ℝ) * stageOneTouchCharge := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by simp [ENNReal.mul_eq_top]), ENNReal.toReal_mul,
          ENNReal.toReal_ofReal smudgeNonneg, ENNReal.toReal_ofReal chargeNonneg, ENNReal.toReal_natCast]
    _ = stageOneTouchError (adversary.firstQueryBudget parameter) + smudgeError + exceptionalError := by
        unfold stageOneTouchError
        ring

end

end Kriterion.CRT.Privacy.Flags
