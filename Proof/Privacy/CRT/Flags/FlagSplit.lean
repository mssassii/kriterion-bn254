/-
**P8, the flag guess split into no-abort, the doubling and the wrap** (for a shadow whose reveals are a row event `D`
on the curve and a state event `W`, as `H8.crtShadow`: `rowsDoubling ∨ replayWraps ∘ stateTable`, and
`replayWraps ∘ stateTable`).

At the empty stage-1 state, `M'`'s stage 2 flags on an abort or a reveal (`flagAt`). The reveal `D t ∨ W s` splits:

* `flagAt_le_rows`: the row event costs at most its mass under the rows kernel (`doublingAt`), whatever follows;
* `flagAt_le_state`: with the state event alone, the flag is an abort (the same stage 2 with no reveal at all,
  `withReveal … False`) or an unflagged final state in `W` (`wrapAt`).

`crtFlagGuess_of`: `CrtFlagGuess` from no abort, a doubling bound `δ` and a wrap bound `ω` (in the weight form).
-/

import Proof.Privacy.CRT.Flags.FlagMass

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst
open scoped ENNReal

noncomputable section

/-! ### 1. Reveals and weights -/

section Weights

variable {Source FI EI : Type}

/-- A shadow with its reveals replaced by one state event (the same on and off the curve). -/
def withReveal (shadow : CrtShadow Source FI EI) (W : Source → AffineInput → LazyOracle.State FI EI → Prop) :
    CrtShadow Source FI EI :=
  { shadow with
    revealOn := fun source u _ _ state => W source u state
    revealOff := fun source u _ state => W source u state }

open Classical in
/-- `1` on rows with the row event. -/
def rowsWeight (D : (Fin 91 → FieldMacToECMac.HomogeneousValue) → Prop) :
    Option (Fin 91 → FieldMacToECMac.HomogeneousValue) → ℝ≥0∞
  | some targets => if D targets then 1 else 0
  | none => 0

open Classical in
/-- `1` on an unflagged outcome whose state has the state event. -/
def stateWeight (W : LazyOracle.State FI EI → Prop) : Outcome FI EI → ℝ≥0∞
  | some (some (_, state)) => if W state then 1 else 0
  | _ => 0

theorem tsum_le_add {α : Type} (μ : PMF α) (L A C : α → ℝ≥0∞) (each : ∀ a, L a ≤ A a + C a) :
    ∑' a, μ a * L a ≤ ∑' a, μ a * A a + ∑' a, μ a * C a := by
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; exact mul_le_mul' le_rfl (each a)

theorem tsum_le_add_const {α : Type} (μ : PMF α) (L A : α → ℝ≥0∞) (c : ℝ≥0∞) (each : ∀ a, L a ≤ A a + c) :
    ∑' a, μ a * L a ≤ ∑' a, μ a * A a + c := by
  calc ∑' a, μ a * L a ≤ ∑' a, μ a * (A a + c) := ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (each a)
    _ = ∑' a, μ a * A a + c := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem tsum_flagDown_le_one (μ : PMF (Outcome FI EI)) : ∑' o, μ o * flagDown o ≤ 1 := by
  calc ∑' o, μ o * flagDown o ≤ ∑' o, μ o * 1 := ENNReal.tsum_le_tsum fun o => mul_le_mul' le_rfl (by
        rcases o with _ | _ | _ <;> simp [flagDown])
    _ = 1 := by simp only [mul_one, PMF.tsum_coe]

end Weights

/-! ### 2. The leaves -/

section Leaves

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- A state event at the ending: a flag without it is none, the event is the outcome's. -/
theorem finish_state_le (labels : LamportSignature) (W : LazyOracle.State FI EI → Prop)
    (invariant : ∀ state, W (mergeState LazyOracle.empty state) ↔ W state) (state : LazyOracle.State FI EI) :
    flagDown (finishPrivate LazyOracle.empty labels (W state) state) ≤
      flagDown (finishPrivate LazyOracle.empty labels False state) +
        stateWeight W (finishPrivate LazyOracle.empty labels False state) := by
  unfold finishPrivate
  rw [if_neg (show ¬ (Meets LazyOracle.empty state ∨ False) from
    fun either => either.elim (not_meets_empty state) id)]
  by_cases event : W state
  · rw [if_pos (show Meets LazyOracle.empty state ∨ W state from Or.inr event)]
    simp only [flagDown, stateWeight, if_pos ((invariant state).mpr event), zero_add]
    exact le_rfl
  · rw [if_neg (show ¬ (Meets LazyOracle.empty state ∨ W state) from
      fun either => either.elim (not_meets_empty state) event)]
    simp [flagDown]

end Leaves

/-! ### 3. The two splits -/

variable {FI EI : Type} (E : CrtEntry FI EI)

section Split

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The row event's mass under the rows kernel (none off the curve). -/
def doublingAt (scalar : NonZeroScalar) (u : AffineInput)
    (D : (Fin 91 → FieldMacToECMac.HomogeneousValue) → Prop) : ℝ≥0∞ :=
  match (E.scheme inferInstance inferInstance).function scalar u with
  | some Q => ∑' r, (viewHere E).realRows scalar u Q r * rowsWeight D r
  | none => 0

/-- The mass of an unflagged final state with the state event, in the stage 2 with no reveal. -/
def wrapAt (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI) (scalar : NonZeroScalar)
    (source : (viewHere E).Source) (u : AffineInput)
    (W : (viewHere E).Source → AffineInput → LazyOracle.State FI EI → Prop) : ℝ≥0∞ :=
  ∑' o, middleStage2 E (withReveal shadow fun _ _ _ => False) offRun scalar source u
    ((E.scheme inferInstance inferInstance).function scalar u) LazyOracle.empty o * stateWeight (W source u) o

/-- **The row event costs its rows mass.** -/
theorem flagAt_le_rows (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput)
    (D : (Fin 91 → FieldMacToECMac.HomogeneousValue) → Prop)
    (W : (viewHere E).Source → AffineInput → LazyOracle.State FI EI → Prop)
    (onSplit : ∀ targets coin state, shadow.revealOn source u targets coin state ↔ D targets ∨ W source u state)
    (offSplit : ∀ coin state, shadow.revealOff source u coin state ↔ W source u state) :
    flagAt E shadow offRun scalar source u ≤
      flagAt E (withReveal shadow W) offRun scalar source u + doublingAt E scalar u D := by
  unfold flagAt doublingAt
  generalize (E.scheme inferInstance inferInstance).function scalar u = output
  cases output with
  | none =>
    have same : ∀ coin state, shadow.revealOff source u coin state = W source u state := fun coin state =>
      propext (offSplit coin state)
    simp only [middleStage2, withReveal, same, add_zero]
    exact le_rfl
  | some target =>
    simp only [middleStage2, withReveal]
    rw [tsum_bind_mul, tsum_bind_mul]
    refine tsum_le_add_const _ _ _ _ fun ran => ?_
    rw [if_neg (not_meets_empty ran.2), if_neg (not_meets_empty ran.2), tsum_bind_mul, tsum_bind_mul]
    refine tsum_le_add _ _ _ _ fun drawnRows => ?_
    rcases drawnRows with _ | targets
    · simp only [rowsWeight, add_zero]
      exact le_rfl
    · by_cases event : D targets
      · simp only [rowsWeight, if_pos event]
        exact le_trans (tsum_flagDown_le_one _) le_add_self
      · have same : ∀ coin state, shadow.revealOn source u targets coin state = W source u state :=
          fun coin state => propext ((onSplit targets coin state).trans (or_iff_right event))
        simp only [rowsWeight, if_neg event, add_zero, same]
        exact le_rfl

/-- **With a state event alone, a flag is an abort or an unflagged final state with the event.** -/
theorem flagAt_le_state (shadow : CrtShadow (viewHere E).Source FI EI) (offRun : OffRun FI EI)
    (scalar : NonZeroScalar) (source : (viewHere E).Source) (u : AffineInput)
    (W : (viewHere E).Source → AffineInput → LazyOracle.State FI EI → Prop)
    (invariant : ∀ state, W source u (mergeState LazyOracle.empty state) ↔ W source u state) :
    flagAt E (withReveal shadow W) offRun scalar source u ≤
      flagAt E (withReveal shadow fun _ _ _ => False) offRun scalar source u +
        wrapAt E shadow offRun scalar source u W := by
  unfold flagAt wrapAt
  generalize (E.scheme inferInstance inferInstance).function scalar u = output
  cases output with
  | none =>
    simp only [middleStage2, withReveal]
    rw [tsum_bind_mul, tsum_bind_mul, tsum_bind_mul]
    refine tsum_le_add _ _ _ _ fun coin => ?_
    rw [tsum_map_mul, tsum_map_mul, tsum_map_mul]
    exact tsum_le_add _ _ _ _ fun p => finish_state_le _ (W source u) invariant p.2
  | some target =>
    simp only [middleStage2, withReveal]
    rw [tsum_bind_mul, tsum_bind_mul, tsum_bind_mul]
    refine tsum_le_add _ _ _ _ fun ran => ?_
    simp only [if_neg (not_meets_empty ran.2)]
    rw [tsum_bind_mul, tsum_bind_mul, tsum_bind_mul]
    refine tsum_le_add _ _ _ _ fun drawnRows => ?_
    rcases drawnRows with _ | targets
    · dsimp only
      simp only [tsum_pure_mul_eq, flagDown, stateWeight, add_zero]
      exact le_rfl
    · dsimp only
      rw [tsum_bind_mul, tsum_bind_mul, tsum_bind_mul]
      refine tsum_le_add _ _ _ _ fun drawn => ?_
      rcases drawn with _ | drawn
      · dsimp only
        simp only [tsum_pure_mul_eq, flagDown, stateWeight, add_zero]
        exact le_rfl
      · dsimp only
        cases programHashAll (programRequests ran.1.key drawn) ran.2 with
        | none =>
          dsimp only
          simp only [tsum_pure_mul_eq, flagDown, stateWeight, add_zero]
          exact le_rfl
        | some installed =>
          dsimp only
          rw [tsum_bind_mul, tsum_bind_mul, tsum_bind_mul]
          refine tsum_le_add _ _ _ _ fun coin => ?_
          rw [tsum_map_mul, tsum_map_mul, tsum_map_mul]
          exact tsum_le_add _ _ _ _ fun p => finish_state_le _ (W source u) invariant p.2

end Split

/-! ### 4. `CrtFlagGuess` from its three parts -/

/-- **`CrtFlagGuess` from no abort, a doubling bound and a wrap bound.** -/
theorem crtFlagGuess_of [fixedFinite : Finite FI] [encFinite : Finite EI]
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI)
    (D : (Fin 91 → FieldMacToECMac.HomogeneousValue) → Prop)
    (W : ∀ [FieldCertificate] [GroupCertificate],
      (viewHere E).Source → AffineInput → LazyOracle.State FI EI → Prop)
    (onSplit : ∀ [FieldCertificate] [GroupCertificate] source u targets coin state,
      shadow.revealOn source u targets coin state ↔ D targets ∨ W source u state)
    (offSplit : ∀ [FieldCertificate] [GroupCertificate] source u coin state,
      shadow.revealOff source u coin state ↔ W source u state)
    (invariant : ∀ [FieldCertificate] [GroupCertificate] source u (state : LazyOracle.State FI EI),
      W source u (mergeState LazyOracle.empty state) ↔ W source u state)
    (δ ω : ℝ≥0∞)
    (noAbort : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar)
      (source : (viewHere E).Source) (u : AffineInput),
      letI := field
      letI := group
      letI := @Fintype.ofFinite FI fixedFinite
      letI := @Fintype.ofFinite EI encFinite
      letI := Classical.decEq FI
      letI := Classical.decEq EI
      flagAt E (withReveal shadow fun _ _ _ => False) (tableRun (swappedTableLaw E.layout)) scalar source u = 0)
    (doubling : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar)
      (u : AffineInput), (letI := field; letI := group; doublingAt E scalar u D) ≤ δ)
    (wrap : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar)
      (u : AffineInput),
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
              wrapAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u W)
          ≤ ω * ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
              weight ((viewHere E).publish source))) :
    CrtFlagGuess E shadow (δ + ω) := by
  intro field group scalar u
  letI := field
  letI := group
  letI := @Fintype.ofFinite FI fixedFinite
  letI := @Fintype.ofFinite EI encFinite
  letI := Classical.decEq FI
  letI := Classical.decEq EI
  letI := (viewHere E).sourceFintype
  haveI := (viewHere E).sourceNonempty
  intro weight
  have each : ∀ source, flagAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u ≤
      δ + wrapAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u W := by
    intro source
    calc _ ≤ flagAt E (withReveal shadow W) (tableRun (swappedTableLaw E.layout)) scalar source u +
          doublingAt E scalar u D :=
          flagAt_le_rows E shadow _ scalar source u D W (onSplit source u) (offSplit source u)
      _ ≤ (flagAt E (withReveal shadow fun _ _ _ => False) (tableRun (swappedTableLaw E.layout)) scalar source u +
            wrapAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u W) + δ :=
          add_le_add (flagAt_le_state E shadow _ scalar source u W (invariant source u))
            (doubling field group scalar u)
      _ = δ + wrapAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u W := by
          rw [noAbort field group scalar source u, zero_add, add_comm]
  calc ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        (weight ((viewHere E).publish source) * flagAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u)
      ≤ ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
          (weight ((viewHere E).publish source) *
            (δ + wrapAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u W)) :=
        ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl (mul_le_mul' le_rfl (each source))
    _ = δ * ∑' source, PMF.uniformOfFintype (viewHere E).Source source * weight ((viewHere E).publish source) +
          ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
            (weight ((viewHere E).publish source) *
              wrapAt E shadow (tableRun (swappedTableLaw E.layout)) scalar source u W) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun source => ?_
        ring
    _ ≤ δ * ∑' source, PMF.uniformOfFintype (viewHere E).Source source * weight ((viewHere E).publish source) +
          ω * ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
            weight ((viewHere E).publish source) :=
        add_le_add le_rfl (wrap field group scalar u weight)
    _ = (δ + ω) * ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
          weight ((viewHere E).publish source) := by ring

end

end Kriterion.CRT.Privacy.Flags
