/-
**P8's zero-`Δ` row: `CrtDeltaGuess`** (for `Flags/CoincidenceSplit.lean`).

Against every weight on the published value, one of the two input `Δ`s is zero with mass at most `2/2^128` under the
swapped tape. Each coordinate's `Δ` is uniform and independent of the fine view (`DeltaView.fine_split`),
and the published value is a function of the fine view (`StageOneFactors`); so the weighted mass of `Δ_κ = 0` is exactly `2^-128` of the total weight (`weighted_residual_eq`), and the
union over the two coordinates gives `2/2^128`.
-/

import Proof.Privacy.CRT.Hidden.DeltaView
import Proof.Privacy.CRT.Flags.CoincidenceSplit

set_option autoImplicit false

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.Instance (crtEntry)
open scoped ENNReal

noncomputable section

namespace DeltaGuess

open Kriterion.CRT.Privacy.PublicFirst (tsum_bind_mul tsum_map_mul)

/-- **A uniform residual independent of a fine view**: against any weight on a coarser view, the weighted mass of
"the residual is `r₀`" is `1/#R` of the total weight. -/
theorem weighted_residual_eq {Ω V W R : Type} [Fintype R] [Nonempty R] (μ : PMF Ω) (view : Ω → V)
    (fine : Ω → W) (coarse : W → V) (hview : ∀ ω, view ω = coarse (fine ω)) (res : Ω → R)
    (hsplit : μ.map (fun ω => (fine ω, res ω)) =
      (μ.map fine).bind fun w => (PMF.uniformOfFintype R).map fun r => (w, r))
    (weight : V → ℝ≥0∞) (r₀ : R) :
    ∑' ω, μ ω * (weight (view ω) * Flags.ind (res ω = r₀)) =
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑' ω, μ ω * weight (view ω) := by
  classical
  let h : W × R → ℝ≥0∞ := fun p => weight (coarse p.1) * Flags.ind (p.2 = r₀)
  have lhs : ∑' ω, μ ω * (weight (view ω) * Flags.ind (res ω = r₀)) =
      ∑' p, (μ.map fun ω => (fine ω, res ω)) p * h p := by
    rw [tsum_map_mul]
    refine tsum_congr fun ω => ?_
    rw [hview ω]
  have inner : ∀ w, ∑' q, ((PMF.uniformOfFintype R).map fun r => (w, r)) q * h q =
      weight (coarse w) * (Fintype.card R : ℝ≥0∞)⁻¹ := by
    intro w
    rw [tsum_map_mul]
    show ∑' r, (PMF.uniformOfFintype R) r * (weight (coarse w) * Flags.ind (r = r₀)) = _
    rw [tsum_eq_single r₀ fun r ne => by rw [Flags.ind, if_neg ne, mul_zero, mul_zero],
      Flags.ind_of rfl, mul_one, PMF.uniformOfFintype_apply, mul_comm]
  rw [lhs, hsplit, tsum_bind_mul]
  simp only [inner]
  have rhs : ∑' ω, μ ω * weight (view ω) = ∑' w, (μ.map fine) w * weight (coarse w) := by
    rw [tsum_map_mul]
    refine tsum_congr fun ω => ?_
    rw [hview ω]
  rw [rhs, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun w => ?_
  ring

theorem ind_or_le (P Q : Prop) : Flags.ind (P ∨ Q) ≤ Flags.ind P + Flags.ind Q := by
  classical
  unfold Flags.ind
  by_cases p : P
  · rw [if_pos (Or.inl p), if_pos p]
    exact le_self_add
  · by_cases q : Q
    · rw [if_pos (Or.inr q), if_pos q]
      exact le_add_self
    · rw [if_neg (by tauto)]
      exact zero_le

end DeltaGuess

/-- **The published value is a function of the fine view** (the named fact `crtDeltaGuess_of` needs; `Hidden/DeltaView.lean`, at stage 1): for each coordinate there is an input at which two
tapes with the same fine view publish the same value. -/
def StageOneFactors : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (κ : Fin 2),
    ∃ u : AffineInput, ∀ tape tape' : TableTape crtEntry,
      DeltaView.fine parameter scalar u κ tape = DeltaView.fine parameter scalar u κ tape' →
        stageOneView crtEntry parameter scalar tape = stageOneView crtEntry parameter scalar tape'

open DeltaGuess in
/-- **`CrtDeltaGuess` for the concrete entry**, from the stage-1 functional dependence. -/
theorem crtDeltaGuess_of (factors : StageOneFactors) : Flags.CrtDeltaGuess := by
  intro field group parameter scalar
  letI := field
  letI := group
  intro weight
  classical
  -- one coordinate: the weighted mass of `Δ_κ = 0` is `2^-128` of the total
  have single : ∀ κ : Fin 2,
      ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) * Flags.ind (DeltaView.res κ tape = 0)) =
        ((2 : ℝ≥0∞) ^ 128)⁻¹ *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
    intro κ
    obtain ⟨u, fd⟩ := factors parameter scalar κ
    let weight' : DeltaView.WType → ℝ≥0∞ := fun w =>
      @dite _ (∃ tape, DeltaView.fine parameter scalar u κ tape = w) (Classical.propDecidable _)
        (fun h => weight (stageOneView crtEntry parameter scalar h.choose)) (fun _ => 0)
    have hview : ∀ tape, weight (stageOneView crtEntry parameter scalar tape) =
        weight' (DeltaView.fine parameter scalar u κ tape) := by
      intro tape
      have exists_ : ∃ tape', DeltaView.fine parameter scalar u κ tape' =
          DeltaView.fine parameter scalar u κ tape := ⟨tape, rfl⟩
      show _ = @dite _ _ (Classical.propDecidable _) _ _
      rw [dif_pos exists_, fd tape _ exists_.choose_spec.symm]
    have card : (Fintype.card Block : ℝ≥0∞) = 2 ^ 128 := by
      have cardNat : Fintype.card Block = 2 ^ 128 :=
        (Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ :
          Block ≃ Fin (2 ^ 128))).trans (Fintype.card_fin _)
      rw [cardNat, Nat.cast_pow, Nat.cast_ofNat]
    refine (weighted_residual_eq (swappedTableTape crtEntry)
      (fun tape => weight (stageOneView crtEntry parameter scalar tape)) (DeltaView.fine parameter scalar u κ)
      weight' hview (DeltaView.res κ) (DeltaView.fine_split parameter scalar u κ) id 0).trans ?_
    rw [card]
    rfl
  have resX : ∀ tape : TableTape crtEntry, DeltaView.res 0 tape = tape.1.inputDelta .x := fun tape => by
    unfold DeltaView.res
    exact DeltaView.deltaAt_eq_deltaOf tape.1 0
  have resY : ∀ tape : TableTape crtEntry, DeltaView.res 1 tape = tape.1.inputDelta .y := fun tape => by
    unfold DeltaView.res
    exact DeltaView.deltaAt_eq_deltaOf tape.1 1
  have singleX := single 0
  have singleY := single 1
  simp only [resX, resY] at singleX singleY
  calc ∑' tape, swappedTableTape crtEntry tape *
        (weight (stageOneView crtEntry parameter scalar tape) *
          Flags.ind (tape.1.inputDelta .x = 0 ∨ tape.1.inputDelta .y = 0))
      ≤ ∑' tape, (swappedTableTape crtEntry tape *
            (weight (stageOneView crtEntry parameter scalar tape) * Flags.ind (tape.1.inputDelta .x = 0)) +
          swappedTableTape crtEntry tape *
            (weight (stageOneView crtEntry parameter scalar tape) * Flags.ind (tape.1.inputDelta .y = 0))) := by
        refine ENNReal.tsum_le_tsum fun tape => ?_
        rw [← mul_add, ← mul_add]
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (ind_or_le _ _))
    _ = ((2 : ℝ≥0∞) ^ 128)⁻¹ *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) +
        ((2 : ℝ≥0∞) ^ 128)⁻¹ *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
        rw [ENNReal.tsum_add, singleX, singleY]
    _ = ENNReal.ofReal (2 / 2 ^ 128) *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
        rw [← add_mul]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, div_eq_mul_inv, two_mul]

end

end Kriterion.CRT.Paths
