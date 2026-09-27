/-
**The sampler cutoff of the CRT machine law** (`LawShape.SamplerCutoff`, the third part of M7).

`I` runs route M with the exact samplers (`LawShape.exactSamplers`) and `B` with the machine's bounded ones
(`LawShape.boundedHybrid`); nothing else differs. A hybrid over the four sampler knobs bounds the two games by the
source's distance, the rows kernel's worst distance at a valid input, and `273` times the preimage's and the fourth
block's worst distances (one each per collector, `drawAll_etvDist_le`): `samplerCutoff_of`.
-/

import Proof.Simulator.CRT.LawShape
import Proof.Privacy.CRT.Refill.Hop
import Proof.Simulator.CutoffMass
import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.SimMachine.Cutoff

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC
open Kriterion.CRT.Privacy (RouteMView Reader lazyReader routeMReplay collectorMasks drawAll collectorList
  programHashAll programRequests)
open Kriterion.CRT.SimMachine.LawShape
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le_const advantage_eq_etvDist)
open scoped ENNReal

noncomputable section

/-! ### Distances through binds -/

/-- Two first draws and two continuations: the draws' distance plus the continuations' worst distance. -/
theorem etvDist_bind_bind_le {α β : Type} (p q : PMF α) (f g : α → PMF β) (c : ℝ≥0∞)
    (each : ∀ a, (f a).etvDist (g a) ≤ c) : (p.bind f).etvDist (q.bind g) ≤ p.etvDist q + c :=
  (PMF.etvDist_triangle _ (q.bind f) _).trans
    (add_le_add (PMF.etvDist_bind_right_le _ _ _) (etvDist_bind_left_le_const _ _ _ _ each))

/-- **Independent draws over a list**: at most the sum of the per-element distances. -/
theorem drawAll_etvDist_le {α β : Type} (f g : α → PMF (Option β)) (c : ℝ≥0∞) (each : ∀ a, (f a).etvDist (g a) ≤ c) :
    ∀ L : List α, (drawAll f L).etvDist (drawAll g L) ≤ L.length * c
  | [] => by simp [drawAll]
  | a :: rest => by
      have ih := drawAll_etvDist_le f g c each rest
      simp only [drawAll]
      refine (etvDist_bind_bind_le _ _ _ _ ((rest.length : ℝ≥0∞) * c) fun drawn => ?_).trans ?_
      · cases drawn with
        | none => simp
        | some b => exact (Kriterion.ArgoMAC.Security.Phase3.etvDist_map_le' _ _ _).trans ih
      · rw [List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm]
        exact add_le_add_right (each a) _

theorem collectorList_length : collectorList.length = 273 := by
  simp [collectorList, List.length_flatMap]

/-- One collector's draw: the preimage's distance plus the fourth block's. -/
theorem collectorDraw_etvDist_le {Source : Type} [FieldCertificate] (S1 S2 : RouteMSamplers Source) (δp δf : ℝ≥0∞)
    (preimage : ∀ x, (S1.preimage x).etvDist (S2.preimage x) ≤ δp) (fourth : S1.fourth.etvDist S2.fourth ≤ δf)
    (x : BaseField) :
    ((S1.preimage x).bind fun limbs => match limbs with
        | none => PMF.pure none
        | some limbs => S1.fourth.map (Option.map fun fourth => (limbs, fourth))).etvDist
      ((S2.preimage x).bind fun limbs => match limbs with
        | none => PMF.pure none
        | some limbs => S2.fourth.map (Option.map fun fourth => (limbs, fourth))) ≤ δp + δf := by
  refine (etvDist_bind_bind_le _ _ _ _ δf fun limbs => ?_).trans (add_le_add (preimage x) le_rfl)
  cases limbs with
  | none => simp
  | some limbs => exact (Kriterion.ArgoMAC.Security.Phase3.etvDist_map_le' _ _ _).trans fourth

/-- **Route M with two sets of samplers**: the source's distance, the rows kernel's worst distance at a valid input,
and `273` times the preimage's and the fourth block's worst distances. -/
theorem routeMWith_etvDist_le [FieldCertificate] {FI EI Randomness Public Key Oracle Aux : Type}
    [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (view : RouteMView Public) (S1 S2 : RouteMSamplers view.Source) (reader : Reader FI EI)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : ℕ) (scalar : NonZeroScalar) (auxiliary : Aux) (δr δp δf : ℝ≥0∞)
    (rows : ∀ u target, scheme.function scalar u = some target → (S1.rows u target).etvDist (S2.rows u target) ≤ δr)
    (preimage : ∀ x, (S1.preimage x).etvDist (S2.preimage x) ≤ δp) (fourth : S1.fourth.etvDist S2.fourth ≤ δf) :
    (Privacy.abstractIdealGame scheme (routeMWith view S1 reader) adversary parameter scalar auxiliary).etvDist
        (Privacy.abstractIdealGame scheme (routeMWith view S2 reader) adversary parameter scalar auxiliary)
      ≤ S1.source.etvDist S2.source + (δr + 273 * (δp + δf)) := by
  rw [Privacy.Refill.abstractIdealGame_eq_staged, Privacy.Refill.abstractIdealGame_eq_staged]
  unfold Privacy.Refill.stagedGame
  refine (etvDist_bind_bind_le _ _ _ _ _ (fun first => ?_)).trans
    (add_le_add (Kriterion.ArgoMAC.Security.Phase3.etvDist_map_le' _ _ _) le_rfl)
  rcases first with _ | ⟨circuit, state, oracle⟩
  · simp
  refine etvDist_bind_left_le_const _ _ _ _ fun selected => ?_
  cases output : scheme.function scalar selected.1.1 with
  | none => simp [routeMWith]
  | some target =>
      simp only [routeMWith, PMF.bind_bind]
      refine etvDist_bind_left_le_const _ _ _ _ fun ran => ?_
      refine (etvDist_bind_bind_le _ _ _ _ _ (fun drawnRows => ?_)).trans
        (add_le_add (rows _ _ output) le_rfl)
      cases drawnRows with
      | none => simp
      | some targets =>
          simp only [PMF.bind_map]
          refine (PMF.etvDist_bind_right_le _ _ _).trans ?_
          refine (drawAll_etvDist_le _ _ (δp + δf) (fun c =>
            collectorDraw_etvDist_le S1 S2 δp δf preimage fourth _) collectorList).trans ?_
          rw [collectorList_length]
          norm_num

/-- **The sampler cutoff from per-sampler bounds** (generic in the entry): if the bounded source is within `δs` of the
uniform source, the bounded rows within `δr` of the view's simulated rows at every valid input, the bounded preimage
within `δp` of the view's at every value, and the bounded fourth block within `δf` of the view's, and
`δs + δr + 273 (δp + δf)` is at most `machineCutoffError`, then `SamplerCutoff` holds. -/
theorem samplerCutoff_of {FI EI : Type} [Finite FI] [Finite EI] (E : Privacy.CrtEntry FI EI) (bounded : BoundedSamplers E)
    (δs δr δp δf : ℝ≥0∞)
    (source : ∀ (field : FieldCertificate) (group : @GroupCertificate field),
      (letI := (E.view field group).sourceFintype
       letI := (E.view field group).sourceNonempty
       (PMF.uniformOfFintype (E.view field group).Source).map some).etvDist (bounded field group).source ≤ δs)
    (rows : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar) (u : AffineInput)
      (target : @Point field), (E.scheme field group).function scalar u = some target →
        ((E.view field group).simRows scalar u target).etvDist ((bounded field group).rows u target) ≤ δr)
    (preimage : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (x : BaseField),
      ((E.view field group).preimage x).etvDist ((bounded field group).preimage x) ≤ δp)
    (fourth : ∀ (field : FieldCertificate) (group : @GroupCertificate field),
      (E.view field group).fourth.etvDist (bounded field group).fourth ≤ δf)
    (total : δs + (δr + 273 * (δp + δf)) ≤ ENNReal.ofReal Privacy.machineCutoffError) :
    SamplerCutoff E bounded := by
  intro field group adversary parameter scalar
  simp only [Privacy.atSolution, Privacy.crtChain]
  rw [advantage_eq_etvDist]
  refine ENNReal.toReal_le_of_le_ofReal (Privacy.frac_nonneg _ _) ?_
  let _fintypeFI := Fintype.ofFinite FI
  let _fintypeEI := Fintype.ofFinite EI
  let _decFI := Classical.decEq FI
  let _decEI := Classical.decEq EI
  unfold Privacy.idealHybrid boundedHybrid
  rw [routeMSimulator_eq_with]
  refine (routeMWith_etvDist_le _ _ _ _ _ adversary parameter scalar () δr δp δf
    (fun u target valid => rows field group scalar u target valid) (preimage field group) (fourth field group)).trans ?_
  refine le_trans (add_le_add ?_ le_rfl) total
  exact source field group

/-! ### Abort-closeness gives the distance -/

open Kriterion.ArgoMAC.PlanB.SimMachine (AbortClose none_add_tsum_some tsum_some_le_one)

/-- **A bounded sampler abort-close to an exact one is within the extra abort mass.** -/
theorem abortClose_etvDist_le {α : Type} {ε : ℝ≥0∞} {b i : PMF (Option α)} (close : AbortClose ε b i) :
    i.etvDist b ≤ ε := by
  have hb := none_add_tsum_some b
  have hi := none_add_tsum_some i
  have le : ∑' a, b (some a) ≤ ∑' a, i (some a) := ENNReal.tsum_le_tsum close.1
  have biFin : ∑' a, b (some a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_some_le_one b)
  have iiFin : ∑' a, i (some a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_some_le_one i)
  have iNoneFin : i none ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hi ▸ le_self_add)
  have noneLe : i none ≤ b none := by
    refine (ENNReal.add_le_add_iff_right iiFin).mp ?_
    rw [hi, ← hb]
    exact add_le_add le_rfl le
  -- the value masses differ by the abort masses' difference
  have diff : ∑' a, i (some a) - ∑' a, b (some a) = b none - i none := by
    have split : ∑' a, i (some a) = ∑' a, b (some a) + (∑' a, i (some a) - ∑' a, b (some a)) :=
      (add_tsub_cancel_of_le le).symm
    have total : i none + (∑' a, i (some a) - ∑' a, b (some a)) + ∑' a, b (some a) = b none + ∑' a, b (some a) := by
      rw [hb, add_assoc, add_comm (_ - _), ← split, hi]
    have cancel := (ENNReal.add_left_inj biFin).mp total
    rw [← cancel, ENNReal.add_sub_cancel_left iNoneFin]
  unfold PMF.etvDist
  rw [Kriterion.ArgoMAC.PlanB.SimMachine.tsum_option]
  have noneTerm : ENNReal.absDiff (i none) (b none) = b none - i none := by
    unfold ENNReal.absDiff
    rw [tsub_eq_zero_of_le noneLe, zero_add]
  have someTerm : ∑' a, ENNReal.absDiff (i (some a)) (b (some a)) = ∑' a, i (some a) - ∑' a, b (some a) := by
    have eq : ∑' a, i (some a) = ∑' a, b (some a) + ∑' a, (i (some a) - b (some a)) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun a => (add_tsub_cancel_of_le (close.1 a)).symm
    have sub : ∑' a, (i (some a) - b (some a)) = ∑' a, i (some a) - ∑' a, b (some a) :=
      ENNReal.eq_sub_of_add_eq biFin (by rw [add_comm]; exact eq.symm)
    rw [← sub]
    refine tsum_congr fun a => ?_
    unfold ENNReal.absDiff
    rw [tsub_eq_zero_of_le (close.1 a), add_zero]
  rw [noneTerm, someTerm, diff, ← two_mul]
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm]
  exact mul_le_mul' (tsub_le_iff_left.mpr close.2) le_rfl

/-! ### The machine's rows, preimage and fourth samplers at the CRT entry -/

section Concrete

open Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.Phase3.Glue

variable [FieldCertificate] [GroupCertificate]

/-- **The machine's rows kernel**: xinshu's tail and lift laws through `targetRows`, the shape of `simulatedRows`. -/
def boundedRows : AffineInput → Point → PMF (Option (Fin digitCount → FieldMacToECMac.HomogeneousValue)) :=
  fun _ target => tailLaw.bind fun tail => match tail with
    | none => PMF.pure none
    | some tail => liftLaw.bind fun lift => match lift with
      | none => PMF.pure none
      | some lift => PMF.pure (some (targetRows target tail lift))

/-- The rows' extra abort mass: the tail's and the lifts' (`91` randomiser pairs). -/
def rowsMass : ℝ≥0∞ :=
  (90 * rejectLaw fieldWidth curveXAccept attempts none + (affineCount : ℝ≥0∞)⁻¹) +
    ((digitCount : ℝ≥0∞) * (((2 : Nat) : ℝ≥0∞) *
      rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none) + 0)

theorem boundedRows_close (u : AffineInput) (target : Point) :
    AbortClose rowsMass (boundedRows u target) (Security.Phase3.simulatedRows u target) := by
  have lift := AbortClose.optionProduct digitCount (fun _ => pairLaw)
    (fun _ => (PMF.uniformOfFintype (NonZeroBase × NonZeroBase)).map some) (fun _ => pair_close)
  rw [optionProduct_uniform] at lift
  unfold boundedRows Security.Phase3.simulatedRows rowsMass
  refine AbortClose.bind_opt tail_close _ _ rfl rfl fun tail => ?_
  exact AbortClose.bind_opt lift _ _ rfl rfl fun _ => AbortClose.refl _

/-- The rows' extra abort mass is below `2^-129`. -/
theorem rowsMass_le : rowsMass ≤ ((2 : ℝ≥0∞) ^ 129)⁻¹ := by
  have points : ((90 : Nat) : ℝ≥0∞) * rejectLaw fieldWidth curveXAccept attempts none ≤ ((2 : ℝ≥0∞) ^ 131)⁻¹ :=
    (mul_le_mul' le_rfl curveXAbort_le).trans
      (mul_inv_pow_le 90 170 131 (count_le _ 7 131 170 (by decide) (by decide)))
  rw [Nat.cast_ofNat] at points
  have tailPart : 90 * rejectLaw fieldWidth curveXAccept attempts none + (affineCount : ℝ≥0∞)⁻¹ ≤
      ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
    rw [← inv_pow_add_self 130 131 rfl]
    exact add_le_add points affineCount_inv_le
  have lambdas : (digitCount : ℝ≥0∞) * (((2 : Nat) : ℝ≥0∞) *
      rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none) ≤
      ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
    rw [← mul_assoc, ← Nat.cast_mul]
    exact (mul_le_mul' le_rfl lambdaAbort_le).trans (mul_inv_pow_le _ 500 130
      (count_le _ 8 130 500 (by unfold digitCount; decide) (by decide)))
  unfold rowsMass
  rw [add_zero, ← inv_pow_add_self 129 130 rfl]
  exact add_le_add tailPart lambdas

/-- `273` preimages' extra abort mass is below `2^-130`. -/
theorem preimagesMass_le : (273 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 399)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
  have := mul_inv_pow_le 273 399 130 (count_le _ 9 130 399 (by decide) (by decide))
  simpa using this

end Concrete

end

end Kriterion.CRT.SimMachine.Cutoff
