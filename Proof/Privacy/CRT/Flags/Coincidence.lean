/-
**P8, the coincidence flag: the bound under `G1U`'s stage 1 from a per-input guess** (port of xinshu's
`PublicFirst/LiftGuess.lean` to the CRT games).

`CrtCoincidenceBound` (`PublicFirst/Hop.lean`) asks the mass of `Coincide` under `G1U`'s stage 1, where the input is
the adversary's, chosen after the stage-1 view. In the hash-only CRT the stage-1 oracle is empty, so the view is the
published value alone (`stageOneView`). As in the hidden hop, it suffices to bound, **for every fixed input**, the
coincidence mass against every weight on the view (`CrtCoincidenceGuess`): the adaptive choice is absorbed exactly,
because the stage-1 law of each outcome is a function of the view (`coincidenceMass_eq`).

* `coincideWeight`, `stageOneAt`, `coincidenceMass_eq`, `coincidenceMass_le`;
* `CrtCoincidenceGuess error`: the per-input guessing bound (the P8 row that carries the mathematics: the 182 digest
  keys `key(u) = key_s` with `u ≠ exc_s`, two final sites per digit, and off the curve the mask key `K' = K`);
* `crtCoincidenceBound_of_guess`.
-/

import Proof.Privacy.CRT.PublicFirst.Hop

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

section Guess

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

open Classical in
/-- The coincidence indicator at a fixed input. -/
def coincideWeight (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E)
    (u : AffineInput) : ℝ≥0∞ :=
  if Coincide E T parameter scalar tape u then 1 else 0

/-- The stage-1 law of an outcome, from the view (the published value; the stage-1 oracle is empty). -/
def stageOneAt (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (view : E.Public)
    (selected : (AffineInput × adversary.State) × LazyOracle.State FI EI) : ℝ≥0∞ :=
  LazyOracle.run (adversary.chooseInput parameter view ()) LazyOracle.empty selected

open Classical in
/-- **The coincidence mass, stage 1 first.** -/
theorem coincidenceMass_eq (T : CrtTable) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    coincidenceMass E T adversary parameter scalar =
      ∑' tape, swappedTableTape E tape *
        ∑' selected, stageOneAt E adversary parameter (stageOneView E parameter scalar tape) selected *
          coincideWeight E T parameter scalar tape selected.1.1 := by
  unfold coincidenceMass stageOneLaw
  rewrite [toOuterMeasure_eq_tsum, tsum_bind_mul]
  refine tsum_congr fun tape => ?_
  rewrite [tsum_map_mul]
  refine congrArg (fun value => swappedTableTape E tape * value) (tsum_congr fun selected => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  unfold coincideWeight
  by_cases hit : Coincide E T parameter scalar tape selected.1.1
  · have inside : (tape, selected) ∈ {x : TableTape E × ((AffineInput × adversary.State) ×
        LazyOracle.State FI EI) | Coincide E T parameter scalar x.1 x.2.1.1} := hit
    rw [if_pos inside, if_pos hit]
  · have outside : (tape, selected) ∉ {x : TableTape E × ((AffineInput × adversary.State) ×
        LazyOracle.State FI EI) | Coincide E T parameter scalar x.1 x.2.1.1} := hit
    rw [if_neg outside, if_neg hit]

/-- **The coincidence mass from a per-input guessing bound.** -/
theorem coincidenceMass_le (T : CrtTable) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) (error : ℝ≥0∞)
    (guess : ∀ (u : AffineInput) (weight : E.Public → ℝ≥0∞),
      ∑' tape, swappedTableTape E tape *
          (weight (stageOneView E parameter scalar tape) * coincideWeight E T parameter scalar tape u)
        ≤ error * ∑' tape, swappedTableTape E tape * weight (stageOneView E parameter scalar tape)) :
    coincidenceMass E T adversary parameter scalar ≤ error := by
  rw [coincidenceMass_eq]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  calc ∑' selected, ∑' tape, swappedTableTape E tape *
        (stageOneAt E adversary parameter (stageOneView E parameter scalar tape) selected *
          coincideWeight E T parameter scalar tape selected.1.1)
      ≤ ∑' selected, error * ∑' tape, swappedTableTape E tape *
          stageOneAt E adversary parameter (stageOneView E parameter scalar tape) selected :=
        ENNReal.tsum_le_tsum fun selected =>
          guess selected.1.1 fun view => stageOneAt E adversary parameter view selected
    _ = error * ∑' tape, swappedTableTape E tape *
          ∑' selected, stageOneAt E adversary parameter (stageOneView E parameter scalar tape) selected := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left]
    _ = error := by
        have total : ∀ tape, ∑' selected,
            stageOneAt E adversary parameter (stageOneView E parameter scalar tape) selected = 1 :=
          fun tape => PMF.tsum_coe _
        simp only [total, mul_one, PMF.tsum_coe]

end Guess

/-- **The per-input guessing bound** (P8): at every fixed input, against every weight on the stage-1 view, the reach's
entries differ from the designed ones with mass at most `error`. -/
def CrtCoincidenceGuess [fixedFinite : Finite FI] [encFinite : Finite EI] (T : CrtTable) (error : ℝ≥0∞) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput),
    (letI := field
     letI := group
     letI := @Fintype.ofFinite FI fixedFinite
     letI := @Fintype.ofFinite EI encFinite
     letI := Classical.decEq FI
     letI := Classical.decEq EI
     ∀ weight : E.Public → ℝ≥0∞,
       ∑' tape, swappedTableTape E tape *
           (weight (stageOneView E parameter scalar tape) * coincideWeight E T parameter scalar tape u)
         ≤ error * ∑' tape, swappedTableTape E tape * weight (stageOneView E parameter scalar tape))

/-- **`CrtCoincidenceBound` from the per-input guessing bound.** -/
theorem crtCoincidenceBound_of_guess [fixedFinite : Finite FI] [encFinite : Finite EI] (T : CrtTable)
    (guess : CrtCoincidenceGuess E T (ENNReal.ofReal coincidenceError)) :
    CrtCoincidenceBound E T coincidenceError := by
  intro field group adversary parameter scalar _
  letI := field
  letI := group
  letI := @Fintype.ofFinite FI fixedFinite
  letI := @Fintype.ofFinite EI encFinite
  letI := Classical.decEq FI
  letI := Classical.decEq EI
  have bound := coincidenceMass_le E T adversary parameter scalar _
    (fun u => guess field group parameter scalar u)
  have nonneg : 0 ≤ coincidenceError := by unfold coincidenceError; exact frac_nonneg _ _
  calc (coincidenceMass E T adversary parameter scalar).toReal
      ≤ (ENNReal.ofReal coincidenceError).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
    _ = coincidenceError := ENNReal.toReal_ofReal nonneg

end

end Kriterion.CRT.Privacy.Flags
