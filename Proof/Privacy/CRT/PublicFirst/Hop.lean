/-
**P7, the public-first hop `G1U → HW`, part 2: the assembly** (port of xinshu's `LiftHop.planB_publicFirst_of_designed`
to the CRT chain).

The frozen hop `publicFirst` of `crt_oracleAdaptivePrivacy_of` follows from two named obligations:

* `CrtCoincidenceBound T coincidenceError` (P8): under `G1U`'s stage 1 the reach's entries differ from the designed
  ones with mass at most `185/2^128` (the 182 digest-key collisions `key(u) = key_s` with `u ≠ exc_s`, two final
  sites per digit, the off-curve mask key, the two `Δ = 0` events);
* `CrtMiddleObligation T` (P7 and P8): two flagged games, `upper` below `G1U°` and `lower` below `HW`, with `upper`'s
  flag mass at most `stageOneTouchError q₁ + smudgeError + exceptionalError` and their total variation at most
  `padSwapError` (the off-curve third swap). xinshu's `M'` and `M` are the intended witnesses.

`crt_publicFirst_of_designed`: the advantage of `G1U` against `HW` is at most the coincidence mass (the designed
hop, `designed_hop_le`) plus the overlap bound (`advantage_le_of_overlap_tv`), and `coreUntilBad_iff` turns the
advantage bound into the hop's `GameCoreUntilBad` shape.
-/

import Proof.Privacy.CRT.PublicFirst.Designed

namespace Kriterion.CRT.Privacy.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

/-- **The coincidence bound** (P8): under `G1U`'s stage 1, at the instances `Solution.adaptivePrivacy` installs, the
reach's entries differ from the designed ones with mass at most `error`. -/
def CrtCoincidenceBound [fixedFinite : Finite FI] [encFinite : Finite EI] (T : CrtTable) (error : ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      (letI := field
       letI := group
       letI := @Fintype.ofFinite FI fixedFinite
       letI := @Fintype.ofFinite EI encFinite
       letI := Classical.decEq FI
       letI := Classical.decEq EI
       coincidenceMass E T adversary parameter scalar).toReal ≤ error

/-- **The middle obligation** (P7 and P8): a flagged game below `G1U°` and one below `HW`, with the first's flag
mass at most the stage-1 touch, the wrap event and the doubling, and their total variation at most the third
swap. -/
def CrtMiddleObligation [Finite FI] [Finite EI] (T : CrtTable) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ upper lower : PMF (Option Bool),
        Below (atSolution (hiddenDesignedHybrid E T) field group adversary parameter scalar) upper ∧
        Below (atSolution (crtChain E).publicFirst field group adversary parameter scalar) lower ∧
        (upper none).toReal ≤
          stageOneTouchError (adversary.firstQueryBudget parameter) + smudgeError + exceptionalError ∧
        (upper.etvDist lower).toReal ≤ padSwapError

/-- **The public-first hop from the coincidence bound and the middle obligation.** -/
theorem crt_publicFirst_of_designed [fixedFinite : Finite FI] [encFinite : Finite EI] (T : CrtTable)
    (coincidence : CrtCoincidenceBound E T coincidenceError) (middle : CrtMiddleObligation E T) :
    GameCoreUntilBad (crtChain E).hiddenDeleted (crtChain E).publicFirst fun first _ =>
      stageOneTouchError first + smudgeError + exceptionalError + coincidenceError + padSwapError := by
  intro field group adversary parameter scalar small
  obtain ⟨upper, lower, belowDesigned, belowHW, mass, tv⟩ := middle field group adversary parameter scalar small
  have coincidenceLe := coincidence field group adversary parameter scalar small
  refine coreUntilBad_iff.mpr ?_
  letI := field
  letI := group
  letI := @Fintype.ofFinite FI fixedFinite
  letI := @Fintype.ofFinite EI encFinite
  letI := Classical.decEq FI
  letI := Classical.decEq EI
  have hop := designed_hop_le E T adversary parameter scalar
  have overlap := advantage_le_of_overlap_tv belowDesigned belowHW
  have triangle : Assumptions.advantage
      (atSolution (crtChain E).hiddenDeleted field group adversary parameter scalar)
      (atSolution (crtChain E).publicFirst field group adversary parameter scalar) ≤
    Assumptions.advantage (hiddenDeletedHybrid E adversary parameter scalar)
        (hiddenDeletedWith E (designedRule E T) adversary parameter scalar) +
      Assumptions.advantage (atSolution (hiddenDesignedHybrid E T) field group adversary parameter scalar)
        (atSolution (crtChain E).publicFirst field group adversary parameter scalar) := by
    unfold Assumptions.advantage
    exact abs_sub_le _ _ _
  refine le_trans triangle (le_trans (add_le_add (hop.trans coincidenceLe)
    (overlap.trans (add_le_add mass tv))) ?_)
  linarith

end

end Kriterion.CRT.Privacy.PublicFirst
