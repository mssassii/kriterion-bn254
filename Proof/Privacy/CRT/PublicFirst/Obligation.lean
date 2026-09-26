/-
**P7, the public-first hop `G1U → HW`, part 4: the middle obligation from four named statements.**

`CrtMiddleObligation T` (`Hop.lean`) follows from:

* `CrtLiftCore T shadow` (the core H8 with the laws P6): `M'` is below `G1U°`
  (`below_of_core`);
* `CrtMiddleBelow shadow` (P7, plumbing): `M` is below `HW`: the private run merged is `HW`'s run off a meeting, a
  failed program or a rows or preimage abort is `HW`'s abort, and the shadow's discarded lazy questions do not change
  the adversary's stage 2;
* `CrtFlagMass shadow` (P8): `M'`'s flag mass is at most the stage-1 touch, the wrap event and the doubling;
* `CrtThirdSwap shadow` (P8): `M'` and `M` are within `padSwapError` (they differ only in the off-curve reader).

`M'` is `middleGame E shadow (tableRun (swappedTableLaw E.layout))`, `M` is `middleGame E shadow lazyRun`.
-/

import Proof.Privacy.CRT.PublicFirst.Middle
import Proof.Privacy.CRT.Named

namespace Kriterion.CRT.Privacy.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

/-- **`M` is below `HW`** (P7): for every shadow, at every instance. -/
def CrtMiddleBelow (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI) :
    Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar),
    Below (publicFirstHybrid E adversary parameter scalar) (middleGame E shadow lazyRun adversary parameter scalar)

/-- **The flag mass of `M'`** (P8): at most the stage-1 touch (`4/2^128` per stage-1 query), the wrap event and the
doubling, against every adversary below `2^100` queries. -/
def CrtFlagMass [fixedFinite : Finite FI] [encFinite : Finite EI]
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      (letI := field
       letI := group
       letI := @Fintype.ofFinite FI fixedFinite
       letI := @Fintype.ofFinite EI encFinite
       letI := Classical.decEq FI
       letI := Classical.decEq EI
       middleGame E shadow (tableRun (swappedTableLaw E.layout)) adversary parameter scalar none).toReal ≤
        stageOneTouchError (adversary.firstQueryBudget parameter) + smudgeError + exceptionalError

/-- **The off-curve third swap** (P8): `M'` and `M` are within `padSwapError`. -/
def CrtThirdSwap [fixedFinite : Finite FI] [encFinite : Finite EI]
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      (letI := field
       letI := group
       letI := @Fintype.ofFinite FI fixedFinite
       letI := @Fintype.ofFinite EI encFinite
       letI := Classical.decEq FI
       letI := Classical.decEq EI
       (middleGame E shadow (tableRun (swappedTableLaw E.layout)) adversary parameter scalar).etvDist
         (middleGame E shadow lazyRun adversary parameter scalar)).toReal ≤ padSwapError

/-- **The middle obligation from the core, `M` below `HW`, the flag mass and the third swap.** -/
theorem crtMiddleObligation_of [fixedFinite : Finite FI] [encFinite : Finite EI] (T : CrtTable)
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI)
    (core : CrtLiftCore E T shadow) (below : CrtMiddleBelow E shadow)
    (flag : CrtFlagMass E shadow) (swap : CrtThirdSwap E shadow) : CrtMiddleObligation E T := by
  intro field group adversary parameter scalar small
  letI := field
  letI := group
  letI := @Fintype.ofFinite FI fixedFinite
  letI := @Fintype.ofFinite EI encFinite
  letI := Classical.decEq FI
  letI := Classical.decEq EI
  exact ⟨middleGame E shadow (tableRun (swappedTableLaw E.layout)) adversary parameter scalar,
    middleGame E shadow lazyRun adversary parameter scalar,
    below_of_core E T shadow core adversary parameter scalar,
    below adversary parameter scalar,
    flag field group adversary parameter scalar small,
    swap field group adversary parameter scalar small⟩

/-- **The public-first hop** (H8, `Named.CrtPublicFirstHop`) from the coincidence bound, the core, `M` below `HW`,
the flag mass and the third swap. -/
theorem crt_publicFirst_of_parts [Finite FI] [Finite EI] (T : CrtTable)
    (shadow : ∀ [FieldCertificate] [GroupCertificate], CrtShadow (viewHere E).Source FI EI)
    (coincidence : CrtCoincidenceBound E T coincidenceError) (core : CrtLiftCore E T shadow)
    (below : CrtMiddleBelow E shadow) (flag : CrtFlagMass E shadow) (swap : CrtThirdSwap E shadow) :
    CrtPublicFirstHop E :=
  crt_publicFirst_of_designed E T coincidence (crtMiddleObligation_of E T shadow core below flag swap)

end

end Kriterion.CRT.Privacy.PublicFirst
