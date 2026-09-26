/-
**The rows of the CRT chain as named propositions over a generic entry**.

Why this file exists. A hop statement such as
`HopBound (crtChain E).tablePlanted (crtChain E).padSwapped fun _ _ => padSwapError` elaborates the two games as
lambdas over the instance binders `[Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]`. When the statement
is written again in a file where `FI = EI = Empty`, instance resolution fills both `Fintype` slots with the last
local instance, so the term differs from the generic statement instantiated at `Empty` (the games receive
`inst_3 inst_3` instead of `inst_2 inst_3`). The two propositions are then not syntactically equal, and the unifier
times out trying to unfold the games. Stating each row once here, with `FI` and `EI` distinct variables, and
instantiating the name at the concrete entry avoids this: `CrtSwapHop crtEntry` unfolds to exactly the type of
`crt_swap crtEntry rfl`.

Each name below is one row of `crt_oracleAdaptivePrivacy_of`; `crt_privacy_of_named` is that theorem restated
through the names.
-/

import Proof.Privacy.CRT.Statements

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

/-- H1: `G0` is the lazy real game (P1). -/
def CrtRealLazy [Finite FI] [Finite EI] : Prop := RealIsLazy E.toEntrySig (crtChain E).real

/-- H2: `G0 → G0T`, the planted table (P6a1). -/
def CrtTableHop [Finite FI] [Finite EI] : Prop :=
  HopBound (crtChain E).real (crtChain E).tablePlanted fun _ _ => tCollisionError

/-- H3: `G0T → G0U`, the pad swap (P1). -/
def CrtSwapHop [Finite FI] [Finite EI] : Prop :=
  HopBound (crtChain E).tablePlanted (crtChain E).padSwapped fun _ _ => padSwapError

/-- H8: `G1U → HW`, the public-first hop (the core). -/
def CrtPublicFirstHop [Finite FI] [Finite EI] : Prop :=
  GameCoreUntilBad (crtChain E).hiddenDeleted (crtChain E).publicFirst fun first _ =>
    stageOneTouchError first + smudgeError + exceptionalError + coincidenceError + padSwapError

/-- H9: `HW → H`, the opening (P9). -/
def CrtOpeningHop [Finite FI] [Finite EI] : Prop :=
  HopBound (crtChain E).publicFirst (crtChain E).opened fun _ _ => outputKernelError

/-- H10: `H → I`, the refill (P10). -/
def CrtRefillHop [Finite FI] [Finite EI] : Prop :=
  HopBound (crtChain E).opened (crtChain E).ideal fun _ _ => padSwapError

/-- H11: the machine law of the ideal game (M7). -/
def CrtMachineHop [Finite FI] [Finite EI] (simulator : BoundedMachine.Simulator) : Prop :=
  MachineLaw E.toEntrySig (crtChain E).ideal simulator machineCutoffError

/-- The conclusion of `crt_oracleAdaptivePrivacy_of`: the privacy field of `Solution` for the entry. -/
def CrtPrivacy [fixedFinite : Finite FI] [encFinite : Finite EI] : Prop :=
  ∀ (field : BN254.FieldCertificate) (group : @BN254.GroupCertificate field),
    letI := field
    letI := @Fintype.ofFinite FI fixedFinite
    letI := @Fintype.ofFinite EI encFinite
    letI := Classical.decEq FI
    letI := Classical.decEq EI
    GarbledCircuit.OracleAdaptivePrivacy (E.scheme field group) E.encoding E.bytes
      (@uniformRandomTape E.Coins (@Fintype.ofFinite E.Coins E.coinsFinite) E.coinWitness)
      (fun parameter scalar coins => (E.garbleProgram field group parameter scalar coins).toOracleProgram)

/-- **`crt_oracleAdaptivePrivacy_of` through the named rows.** -/
theorem crt_privacy_of_named [Finite FI] [Finite EI] [IsEmpty FI] [IsEmpty EI] (T : CrtTable)
    (simulator : BoundedMachine.Simulator) (real : CrtRealLazy E) (table : CrtTableHop E) (swap : CrtSwapHop E)
    (reached : DesignedReached E T)
    (one : CrtStageOneGuess E (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess E T (ENNReal.ofReal crtHiddenCharge) (ENNReal.ofReal hiddenWindowError))
    (publicFirst : CrtPublicFirstHop E) (opening : CrtOpeningHop E) (refill : CrtRefillHop E)
    (machine : CrtMachineHop E simulator) : CrtPrivacy E :=
  crt_oracleAdaptivePrivacy_of E T simulator real table swap reached one two publicFirst opening refill
    machine

end

end Kriterion.CRT.Privacy
