/-
**The tier-2 statements of the CRT privacy proof**.

* The hidden hop's obligations are in `Hidden/Obligations.lean` and its reduction `crt_hidden_of_guess` in
  `Hidden/Reduction.lean` (P2a).
* `crt_oracleAdaptivePrivacy_of`: the privacy field of `Solution` for the CRT entry from the named parts, each a
  row: `G0` is the lazy real game (P1), `G0 → G0T` (P6a1), `G0T → G0U` (P1), the two guesses and the
  containment `DesignedReached` (P2a, P2b), `G1U → HW` (the core), `HW → H` (P9), `H → I` (P10), and the
  machine law (M7). It is proved from `chain_oracleAdaptivePrivacy` and `crt_hidden_of_guess`.
-/

import Proof.Privacy.CRT.Hidden.Reduction

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open scoped ENNReal

noncomputable section

variable {FI EI : Type} (E : CrtEntry FI EI)

/-! ### The privacy field from the named parts -/

/-- **The privacy field of `Solution` for the CRT entry**, from the named parts of the chain. Each hypothesis is one
row; `Glue/Instance.lean` instantiates `E` with the entry `crtEntry`. -/
theorem crt_oracleAdaptivePrivacy_of [fixedFinite : Finite FI] [encFinite : Finite EI] [IsEmpty FI] [IsEmpty EI]
    (T : CrtTable)
    (simulator : BoundedMachine.Simulator)
    (real : RealIsLazy E.toEntrySig (crtChain E).real)
    (table : HopBound (crtChain E).real (crtChain E).tablePlanted fun _ _ => tCollisionError)
    (swap : HopBound (crtChain E).tablePlanted (crtChain E).padSwapped fun _ _ => padSwapError)
    (reached : DesignedReached E T)
    (one : CrtStageOneGuess E (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess E T (ENNReal.ofReal crtHiddenCharge) (ENNReal.ofReal hiddenWindowError))
    (publicFirst : GameCoreUntilBad (crtChain E).hiddenDeleted (crtChain E).publicFirst fun first _ =>
      stageOneTouchError first + smudgeError + exceptionalError + coincidenceError + padSwapError)
    (opening : HopBound (crtChain E).publicFirst (crtChain E).opened fun _ _ => outputKernelError)
    (refill : HopBound (crtChain E).opened (crtChain E).ideal fun _ _ => padSwapError)
    (machine : MachineLaw E.toEntrySig (crtChain E).ideal simulator machineCutoffError) :
    ∀ (field : BN254.FieldCertificate) (group : @BN254.GroupCertificate field),
      letI := field
      letI := @Fintype.ofFinite FI fixedFinite
      letI := @Fintype.ofFinite EI encFinite
      letI := Classical.decEq FI
      letI := Classical.decEq EI
      GarbledCircuit.OracleAdaptivePrivacy (E.scheme field group) E.encoding E.bytes
        (@uniformRandomTape E.Coins (@Fintype.ofFinite E.Coins E.coinsFinite) E.coinWitness)
        (fun parameter scalar coins => (E.garbleProgram field group parameter scalar coins).toOracleProgram) :=
  chain_oracleAdaptivePrivacy E.toEntrySig (crtChain E) simulator real
    ⟨table, swap, crt_hidden_of_guess E T hiddenWindowError hiddenWindowError_nonneg reached one two, publicFirst,
      opening, refill⟩ machine

end

end Kriterion.CRT.Privacy
