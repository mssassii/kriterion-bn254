/-
**The stage-1 functional dependence** (`Paths.StageOneFactors`).

For each coordinate `κ` take the input `u = (0, 0)`. `DeltaView.view_fd` says that two tapes with the
same fine view at `(u, κ)` have the same stage-2 view at `u`; the stage-2 view's first component is the stage-1 view
(`StageOneProof.stageTwoView_fst`, stated over a generic entry so that `rfl` does not unfold the concrete one). So the
stage-1 view is a function of the fine view. The two hypotheses of `view_fd` are the proved `coordRelational` and
`tailRel`.
-/

import Proof.Privacy.CRT.Hidden.CaseConv
import Proof.Privacy.CRT.Hidden.StageOne
import Proof.Privacy.CRT.Paths.DeltaGuess

set_option autoImplicit false

namespace Kriterion.CRT.Paths

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.Instance (crtEntry)

noncomputable section

namespace StageOneFactorsP3

/-- Equal stage-2 views have equal stage-1 views (for a generic entry). -/
theorem stageOne_eq_of_stageTwo {FI EI : Type} (E : CrtEntry FI EI) [FieldCertificate] [GroupCertificate]
    (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape tape' : TableTape E)
    (same : stageTwoView E T parameter scalar u tape = stageTwoView E T parameter scalar u tape') :
    stageOneView E parameter scalar tape = stageOneView E parameter scalar tape' := by
  rw [← StageOneProof.stageTwoView_fst E T parameter scalar u tape,
    ← StageOneProof.stageTwoView_fst E T parameter scalar u tape', same]

end StageOneFactorsP3

/-- **`StageOneFactors`**: at `u = (0, 0)` the fine view of either coordinate determines the stage-1 view. -/
theorem stageOneFactors : StageOneFactors := by
  intro field group parameter scalar κ
  refine ⟨⟨0, 0⟩, fun tape tape' same => ?_⟩
  exact StageOneFactorsP3.stageOne_eq_of_stageTwo crtEntry Entry.table parameter scalar ⟨0, 0⟩ tape tape'
    (DeltaView.view_fd DeltaView.coordRelational DeltaView.tailRel parameter scalar ⟨0, 0⟩ κ same)

end

end Kriterion.CRT.Paths
