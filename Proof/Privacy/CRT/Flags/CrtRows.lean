/-
**The P7 and P8 rows for `crtEntry` and `crtShadow`**, assembled from the merged parts.

* `crtMiddleBelow_crt`: `CrtMiddleBelow` (P7), with no open input;
* `crtThirdSwap_crt`: `CrtThirdSwap` (P8), with no open input (`crtShadow_offCurve_tagged`);
* `crtWrapGuess_crt`: `CrtWrapGuess`, from `crtWrapTable_le`;
* `crtFlagMass_crt`: `CrtFlagMass` (P8) from one input, the stage-1 touch guess (`CrtTouchGuess`, proved in `Flags/Touch.lean`);
  no abort (`crtNoAbort`), the doubling (`crtRowsDoubling_le`) and the wrap are discharged.
-/

import Proof.Privacy.CRT.Flags.WrapBridge
import Proof.Privacy.CRT.Flags.RowsDoubling
import Proof.Privacy.CRT.Flags.Wrap
import Proof.Privacy.CRT.PublicFirst.Layout

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-- **P7 for the concrete entry.** -/
theorem crtEntry_layout : crtEntry.layout = crtLayout := by
  rfl

theorem crtMiddleBelow_crt : CrtMiddleBelow crtEntry crtShadow := by
  -- the statement binds the instances of `FI` and `EI` separately, although both are `Empty`
  intro field group fintypeFI fintypeEI decFI decEI adversary parameter scalar
  have sized : WellSized crtEntry.layout := by
    rw [crtEntry_layout]
    exact wellSized_crtLayout
  exact @middle_below Empty Empty crtEntry field group fintypeFI fintypeEI decFI decEI sized crtShadow adversary
    parameter scalar

/-- **The wrap guess for the concrete entry** (`crtWrapTable_le`). -/
theorem crtWrapGuess_crt : CrtWrapGuess :=
  crtWrapGuess_of fun field group u => @crtWrapTable_le field group u

/-- **The off-curve third swap for the concrete entry.** -/
theorem crtThirdSwap_crt : CrtThirdSwap crtEntry crtShadow :=
  crtThirdSwap_of_tagged crtEntry (crtEntry_layout ▸ crtLayout_facts) crtShadow Paths.crtShadow_offCurve_tagged

/-- **The flag mass for the concrete entry**, from the stage-1 touch guess (every other part is discharged). -/
theorem crtFlagMass_crt (touch : CrtTouchGuess crtEntry crtShadow (ENNReal.ofReal stageOneTouchCharge)) :
    CrtFlagMass crtEntry crtShadow :=
  crtFlagMass_of crtEntry crtShadow
    (crtFlagGuess_crt crtNoAbort (fun field group scalar u Q valid => by
      letI := field
      letI := group
      exact crtRowsDoubling_le scalar u Q valid) crtWrapGuess_crt)
    touch

end

end Kriterion.CRT.Privacy.Flags
