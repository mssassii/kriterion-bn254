/-
**Route M's preimages and fourth blocks** (M6).

For collector site `k = 3 d + c` (the order of `collectorList`): release-r1's `Opening.preimageOne d c` verbatim (a
multiplier by bounded rejection, then the three limbs of `π + p · m` at `openLimb d c`, which is `Layout.limbCell k`),
then one uniform 128-bit coin word, the unused fourth block, at `Layout.fourthCell k`. The program batch reads the
four halves through `programCells`.
-/

import Construction.Simulator.Opening
import Construction.Simulator.Stage1
import Construction.Simulator.CRT.Layout
import Construction.Simulator.CRT.Programs

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

namespace Preimages

/-- The fourth block of site `k`: 128 fair coins. -/
def fourthCoin (k : Nat) : Prog := Stage1.wordCell 128 (Layout.fourthCell k)

/-- Site `3 d + c`: the preimage of its mask, then its fourth block. -/
def preimageSite (d c : Nat) : Prog := .seq (Opening.preimageOne d c) (fourthCoin (3 * d + c))

/-- **The 273 sites**, digit by digit, collectors `X`, `Y`, `Z`. -/
def preimages : Prog := Prog.rep 91 fun d => Prog.rep 3 fun c => preimageSite d c

/-- The cells the program batch reads: the key, the three limbs and the fourth block of each site. -/
def programCells : Programs.ProgramCells where
  key := Layout.keyCell
  half k b := if b < 3 then Layout.limbCell k b else Layout.fourthCell k

end Preimages

end Kriterion.CRT.SimMachine
