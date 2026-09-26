/-
**Route M's replay on the machine** (`Entry.replayRouteM`): the two coordinates
(`ReplayCoord.lean`), the key (`ReplayKey.lean`) and the non-collector masks
(`ReplayMasks.lean`), on the global layout (`Layout.lean`): delivered values at
`decodedCell κ e`, masks at `maskCell κ e`, the key at `keyCell`.
-/

import Construction.Simulator.CRT.ReplayCoord
import Construction.Simulator.CRT.ReplayKey
import Construction.Simulator.CRT.ReplayMasks
import Construction.Simulator.CRT.Layout
import Construction.CRT.Entry

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The mask cell of non-collector entry `n` (the entry's coordinate and encoding index). -/
def maskCellOf (digits n : Nat) : Nat :=
  Layout.maskCell (Kriterion.CRT.nonCollectorEntry digits n).1 (Kriterion.CRT.nonCollectorEntry digits n).2

/-- The key block's cells: the request, the curve constants at `fieldBase`, the five delivered curve
values (`x3, x5, x7` are `x` encodings `455, 456, 457`; `y4, y6` are `y` encodings `273, 274`), the
key cell. -/
def entryKeyCells : KeyCells :=
  ⟨reqX, reqY, fieldBase, Layout.decodedCell 0 455, Layout.decodedCell 1 273, Layout.decodedCell 0 456,
    Layout.decodedCell 1 274, Layout.decodedCell 0 457, Layout.keyCell⟩

/-- The mask stage's cells: the key, the answer scratch at `maskScratch`, the mask cells. -/
def entryMaskCells (maskScratch : Nat) : MaskCells :=
  ⟨Layout.keyCell, maskScratch, maskCellOf Kriterion.ArgoMAC.PlanB.digitCount⟩

/-- **Route M's replay**: the `x` coordinate, the `y` coordinate, the key, the masks. -/
def entryReplay (coordX coordY : Prog) (maskScratch : Nat) : Prog :=
  .seq coordX
    (.seq coordY
    (.seq (keyBlock entryKeyCells) (maskStage (entryMaskCells maskScratch) Kriterion.ArgoMAC.PlanB.digitCount)))

end Kriterion.CRT.SimMachine
