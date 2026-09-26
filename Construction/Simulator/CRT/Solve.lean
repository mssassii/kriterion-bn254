/-
**Route M's collector solve** (M6): for digit `d`, the three collectors'
masks `π_c = v_c − τ_c`, with `τ_c` the row-level value that makes the collector's row equal the target row
(`BMR.collectorSolve`) and `v_c` the collector's delivered value. The masks go to release-r1's `openTarget d c`, where
the verbatim `Opening.preimageOne` reads them.

Cells read: the request (`reqX`, `reqY`), the row constants (`Opening.rowCell d k`), the replay's delivered values
and masks (`Layout.decodedCell`, `Layout.maskCell`), and the target rows (`openRow d + k`, written by the lifts).

Per row (`BMR.collectorSolve`, the `X` and `Z` collectors with multiplier 1, the `Y` collector `y`):
* `X`: `τ = W.x − (xC0 + r(x7)·x + r(y10))`;
* `Y`: `τ = (W.y − (yC0 + yC4·x² + r(x7')·x² + r(y8)·y + r(y10')))·y⁻¹`;
* `Z`: `τ = W.z − zC0`;
where `r(e) = v_e − π_e` is a non-collector's row-level value.
-/

import Construction.Simulator.Opening
import Construction.Simulator.CRT.Layout

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

namespace Solve

/-- The delivered-value cell of `x` encoding `e`. -/
def decX (e : Nat) : Nat := Layout.decodedCell 0 e
/-- The delivered-value cell of `y` encoding `e`. -/
def decY (e : Nat) : Nat := Layout.decodedCell 1 e
/-- The mask cell of `x` encoding `e`. -/
def maskX (e : Nat) : Nat := Layout.maskCell 0 e
/-- The mask cell of `y` encoding `e`. -/
def maskY (e : Nat) : Nat := Layout.maskCell 1 e

/-- `rAcc += (RAM[dec] − RAM[mask]) · R[factor]`. -/
def addRowScaled (dec mask : Nat) (factor : Register) : Prog :=
  Prog.seqList [loadAt rSel dec, loadAt rD mask, ar .fieldSub rSel rSel rD, ar .fieldMul rSel rSel factor,
    ar .fieldAdd rAcc rAcc rSel]

/-- `rAcc += RAM[dec] − RAM[mask]`. -/
def addRow (dec mask : Nat) : Prog :=
  Prog.seqList [loadAt rSel dec, loadAt rD mask, ar .fieldSub rSel rSel rD, ar .fieldAdd rAcc rAcc rSel]

/-- `rAcc += RAM[cell] · R[factor]`. -/
def addConstScaled (cell : Nat) (factor : Register) : Prog :=
  Prog.seqList [loadAt rSel cell, ar .fieldMul rSel rSel factor, ar .fieldAdd rAcc rAcc rSel]

/-- `RAM[out] = RAM[dec] − (RAM[row] − rAcc)`. -/
def finishMask (row dec out : Nat) : Prog :=
  Prog.seqList [loadAt rSel row, ar .fieldSub rSel rSel rAcc, loadAt rD dec, ar .fieldSub rD rD rSel,
    storeAt out rD]

/-- `RAM[out] = RAM[dec] − (RAM[row] − rAcc) · y⁻¹` with `y` in `rB` (`rAcc` is reused for `y⁻¹`). -/
def finishMaskOverY (row dec out : Nat) : Prog :=
  Prog.seqList [loadAt rSel row, ar .fieldSub rSel rSel rAcc, ar .fieldInv rAcc rB rB,
    ar .fieldMul rSel rSel rAcc, loadAt rD dec, ar .fieldSub rD rD rSel, storeAt out rD]

/-- The `X` row of digit `d` (`rA = x`). -/
def rowX (d : Nat) : Prog :=
  Prog.seqList [loadAt rAcc (Opening.rowCell d 0), addRowScaled (decX (5 * d)) (maskX (5 * d)) rA,
    addRow (decY (3 * d)) (maskY (3 * d)), finishMask (openRow d) (decX (5 * d + 1)) (openTarget d 0)]

/-- The `Y` row of digit `d` (`rB = y`, `rC = x²`). -/
def rowY (d : Nat) : Prog :=
  Prog.seqList [loadAt rAcc (Opening.rowCell d 1), addConstScaled (Opening.rowCell d 2) rC,
    addRowScaled (decX (5 * d + 2)) (maskX (5 * d + 2)) rC,
    addRowScaled (decY (3 * d + 1)) (maskY (3 * d + 1)) rB,
    addRow (decY (3 * d + 2)) (maskY (3 * d + 2)),
    finishMaskOverY (openRow d + 1) (decX (5 * d + 3)) (openTarget d 1)]

/-- The `Z` row of digit `d`. -/
def rowZ (d : Nat) : Prog :=
  Prog.seqList [loadAt rAcc (Opening.rowCell d 3), finishMask (openRow d + 2) (decX (5 * d + 4)) (openTarget d 2)]

/-- The request's `x`, `y`, `x²` into `rA`, `rB`, `rC`. -/
def solvePrefix : Prog := Prog.seqList [loadAt rA reqX, loadAt rB reqY, ar .fieldMul rC rA rA]

/-- **The three collector masks of digit `d`.** -/
def solveDigit (d : Nat) : Prog := Prog.seqList [solvePrefix, rowX d, rowY d, rowZ d]

/-- **The 273 collector masks.** -/
def solve : Prog := Prog.rep 91 solveDigit

/-- The registers the solve changes. -/
def solveClobbers : Clobbers := Clobbers.ofList [rAcc, rAddr, rSel, rA, rB, rC, rD]

end Solve

end Kriterion.CRT.SimMachine
