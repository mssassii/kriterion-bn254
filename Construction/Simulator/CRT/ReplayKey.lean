/-
**The replay of the key** (the construction's `keyM` in `Construction/CRT/Mask.lean`):
the curve check's output `t' = c0 + c1 x³ + c2 y² + x3 x² + y4 y + x5 x + y6 + x7` in the field
(`curveEval`, from the request, the published curve constants and the five delivered curve
values), then one labelled query at `(t' mod 2 ^ 128) + 2 ^ 128 · maskKeyTag` (`keyQuery`); the key
`K` is the answer's first block, stored at `key`.
-/

import Construction.Simulator.Blocks
import Construction.Simulator.CRT.Frame
import Construction.CRT.Mask

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The cells of the key block. -/
structure KeyCells where
  /-- The request `x`, `y` (`fieldWord`s). -/
  reqX : Nat
  reqY : Nat
  /-- The curve constants `c0, c1, c2` at `constBase + 0, 1, 2` (`fieldWord`s). -/
  constBase : Nat
  /-- The delivered curve values `x3, y4, x5, y6, x7` (`fieldWord`s). -/
  x3 : Nat
  y4 : Nat
  x5 : Nat
  y6 : Nat
  x7 : Nat
  /-- Output: the key `K` (a `blockWord`). -/
  key : Nat

/-- `rA := x`, `rB := y`, `rC := x²`, `rD := x³`, `rE := y²`. -/
def curvePowers (kc : KeyCells) : Prog :=
  .seq (loadAt rA kc.reqX)
    (.seq (loadAt rB kc.reqY)
    (.seq (ar .fieldMul rC rA rA)
    (.seq (ar .fieldMul rD rC rA) (ar .fieldMul rE rB rB))))

/-- `rInput := c0 + c1 · x³`. -/
def curveStart (kc : KeyCells) : Prog :=
  .seq (loadAt rInput kc.constBase)
    (.seq (loadAt rAcc (kc.constBase + 1))
    (.seq (ar .fieldMul rAcc rAcc rD) (ar .fieldAdd rInput rInput rAcc)))

/-- `rInput += (cell) · reg`. -/
def curveTerm (cell : Nat) (reg : Register) : Prog :=
  .seq (loadAt rAcc cell) (.seq (ar .fieldMul rAcc rAcc reg) (ar .fieldAdd rInput rInput rAcc))

/-- `rInput += (cell)`. -/
def curveConst (cell : Nat) : Prog :=
  .seq (loadAt rAcc cell) (ar .fieldAdd rInput rInput rAcc)

/-- **The curve check's output** `t'` into `rInput`. -/
def curveEval (kc : KeyCells) : Prog :=
  .seq (curvePowers kc)
    (.seq (curveStart kc)
    (.seq (curveTerm (kc.constBase + 2) rE)
    (.seq (curveTerm kc.x3 rC)
    (.seq (curveTerm kc.y4 rB)
    (.seq (curveTerm kc.x5 rA)
    (.seq (curveConst kc.y6) (curveConst kc.x7)))))))

/-- The key query's input from `rInput = t'`: the low 128 bits plus `2 ^ 128 · maskKeyTag`. -/
def keyInputProg : Prog :=
  .seq (cst rB (2 ^ 128 - 1))
    (.seq (ar .and rInput rInput rB)
    (.seq (cst rB (2 ^ 128 * Kriterion.CRT.maskKeyTag)) (ar .add rInput rInput rB)))

/-- The query and the store of `K`. -/
def keyQuery (kc : KeyCells) : Prog :=
  .seq keyInputProg (.seq (.op (.query 4 rIndex rInput rFirst rSecond)) (storeAt kc.key rFirst))

/-- **The key block.** -/
def keyBlock (kc : KeyCells) : Prog := .seq (curveEval kc) (keyQuery kc)

/-- The key block's registers. -/
def keyClobbers : Clobbers := Clobbers.ofList [rA, rB, rC, rD, rE, rAcc, rAddr, rInput, rFirst, rSecond]

end Kriterion.CRT.SimMachine
