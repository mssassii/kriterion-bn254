/-
**The replay of route M's masks** (the construction's `nonCollectorMasksM`, `Construction/CRT/Mask.lean`):
at the key `K` (a `blockWord` in RAM), for every pair site `k` the three answers at
`K + 2 ^ 128 · maskTag 1 k part` (the cast block's `castQueries`, reused), then the two masks
`sampleFp a₀.1 a₀.2 a₁.1` and `sampleFp a₁.2 a₂.1 a₂.2` in the field (`fpRead`); then the single
site (two answers, one mask) when the non-collector count is odd. Non-collector entry `n` goes to
the cell `maskOf n`. The collector sites are never asked (route M programs them).
-/

import Construction.Simulator.CRT.ReplayCast
import Construction.CRT.Mask
import Construction.Simulator.Layout

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The cells of the mask stage. -/
structure MaskCells where
  /-- The key `K`, a `blockWord`. -/
  key : Nat
  /-- Scratch: the halves of one site's answers (6 cells). -/
  ansBase : Nat
  /-- Output: the mask of non-collector entry `n` (a `fieldWord`). -/
  maskOf : Nat → Nat

/-- The answer cells of the mask stage, as cast cells (the lane base is unused). -/
def MaskCells.site (mc : MaskCells) : CastCells := ⟨mc.key, mc.ansBase, 0⟩

/-- `rA := a + b · 2 ^ 128` in the field, from the blocks at `src`, `src + 1`. -/
def fpLow (src : Nat) : Prog :=
  .seq (loadAt rA src)
    (.seq (loadAt rB (src + 1))
    (.seq (cst rC (2 ^ 128))
    (.seq (ar .fieldMul rB rB rC) (ar .fieldAdd rA rA rB))))

/-- `rA += c · 2 ^ 256` in the field (`c` at `src + 2`), stored at `dst`. -/
def fpHigh (src dst : Nat) : Prog :=
  .seq (loadAt rB (src + 2))
    (.seq (cst rC c256)
    (.seq (ar .fieldMul rB rB rC)
    (.seq (ar .fieldAdd rA rA rB) (storeAt dst rA))))

/-- `dst := sampleFp (src) (src + 1) (src + 2)`. -/
def fpRead (src dst : Nat) : Prog := .seq (fpLow src) (fpHigh src dst)

/-- Pair site `k`: three answers, the masks of entries `2 k` and `2 k + 1`. -/
def maskPairSite (mc : MaskCells) (k : Nat) : Prog :=
  .seq (castQueries mc.site (Kriterion.CRT.maskTag 1 k) 3)
    (.seq (fpRead mc.ansBase (mc.maskOf (2 * k))) (fpRead (mc.ansBase + 3) (mc.maskOf (2 * k + 1))))

/-- The single site (after `pairs` pair sites): two answers, the mask of entry `2 · pairs`. -/
def maskSingleSite (mc : MaskCells) (pairs : Nat) : Prog :=
  .seq (castQueries mc.site (Kriterion.CRT.maskTag 1 pairs) 2) (fpRead mc.ansBase (mc.maskOf (2 * pairs)))

/-- **The mask stage** of route M for `digits` digits. -/
def maskStage (mc : MaskCells) (digits : Nat) : Prog :=
  .seq (Prog.rep (Kriterion.CRT.pairSites digits) (maskPairSite mc))
    (if Kriterion.CRT.singleSites digits = 1 then maskSingleSite mc (Kriterion.CRT.pairSites digits)
     else .skip 0)

/-- The mask stage writes its answer scratch and the mask cells of its `count` entries. -/
def maskWrites (mc : MaskCells) (count : Nat) : Writes :=
  (Writes.region ⟨mc.ansBase, 6⟩).union fun address => ∃ n, n < count ∧ address = word (mc.maskOf n)

/-- The mask stage's registers. -/
def maskClobbers : Clobbers := Clobbers.ofList [rA, rB, rC, rAddr, rInput, rFirst, rSecond]

end Kriterion.CRT.SimMachine
