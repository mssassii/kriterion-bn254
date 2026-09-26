/-
**The CRT machine's global RAM map** (M7).

The regions of xinshu's `Construction/Simulator/Layout.lean` are kept where the CRT entry stores the same data, so
that the verbatim blocks (request, label selection and emission, the opening's tail, Horner, lambdas, lifts,
preimage limbs) run unchanged:

* `fieldBase` (`2^40`): the curve constants (cells `0 .. 2`) and the row constants (`3 + 4 d + slot`,
  `xC0, yC0, yC4, zC0`, release-r1's `Opening.rowCell`);
* `exceptionBase` (`2^41`): the `91 · 6` exception bytes (`6 d + slot`);
* `requestBase` (`2^43`), `labelBase` (`2^44`, the `508` selected labels), `tmpBase` (`2^48`), `openBase` (`2^49`),
  `keyBase` (`2^50`: `keyBase + 2 i + b` is label `b` of input bit `i`, stored as `Z_i` and `Z_i ⊕ Δ`).

The CRT source and the replay's outputs get new regions, one per power of two from `2^51`, each laid out in the
order of `Entry.Source` (`Construction/CRT/Layout.lean`), so that stage 1 writes and `extractSource` reads the source
field by field:

| region | base | cell | content |
|---|---|---|---|
| source joins | `2^51` | `sourceJoin κ index` | `Source.joins κ index` (`blockWord`) |
| source pins | `2^52` | `sourcePin κ k lane` | lane `lane` of `Source.pins κ k` (`word lane.val`) |
| residue digits | `2^53` | `residueCell κ i e` | the mixed-radix digit `J_{κ,e,i}` of record `e` (`word`) |
| hints | `2^54` | `hintCell κ e` | the published hint (`word 0`; the source's records carry hint 0) |
| deltas | `2^55` | `deltaCell κ` | `Source.deltas κ` (`blockWord`) |
| decoded values | `2^56` | `decodedCell κ e` | the replay's delivered value `v_e` (`fieldWord`) |
| masks | `2^57` | `maskCell κ e` | `π_e` (`fieldWord`): non-collectors by the replay, collectors by the opening |
| key | `2^58` | `keyCell` | `K = (hash t').1` (`blockWord`) |
| fourth blocks | `2^59` | `fourthCell k` | the unused fourth block of collector site `k` |
| replay scratch | `2^60` | `replayScratch κ` | the coordinate chains (`CoordCells` and the per-modulus cells) |

Every cell is below `2^62`, far below the word size; the regions are pairwise disjoint because each lies in
`[2^n, 2^n + 2^40)` for a distinct `n ≥ 51`.
-/

import Construction.Simulator.Layout
import Construction.Simulator.CRT.Frame

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

namespace Layout

/-- A published join of coordinate `κ` (flat index of the source). -/
def sourceJoin (κ index : Nat) : Nat := 2 ^ 51 + 2 ^ 24 * κ + index

/-- Lane `lane` of pin `k` of coordinate `κ`. -/
def sourcePin (κ k lane : Nat) : Nat := 2 ^ 52 + 2 ^ 24 * κ + 128 * k + lane

/-- The mixed-radix digit of record `e` of coordinate `κ` at modulus index `i`. -/
def residueCell (κ i e : Nat) : Nat := 2 ^ 53 + 2 ^ 24 * κ + 2 ^ 10 * i + e

/-- The published hint of record `e` of coordinate `κ`. -/
def hintCell (κ e : Nat) : Nat := 2 ^ 54 + 2 ^ 10 * κ + e

/-- The Lamport `Δ` of coordinate `κ`. -/
def deltaCell (κ : Nat) : Nat := 2 ^ 55 + κ

/-- The replay's delivered value of encoding `e` of coordinate `κ`. -/
def decodedCell (κ e : Nat) : Nat := 2 ^ 56 + 2 ^ 10 * κ + e

/-- The mask of row encoding `e` of coordinate `κ`. -/
def maskCell (κ e : Nat) : Nat := 2 ^ 57 + 2 ^ 10 * κ + e

/-- The key `K = (hash t').1`. -/
def keyCell : Nat := 2 ^ 58

/-- The unused fourth block of collector site `k`. -/
def fourthCell (k : Nat) : Nat := 2 ^ 59 + k

/-- The base of the replay's scratch for coordinate `κ` (a window of `2^40` cells). -/
def replayScratch (κ : Nat) : Nat := 2 ^ 60 + 2 ^ 40 * κ

/-- The preimage limb `b < 3` of collector site `k = 3 d + c`: release-r1's `openLimb d c b`. -/
def limbCell (k b : Nat) : Nat := openBase + 2000 + 3 * k + b

theorem limbCell_eq (d c b : Nat) : limbCell (3 * d + c) b = openLimb d c b := by
  unfold limbCell openLimb
  omega

end Layout

end Kriterion.CRT.SimMachine
