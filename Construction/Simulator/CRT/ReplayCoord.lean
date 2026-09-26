/-
**The replay of one coordinate** (`coordEvalM` in `Construction/CRT/Coord.lean`): the chunk loop
(`ReplayChunks.lean`), then the `count` moduli, each in its own window of `2 ^ 20` cells from
`modBase` (`modProg i`, the modulus-256 path or an odd modulus's path), then the decoding
(`ReplayDecode.lean`) into the delivered-value cells.
-/

import Construction.Simulator.CRT.ReplayChunks
import Construction.Simulator.CRT.ReplayDecode
import Construction.CRT.Coord

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The moduli of a table by natural index (`1` off range). -/
def modNat (T : CrtTable) (i : Nat) : Nat := if h : i < T.count then T.modulus ⟨i, h⟩ else 1

/-- The window of modulus `i`: the `2 ^ 20` cells from `modBase + 2 ^ 20 · i`. -/
def modWindow (modBase i : Nat) : Writes :=
  fun address => ∃ x, modBase + 2 ^ 20 * i ≤ x ∧ x < modBase + 2 ^ 20 * (i + 1) ∧ address = word x

/-- The windows of the first `k` moduli. -/
def modsRegion (modBase k : Nat) : Writes :=
  fun address => ∃ x, modBase ≤ x ∧ x < modBase + 2 ^ 20 * k ∧ address = word x

/-- **The replay of one coordinate.** -/
def coordReplay (cc : CoordCells) (T : CrtTable) (coord : Nat) (modProg : Nat → Prog)
    (dc : DecodeCells) (nz S : Nat) : Prog :=
  .seq (chunkLoop cc T.chunkOffset T.chunkWidth (chunkTreeTag coord) (chunkCastTag coord) T.castWidth
      T.chunkCount)
    (.seq (Prog.rep T.count modProg) (decodeAll dc (modNat T) T.count T.wrapBound nz S))

end Kriterion.CRT.SimMachine
