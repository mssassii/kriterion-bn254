/-
**The replay of one modulus** (`modEvalM` in `Construction/CRT/Coord.lean`): here the modulus-256
path, the `chunkZero` kind. The machine computes the hot index `v mod 2 ^ width` with the chunk
prefix at offset 0 (the value of chunk 0), then runs the body (`ReplayBody.lean`) of modulus
`m = 2 ^ width` on chunk 0's leaves, which the chunk loop saved at `leafBase` (`ReplayChunks.lean`).
There is no conversion and no fold: chunk 0's leaves are already the one-hot of `v mod m`.
-/

import Construction.Simulator.CRT.ReplayBody
import Construction.Simulator.CRT.ReplayChunks

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- **The modulus-256 path**: `hot := v mod 2 ^ width`, then the body of modulus `m` (`= 2 ^ width`)
on the one-hot at `bc.vecBase`. -/
def mod256Block (coordCell : Nat) (bc : BodyCells) (m width S q : Nat) (tagOf : Nat → Nat → Nat) :
    Prog :=
  .seq (chunkPrefix coordCell bc.hot 0 width) (bodyBlock bc m S q tagOf)

/-- The path writes the body's cells and the hot index. -/
def mod256Writes (bc : BodyCells) (S q : Nat) : Writes :=
  (bodyWrites bc S q).union (Writes.cell bc.hot)

theorem cost_mod256Block (coordCell : Nat) (bc : BodyCells) (m width S q : Nat)
    (tagOf : Nat → Nat → Nat) :
    (mod256Block coordCell bc m width S q tagOf).cost = 8 + (bodyBlock bc m S q tagOf).cost := by
  rw [mod256Block, Prog.cost_seq]
  rfl

end Kriterion.CRT.SimMachine
