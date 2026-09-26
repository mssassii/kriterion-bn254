/-
**The replay of an odd modulus, the pure parts** (`modEvalM`'s `odd` branch in
`Construction/CRT/Coord.lean`): the word value `σ_m = Σ_c T_{c,m}(α_c)` of the coordinate
(`sigmaBlock`, with `T_{c,m}(α) = α · 2 ^ (8 c) mod m` computed as `(α · (2 ^ (8 c) mod m)) mod m`
by one Barrett reduction per chunk), from which the two stage values `σ mod 2 ^ w0` and
`(σ / 2 ^ w0) mod 2 ^ w1` follow by the chunk prefix. No query.
-/

import Construction.Simulator.CRT.ReplayChunks

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- `rA := α · t` with `α = (v >> offset) mod 2 ^ width` (`v` at `coordCell`). -/
def sigmaTerm (coordCell offset width t : Nat) : Prog :=
  .seq (loadAt rA coordCell)
    (.seq (cst rB offset)
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB (2 ^ width - 1))
    (.seq (ar .and rA rA rB)
    (.seq (cst rB t) (ar .mul rA rA rB))))))

/-- `rAcc += (α_c · (2 ^ offset mod m)) mod m`. -/
def sigmaChunk (coordCell m offset width : Nat) : Prog :=
  .seq (sigmaTerm coordCell offset width (2 ^ offset % m))
    (.seq (barrett rA rC m 32) (ar .add rAcc rAcc rC))

/-- **The word value** `σ_m` of the coordinate at `coordCell`, over `count` chunks, stored at
`sigmaCell`. -/
def sigmaBlock (coordCell sigmaCell m count : Nat) (offset width : Nat → Nat) : Prog :=
  .seq (cst rAcc 0)
    (.seq (Prog.rep count fun c => sigmaChunk coordCell m (offset c) (width c)) (storeAt sigmaCell rAcc))

/-- The sigma block's registers. -/
def sigmaClobbers : Clobbers := Clobbers.ofList [rA, rB, rC, rD, rE, rF, rAcc, rAddr]

end Kriterion.CRT.SimMachine
