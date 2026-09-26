/-
**Route M's hash programs** (M6): the 546 programs of the 273 collector sites. Site `k` (collector number `k = 3 d + c`) gets two
programs at the points `K + 2^128 · tagCode 7 0 0 0 0 k j`, `j = 0, 1`: answer `0` is the first two limbs of the
collector's `sampleFp` preimage, answer `1` is its third limb and the unused fourth block. This is the abstract
simulator's `programRequests` (`Proof/Privacy/CRT/AbstractSimulator.lean`) in the same order.

The block is parametric in its cells (`ProgramCells`): the key `K` and the four halves of each site, each a
`blockWord`. It writes no RAM and clobbers `rAddr`, `rInput`, `rB`, `rFirst`, `rSecond`. A hash program ignores the
index register (`queryFromRegisters` at kind 4).
-/

import Construction.Simulator.Blocks
import Construction.Simulator.CRT.Frame
import Construction.CRT.Interface

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

namespace Programs

/-- The cells the programs read. -/
structure ProgramCells where
  /-- The key `K = (hash t').1`, as a `blockWord`. -/
  key : Nat
  /-- Half `b < 4` of site `k`: `0, 1, 2` the preimage limbs, `3` the fourth block. -/
  half : Nat → Nat → Nat

/-- The number of collector sites. -/
def siteCount : Nat := 273

/-- The tag of answer `j` of mask site `k`, shifted into the high half of the hash input. -/
def tagWord (k j : Nat) : Nat := 2 ^ 128 * tagCode Family.mask 0 0 0 0 k j

/-- The hash input and the two answer words of program `(k, j)`, into `rInput`, `rFirst`, `rSecond`. -/
def programPrefix (cells : ProgramCells) (k j : Nat) : Prog :=
  Prog.seqList [loadAt rInput cells.key, cst rB (tagWord k j), ar .add rInput rInput rB,
    loadAt rFirst (cells.half k (2 * j)), loadAt rSecond (cells.half k (2 * j + 1))]

/-- **One hash program**: `K + 2^128 · tag(k, j) ↦ (half 2j, half 2j+1)`. -/
def programHash (cells : ProgramCells) (k j : Nat) : Prog :=
  .seq (programPrefix cells k j) (.op (.program 4 rIndex rInput rFirst rSecond))

/-- The two programs of site `k`. -/
def programSite (cells : ProgramCells) (k : Nat) : Prog :=
  .seq (programHash cells k 0) (programHash cells k 1)

/-- **The 546 programs**, digit by digit, then the digit's three collectors (site `3 d + c`), as the abstract
simulator's `collectorList`. -/
def programs (cells : ProgramCells) : Prog :=
  Prog.rep 91 fun digit => Prog.rep 3 fun collector => programSite cells (3 * digit + collector)

/-- The programs write no RAM. -/
def programsWrites : Writes := Writes.none

/-- The registers the programs change. -/
def programsClobbers : Clobbers := Clobbers.ofList [rAddr, rInput, rB, rFirst, rSecond]

theorem size_programHash (cells : ProgramCells) (k j : Nat) : (programHash cells k j).size = 9 := by
  simp only [programHash, programPrefix, Prog.seqList, Prog.size_seq, size_cst, size_loadAt, ar, Prog.size]

theorem cost_programHash (cells : ProgramCells) (k j : Nat) : (programHash cells k j).cost = 9 := by
  simp only [programHash, programPrefix, Prog.seqList, Prog.cost_seq, cost_cst, cost_loadAt, ar, Prog.cost]

theorem size_programSite (cells : ProgramCells) (k : Nat) : (programSite cells k).size = 18 := by
  simp only [programSite, Prog.size_seq, size_programHash]

theorem cost_programSite (cells : ProgramCells) (k : Nat) : (programSite cells k).cost = 18 := by
  simp only [programSite, Prog.cost_seq, cost_programHash]

theorem size_programs (cells : ProgramCells) : (programs cells).size = 91 * (3 * 18) :=
  Prog.size_rep _ _ _ fun _ _ => Prog.size_rep _ _ _ fun _ _ => size_programSite cells _

theorem cost_programs (cells : ProgramCells) : (programs cells).cost = 91 * (3 * 18) :=
  Prog.cost_rep _ _ _ fun _ _ => Prog.cost_rep _ _ _ fun _ _ => cost_programSite cells _

end Programs

end Kriterion.CRT.SimMachine
