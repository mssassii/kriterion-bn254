/-
**The decoding of one coordinate** (the last two fields of `coordEvalM` in
`Construction/CRT/Coord.lean`: `crtValue` and `decoded`). For every encoding `e < S` the machine
gathers the residues `L_{e,i}` of the `count` moduli (modulus `i`'s body leaves them at
`outOf i + e`) into the contiguous scratch `gbase + i`, then runs Garner's reconstruction with the
hint (`reconstruct`, `Garner.lean`), which stores `wrapDecode M B h (crt L) mod p` at
`decodedBase + e`. No query.
-/

import Construction.Simulator.CRT.Garner

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- `gbase + i := L_{e,i}` (read at `outOf i + e`) for `i < count`. -/
def gatherResidues (outOf : Nat → Nat) (count gbase e : Nat) : Prog :=
  Prog.rep count fun i => .seq (loadAt rA (outOf i + e)) (storeAt (gbase + i) rA)

/-- The cells of the decoding. -/
structure DecodeCells where
  /-- Modulus `i`'s residue of encoding `e` at `outOf i + e`. -/
  outOf : Nat → Nat
  /-- The published hint of encoding `e` at `hintBase + e`. -/
  hintBase : Nat
  /-- Output: the delivered value of encoding `e` at `decodedBase + e` (a `fieldWord`). -/
  decodedBase : Nat
  /-- Scratch: the gathered residues (`count` cells). -/
  gbase : Nat
  /-- Scratch: Garner's mixed-radix digits (`count` cells). -/
  vaddr : Nat
  /-- Scratch: the limbs of the CRT integer (`nz` cells). -/
  zbase : Nat

/-- Encoding `e`: gather, then reconstruct. -/
def decodeOne (dc : DecodeCells) (mods : Nat → Nat) (count wrapB nz e : Nat) : Prog :=
  .seq (gatherResidues dc.outOf count dc.gbase e)
    (reconstruct mods count (prefixProd mods count) wrapB dc.gbase dc.vaddr dc.zbase nz
      (dc.hintBase + e) (dc.decodedBase + e))

/-- **The decoding** of `S` encodings. -/
def decodeAll (dc : DecodeCells) (mods : Nat → Nat) (count wrapB nz S : Nat) : Prog :=
  Prog.rep S (decodeOne dc mods count wrapB nz)

/-- The decoding writes its scratch (one interval from `gbase` to the end of the limbs) and the
decoded cells. -/
def decodeWrites (dc : DecodeCells) (nz S : Nat) : Writes :=
  Writes.union (fun address => ∃ x, dc.gbase ≤ x ∧ x < dc.zbase + nz ∧ address = word x)
    (Writes.region ⟨dc.decodedBase, S⟩)

end Kriterion.CRT.SimMachine
