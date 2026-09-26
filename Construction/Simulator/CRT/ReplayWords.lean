/-
**The truth-table words** (the construction's `truthWord`
in `Construction/CRT/Chunk.lean`).

The word of an odd modulus `m` of width `ell` is, lane by lane,
`W_i = (Σ_c Σ_α T_{c,m}(α) · A_{c,α,i}) mod 2 ^ ell`, with the compile-time truth values
`T_{c,m}(α) = α · 2 ^ (8 c) mod m` and the chunks' cast lanes `A_{c,α,i}` in RAM (the output region
of `chunkLoop`, `castBase + 32768 c + 128 α + i`). The machine sums in words (the wrap modulo
`2 ^ 256` is harmless because `2 ^ ell` divides it) and masks once per lane. No query.
-/

import Construction.Simulator.CRT.ReplayChunks

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- `rA += t · A_{c,α,i}`. -/
def wordTerm (castBase t c leaf i : Nat) : Prog :=
  .seq (loadAt rB (castBase + 32768 * c + 128 * leaf + i))
    (.seq (cst rC t) (.seq (ar .mul rB rB rC) (ar .add rA rA rB)))

/-- The terms of chunk `c` for lane `i`. -/
def wordChunk (castBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat) (i c : Nat) : Prog :=
  Prog.rep (2 ^ width c) fun leaf => wordTerm castBase (truthOf c leaf) c leaf i

/-- Lane `i` of the word: the sum over `count` chunks, masked to `ell` bits, stored at
`wordBase + i`. -/
def wordLane (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (count ell i : Nat) : Prog :=
  .seq (cst rA 0)
    (.seq (Prog.rep count (wordChunk castBase truthOf width i))
    (.seq (cst rB (2 ^ ell - 1)) (.seq (ar .and rA rA rB) (storeAt (wordBase + i) rA))))

/-- **The word** of one modulus: its 128 lanes. -/
def truthWordBlock (castBase wordBase : Nat) (truthOf : Nat → Nat → Nat) (width : Nat → Nat)
    (count ell : Nat) : Prog :=
  Prog.rep 128 (wordLane castBase wordBase truthOf width count ell)

/-- The word writes its 128 lane cells. -/
def wordWrites (wordBase : Nat) : Writes := Writes.region ⟨wordBase, 128⟩

end Kriterion.CRT.SimMachine
