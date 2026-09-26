/-
**The replay of the body of one modulus** (the construction's `padVectorM` and `bodyEvalM` in `Construction/CRT/Body.lean`).

On the final one-hot `h[ρ]` (`m` cells) with hot index `hot` (in RAM), for every slot `ρ < m` but
the hot one, in ascending order (`bodyEntry`):

* ask the `q` pad answers at `h[ρ] + 2 ^ 128 · tag_(ρ, part)` and store their halves as `2 q` limbs
  (the cast block's `castQueries`, reused);
* read the fraction digits with `fracDigits` (`Arith.lean`): pass `j` leaves digit `S - 1 - j`;
* accumulate `A_e += ρ · d_e` and `B_e += d_e` for every encoding `e < S` (natural numbers; no
  reduction is needed because `A_e < m ^ 3`).

Then (`bodyFinal`) for every `e`: `L_e = (A_e + hot · (J_e + m ^ 2 - B_e)) mod m` by one Barrett
reduction at width 32 (`m ≤ 2 ^ 10`), which is `bodyEvalM`'s
`(weighted + hot · (J_e - known)).val` in `ZMod m`.
-/

import Construction.Simulator.CRT.ReplayCast

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The RAM cells of one modulus's body. -/
structure BodyCells where
  /-- The final one-hot, `m` cells. -/
  vecBase : Nat
  /-- The hot index. -/
  hot : Nat
  /-- Scratch: the pad answers' halves (the limbs of the pad integer), `2 q` cells. -/
  ansBase : Nat
  /-- Scratch: the fraction digits of one slot, `S` cells (pass `j` at `digBase + j`). -/
  digBase : Nat
  /-- Scratch: `A_e` at `accA + e`. -/
  accA : Nat
  /-- Scratch: `B_e` at `accB + e`. -/
  accB : Nat
  /-- Input: the residue join `J_e` at `joinBase + e`. -/
  joinBase : Nat
  /-- Output: the residue `L_e` at `outBase + e`. -/
  outBase : Nat

/-- The query cells of slot `ρ` (the lane base is unused). -/
def BodyCells.slot (bc : BodyCells) (ρ : Nat) : CastCells := ⟨bc.vecBase + ρ, bc.ansBase, 0⟩

/-- `A_e := 0`, `B_e := 0` for every `e < S`. -/
def bodyZero (bc : BodyCells) (S : Nat) : Prog :=
  .seq (cst rA 0) (Prog.rep S fun e => .seq (storeAt (bc.accA + e) rA) (storeAt (bc.accB + e) rA))

/-- `rA := hot xor ρ` (clobbers `rB`, `rAddr`). -/
def bodyTest (bc : BodyCells) (ρ : Nat) : Prog :=
  .seq (loadAt rA bc.hot) (.seq (cst rB ρ) (ar .xor rA rA rB))

/-- `B_e += d_e` with `d_e` the digit of pass `S - 1 - e`, left in `rA`. -/
def bodyAccumB (bc : BodyCells) (S e : Nat) : Prog :=
  .seq (loadAt rA (bc.digBase + (S - 1 - e)))
    (.seq (loadAt rB (bc.accB + e))
    (.seq (ar .add rB rB rA) (storeAt (bc.accB + e) rB)))

/-- `A_e += ρ · rA`. -/
def bodyAccumA (bc : BodyCells) (ρ e : Nat) : Prog :=
  .seq (cst rC ρ)
    (.seq (ar .mul rA rA rC)
    (.seq (loadAt rB (bc.accA + e))
    (.seq (ar .add rB rB rA) (storeAt (bc.accA + e) rB))))

/-- Accumulate digit `d_e` (pass `S - 1 - e`) of slot `ρ`: `B_e += d_e`, `A_e += ρ · d_e`. -/
def bodyAccum (bc : BodyCells) (S ρ e : Nat) : Prog :=
  .seq (bodyAccumB bc S e) (bodyAccumA bc ρ e)

/-- The pad of slot `ρ`: its answers, its digits, its accumulation. -/
def bodyPad (bc : BodyCells) (m S q : Nat) (tagOf : Nat → Nat) (ρ : Nat) : Prog :=
  .seq (castQueries (bc.slot ρ) tagOf q)
    (.seq (setupConsts m)
    (.seq (fracDigits bc.ansBase (2 * q) S fun j => bc.digBase + j)
      (Prog.rep S (bodyAccum bc S ρ))))

/-- One slot: its pad unless it is the hot slot. -/
def bodyEntry (bc : BodyCells) (m S q : Nat) (tagOf : Nat → Nat → Nat) (ρ : Nat) : Prog :=
  .seq (bodyTest bc ρ) (.ite rA (bodyPad bc m S q (tagOf ρ) ρ) (.skip 0))

/-- `rB := J_e + m ^ 2 - B_e`. -/
def bodySumJ (bc : BodyCells) (m e : Nat) : Prog :=
  .seq (loadAt rB (bc.joinBase + e))
    (.seq (cst rC (m * m))
    (.seq (ar .add rB rB rC)
    (.seq (loadAt rC (bc.accB + e)) (ar .sub rB rB rC))))

/-- `rAcc := A_e + hot · rB`. -/
def bodySumH (bc : BodyCells) (e : Nat) : Prog :=
  .seq (loadAt rC bc.hot)
    (.seq (ar .mul rB rB rC)
    (.seq (loadAt rAcc (bc.accA + e)) (ar .add rAcc rAcc rB)))

/-- `rAcc := A_e + hot · (J_e + m ^ 2 - B_e)`. -/
def bodySum (bc : BodyCells) (m e : Nat) : Prog := .seq (bodySumJ bc m e) (bodySumH bc e)

/-- `L_e := rAcc mod m`, stored. -/
def bodyFinal (bc : BodyCells) (m e : Nat) : Prog :=
  .seq (bodySum bc m e) (.seq (barrett rAcc rOut m 32) (storeAt (bc.outBase + e) rOut))

/-- **The body of one modulus.** -/
def bodyBlock (bc : BodyCells) (m S q : Nat) (tagOf : Nat → Nat → Nat) : Prog :=
  .seq (bodyZero bc S)
    (.seq (Prog.rep m (bodyEntry bc m S q tagOf)) (Prog.rep S (bodyFinal bc m)))

/-! ### Frame -/

/-- The body writes its answer, digit and accumulator scratch and its output cells. -/
def bodyWrites (bc : BodyCells) (S q : Nat) : Writes :=
  (((Writes.region ⟨bc.ansBase, 2 * q⟩).union (Writes.region ⟨bc.digBase, S⟩)).union
    ((Writes.region ⟨bc.accA, S⟩).union (Writes.region ⟨bc.accB, S⟩))).union
    (Writes.region ⟨bc.outBase, S⟩)

/-- The body's registers. -/
def bodyClobbers : Clobbers :=
  Clobbers.ofList [rAcc, rOut, rA, rB, rC, rD, rE, rF, rAddr, rM, rMask, rK128, rInput, rFirst,
    rSecond]

end Kriterion.CRT.SimMachine
