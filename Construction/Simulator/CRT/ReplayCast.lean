/-
**The replay of one cast** (the construction's parity `castM` in `Construction/CRT/Chunk.lean`).

A cast of width `l` of a label `E` asks `castAnswers l` hash answers at the tags `tagOf 0, …`, in
order, and reads its 101 lanes block-aligned: lane `i` is the `l` bits at offset
`l · (i mod per)` of block `i / per`, where `per = ⌊128 / l⌋` and block `2 j` (`2 j + 1`) is the
first (second) half of answer `j`. The parity cast keeps the upper `l - 1` bits of that reading and
replaces its low bit by bit `i` of the label `E` (`Parity.parityCastLanes`).

The machine block `castBlock cells l tagOf`:

* `castQueries`: for each answer `j`, `rInput := E + 2 ^ 128 · tag_j`, one kind-4 query, and the
  two halves stored at `ansBase + 2 j` and `ansBase + 2 j + 1`;
* `rD := E` (the label, reloaded from its cell);
* `castLanesProg`: for each lane `i < 101`, `rSecond := bit i of rD`, then load block `i / per`, shift
  right by `l · (i mod per) + 1`, mask with `2 ^ (l - 1) - 1`, double, add `rSecond`, store at
  `laneBase + i`. The lane loop reads the label from `rD` only through its low 128 bits, so the
  extraction stage runs it with `rD` holding its query base `E + 2 ^ 128 · tag`.

Frame (the schema of `Frame.lean`): it writes the answer region (`2 · castAnswers l` cells) and the
lane region (101 active cells); the queries clobber `rA`, `rB`, `rAddr`, `rInput`, `rFirst`,
`rSecond` (`castClobbers`) and the whole block also `rD` (`castBlockClobbers`).
-/

import Construction.Simulator.CRT.Arith
import Construction.Simulator.CRT.ReplayTree
import Construction.CRT.Interface

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The RAM cells of one cast. -/
structure CastCells where
  /-- The cast's label. -/
  label : Nat
  /-- The answers' halves, `2 · castAnswers l` cells. -/
  ansBase : Nat
  /-- The 101 lanes. -/
  laneBase : Nat

/-- Answer `j`: ask at `label + 2 ^ 128 · tag`, store both halves. -/
def castQuery (cells : CastCells) (tag j : Nat) : Prog :=
  .seq (loadAt rInput cells.label)
    (.seq (cst rB (2 ^ 128 * tag))
    (.seq (ar .add rInput rInput rB)
    (.seq (.op (.query 4 rIndex rInput rFirst rSecond))
    (.seq (storeAt (cells.ansBase + 2 * j) rFirst) (storeAt (cells.ansBase + (2 * j + 1)) rSecond)))))

/-- The `count` answers of a cast. -/
def castQueries (cells : CastCells) (tagOf : Nat → Nat) (count : Nat) : Prog :=
  Prog.rep count fun j => castQuery cells (tagOf j) j

/-- `rSecond := (rD >> i) mod 2`, bit `i` of the label held in `rD` (clobbers `rB`). -/
def laneBitProg (i : Nat) : Prog :=
  .seq (cst rB i)
    (.seq (ar .shiftRight rSecond rD rB)
    (.seq (cst rB 1) (ar .and rSecond rSecond rB)))

/-- Lane `i` of width `l`: `2 · ((block >> (l · (i mod per) + 1)) mod 2 ^ (l - 1)) + rSecond`, stored at
`laneBase + i` (clobbers `rA`, `rB`, `rAddr`). -/
def laneUpperProg (cells : CastCells) (l i : Nat) : Prog :=
  .seq (loadAt rA (cells.ansBase + i / Kriterion.CRT.lanesPerBlock l))
    (.seq (cst rB (l * (i % Kriterion.CRT.lanesPerBlock l) + 1))
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB (2 ^ (l - 1) - 1))
    (.seq (ar .and rA rA rB)
    (.seq (ar .add rA rA rA)
    (.seq (ar .add rA rA rSecond) (storeAt (cells.laneBase + i) rA)))))))

/-- Lane `i` of width `l`, block-aligned, with its low bit replaced by bit `i` of `rD`:
`2 · ((block >> (l · (i mod per) + 1)) mod 2 ^ (l - 1)) + ((rD >> i) mod 2)`. -/
def laneExtract (cells : CastCells) (l i : Nat) : Prog :=
  .seq (laneBitProg i) (laneUpperProg cells l i)

/-- The 101 lanes of a cast of width `l`. -/
def castLanesProg (cells : CastCells) (l : Nat) : Prog :=
  Prog.rep Kriterion.CRT.laneCount (laneExtract cells l)

/-- **One cast** of width `l`. -/
def castBlock (cells : CastCells) (l : Nat) (tagOf : Nat → Nat) : Prog :=
  .seq (castQueries cells tagOf (Kriterion.CRT.castAnswers l))
    (.seq (loadAt rD cells.label) (castLanesProg cells l))

/-! ### The casts of one chunk and the pin solve -/

/-- The RAM cells of one chunk's cast phase. -/
structure ChunkCastCells where
  /-- The leaf labels (the tree's last level), one cell per leaf. -/
  levelBase : Nat
  /-- The chunk value `α` (the hot leaf). -/
  alpha : Nat
  /-- The answer scratch of a cast, `2 · castAnswers l` cells. -/
  ansBase : Nat
  /-- The casts: lane `i` of leaf `leaf` at `castBase + 128 · leaf + i`. -/
  castBase : Nat
  /-- The stored half-pin, one lane per cell (the pin lane is twice the cell). -/
  pinBase : Nat

/-- The cast cells of one leaf. -/
def leafCells (cc : ChunkCastCells) (leaf : Nat) : CastCells :=
  ⟨cc.levelBase + leaf, cc.ansBase, cc.castBase + 128 * leaf⟩

/-- The test cells for the hot leaf (only `alpha` is read). -/
def alphaCells (cc : ChunkCastCells) : TreeCells := ⟨0, 0, cc.alpha, fun _ => 0, fun _ => 0⟩

/-- One leaf: cast it unless it is the hot leaf. -/
def castEntry (cc : ChunkCastCells) (width l : Nat) (tagOf : Nat → Nat → Nat) (leaf : Nat) : Prog :=
  .seq (entryTest (alphaCells cc) width leaf)
    (.ite rA (castBlock (leafCells cc leaf) l (tagOf leaf)) (.skip 0))

/-- The casts of every cold leaf, in ascending leaf order. -/
def castLoop (cc : ChunkCastCells) (width l : Nat) (tagOf : Nat → Nat → Nat) : Prog :=
  Prog.rep (2 ^ width) (castEntry cc width l tagOf)

/-- One term of the pin solve for lane `i`: `rD := (rD + 2 ^ l - cast_leaf,i) mod 2 ^ l` unless
`leaf` is hot. -/
def solveTerm (cc : ChunkCastCells) (width l i leaf : Nat) : Prog :=
  .seq (entryTest (alphaCells cc) width leaf)
    (.ite rA
      (.seq (loadAt rB (cc.castBase + 128 * leaf + i))
      (.seq (cst rC (2 ^ l))
      (.seq (ar .add rD rD rC)
      (.seq (ar .sub rD rD rB)
      (.seq (cst rC (2 ^ l - 1)) (ar .and rD rD rC))))))
      (.skip 0))

/-- Lane `i` of the hot cast: the pin (twice the stored half-pin lane) minus the cold casts, stored at
`castBase + 128 · α + i`. -/
def solveLane (cc : ChunkCastCells) (width l i : Nat) : Prog :=
  .seq (loadAt rD (cc.pinBase + i))
    (.seq (ar .add rD rD rD)
    (.seq (Prog.rep (2 ^ width) (solveTerm cc width l i))
    (.seq (loadAt rA cc.alpha)
    (.seq (cst rB 128)
    (.seq (ar .mul rA rA rB)
    (.seq (cst rB (cc.castBase + i))
    (.seq (ar .add rA rA rB) (.op (.store rA rD)))))))))

/-- The pin solve: the 101 lanes of the hot cast. -/
def pinSolve (cc : ChunkCastCells) (width l : Nat) : Prog := Prog.rep laneCount (solveLane cc width l)

/-- **The cast phase of one chunk** (after its tree). -/
def chunkCastPhase (cc : ChunkCastCells) (width l : Nat) (tagOf : Nat → Nat → Nat) : Prog :=
  .seq (castLoop cc width l tagOf) (pinSolve cc width l)

/-- **One chunk after its value is in RAM**: the tree, then the cast phase. -/
def chunkReplay (cells : TreeCells) (cc : ChunkCastCells) (tagTree tagCast : Nat → Nat → Nat)
    (width l : Nat) : Prog :=
  .seq (treeEval cells tagTree width) (chunkCastPhase cc width l tagCast)

/-- The cast phase writes the answer scratch and the cast region. -/
def chunkCastWrites (cc : ChunkCastCells) (width l : Nat) : Writes :=
  (Writes.region ⟨cc.ansBase, 2 * castAnswers l⟩).union
    (Writes.region ⟨cc.castBase, 128 * 2 ^ width⟩)

/-- The cast phase's registers. -/
def chunkCastClobbers : Clobbers :=
  Clobbers.ofList [rA, rB, rC, rD, rAddr, rInput, rFirst, rSecond]

/-! ### Frame -/

/-- A cast writes its answer region and its lane region. -/
def castWrites (cells : CastCells) (l : Nat) : Writes :=
  (Writes.region ⟨cells.ansBase, 2 * Kriterion.CRT.castAnswers l⟩).union
    (Writes.region ⟨cells.laneBase, Kriterion.CRT.laneCount⟩)

/-- A cast's query registers. -/
def castClobbers : Clobbers := Clobbers.ofList [rA, rB, rAddr, rInput, rFirst, rSecond]

/-- The registers of a whole cast block (the queries, and `rD` for the label). -/
def castBlockClobbers : Clobbers := Clobbers.ofList [rA, rB, rD, rAddr, rInput, rFirst, rSecond]

/-! ### Costs -/

theorem cost_castQuery (cells : CastCells) (tag j : Nat) : (castQuery cells tag j).cost = 9 := rfl
theorem cost_laneExtract (cells : CastCells) (l i : Nat) : (laneExtract cells l i).cost = 14 := rfl

theorem cost_castBlock (cells : CastCells) (l : Nat) (tagOf : Nat → Nat) :
    (castBlock cells l tagOf).cost = 9 * Kriterion.CRT.castAnswers l + 2 + 14 * laneCount := by
  simp only [castBlock, castQueries, castLanesProg, Prog.cost]
  rw [Prog.cost_rep _ _ 9 (fun j _ => cost_castQuery cells (tagOf j) j),
    Prog.cost_rep _ _ 14 (fun i _ => cost_laneExtract cells l i)]
  rw [cost_loadAt]
  simp only [Kriterion.CRT.laneCount]
  omega

end Kriterion.CRT.SimMachine
