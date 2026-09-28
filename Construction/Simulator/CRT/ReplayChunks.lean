/-
**The replay of a coordinate's chunks** (the blocks `chunkTree κ c` and `chunkCasts κ c` for
`c = 0 .. count - 1`, the first loop of heterogeneous blocks: the last chunk is narrower).

Per chunk `c` the machine computes the chunk value `α_c = (v >> offset_c) mod 2 ^ width_c` into the
scratch cell `alpha` (`chunkPrefix`, `widePrefix` pattern), runs `chunkReplay` with the
chunk's cells, and saves the chunk's leaves (`saveLeaves`; the modulus-256 body reads chunk 0's). The
tree and cast scratch is shared by all chunks; the inputs (bit labels, joins, pins) and the outputs
(casts, leaves) are per chunk. The joins are read in place in the source region (flat layout,
`Layout.lean`), so their cells are a function `chunkJoin c n`; every input lies below
the scratch, and the scratch below the outputs, so every disjointness fact is arithmetic.

Costs: `Prog.rep` over blocks of unequal cost has the sum rule `cost_rep_sum`, which replaces
xinshu's uniform `cost_rep` for heterogeneous loops.
-/

import Construction.Simulator.CRT.ReplayCast

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! ### Heterogeneous loops -/

theorem cost_rep_sum (count : Nat) (body : Nat → Prog) :
    (Prog.rep count body).cost = ∑ index ∈ Finset.range count, (body index).cost := by
  induction count with
  | zero => rw [Prog.rep]; rfl
  | succ count ih =>
      rw [Prog.rep, Prog.cost_seq, ih, Finset.sum_range_succ]

theorem size_rep_sum (count : Nat) (body : Nat → Prog) :
    (Prog.rep count body).size = ∑ index ∈ Finset.range count, (body index).size := by
  induction count with
  | zero => rw [Prog.rep]; rfl
  | succ count ih =>
      rw [Prog.rep, Prog.size_seq, ih, Finset.sum_range_succ]

/-! ### The cells of a coordinate -/

/-- The RAM layout of one coordinate's chunk phase. -/
structure CoordCells where
  /-- The coordinate value `v`. -/
  coordCell : Nat
  /-- The evaluator's label of coordinate bit `j` at `labelBase + j`. -/
  labelBase : Nat
  /-- The cell of chunk `c`'s join of tree level `n` (in place in the source region). -/
  chunkJoin : Nat → Nat → Nat
  /-- Chunk `c`'s pin lane `i` at `pinBase + 128 · c + i`. -/
  pinBase : Nat
  /-- Scratch: the current chunk value. -/
  alpha : Nat
  /-- Scratch: tree levels (256 cells). -/
  levelBase : Nat
  /-- Scratch: tree materials (256 cells). -/
  matBase : Nat
  /-- Scratch: cast answers. -/
  ansBase : Nat
  /-- Output: chunk `c`, leaf `ℓ`, lane `i` at `castBase + 32768 · c + 128 · ℓ + i`. -/
  castBase : Nat
  /-- Output: chunk `c`'s leaf label `ℓ` at `leafBase + 256 · c + ℓ`. -/
  leafBase : Nat

/-- The tree cells of chunk `c` whose first bit is `offset`. -/
def CoordCells.tree (cc : CoordCells) (offset c : Nat) : TreeCells :=
  ⟨cc.levelBase, cc.matBase, cc.alpha, cc.chunkJoin c, fun n => cc.labelBase + offset + n⟩

/-- The cast cells of chunk `c`. -/
def CoordCells.cast (cc : CoordCells) (c : Nat) : ChunkCastCells :=
  ⟨cc.levelBase, cc.alpha, cc.ansBase, cc.castBase + 32768 * c, cc.pinBase + 128 * c⟩

/-! ### The blocks -/

/-- `alpha := (v >> offset) mod 2 ^ width`. -/
def chunkPrefix (coordCell alpha offset width : Nat) : Prog :=
  .seq (loadAt rA coordCell)
    (.seq (cst rB offset)
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB (2 ^ width - 1))
    (.seq (ar .and rA rA rB) (storeAt alpha rA)))))

/-- Copy the `2 ^ width` leaves of the tree level at `levelBase` to `leafBase + 256 · c`. -/
def saveLeaves (levelBase leafBase width c : Nat) : Prog :=
  Prog.rep (2 ^ width) fun leaf =>
    .seq (loadAt rA (levelBase + leaf)) (storeAt (leafBase + 256 * c + leaf) rA)

/-- Chunk `c`: its value, its tree, its casts, its saved leaves. -/
def chunkStep (cc : CoordCells) (offset width : Nat → Nat) (tagTree tagCast : Nat → Nat → Nat → Nat)
    (l c : Nat) : Prog :=
  .seq (chunkPrefix cc.coordCell cc.alpha (offset c) (width c))
    (.seq (chunkReplay (cc.tree (offset c) c) (cc.cast c) (tagTree c) (tagCast c) (width c) l)
      (saveLeaves cc.levelBase cc.leafBase (width c) c))

/-- **The chunks `0 .. count - 1` of a coordinate.** -/
def chunkLoop (cc : CoordCells) (offset width : Nat → Nat) (tagTree tagCast : Nat → Nat → Nat → Nat)
    (l count : Nat) : Prog :=
  Prog.rep count (chunkStep cc offset width tagTree tagCast l)

/-- The chunk phase writes the scratch and the outputs: every cell from `alpha` to the end of the
leaf region. -/
def chunkLoopWrites (cc : CoordCells) (count : Nat) : Writes :=
  fun address => ∃ x, cc.alpha ≤ x ∧ x < cc.leafBase + 256 * count ∧ address = word x

/-- The chunk phase's registers. -/
def chunkLoopClobbers : Clobbers :=
  Clobbers.ofList [rA, rB, rC, rD, rE, rAddr, rInput, rFirst, rSecond]

/-! ### Costs (the heterogeneous sum rule at work) -/

theorem cost_treeEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (levels : Nat) :
    (treeEval cells tagOf levels).cost =
      8 + ∑ k ∈ Finset.range (levels - 1), (16 + 27 * 2 ^ (k + 1)) := by
  simp only [treeEval, Prog.cost_seq, cost_rep_sum, cost_treeStep]
  rfl

theorem cost_castEntry (cc : ChunkCastCells) (width l : Nat) (tagOf : Nat → Nat → Nat) (leaf : Nat) :
    (castEntry cc width l tagOf leaf).cost = 8 + (9 * castAnswers l + 8 * laneCount) := by
  simp only [castEntry, Prog.cost_seq, Prog.cost_ite, cost_castBlock]
  show 6 + (1 + max (9 * castAnswers l + 8 * laneCount + 1) 0) = _
  omega

theorem cost_solveTerm (cc : ChunkCastCells) (width l i leaf : Nat) :
    (solveTerm cc width l i leaf).cost = 15 := rfl

theorem cost_solveLane (cc : ChunkCastCells) (width l i : Nat) :
    (solveLane cc width l i).cost = 9 + 15 * 2 ^ width := by
  simp only [solveLane, Prog.cost_seq, Prog.cost_rep _ _ 15 (fun leaf _ => cost_solveTerm cc width l i leaf)]
  show 2 + (2 ^ width * 15 + (2 + (1 + (1 + (1 + (1 + 1)))))) = _
  omega

theorem cost_chunkCastPhase (cc : ChunkCastCells) (width l : Nat) (tagOf : Nat → Nat → Nat) :
    (chunkCastPhase cc width l tagOf).cost =
      2 ^ width * (8 + (9 * castAnswers l + 8 * laneCount)) + laneCount * (9 + 15 * 2 ^ width) := by
  simp only [chunkCastPhase, castLoop, pinSolve, Prog.cost_seq,
    Prog.cost_rep _ _ _ (fun leaf _ => cost_castEntry cc width l tagOf leaf),
    Prog.cost_rep _ _ _ (fun i _ => cost_solveLane cc width l i), laneCount]

theorem cost_saveLeaves (levelBase leafBase width c : Nat) :
    (saveLeaves levelBase leafBase width c).cost = 4 * 2 ^ width := by
  rw [saveLeaves, Prog.cost_rep _ _ 4 (fun leaf _ => rfl), mul_comm]

/-- **The cost of chunk `c`**, a closed form in its width. -/
theorem cost_chunkStep (cc : CoordCells) (offset width : Nat → Nat)
    (tagTree tagCast : Nat → Nat → Nat → Nat) (l c : Nat) :
    (chunkStep cc offset width tagTree tagCast l c).cost =
      8 + (8 + ∑ k ∈ Finset.range (width c - 1), (16 + 27 * 2 ^ (k + 1))) +
        (2 ^ width c * (8 + (9 * castAnswers l + 8 * laneCount)) + laneCount * (9 + 15 * 2 ^ width c)) +
        4 * 2 ^ width c := by
  simp only [chunkStep, chunkReplay, Prog.cost_seq, cost_treeEval, cost_chunkCastPhase, cost_saveLeaves]
  rw [show (chunkPrefix cc.coordCell cc.alpha (offset c) (width c)).cost = 8 from rfl]
  ring

/-- **The cost of the chunk loop**: the sum over chunks of unequal width. -/
theorem cost_chunkLoop (cc : CoordCells) (offset width : Nat → Nat)
    (tagTree tagCast : Nat → Nat → Nat → Nat) (l count : Nat) :
    (chunkLoop cc offset width tagTree tagCast l count).cost =
      ∑ c ∈ Finset.range count, (8 + (8 + ∑ k ∈ Finset.range (width c - 1), (16 + 27 * 2 ^ (k + 1))) +
        (2 ^ width c * (8 + (9 * castAnswers l + 8 * laneCount)) + laneCount * (9 + 15 * 2 ^ width c)) +
        4 * 2 ^ width c) := by
  simp only [chunkLoop, cost_rep_sum, cost_chunkStep]

end Kriterion.CRT.SimMachine
