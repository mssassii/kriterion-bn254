/-
**The replay of one one-hot tree level** (one level at a time; the same step serves the extraction trees' known-bit levels and
the growth of the kept one-hot).

At level `n ≥ 1` the evaluator holds the `2 ^ n` labels `E_s` of the level, the tree's value `α`
(the active slot is `α mod 2 ^ n`), its bit-`n` label `L` and the published join `J`. It hashes
every slot but the active one in ascending order, `y_s = (H(E_s + 2 ^ 128 · tag_s)).1`, recovers
the active material `y_h = J ⊕ L ⊕ (the other y_s)`, and extends the level in place: entry `s`
becomes `E_s ⊕ y_s` and entry `s + 2 ^ n` becomes `y_s` (`Construction/CRT/Tree.lean`,
`evalStepM` and `extendLevel`).

The machine block `treeStep cells tagOf n` follows `wideStep`
 with the CRT's hash in place of the fixed-key pair:

* `rD := 0`;
* `treeEntry` for every slot `s < 2 ^ n`: `entryTest` puts `(α mod 2 ^ n) xor s` in `rA`; if it is
  nonzero, `entryInput` builds the hash input `E_s + 2 ^ 128 · tag_s` in `rInput`, one kind-4
  query leaves the material in `rFirst`, and `entryStore` stores it at `matBase + s` and adds it
  into `rD`; otherwise a padded skip;
* `treeRecover`: `rD ⊕ J ⊕ L` stored at `matBase + (α mod 2 ^ n)`;
* `treeLevel`: the extension in place.

Its frame (the schema of `Frame.lean`): it writes the level region `levelBase .. + 2 ^ (n + 1)` and
the material region `matBase .. + 2 ^ n`, and clobbers `rA`, `rB`, `rC`, `rD`, `rE`, `rAddr` and the
oracle operands `rInput`, `rFirst`, `rSecond`.
-/

import Construction.Simulator.CRT.Arith

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The RAM cells one tree's evaluation uses. -/
structure TreeCells where
  /-- The level labels, `2 ^ levels` cells (level `n` in the first `2 ^ n`). -/
  levelBase : Nat
  /-- The step materials, `2 ^ (levels - 1)` cells. -/
  matBase : Nat
  /-- The tree's value `α`. -/
  alpha : Nat
  /-- The published join of level `n`. -/
  join : Nat → Nat
  /-- The evaluator's label of bit `n`. -/
  bit : Nat → Nat

/-- `rA := (α mod 2 ^ n) xor s` (clobbers `rB`, `rAddr`). -/
def entryTest (cells : TreeCells) (n s : Nat) : Prog :=
  .seq (loadAt rA cells.alpha)
    (.seq (cst rB (2 ^ n - 1))
    (.seq (ar .and rA rA rB)
    (.seq (cst rB s) (ar .xor rA rA rB))))

/-- `rInput := E_s + 2 ^ 128 · tag` (clobbers `rB`, `rAddr`). -/
def entryInput (cells : TreeCells) (tag s : Nat) : Prog :=
  .seq (loadAt rInput (cells.levelBase + s))
    (.seq (cst rB (2 ^ 128 * tag)) (ar .add rInput rInput rB))

/-- `RAM[matBase + s] := rFirst`; `rD := rD xor rFirst` (clobbers `rAddr`). -/
def entryStore (cells : TreeCells) (s : Nat) : Prog :=
  .seq (storeAt (cells.matBase + s) rFirst) (ar .xor rD rD rFirst)

/-- The paid arm of an entry: build the input, ask the hash, store the material. -/
def entryHash (cells : TreeCells) (tag s : Nat) : Prog :=
  .seq (entryInput cells tag s)
    (.seq (.op (.query 4 rIndex rInput rFirst rSecond)) (entryStore cells s))

/-- One slot of level `n`. -/
def treeEntry (cells : TreeCells) (tagOf : Nat → Nat) (n s : Nat) : Prog :=
  .seq (entryTest cells n s) (.ite rA (entryHash cells (tagOf s) s) (.skip 0))

/-- The active material `rD ⊕ J ⊕ L` to `matBase + (α mod 2 ^ n)`. -/
def treeRecover (cells : TreeCells) (n : Nat) : Prog :=
  .seq (loadAt rE (cells.join n))
    (.seq (ar .xor rD rD rE)
    (.seq (loadAt rE (cells.bit n))
    (.seq (ar .xor rD rD rE)
    (.seq (loadAt rA cells.alpha)
    (.seq (cst rB (2 ^ n - 1))
    (.seq (ar .and rA rA rB)
    (.seq (cst rB cells.matBase)
    (.seq (ar .add rA rA rB) (.op (.store rA rD))))))))))

/-- One entry of the extension: `E_{s + 2^n} := y_s`, `E_s := E_s ⊕ y_s`. -/
def treeLevelBody (cells : TreeCells) (n s : Nat) : Prog :=
  .seq (loadAt rE (cells.levelBase + s))
    (.seq (loadAt rC (cells.matBase + s))
    (.seq (storeAt (cells.levelBase + s + 2 ^ n) rC)
    (.seq (ar .xor rE rE rC) (storeAt (cells.levelBase + s) rE))))

/-- The extension of level `n`, in place. -/
def treeLevel (cells : TreeCells) (n : Nat) : Prog := Prog.rep (2 ^ n) (treeLevelBody cells n)

/-- **One paid level** of a tree with known bits. -/
def treeStep (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) : Prog :=
  .seq (cst rD 0)
    (.seq (Prog.rep (2 ^ n) (treeEntry cells tagOf n))
    (.seq (treeRecover cells n) (treeLevel cells n)))

/-! ### The whole tree -/

/-- Level 1: both slots hold the bit-0 label (step 0 is free). -/
def treePrefix (cells : TreeCells) : Prog :=
  .seq (loadAt rInput (cells.bit 0))
    (.seq (storeAt cells.levelBase rInput) (storeAt (cells.levelBase + 1) rInput))

/-- **A tree over `levels` bits with known bits** (`tagOf n s` the tag of slot `s` at level `n`): level 1, then the paid levels `1 .. levels - 1`. -/
def treeEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (levels : Nat) : Prog :=
  .seq (treePrefix cells) (Prog.rep (levels - 1) fun k => treeStep cells (tagOf (k + 1)) (k + 1))

/-- **The growth of a one-hot** of `2 ^ start` labels by `count` known bits: the paid levels `start, …, start + count - 1`, in place. -/
def growEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (start count : Nat) : Prog :=
  Prog.rep count fun k => treeStep cells (tagOf (start + k)) (start + k)

/-! ### The frame of a level (the schema of `Frame.lean`) -/

/-- A level writes the level region and the material region. -/
def treeStepWrites (cells : TreeCells) (n : Nat) : Writes :=
  (Writes.region ⟨cells.levelBase, 2 ^ (n + 1)⟩).union (Writes.region ⟨cells.matBase, 2 ^ n⟩)

/-- A whole tree over `levels` bits writes the level region and the material region (sized
`2 ^ levels` each, an over-approximation of the materials). -/
def treeEvalWrites (cells : TreeCells) (levels : Nat) : Writes :=
  (Writes.region ⟨cells.levelBase, 2 ^ levels⟩).union (Writes.region ⟨cells.matBase, 2 ^ levels⟩)

/-- A level clobbers the scratch registers and the oracle operands it uses. -/
def treeStepClobbers : Clobbers := Clobbers.ofList [rA, rB, rC, rD, rE, rAddr, rInput, rFirst, rSecond]

/-! ### Sizes and costs -/

theorem cost_entryHash (cells : TreeCells) (tag s : Nat) : (entryHash cells tag s).cost = 8 := rfl
theorem cost_treeEntry (cells : TreeCells) (tagOf : Nat → Nat) (n s : Nat) :
    (treeEntry cells tagOf n s).cost = 16 := rfl
theorem size_treeEntry (cells : TreeCells) (tagOf : Nat → Nat) (n s : Nat) :
    (treeEntry cells tagOf n s).size = 25 := rfl
theorem cost_treeRecover (cells : TreeCells) (n : Nat) : (treeRecover cells n).cost = 13 := rfl
theorem cost_treeLevelBody (cells : TreeCells) (n s : Nat) : (treeLevelBody cells n s).cost = 9 := rfl

theorem cost_treeStep (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) :
    (treeStep cells tagOf n).cost = 14 + 25 * 2 ^ n := by
  simp only [treeStep, treeLevel, Prog.cost, cst]
  rw [Prog.cost_rep _ _ 16 (fun s _ => cost_treeEntry cells tagOf n s),
    Prog.cost_rep _ _ 9 (fun s _ => cost_treeLevelBody cells n s), cost_treeRecover]
  omega

end Kriterion.CRT.SimMachine
