/-
**The replay of the folds modulo `m`** (the construction's
`foldEvalM` and `foldsEvalM` in `Construction/CRT/Fold.lean`).

One fold at bit position `j` over a one-hot vector `h[ρ]`, `ρ < m`, with hot index `hot` (a run-time
value in RAM) and compile-time shift `s = 2 ^ j mod m`:

* `rD := 0`; for every `ρ < m` (`foldEntry`): unless `ρ = hot`, ask `u_ρ = clip (H(embed h[ρ] + 2 ^ 128 · tag_ρ)).1`,
  store it at `matBase + ρ` and add it into `rD` (the tree step's `entryHash`, reused);
* `foldRecover`: `u_hot = rD ⊕ join ⊕ bitLabel` stored at `matBase + hot` (a run-time address);
* `foldUpdate`: `h[ρ] := h[ρ] ⊕ u_ρ ⊕ u_((ρ + m - s) mod m)` in place (the source index is a
  compile-time constant);
* between folds (`hotUpdate`): `hot := (hot + bit_j(σ) · s) mod m`, one conditional subtraction.
-/

import Construction.Simulator.CRT.ReplayTree

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The RAM cells of one modulus's folds. -/
structure FoldCells where
  /-- The one-hot vector `h[ρ]`, `m` cells. -/
  vecBase : Nat
  /-- The materials `u_ρ`, `m` cells. -/
  matBase : Nat
  /-- The hot index. -/
  hot : Nat
  /-- The value `σ_m` whose bits drive the hot index. -/
  sigma : Nat
  /-- The published join of bit position `j`. -/
  join : Nat → Nat
  /-- The evaluator's label of bit position `j`. -/
  bit : Nat → Nat

/-- The tree cells that let the fold reuse the tree step's hashing piece. -/
def FoldCells.asTree (cells : FoldCells) : TreeCells :=
  ⟨cells.vecBase, cells.matBase, cells.hot, cells.join, cells.bit⟩

/-- `rA := hot xor ρ` (clobbers `rB`, `rAddr`). -/
def foldTest (cells : FoldCells) (ρ : Nat) : Prog :=
  .seq (loadAt rA cells.hot) (.seq (cst rB ρ) (ar .xor rA rA rB))

/-- One residue of a fold. -/
def foldEntry (cells : FoldCells) (tagOf : Nat → Nat) (ρ : Nat) : Prog :=
  .seq (foldTest cells ρ) (.ite rA (entryHash cells.asTree (tagOf ρ) ρ) (.skip 0))

/-- The hot material `rD ⊕ join ⊕ bitLabel` to `matBase + hot`. -/
def foldRecover (cells : FoldCells) (j : Nat) : Prog :=
  .seq (loadAt rE (cells.join j))
    (.seq (ar .xor rD rD rE)
    (.seq (loadAt rE (cells.bit j))
    (.seq (ar .xor rD rD rE)
    (.seq (loadAt rA cells.hot)
    (.seq (cst rB cells.matBase)
    (.seq (ar .add rA rA rB) (.op (.store rA rD))))))))

/-- The source residue of `ρ` for the shift `s`. -/
def foldSourceNat (m s ρ : Nat) : Nat := (ρ + m - s % m) % m

/-- One residue of the new vector: `h[ρ] := h[ρ] ⊕ u_ρ ⊕ u_src`. -/
def foldUpdate (cells : FoldCells) (m s ρ : Nat) : Prog :=
  .seq (loadAt rE (cells.vecBase + ρ))
    (.seq (loadAt rC (cells.matBase + ρ))
    (.seq (ar .xor rE rE rC)
    (.seq (loadAt rC (cells.matBase + foldSourceNat m s ρ))
    (.seq (ar .xor rE rE rC) (storeAt (cells.vecBase + ρ) rE)))))

/-- **One fold** at bit position `j` with shift `s` and tags `tagOf ρ`. -/
def foldStep (cells : FoldCells) (m s j : Nat) (tagOf : Nat → Nat) : Prog :=
  .seq (cst rD 0)
    (.seq (Prog.rep m (foldEntry cells tagOf))
    (.seq (foldRecover cells j) (Prog.rep m (foldUpdate cells m s))))

/-- `rA := bit_j(σ) · s`. -/
def hotBit (cells : FoldCells) (s j : Nat) : Prog :=
  .seq (loadAt rA cells.sigma)
    (.seq (cst rB j)
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB 1)
    (.seq (ar .and rA rA rB)
    (.seq (cst rB s) (ar .mul rA rA rB))))))

/-- `hot := (rA + hot) mod m` for `rA + hot < 2 m`. -/
def hotReduce (cells : FoldCells) (m : Nat) : Prog :=
  .seq (loadAt rB cells.hot)
    (.seq (ar .add rA rA rB)
    (.seq (cst rC m)
    (.seq (ar .less rD rA rC)
    (.seq (cst rE 1)
    (.seq (ar .sub rD rE rD)
    (.seq (ar .mul rD rD rC)
    (.seq (ar .sub rA rA rD) (storeAt cells.hot rA))))))))

/-- `hot := (hot + bit_j(σ) · s) mod m` for `s < m`. -/
def hotUpdate (cells : FoldCells) (m s j : Nat) : Prog :=
  .seq (hotBit cells s j) (hotReduce cells m)

/-- The folds at bit positions `start, …, start + count - 1`, each followed by its hot update. -/
def foldsLoop (cells : FoldCells) (m start count : Nat) (tagOf : Nat → Nat → Nat) : Prog :=
  Prog.rep count fun k =>
    .seq (foldStep cells m (2 ^ (start + k) % m) (start + k) (tagOf (start + k)))
      (hotUpdate cells m (2 ^ (start + k) % m) (start + k))

/-! ### The reindex modulo `m` and the first hot index -/

/-- One leaf of residue `ρ`'s class: `rD ^= K_leaf` if `leaf ≡ ρ (mod m)` (decided at compile time;
the other leaves cost nothing). -/
def reindexStep (levelBase m ρ leaf : Nat) : Prog :=
  if leaf % m = ρ then .seq (loadAt rC (levelBase + leaf)) (ar .xor rD rD rC) else .skip 0

/-- `h[ρ] := XOR of the labels K_leaf with leaf ≡ ρ (mod m)`, `leaf < 2 ^ n`. -/
def reindexResidue (levelBase vecBase n m ρ : Nat) : Prog :=
  .seq (cst rD 0)
    (.seq (Prog.rep (2 ^ n) (reindexStep levelBase m ρ)) (storeAt (vecBase + ρ) rD))

/-- **The reindex** of the kept one-hot of `2 ^ n` labels at `levelBase` into the `m` cells at
`vecBase` (the construction's `reindex`). -/
def reindexBlock (levelBase vecBase n m : Nat) : Prog :=
  Prog.rep m (reindexResidue levelBase vecBase n m)

/-- `hot := (σ mod 2 ^ keep) mod m`, the folds' first hot index. -/
def hotInit (cells : FoldCells) (keep m : Nat) : Prog :=
  .seq (.seq (loadAt rAcc cells.sigma) (.seq (cst rB (2 ^ keep - 1)) (ar .and rAcc rAcc rB)))
    (.seq (barrett rAcc rOut m 16) (storeAt cells.hot rOut))

/-! ### Frame -/

/-- A fold writes the vector and the materials. -/
def foldWrites (cells : FoldCells) (m : Nat) : Writes :=
  (Writes.region ⟨cells.vecBase, m⟩).union (Writes.region ⟨cells.matBase, m⟩)

/-- The folds also write the hot index. -/
def foldsWrites (cells : FoldCells) (m : Nat) : Writes :=
  (foldWrites cells m).union (Writes.cell cells.hot)

end Kriterion.CRT.SimMachine
