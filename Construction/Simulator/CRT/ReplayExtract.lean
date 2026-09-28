/-
**The replay of one fused extraction stage**, against the
evaluator `extStageEvalM` (`Construction/CRT/Extract.lean`) in round order.

The evaluator's state between rounds (`StageState`) lives in RAM (`StageCells`): the level XORs, the class sums `R_j` and cast sums `T_j` (one lane per
cell), the active label, the bit labels, and the node labels by absolute slot (extended in place,
so the leaves end in the node region). An expansion of the closed node at level `start`, slot
`slot` (a data-dependent cell), runs static loops over the relative slots `t` of each level
(`2 ^ d` at depth `d`) and over the relative leaves; the absolute slot `slot + 2 ^ start · t` and
the tag `base + stride · (absolute slot)` are computed at run time (the tags of the layout are affine
in the slot with stride 64). This matches `subtreeM` (levels ascending, relative slots ascending)
and the cast table of `expandM` (relative leaves ascending) query for query.

Blocks:
* `stagePrefix`: `sub := reduce_w R^E` and `b_0^E := laneBit sub 0` (lane by lane), the active label
  and bit 0, the zeroed sums, the closed slot `(s mod 2) xor 1` and its label;
* `expandReplay start`: the subtree levels (`hashEntry`, `extendEntry`), then per leaf the cast
  (`castInputBase`, `castQueryDyn`, the lane extraction of `ReplayCast.lean`) and its addition to the
  class and cast sums of the levels `start .. w` (`accLevel`);
* `roundReplay n`: the class sum `R_n + q_n (P − T_n)` and the bit plane `n` of
  `sub − reduce_w res_n` lane by lane (`roundLane`), the bit label, the hot material
  `b ⊕ J_n ⊕ Y_n`, the branch on bit `n` of `s`, then `expandReplay (n + 1)`;
* `stageFinal`: the upcast `R_w + s (P − T_w)`, the peel `((R^E − U) mod 2 ^ rb) / 2 ^ w` lane by lane,
  and the active leaf's label at node `s`.
-/

import Construction.Simulator.CRT.ReplayCast

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-- The RAM cells of one fused stage. -/
structure StageCells where
  /-- The stage value `s` (input). -/
  value : Nat
  /-- The remainder label `R^E`, lane `i` at `remBase + i` (input). -/
  remBase : Nat
  /-- The join `J_n` at `joinBase + n` (input, `1 ≤ n < w`). -/
  joinBase : Nat
  /-- The stored half-pin, lane `i` at `pinBase + i` (input; the pin lane is twice the cell). -/
  pinBase : Nat
  /-- `sub = reduce_w R^E`, lane `i` at `subBase + i` (scratch). -/
  subBase : Nat
  /-- Node labels by absolute slot, `2 ^ w` cells; the leaves at the end (output). -/
  nodeBase : Nat
  /-- One level's materials by relative slot (scratch). -/
  matBase : Nat
  /-- The level XOR `Y_L` at `levelSumBase + L` (scratch). -/
  levelSumBase : Nat
  /-- The class sum `R_j`, lane `i` at `classBase + 128 · j + i` (scratch, `j ≤ w`). -/
  classBase : Nat
  /-- The cast sum `T_j`, lane `i` at `castSumBase + 128 · j + i` (scratch, `j ≤ w`). -/
  castSumBase : Nat
  /-- One cast's answers (scratch). -/
  ansBase : Nat
  /-- One cast's lanes (scratch). -/
  laneBase : Nat
  /-- The active label (scratch). -/
  active : Nat
  /-- The slot of the subtree being expanded (scratch). -/
  slot : Nat
  /-- The bit label `b^E_n` at `bitBase + n` (output). -/
  bitBase : Nat
  /-- The next remainder, lane `i` at `nextBase + i` (output). -/
  nextBase : Nat

/-- The cast cells of the stage (only the answer and lane regions are used). -/
def StageCells.castCells (cells : StageCells) : CastCells := ⟨0, cells.ansBase, cells.laneBase⟩

/-! ### Expansion: the subtree levels -/

/-- `rF := slot + 2 ^ start · t` (clobbers `rB`, `rAddr`). -/
def absSlot (cells : StageCells) (start t : Nat) : Prog :=
  .seq (loadAt rF cells.slot) (.seq (cst rB (2 ^ start * t)) (ar .add rF rF rB))

/-- `rInput := node[x] + 2 ^ 128 · (base + stride · x)` with `x` in `rF` (clobbers `rB`, `rC`,
`rAddr`). -/
def nodeInput (cells : StageCells) (base stride : Nat) : Prog :=
  .seq (cst rB cells.nodeBase)
    (.seq (ar .add rAddr rF rB)
    (.seq (.op (.load rInput rAddr))
    (.seq (cst rB (2 ^ 128 * stride))
    (.seq (ar .mul rC rF rB)
    (.seq (ar .add rInput rInput rC)
    (.seq (cst rB (2 ^ 128 * base)) (ar .add rInput rInput rB)))))))

/-- The material to `mat[t]` and into `Y_L` (clobbers `rE`, `rAddr`). -/
def matStore (cells : StageCells) (level t : Nat) : Prog :=
  .seq (storeAt (cells.matBase + t) rFirst)
    (.seq (loadAt rE (cells.levelSumBase + level))
    (.seq (ar .xor rE rE rFirst) (storeAt (cells.levelSumBase + level) rE)))

/-- One hashed node of level `level` (relative slot `t`). -/
def hashEntry (cells : StageCells) (start level base stride t : Nat) : Prog :=
  .seq (absSlot cells start t)
    (.seq (nodeInput cells base stride)
    (.seq (.op (.query 4 rIndex rInput rFirst rSecond))
      (.seq (clipReg rFirst) (matStore cells level t))))

/-- One node of the extension of level `level`: `node[x] ^= mat[t]`, `node[x + 2 ^ level] := mat[t]`
(clobbers `rB`, `rC`, `rE`, `rF`, `rAddr`). -/
def extendEntry (cells : StageCells) (start level t : Nat) : Prog :=
  .seq (absSlot cells start t)
    (.seq (cst rB cells.nodeBase)
    (.seq (ar .add rF rF rB)
    (.seq (loadAt rC (cells.matBase + t))
    (.seq (.op (.load rE rF))
    (.seq (ar .xor rE rE rC)
    (.seq (.op (.store rF rE))
    (.seq (cst rB (2 ^ level))
    (.seq (ar .add rF rF rB) (.op (.store rF rC))))))))))

/-- One level of a subtree at depth `d` below `start`. -/
def subtreeLevel (cells : StageCells) (start d base stride : Nat) : Prog :=
  .seq (Prog.rep (2 ^ d) (hashEntry cells start (start + d) base stride))
    (Prog.rep (2 ^ d) (extendEntry cells start (start + d)))

/-- The subtree below the closed node at level `start`: its levels `start .. start + depth − 1`. -/
def subtreeReplay (cells : StageCells) (start depth : Nat) (treeBase : Nat → Nat) (stride : Nat) :
    Prog :=
  Prog.rep depth fun d => subtreeLevel cells start d (treeBase (start + d)) stride

/-! ### Expansion: the casts and the sums -/

/-- `rD := node[α] + 2 ^ 128 · (base + stride · α)` for `α = slot + 2 ^ start · t` (clobbers `rB`,
`rC`, `rF`, `rAddr`). -/
def castInputBase (cells : StageCells) (start t base stride : Nat) : Prog :=
  .seq (absSlot cells start t)
    (.seq (cst rB cells.nodeBase)
    (.seq (ar .add rAddr rF rB)
    (.seq (.op (.load rD rAddr))
    (.seq (cst rB (2 ^ 128 * stride))
    (.seq (ar .mul rC rF rB)
    (.seq (ar .add rD rD rC)
    (.seq (cst rB (2 ^ 128 * base)) (ar .add rD rD rB))))))))

/-- Answer `j` of the current cast: ask at `rD + 2 ^ 128 · j`, store both halves. -/
def castQueryDyn (cells : StageCells) (j : Nat) : Prog :=
  .seq (cst rB (2 ^ 128 * j))
    (.seq (ar .add rInput rD rB)
    (.seq (.op (.query 4 rIndex rInput rFirst rSecond))
    (.seq (storeAt (cells.ansBase + 2 * j) rFirst) (storeAt (cells.ansBase + (2 * j + 1)) rSecond))))

/-- The cast of relative leaf `t` of width `rb` into the lane scratch. -/
def castDyn (cells : StageCells) (rb start t base stride : Nat) : Prog :=
  .seq (castInputBase cells start t base stride)
    (.seq (Prog.rep (Kriterion.CRT.castAnswers rb) (castQueryDyn cells))
      (castLanesProg cells.castCells rb))

/-- Lane `i` into the class sum of level `j`: `R_j[i] := (R_j[i] + rF · lane_i) mod 2 ^ rb`, with
`rF = α mod 2 ^ j` (clobbers `rA`, `rB`, `rC`, `rE`, `rAddr`). -/
def accClass (cells : StageCells) (rb j i : Nat) : Prog :=
  .seq (loadAt rC (cells.laneBase + i))
    (.seq (loadAt rE (cells.classBase + 128 * j + i))
    (.seq (ar .mul rA rF rC)
    (.seq (ar .add rE rE rA)
    (.seq (cst rB (2 ^ rb - 1))
    (.seq (ar .and rE rE rB) (storeAt (cells.classBase + 128 * j + i) rE))))))

/-- Lane `i` into the cast sum of level `j`: `T_j[i] := (T_j[i] + lane_i) mod 2 ^ rb` (clobbers `rB`,
`rC`, `rE`, `rAddr`). -/
def accCast (cells : StageCells) (rb j i : Nat) : Prog :=
  .seq (loadAt rC (cells.laneBase + i))
    (.seq (loadAt rE (cells.castSumBase + 128 * j + i))
    (.seq (ar .add rE rE rC)
    (.seq (cst rB (2 ^ rb - 1))
    (.seq (ar .and rE rE rB) (storeAt (cells.castSumBase + 128 * j + i) rE)))))

/-- The current cast into the sums of level `j` (`α = slot + 2 ^ start · t`). -/
def accLevel (cells : StageCells) (rb start t j : Nat) : Prog :=
  .seq (absSlot cells start t)
    (.seq (cst rB (2 ^ j - 1))
    (.seq (ar .and rF rF rB)
      (Prog.rep Kriterion.CRT.laneCount fun i => .seq (accClass cells rb j i) (accCast cells rb j i))))

/-- Relative leaf `t`: its cast, then its terms of the sums of levels `start .. w`. -/
def leafEntry (cells : StageCells) (w rb start base stride t : Nat) : Prog :=
  .seq (castDyn cells rb start t base stride)
    (Prog.rep (w - start + 1) fun k => accLevel cells rb start t (start + k))

/-- **The expansion of the closed node at level `start`** (the node's label already at
`node[slot]`, the slot at `cells.slot`). -/
def expandReplay (cells : StageCells) (w rb start : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) :
    Prog :=
  .seq (subtreeReplay cells start (w - start) treeBase stride)
    (Prog.rep (2 ^ (w - start)) (leafEntry cells w rb start castBase stride))

/-! ### A round -/

/-- `rC := (P_i + 2 ^ rb − T_n[i]) · q` with `q` in `rF`, where the pin lane `P_i` is twice the stored
half-pin cell (clobbers `rB`, `rC`, `rE`, `rAddr`). -/
def resHead (cells : StageCells) (rb n i : Nat) : Prog :=
  .seq (loadAt rC (cells.pinBase + i))
    (.seq (ar .add rC rC rC)
    (.seq (loadAt rE (cells.castSumBase + 128 * n + i))
    (.seq (cst rB (2 ^ rb))
    (.seq (ar .add rC rC rB)
    (.seq (ar .sub rC rC rE) (ar .mul rC rC rF))))))

/-- `rC := (rC + R_n[i]) mod 2 ^ rb` (clobbers `rB`, `rC`, `rE`, `rAddr`). -/
def resTail (cells : StageCells) (rb n i : Nat) : Prog :=
  .seq (loadAt rE (cells.classBase + 128 * n + i))
    (.seq (ar .add rC rC rE)
    (.seq (cst rB (2 ^ rb - 1)) (ar .and rC rC rB)))

/-- `rC := (R_n[i] + q · (P_i + 2 ^ rb − T_n[i])) mod 2 ^ rb` with `q` in `rF` (clobbers `rB`, `rC`,
`rE`, `rAddr`). -/
def roundRes (cells : StageCells) (rb n i : Nat) : Prog :=
  .seq (resHead cells rb n i) (resTail cells rb n i)

/-- `rE := (sub_i + 2 ^ w − (rC mod 2 ^ w)) mod 2 ^ w` (clobbers `rB`, `rC`, `rE`, `rAddr`). -/
def roundDiff (cells : StageCells) (w i : Nat) : Prog :=
  .seq (cst rB (2 ^ w - 1))
    (.seq (ar .and rC rC rB)
    (.seq (loadAt rE (cells.subBase + i))
    (.seq (cst rB (2 ^ w))
    (.seq (ar .add rE rE rB)
    (.seq (ar .sub rE rE rC)
    (.seq (cst rB (2 ^ w - 1)) (ar .and rE rE rB)))))))

/-- Bit `n` of `rE` into bit `i` of `rD` (clobbers `rB`, `rE`). -/
def bitInsert (n i : Nat) : Prog :=
  .seq (cst rB n)
    (.seq (ar .shiftRight rE rE rB)
    (.seq (cst rB 1)
    (.seq (ar .and rE rE rB)
    (.seq (cst rB i)
    (.seq (ar .shiftLeft rE rE rB) (ar .xor rD rD rE))))))

/-- Lane `i` of round `n`: its class sum, its difference, its bit plane `n`. -/
def roundLane (cells : StageCells) (w rb n i : Nat) : Prog :=
  .seq (roundRes cells rb n i) (.seq (roundDiff cells w i) (bitInsert n i))

/-- The bit label of round `n` into `rD` and `bits[n]` (`q = s mod 2 ^ n` into `rF`). -/
def roundBit (cells : StageCells) (w rb n : Nat) : Prog :=
  .seq (loadAt rF cells.value)
    (.seq (cst rB (2 ^ n - 1))
    (.seq (ar .and rF rF rB)
    (.seq (cst rD 0)
    (.seq (Prog.rep Kriterion.CRT.laneCount (roundLane cells w rb n))
      (storeAt (cells.bitBase + n) rD)))))

/-- The hot material into `rD` and the left child into `rE` (clobbers `rE`, `rAddr`). -/
def roundHot (cells : StageCells) (n : Nat) : Prog :=
  .seq (loadAt rE (cells.joinBase + n))
    (.seq (ar .xor rD rD rE)
    (.seq (loadAt rE (cells.levelSumBase + n))
    (.seq (ar .xor rD rD rE)
    (.seq (loadAt rE cells.active) (ar .xor rE rE rD)))))

/-- Bit `n` of `s` into `rA` (clobbers `rB`, `rAddr`). -/
def roundTest (cells : StageCells) (n : Nat) : Prog :=
  .seq (loadAt rA cells.value)
    (.seq (cst rB n)
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB 1) (ar .and rA rA rB))))

/-- Bit set: the right child is active; the left child (in `rE`) is closed at slot `q` (in `rF`). -/
def roundSet (cells : StageCells) : Prog :=
  .seq (storeAt cells.active rD)
    (.seq (storeAt cells.slot rF)
    (.seq (cst rB cells.nodeBase)
    (.seq (ar .add rAddr rF rB) (.op (.store rAddr rE)))))

/-- Bit clear: the left child (in `rE`) is active; the right child (in `rD`) is closed at slot
`q + 2 ^ n`. -/
def roundClear (cells : StageCells) (n : Nat) : Prog :=
  .seq (storeAt cells.active rE)
    (.seq (cst rB (2 ^ n))
    (.seq (ar .add rF rF rB)
    (.seq (storeAt cells.slot rF)
    (.seq (cst rB cells.nodeBase)
    (.seq (ar .add rAddr rF rB) (.op (.store rAddr rD)))))))

/-- The deterministic part of round `n`. -/
def roundPrefix (cells : StageCells) (w rb n : Nat) : Prog :=
  .seq (roundBit cells w rb n)
    (.seq (roundHot cells n)
    (.seq (roundTest cells n) (.ite rA (roundSet cells) (roundClear cells n))))

/-- **Round `n`** (`1 ≤ n < w`). -/
def roundReplay (cells : StageCells) (w rb n : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) :
    Prog :=
  .seq (roundPrefix cells w rb n) (expandReplay cells w rb (n + 1) treeBase castBase stride)

/-! ### Prefix and final -/

/-- Lane `i` of the prefix: `sub_i := R^E_i mod 2 ^ w` (clobbers `rB`, `rC`, `rAddr`). -/
def subLane (cells : StageCells) (w i : Nat) : Prog :=
  .seq (loadAt rC (cells.remBase + i))
    (.seq (cst rB (2 ^ w - 1))
    (.seq (ar .and rC rC rB) (storeAt (cells.subBase + i) rC)))

/-- Bit `b` of the lane at `base + i` into bit `i` of `rD` (clobbers `rB`, `rE`, `rAddr`). -/
def packLane (base b i : Nat) : Prog :=
  .seq (loadAt rE (base + i)) (bitInsert b i)

/-- **The lane-bit pack**: `rD := laneBit lanes b` for the 101 active lanes at `base .. base + 100`
(clobbers `rB`, `rD`, `rE`, `rAddr`). -/
def lanePack (base b : Nat) : Prog :=
  .seq (cst rD 0) (Prog.rep Kriterion.CRT.laneCount (packLane base b))

/-- Zero `count` cells from `base` (clobbers `rB`, `rAddr`). -/
def zeroCells (base count : Nat) : Prog :=
  .seq (cst rB 0) (Prog.rep count fun k => storeAt (base + k) rB)

/-- The closed level-1 slot `(s mod 2) xor 1` into `cells.slot`, and the label in `rD` at its
node (clobbers `rB`, `rF`, `rAddr`). -/
def prefixSlot (cells : StageCells) : Prog :=
  .seq (loadAt rF cells.value)
    (.seq (cst rB 1)
    (.seq (ar .and rF rF rB)
    (.seq (ar .xor rF rF rB)
    (.seq (storeAt cells.slot rF)
    (.seq (cst rB cells.nodeBase)
    (.seq (ar .add rAddr rF rB) (.op (.store rAddr rD))))))))

/-- The prefix: `sub`, `b_0^E` (active and bit 0), zero sums, the closed level-1 slot and its
label. -/
def stagePrefix (cells : StageCells) (w : Nat) : Prog :=
  .seq (Prog.rep Kriterion.CRT.laneCount (subLane cells w))
    (.seq (lanePack cells.subBase 0)
    (.seq (storeAt cells.active rD)
    (.seq (storeAt cells.bitBase rD)
    (.seq (zeroCells cells.levelSumBase w)
    (.seq (zeroCells cells.classBase (128 * (w + 1)))
    (.seq (zeroCells cells.castSumBase (128 * (w + 1))) (prefixSlot cells)))))))

/-- The peel of lane `i`: with `U_i` in `rC`, `next[i] := ((R^E_i + 2 ^ rb − U_i) mod 2 ^ rb) >> w`
(clobbers `rB`, `rE`, `rAddr`). -/
def finalTail (cells : StageCells) (w rb i : Nat) : Prog :=
  .seq (loadAt rE (cells.remBase + i))
    (.seq (cst rB (2 ^ rb))
    (.seq (ar .add rE rE rB)
    (.seq (ar .sub rE rE rC)
    (.seq (cst rB (2 ^ rb - 1))
    (.seq (ar .and rE rE rB)
    (.seq (cst rB w)
    (.seq (ar .shiftRight rE rE rB) (storeAt (cells.nextBase + i) rE))))))))

/-- The upcast lane `U_i = (R_w[i] + s (P_i + 2 ^ rb − T_w[i])) mod 2 ^ rb` into `rC` (with `s` in
`rF`), then the peel into `next[i]`. -/
def finalLane (cells : StageCells) (w rb i : Nat) : Prog :=
  .seq (roundRes cells rb w i) (finalTail cells w rb i)

/-- The final block: the next remainder, and the active leaf's label at node `s`. -/
def stageFinal (cells : StageCells) (w rb : Nat) : Prog :=
  .seq (loadAt rF cells.value)
    (.seq (Prog.rep Kriterion.CRT.laneCount (finalLane cells w rb))
    (.seq (loadAt rE cells.active)
    (.seq (cst rB cells.nodeBase)
    (.seq (ar .add rAddr rF rB) (.op (.store rAddr rE))))))

/-- **The replay of one fused stage** of width `w` and cast width `rb`, with tree tags
`treeBase level + stride · slot` and cast tags `castBase + stride · leaf + part`. -/
def stageReplay (cells : StageCells) (w rb : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) :
    Prog :=
  .seq (stagePrefix cells w)
    (.seq (expandReplay cells w rb 1 treeBase castBase stride)
    (.seq (Prog.rep (w - 1) fun k => roundReplay cells w rb (k + 1) treeBase castBase stride)
      (stageFinal cells w rb)))

/-! ### Frame (the schema of `Frame.lean`) -/

/-- The stage writes its scratch and output regions. -/
def stageWrites (cells : StageCells) (w rb : Nat) : Writes :=
  (Writes.region ⟨cells.subBase, Kriterion.CRT.laneCount⟩).union <|
  (Writes.region ⟨cells.nodeBase, 2 ^ w⟩).union <|
  (Writes.region ⟨cells.matBase, 2 ^ w⟩).union <|
  (Writes.region ⟨cells.levelSumBase, w⟩).union <|
  (Writes.region ⟨cells.classBase, 128 * (w + 1)⟩).union <|
  (Writes.region ⟨cells.castSumBase, 128 * (w + 1)⟩).union <|
  (Writes.region ⟨cells.ansBase, 2 * Kriterion.CRT.castAnswers rb⟩).union <|
  (Writes.region ⟨cells.laneBase, Kriterion.CRT.laneCount⟩).union <|
  (Writes.cell cells.active).union <|
  (Writes.cell cells.slot).union <|
  (Writes.region ⟨cells.bitBase, w⟩).union (Writes.region ⟨cells.nextBase, Kriterion.CRT.laneCount⟩)

/-- The stage's registers. -/
def stageClobbers : Clobbers :=
  Clobbers.ofList [rA, rB, rC, rD, rE, rF, rAddr, rInput, rFirst, rSecond]

end Kriterion.CRT.SimMachine
