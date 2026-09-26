/-
**The conversion replay is a tree block** (for the valid arm of `Stage2Law`).

Every operation of `conversionReplay` is a constant, an arithmetic operation, a load, a store or a hash query, so
`OpsSatisfy TreeOp` holds, and release-r1's `sem_eq_runT` runs the conversion by its tree. The deterministic blocks
follow from their `Op.Det` lemmas. The blocks with a query are unfolded by hand. The growth and fold parts repeat
the proofs in `Proof/Simulator/CRT/ReplayTreeOps.lean`, so that this file does not import that one and
`ReplayTreeOps.lean` can import this one.
-/

import Proof.Simulator.CRT.ReplayConversion
import Proof.Simulator.OracleUse

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT

namespace ConvTreeOps

theorem opsSatisfy_weaken {P Q : Op → Prop} (weaker : ∀ operation, P operation → Q operation) :
    ∀ program : Prog, program.OpsSatisfy P → program.OpsSatisfy Q
  | .op operation, holds => weaker operation holds
  | .popBit _ _, _ => trivial
  | .skip _, _ => trivial
  | .abort _, _ => trivial
  | .seq first second, ⟨one, two⟩ => ⟨opsSatisfy_weaken weaker first one, opsSatisfy_weaken weaker second two⟩
  | .ite _ whenSet whenClear, ⟨one, two⟩ =>
      ⟨opsSatisfy_weaken weaker whenSet one, opsSatisfy_weaken weaker whenClear two⟩

theorem treeOp_det (operation : Op) (det : Op.Det operation) : TreeOp operation := by
  cases operation <;> simp_all [Op.Det, TreeOp]

/-- A deterministic block is a tree block. -/
theorem tree_of_det {program : Prog} (det : program.OpsSatisfy Op.Det) : program.OpsSatisfy TreeOp :=
  opsSatisfy_weaken treeOp_det program det

/-! ### The growth (as in `treeOps_growEval`) -/

theorem tree_entryHash (cells : TreeCells) (tag s : Nat) : (entryHash cells tag s).OpsSatisfy TreeOp :=
  ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩

theorem tree_treeStep (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) :
    (treeStep cells tagOf n).OpsSatisfy TreeOp :=
  ⟨trivial, opsSatisfy_rep _ _ (fun s _ => ⟨tree_of_det (det_entryTest cells n s), tree_entryHash cells (tagOf s) s,
      trivial⟩),
    tree_of_det (det_treeRecover cells n), tree_of_det (det_treeLevel cells n)⟩

theorem tree_growEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (start count : Nat) :
    (growEval cells tagOf start count).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun _ _ => tree_treeStep cells _ _

/-! ### The folds (as in `treeOps_foldsLoop`) -/

theorem tree_foldsLoop (cells : FoldCells) (m start count : Nat) (tagOf : Nat → Nat → Nat) :
    (foldsLoop cells m start count tagOf).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun _ _ =>
    ⟨⟨trivial, opsSatisfy_rep _ _ (fun _ _ => ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩,
        tree_entryHash _ _ _, trivial⟩),
      ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, trivial, trivial⟩,
      opsSatisfy_rep _ _ (fun _ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial,
        ⟨trivial, trivial⟩⟩)⟩,
    ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial⟩,
      ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩⟩

/-! ### One fused extraction stage -/

theorem tree_hashEntry (cells : StageCells) (start level base stride t : Nat) :
    (hashEntry cells start level base stride t).OpsSatisfy TreeOp :=
  ⟨tree_of_det (det_absSlot cells start t), tree_of_det (det_nodeInput cells base stride), trivial,
    tree_of_det (det_matStore cells level t)⟩

theorem tree_subtreeLevel (cells : StageCells) (start d base stride : Nat) :
    (subtreeLevel cells start d base stride).OpsSatisfy TreeOp :=
  ⟨opsSatisfy_rep _ _ fun t _ => tree_hashEntry cells start (start + d) base stride t,
    opsSatisfy_rep _ _ fun t _ => tree_of_det (det_extendEntry cells start (start + d) t)⟩

theorem tree_subtreeReplay (cells : StageCells) (start depth : Nat) (treeBase : Nat → Nat) (stride : Nat) :
    (subtreeReplay cells start depth treeBase stride).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun d _ => tree_subtreeLevel cells start d (treeBase (start + d)) stride

theorem tree_castQueryDyn (cells : StageCells) (j : Nat) : (castQueryDyn cells j).OpsSatisfy TreeOp :=
  ⟨trivial, trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

theorem tree_castLanesProg (cells : CastCells) (l : Nat) : (castLanesProg cells l).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩

theorem tree_castDyn (cells : StageCells) (rb start t base stride : Nat) :
    (castDyn cells rb start t base stride).OpsSatisfy TreeOp :=
  ⟨tree_of_det (det_castInputBase cells start t base stride),
    opsSatisfy_rep _ _ (fun j _ => tree_castQueryDyn cells j), tree_castLanesProg cells.castCells rb⟩

theorem tree_leafEntry (cells : StageCells) (w rb start base stride t : Nat) :
    (leafEntry cells w rb start base stride t).OpsSatisfy TreeOp :=
  ⟨tree_castDyn cells rb start t base stride,
    opsSatisfy_rep _ _ fun k _ => tree_of_det (det_accLevel cells rb start t (start + k))⟩

theorem tree_expandReplay (cells : StageCells) (w rb start : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) :
    (expandReplay cells w rb start treeBase castBase stride).OpsSatisfy TreeOp :=
  ⟨tree_subtreeReplay cells start (w - start) treeBase stride,
    opsSatisfy_rep _ _ fun t _ => tree_leafEntry cells w rb start castBase stride t⟩

theorem tree_roundReplay (cells : StageCells) (w rb n : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) :
    (roundReplay cells w rb n treeBase castBase stride).OpsSatisfy TreeOp :=
  ⟨tree_of_det (det_roundPrefix cells w rb n), tree_expandReplay cells w rb (n + 1) treeBase castBase stride⟩

theorem tree_stageReplay (cells : StageCells) (w rb : Nat) (treeBase : Nat → Nat) (castBase stride : Nat) :
    (stageReplay cells w rb treeBase castBase stride).OpsSatisfy TreeOp :=
  ⟨tree_of_det (det_stagePrefix cells w), tree_expandReplay cells w rb 1 treeBase castBase stride,
    opsSatisfy_rep _ _ (fun k _ => tree_roundReplay cells w rb (k + 1) treeBase castBase stride),
    tree_of_det (det_stageFinal cells w rb)⟩

end ConvTreeOps

open ConvTreeOps in
/-- **The conversion of one odd modulus is a tree block** (no coin, no lookup, no program). -/
theorem TreeOps.treeOps_conversionReplay (coord i : Nat) (row : OddRow) (m W : Nat)
    (joinBase pinBase growJoin foldJoin : Nat → Nat) :
    (conversionReplay coord i row m W joinBase pinBase growJoin foldJoin).OpsSatisfy TreeOp :=
  ⟨tree_of_det (det_stageValue0 _ _), tree_of_det (det_stageValue1 _ _ _), tree_stageReplay _ _ _ _ _ _,
    tree_stageReplay _ _ _ _ _ _, tree_of_det (det_lastBitProg _ _), tree_of_det (det_saveLeaves _ _ _ _),
    tree_growEval _ _ _ _, tree_of_det (det_reindexBlock _ _ _ _), tree_of_det (det_hotInit _ _ _),
    tree_foldsLoop _ _ _ _ _⟩

end Kriterion.CRT.SimMachine
