/-
**The replay is a tree block** (no coin, no lookup, no program): `OpsSatisfy TreeOp` for every
block of the replay with a hash query, so that release-r1's `sem_eq_runT` runs it by its tree. The
deterministic blocks follow from their `Op.Det` lemmas (`treeOps_of_det`).
-/

import Proof.Simulator.CRT.ReplayMachine
import Proof.Simulator.CRT.ReplayConversionTreeOps
import Proof.Simulator.OracleUse

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT

namespace TreeOps

theorem opsSatisfy_mono {P Q : Op → Prop} (weaker : ∀ operation, P operation → Q operation) :
    ∀ program : Prog, program.OpsSatisfy P → program.OpsSatisfy Q
  | .op operation, holds => weaker operation holds
  | .popBit _ _, _ => trivial
  | .skip _, _ => trivial
  | .abort _, _ => trivial
  | .seq first second, ⟨one, two⟩ => ⟨opsSatisfy_mono weaker first one, opsSatisfy_mono weaker second two⟩
  | .ite _ whenSet whenClear, ⟨one, two⟩ =>
      ⟨opsSatisfy_mono weaker whenSet one, opsSatisfy_mono weaker whenClear two⟩

theorem treeOp_of_det (operation : Op) (det : Op.Det operation) : TreeOp operation := by
  cases operation <;> simp_all [Op.Det, TreeOp]

/-- A deterministic block is a tree block. -/
theorem treeOps_of_det {program : Prog} (det : program.OpsSatisfy Op.Det) : program.OpsSatisfy TreeOp :=
  opsSatisfy_mono treeOp_of_det program det

variable [BN254.FieldCertificate]

/-! ### The tree -/

theorem treeOps_entryHash (cells : TreeCells) (tag s : Nat) : (entryHash cells tag s).OpsSatisfy TreeOp :=
  ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩

theorem treeOps_treeEntry (cells : TreeCells) (tagOf : Nat → Nat) (n s : Nat) :
    (treeEntry cells tagOf n s).OpsSatisfy TreeOp :=
  ⟨treeOps_of_det (det_entryTest cells n s), treeOps_entryHash cells (tagOf s) s, trivial⟩

theorem treeOps_treeStep (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) :
    (treeStep cells tagOf n).OpsSatisfy TreeOp :=
  ⟨trivial, opsSatisfy_rep _ _ (fun s _ => treeOps_treeEntry cells tagOf n s),
    treeOps_of_det (det_treeRecover cells n), treeOps_of_det (det_treeLevel cells n)⟩

theorem treeOps_treeEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (levels : Nat) :
    (treeEval cells tagOf levels).OpsSatisfy TreeOp :=
  ⟨treeOps_of_det (det_treePrefix cells), opsSatisfy_rep _ _ fun _ _ => treeOps_treeStep cells _ _⟩

theorem treeOps_growEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (start count : Nat) :
    (growEval cells tagOf start count).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun _ _ => treeOps_treeStep cells _ _

/-! ### The casts and the chunks -/

theorem treeOps_castQuery (cells : CastCells) (tag j : Nat) : (castQuery cells tag j).OpsSatisfy TreeOp :=
  ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

theorem treeOps_castQueries (cells : CastCells) (tagOf : Nat → Nat) (count : Nat) :
    (castQueries cells tagOf count).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun j _ => treeOps_castQuery cells _ j

theorem treeOps_castBlock (cells : CastCells) (l : Nat) (tagOf : Nat → Nat) :
    (castBlock cells l tagOf).OpsSatisfy TreeOp :=
  ⟨treeOps_castQueries cells tagOf _, ⟨trivial, trivial⟩, treeOps_of_det (det_castLanesProg cells l)⟩

theorem treeOps_chunkCastPhase (cc : ChunkCastCells) (width l : Nat) (tagOf : Nat → Nat → Nat) :
    (chunkCastPhase cc width l tagOf).OpsSatisfy TreeOp :=
  ⟨opsSatisfy_rep _ _ (fun leaf _ => ⟨treeOps_of_det (det_entryTest _ width leaf),
      treeOps_castBlock _ l _, trivial⟩),
    treeOps_of_det (det_pinSolve cc width l)⟩

theorem treeOps_chunkLoop (cc : CoordCells) (offset width : Nat → Nat) (tagTree tagCast : Nat → Nat → Nat → Nat)
    (l count : Nat) : (chunkLoop cc offset width tagTree tagCast l count).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun _ _ =>
    ⟨treeOps_of_det (det_chunkPrefix _ _ _ _),
      ⟨treeOps_treeEval _ _ _, treeOps_chunkCastPhase _ _ _ _⟩, treeOps_of_det (det_saveLeaves _ _ _ _)⟩

/-! ### The folds (for the conversion) and the body -/

theorem treeOps_foldsLoop (cells : FoldCells) (m start count : Nat) (tagOf : Nat → Nat → Nat) :
    (foldsLoop cells m start count tagOf).OpsSatisfy TreeOp :=
  opsSatisfy_rep _ _ fun k _ =>
    ⟨⟨trivial, opsSatisfy_rep _ _ (fun ρ _ => ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩,
        treeOps_entryHash _ _ _, trivial⟩),
      ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, trivial, trivial⟩,
      opsSatisfy_rep _ _ (fun ρ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial,
        ⟨trivial, trivial⟩⟩)⟩,
    ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial⟩,
      ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩⟩

theorem treeOps_bodyBlock (bc : BodyCells) (m S q : Nat) (tagOf : Nat → Nat → Nat) :
    (bodyBlock bc m S q tagOf).OpsSatisfy TreeOp :=
  ⟨⟨trivial, opsSatisfy_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩⟩,
    opsSatisfy_rep _ _ (fun ρ _ => ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩,
      ⟨treeOps_castQueries _ _ _, ⟨trivial, trivial, trivial⟩, treeOps_of_det (det_fracDigits _ _ _ _),
        opsSatisfy_rep _ _ fun _ _ => ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩,
          ⟨trivial, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩⟩⟩, trivial⟩),
    opsSatisfy_rep _ _ fun _ _ =>
      ⟨⟨⟨⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial⟩,
        ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial⟩⟩,
        treeOps_of_det (det_barrett _ _ _ _), ⟨trivial, trivial⟩⟩⟩

/-! ### The moduli, the key, the masks, the whole replay -/

theorem treeOps_modProg (T : CrtTable) (S coord : Nat) (cc : CoordCells) (modBase : Nat)
    (joinBaseOf : Nat → Nat) (convProgOf : Nat → Prog) (vecOf hotOf : Nat → Nat)
    (convTree : ∀ i, (convProgOf i).OpsSatisfy TreeOp) (i : Nat) :
    (modProg T S coord cc modBase joinBaseOf convProgOf vecOf hotOf i).OpsSatisfy TreeOp := by
  unfold modProg
  split
  · split
    · exact ⟨treeOps_of_det (det_chunkPrefix _ _ _ _), treeOps_bodyBlock _ _ _ _ _⟩
    · exact ⟨treeOps_of_det (det_truthWordBlock _ _ _ _ _ _), treeOps_of_det (det_sigmaBlock _ _ _ _ _ _),
        convTree i, treeOps_bodyBlock _ _ _ _ _⟩
  · trivial

theorem treeOps_keyBlock (kc : KeyCells) : (keyBlock kc).OpsSatisfy TreeOp :=
  ⟨treeOps_of_det (det_curveEval kc), treeOps_of_det det_keyInputProg, trivial, ⟨trivial, trivial⟩⟩

theorem treeOps_maskStage (mc : MaskCells) (digits : Nat) : (maskStage mc digits).OpsSatisfy TreeOp := by
  refine ⟨opsSatisfy_rep _ _ fun k _ => ⟨treeOps_castQueries _ _ _, treeOps_of_det (det_fpRead _ _),
    treeOps_of_det (det_fpRead _ _)⟩, ?_⟩
  split
  · exact ⟨treeOps_castQueries _ _ _, treeOps_of_det (det_fpRead _ _)⟩
  · trivial

theorem treeOps_coordReplay (cc : CoordCells) (T : CrtTable) (coord : Nat) (modProgOf : Nat → Prog)
    (dc : DecodeCells) (nz S : Nat) (modTree : ∀ i, (modProgOf i).OpsSatisfy TreeOp) :
    (coordReplay cc T coord modProgOf dc nz S).OpsSatisfy TreeOp :=
  ⟨treeOps_chunkLoop _ _ _ _ _ _ _, opsSatisfy_rep _ _ (fun i _ => modTree i),
    treeOps_of_det (det_decodeAll _ _ _ _ _ _)⟩

/-- The replay is a tree block, given that the conversions are. -/
theorem treeOps_replay_of (convTree : ∀ κ i, (Machine.convProg κ i).OpsSatisfy TreeOp) :
    Machine.replay.OpsSatisfy TreeOp :=
  ⟨treeOps_coordReplay _ _ _ _ _ _ _ (treeOps_modProg _ _ _ _ _ _ _ _ _ (convTree 0)),
    treeOps_coordReplay _ _ _ _ _ _ _ (treeOps_modProg _ _ _ _ _ _ _ _ _ (convTree 1)),
    treeOps_keyBlock _, treeOps_maskStage _ _⟩

omit [BN254.FieldCertificate] in
/-- Every modulus's conversion is a tree block (`treeOps_conversionReplay`). -/
theorem treeOps_convProg (κ i : Nat) : (Machine.convProg κ i).OpsSatisfy TreeOp := by
  unfold Machine.convProg
  split
  · split
    · exact treeOps_conversionReplay _ _ _ _ _ _ _ _ _
    · trivial
  · trivial

/-- **The replay is a tree block.** -/
theorem treeOps_replay : Machine.replay.OpsSatisfy TreeOp :=
  treeOps_replay_of treeOps_convProg

end TreeOps

end Kriterion.CRT.SimMachine
