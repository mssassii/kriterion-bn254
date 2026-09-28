/-
Axiom audit of the standalone no-joins privacy lemmas (`Proof/Privacy/CRT/NoJoins/*`).
Run with `lake env lean Scratch/NoJoinsPrivacyAudit.lean` after `lake build Proof.Privacy.CRT.NoJoins.Law`.
-/
import Proof.Privacy.CRT.NoJoins.Law
import Lean

open Kriterion.CRT.Privacy.NoJoins in
run_cmd do
  for name in [`Kriterion.CRT.Privacy.NoJoins.hotXorEquiv, `Kriterion.CRT.Privacy.NoJoins.clip_selected_hot,
      `Kriterion.CRT.Privacy.NoJoins.bitEquiv, `Kriterion.CRT.Privacy.NoJoins.keysEquiv_fst,
      `Kriterion.CRT.Privacy.NoJoins.chunkJoin_tagOnly, `Kriterion.CRT.Privacy.NoJoins.keyZero_tagOnly,
      `Kriterion.CRT.Privacy.NoJoins.keyOf_tagOnly, `Kriterion.CRT.Privacy.NoJoins.selectedLabels_keyOfZeros,
      `Kriterion.CRT.Privacy.NoJoins.labelsFor_tagOnly, `Kriterion.CRT.Privacy.NoJoins.scheme_encode_tagOnly,
      `Kriterion.CRT.Privacy.NoJoins.hotTreeBit_chunkTreeTag, `Kriterion.CRT.Privacy.NoJoins.withHotTree_other,
      `Kriterion.CRT.Privacy.NoJoins.coldSum_withHotTree, `Kriterion.CRT.Privacy.NoJoins.levelSum_withHotTree,
      `Kriterion.CRT.Privacy.NoJoins.actualZeros_withHotTree, `Kriterion.CRT.Privacy.NoJoins.keyOf_withHotTree,
      `Kriterion.CRT.Privacy.NoJoins.labelsFor_withHotTree, `Kriterion.CRT.Privacy.NoJoins.actualZeros_law,
      `Kriterion.CRT.Privacy.NoJoins.sourceLabels_law, `Kriterion.CRT.Privacy.NoJoins.actualLabels_law,
      `Kriterion.CRT.Privacy.NoJoins.labelsFor_law, `Kriterion.CRT.Privacy.NoJoins.source_labels_law,
      `Kriterion.CRT.Privacy.NoJoins.labels_payload_joint, `Kriterion.CRT.Privacy.NoJoins.residual_product,
      `Kriterion.CRT.Privacy.NoJoins.residual_guess, `Kriterion.CRT.Privacy.NoJoins.labels_residual,
      `Kriterion.CRT.Privacy.NoJoins.uniform_clip_block, `Kriterion.CRT.Privacy.NoJoins.uniform_eval,
      `Kriterion.CRT.Privacy.NoJoins.clip_delta_guess, `Kriterion.CRT.Privacy.NoJoins.delta_guess] do
    let axioms ← Lean.collectAxioms name
    let illegal := axioms.filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "No-joins privacy lemmas: only propext, Classical.choice, Quot.sound (30 declarations)"
