/-
Axiom audit of the no-joins privacy integration: the restated named inputs (joint label law `Laws.LabelsSplit`,
the H8 re-cut `CrtConvSplit`/`CrtRestSplit`/`RealReads`, the actual-label fine view and tail of `Hidden/DeltaView*`)
and the final privacy theorem. Run with `lake env lean Scratch/NoJoinsPrivacyIntegrated.lean` after
`lake build Proof.Privacy.CRT.Final`.
-/
import Proof.Privacy.CRT.Final
import Proof.Privacy.CRT.NoJoins.Relabel
import Lean

run_cmd do
  let names := [`Kriterion.CRT.Privacy.Final.crtEntry_adaptivePrivacy, `Kriterion.CRT.Assembly.crtPrivacy,
    `Kriterion.CRT.Privacy.Laws.labelsSplit, `Kriterion.CRT.Privacy.Laws.crtRestSplit_of,
    `Kriterion.CRT.Privacy.Laws.LabelsSplitProof.tapeLabels_eq,
    `Kriterion.CRT.Privacy.Laws.realReads, `Kriterion.CRT.Privacy.ConvSplit.crtConvSplit,
    `Kriterion.CRT.Privacy.DeltaView.fine_split, `Kriterion.CRT.Privacy.DeltaView.rest_split,
    `Kriterion.CRT.Privacy.DeltaView.labelsAt_setDelta, `Kriterion.CRT.Privacy.DeltaView.fillMass_setDelta,
    `Kriterion.CRT.Privacy.DeltaView.view_fd, `Kriterion.CRT.Privacy.DeltaView.garbler_rel,
    `Kriterion.CRT.Privacy.DeltaView.garbleCM_asked, `Kriterion.CRT.Privacy.DeltaView.garbleCM_eval,
    `Kriterion.CRT.Privacy.DeltaView.convAgree_of_joins, `Kriterion.CRT.Privacy.DeltaView.joins_of_labels,
    `Kriterion.CRT.Privacy.DeltaView.tailRel, `Kriterion.CRT.Privacy.DeltaView.deltaGivenView,
    `Kriterion.CRT.Privacy.DeltaView.convHot_case, `Kriterion.CRT.Privacy.KeyZero.keyOf_congr,
    `Kriterion.CRT.Privacy.NoJoins.selZ_fillOne_shift, `Kriterion.CRT.Privacy.NoJoins.actualZeros_fillOne,
    `Kriterion.CRT.Privacy.NoJoins.clip_selZ_actual, `Kriterion.CRT.Privacy.NoJoins.coordGarbleM_zero,
    `Kriterion.CRT.Privacy.NoJoins.asked_coordGarbleM_zero]
  for name in names do
    let axioms ← Lean.collectAxioms name
    let illegal := axioms.filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo m!"No-joins privacy integration: only propext, Classical.choice, Quot.sound ({names.length} declarations)"
