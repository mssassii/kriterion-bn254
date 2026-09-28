# Proof map

This map covers the CRT entry with the sign row against the challenge library `aaf2789`. The top-level
`README.md` explains the construction and the argument, and `Intuition.md` the ideas. This file says which
module supplies which proof obligation. **Current status:** the combined 84-modulus, selected width-8/9 tree has passed its full build,
metric/encoding audit and whole-tree axiom audit (23,742 declarations; the three permitted axioms).
See the root README for evidence.

`Proof.lean` imports `Proof.Correctness.CRT.EntryCorrect`, `Proof.LamportCompatibility.Labels` and
`Proof.Privacy.CRT.Final`, and `Construction.lean` imports the entry and the simulator machine, so a bare
`lake build` compiles every module named here and every module they import. `Submission.lean` names the
fields. The baseline proved every field without admissions and passed the three-axiom audit.
The combined tree introduces no admitted proof. Its current audit is `Scratch/CombinedAudit.lean`,
with `Scratch/ProofAudit.lean` checking every construction and proof declaration.

## 1. The fields of `Kriterion.Solution`

| field | proved by | where |
|---|---|---|
| `garbleProgram`, `garbleQueries`, `garbleProgramCorrect` | `Entry.garbleProgram` at `Entry.garbleBudget` (1,061,622); `Submission.garbleProgramCorrect` | `Construction/CRT/Entry.lean`, `Bounds.lean`, `BudgetFacts.lean`; `Submission.lean` |
| `evaluateProgram`, `evaluateQueries`, `evaluateProgramCorrect` | `Entry.evaluateProgram` at `Entry.evaluateBudget` (1,054,788); `Submission.evaluateProgramCorrect` | the same |
| `ciphertextSize` | `Entry.Wire.encoding_length` (128,276) | `Construction/CRT/Public.lean` |
| `lamportCompatible` | `Lamport.selectedLabels_eq` | `Proof/LamportCompatibility/Labels.lean` |
| `functionCorrect` | `rfl` | `Submission.lean` |
| `perfectCorrectness` | `EntryCorrect.perfectCorrectness` | `Proof/Correctness/CRT/EntryCorrect.lean` |
| `adaptivePrivacy` | `Final.crtEntry_adaptivePrivacy : CrtPrivacy crtEntry` | `Proof/Privacy/CRT/Final.lean` |

## 2. Perfect correctness (`Proof/Correctness/CRT/`)

Every statement below holds for every hash function `H : HashN` read on natural inputs, with the
garbler's answers at hot positions as free parameters, so the same statements serve the privacy proof on
answer tables.

| module | statement |
|---|---|
| `TreeSteps.lean` | the one-hot tree step: the evaluator's labels are the garbler's masks XOR the bit times `Δ` at every slot |
| `ChunkStep.lean` | a chunk: tree, casts and pin give the arithmetic label of every leaf |
| `Word.lean` | the truth-table word is an arithmetic label of `σ_m`, and `σ_m ≡ v (mod m)` with `σ_m < 2^ℓ` |
| `ExtractStage.lean`, `StageProgram.lean` | the round invariant of a fused extraction stage, generic in the stage and cast widths, and the same for the stage's query programs |
| `FoldChain.lean` | reindex modulo `m`, the folds and the pin codec |
| `Conversion.lean` | one odd modulus: the one-hot vector over `Z_m` hot at `v mod m` |
| `BodyStep.lean` | the body: `L = R + (v mod m)·a mod m` |
| `Arith.lean`, `Record.lean` | lane arithmetic, the wrap hint (`wrapHint_exact`), the per-encoding records |
| `Delivery.lean` | one coordinate delivers `a_e·v + O_e` for every encoding |
| `RealTable.lean` | the 84-row table satisfies the delivery conditions (by `decide +kernel`) |
| `FlatLayout.lean` | the evaluator reads exactly the published cells, and the flat layout round-trips |
| `EntryDelivery.lean` | both coordinates on the entry's published value |
| `DigestUnlock.lean` | the hash digest unlocks the digit of an exceptional input of either kind (`digestUnlock_exceptional` at `Q = K`, `digestUnlock_triple` at `Q = 2K`) |
| `EntryDecode.lean` | the decode chain of the rows, for any gadget with the unlock property at both exceptional inputs (`zeroRow_exceptional`, `signZero_triple`) |
| `EntryCorrect.lean` | the assembly: `perfectCorrectness` for every coins, oracle and input |

The rows' decode is `Proof/Correctness/JacobianMixed.lean`: the sign root (`signRoot`), the tangent's other
zero (`tangentZero_double`), the decode of each row (`decodeEvaluateOutputKeyRow`), and the digits of the two
exceptional cases (`exceptionDigitCorrect`, `tripleDigitCorrect`).

## 3. Adaptive privacy (`Proof/Privacy/CRT/`)

`Statements.lean` states the chain `G0 → G0T → G0U → G1U → HW → H → I → M` as
`crt_oracleAdaptivePrivacy_of`; `Named.lean` names its rows over a generic entry; `Hybrids.lean` defines the
games; `EntryInstance.lean` reads the entry as `crtEntry`; `Glue/Instance.lean` discharges the rows at
`crtEntry` up to six rows it takes as hypotheses (`crtEntry_privacy_of_table`); `Final.lean` proves those six
from their leaves (`Assembly.privacy_of_leaves`, `Assembly.crtPrivacy`) and gives the field
`Final.crtEntry_adaptivePrivacy`.

| row | statement | where |
|---|---|---|
| H1 | `G0` is the challenge's lazy real game | `Laws/Table.lean`, `Paths/TableFacts.lean`, `Glue/Instance.lean` |
| H2 | `G0 → G0T`, the table-planted game, `1,759,967/p` | `Laws/Table.lean` |
| H3 | `G0T → G0U`, the pad and mask swap | `Swap/` (`Hop`, `Layout`, `Reading`), `EntryInstance.lean` (`crtEntry_swap`) |
| H5 | `G0U → G1U`, the reach: the honest evaluator reaches every designed-visible entry (`crtEntry_designedReached`) | `Designed.lean`, `Hidden/Reached.lean`, `Hidden/Align*.lean`, `Glue/Containment.lean` |
| H6 | the stage-one guess: a stage-1 query touches a hidden garbler entry with probability at most the per-query charge (`crtEntry_stageOneGuess_of`: the never-hot casts, the bridge key, the reachability of the conversion and body tags) | `Hidden/StageOne*.lean`, `Hidden/Reach.lean` |
| H7 | the stage-two guess, split by the family of the touched tag (`crtEntry_stageTwoGuess_of`), with the curve-window term | `Hidden/StageTwo*.lean`, `Hidden/Case*.lean`, `Flags/CurveWindow.lean` |
| H5 to H7 | the hidden deletion from the guesses (`crt_hidden_of_guess`) | `Hidden/Reduction.lean`, `Hidden/GuessCore.lean` |
| H8 | `G1U → HW`, the public-first hop: the core (solve inversion of the conversion, the wrap-hint coupling, the body, masks and rows, `crtLiftCore_of_factors`), the coincidence guess (`crtCoincidenceGuess_of`), the flag mass (`crtFlagMass_crt`, from the stage-1 touch guess `Flags.crtTouchGuess`), the third swap | `PublicFirst/`, `Core/`, `Laws/`, `Paths/`, `Flags/` |
| H9 | `HW → H`, the opening, with two scales per digit, `455/(r − 1)` | `Glue/Instance.lean` (`crt_opening_of_rows`, `crtEntry_opening`), with `Proof/Privacy/Phase3/OpeningBound.lean` |
| H10 | `H → I`, the refill | `Refill/` (`crt_refill_of_layout`) |
| H11 | `I → M`, the machine law (`crtEntry_machineHop_of`) | `Glue/MachineCrt.lean`, with `Proof/Simulator/CRT/` |
| budget | the error terms and `chainError_budget` | `Glue/Budget.lean`, `Glue/BudgetData.lean`, `Glue/BudgetFacts.lean` |

The sign row and the second exceptional case enter the chain in these modules:

| module | statement |
|---|---|
| `Core/BodyMaskRowParts.lean` | `BMR.rowEquiv`: a digit's 7 row offsets against its 3 published constants and its 4 non-collector values; the inverse divides by `3 − y²` (`signDet_ne_zero`, from `three_not_square` in `Proof/Privacy/Phase3/OnCurveNonzero.lean`) |
| `Core/BodyMaskRowJoint.lean`, `Core/BodyMaskRowOff.lean` | the rows' bijection with the pads, masks and coins, on the curve (`bmrEquiv`) and off it (`bmrEquivOff`, whose residual holds the offsets of the four encodings that no constant absorbs) |
| `Core/BmrEntry.lean` | the doubling event of either kind shows in the true rows; the sign row vanishes at `2K` (`sign_double`) |
| `Flags/RowsDoubling.lean` | the flag of a target row with `Z = 0` or `S = 0` for the normalized rows kernel: three targets per digit, `364/#Point ≤ 364/(r − 1)` (`crtRowsDoubling_le`) |
| `Flags/NormFlag.lean` | the row normalization's flag (a hidden source cell is zero): `182/p` against every weight on the published value (`normFlag_le`) |
| `Core/BmrNorm.lean` | the normalized public-first core: the field-scale bijection, the sign split, `nCore_weighted` / `nCoreOff_weighted` |
| `NormRows.lean` | the rows kernel of the normalized rows (`normRealRows`) and its opening bound `455/#Point` (`normRows_etvDist_le`) |
| `Core/DigestSplit.lean` | off the doubling event the one-byte entries are uniform, with the finals at the two sites `2o + k` of each digit |
| `Core/FinalCoincide.lean`, `Flags/CoincidenceSplit.lean` | a hidden final that the evaluator's path reaches: `182/2^128` over the 182 final sites (`crtEntry_finalCoincide`); with the two `Δ = 0` events, `184/2^128 ≤ 185/2^128` (`crtCoincidenceGuess_of`) |
| `Proof/Privacy/Phase3/Opening.lean`, `OpeningBound.lean` | the lift `(λ²x, t²y, λ)` (`lift`); the real rows are lifts at uniform `(λ, t)` off `Q = K` and `Q = 2K` (`lifts_law`), whose mass is at most `273/#Point` (`bn254_doubling_real_le`); the kernel bound `455/#Point` (`rows_etvDist_le`) |

## 4. The simulator machine (`Construction/Simulator/CRT/`, `Proof/Simulator/CRT/`)

The machine's code is under `Construction/Simulator/CRT/`: the layout, stage 1 (`Stage1.lean`), the replay
blocks (`Replay*.lean`), the arithmetic (`Arith.lean`, `Garner.lean`), the solve (`Solve.lean`: the sign
row's collector `rowY_cubic`, read with `x²`, has its target scaled by `(x·x)⁻¹`), the preimages, the
programs, the top-level design with its cost bound `size + 1 + firstFuel + secondFuel ≤ 2^60`
(`Design.lean`) and the valid arm (`Simulator.lean`). The closed simulator `CrtTop.crtSimulator` is defined
in `Proof/Simulator/CRT/Machine.lean` with its cost bound `crt_within`. Its law is proved under
`Proof/Simulator/CRT/`: stage 1's law (`Stage1Law.lean`, `Stage1LawFinal.lean`) and what stage 1 leaves in
memory (`Stage1Retained.lean`), the replay's agreement with the evaluator block by block (`Replay*.lean`),
the word arithmetic (`Barrett.lean`, `Limbs.lean`, `FracDigits.lean`), the solve (`Solve.lean`,
`OutCells.lean`), the preimages and the programs. The opening's lift pairs `(λ, t)` are drawn in
`Construction/Simulator/Opening.lean`, with their law in `Proof/Simulator/Law.lean` (`pairLaw`, `liftLaw`)
and `Proof/Simulator/OpeningLift.lean`. The files of xinshu's switch-system machine that the CRT
machine does not use (27 modules under `Construction/Simulator/` and `Proof/Simulator/`) are removed, and
`Construction/Simulator.lean` is only the root of the CRT machine.

## 5. Parts of xinshu's proof

`Proof/Privacy/Phase3/` supplies the lazy-oracle glue (`Glue/OracleLaw.lean`, `Glue/LazyIdeal.lean`), the
hybrid shapes and the until-bad lemmas, the union bounds of the hidden hop, and the opening
(`Opening.lean`, `OpeningBound.lean`), which this entry changes to the sign row's two-scale lift and its
collector `rowY_cubic`; `Proof/Simulator/` supplies the semantics of the machine's assembly language, its
compiler-correctness theorem, and the sampler and preimage laws, with the lift sampler over pairs
`(λ, t)`. The rows' correctness is `Proof/Correctness/JacobianMixed.lean` (§2), with the sign row's decode.
