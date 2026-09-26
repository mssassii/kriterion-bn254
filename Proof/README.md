# Proof map

This map covers the CRT entry against the challenge library `aaf2789`. The top-level `README.md` explains
the construction and the argument, and `Intuition.md` the ideas. This file says which module proves which
obligation.

`Proof.lean` imports `Proof.Correctness.CRT.EntryCorrect`, `Proof.LamportCompatibility.Labels` and
`Proof.Privacy.CRT.Final`, and `Construction.lean` imports the entry and the simulator machine, so a bare
`lake build` compiles every module named here and every module they import. `Submission.lean` names the
fields. Every field is proved; there is no `sorry` in the tree, and every declaration uses only `propext`,
`Classical.choice` and `Quot.sound` (`Scratch/ProofAudit.lean`).

## 1. The fields of `Kriterion.Solution`

| field | proved by | where |
|---|---|---|
| `garbleProgram`, `garbleQueries`, `garbleProgramCorrect` | `Entry.garbleProgram` at `Entry.garbleBudget` (995,088); `Submission.garbleProgramCorrect` | `Construction/CRT/Entry.lean`, `Bounds.lean`, `BudgetFacts.lean`; `Submission.lean` |
| `evaluateProgram`, `evaluateQueries`, `evaluateProgramCorrect` | `Entry.evaluateProgram` at `Entry.evaluateBudget` (987,209); `Submission.evaluateProgramCorrect` | the same |
| `ciphertextSize` | `Entry.Wire.encoding_length` (182,936) | `Construction/CRT/Public.lean` |
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
| `RealTable.lean` | the 85-row table satisfies the delivery conditions (by `decide +kernel`) |
| `FlatLayout.lean` | the evaluator reads exactly the published cells, and the flat layout round-trips |
| `EntryDelivery.lean` | both coordinates on the entry's published value |
| `DigestUnlock.lean` | the hash digest unlocks the digit of an exceptional input |
| `EntryDecode.lean` | the decode chain of the rows, for any gadget with the unlock property |
| `EntryCorrect.lean` | the assembly: `perfectCorrectness` for every coins, oracle and input |

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
| H2 | `G0 → G0T`, the table-planted game, `995,088/p` | `Laws/Table.lean` |
| H3 | `G0T → G0U`, the pad and mask swap | `Swap/` (`Hop`, `Layout`, `Reading`), `EntryInstance.lean` (`crtEntry_swap`) |
| H5 | `G0U → G1U`, the reach: the honest evaluator reaches every designed-visible entry (`crtEntry_designedReached`) | `Designed.lean`, `Hidden/Reached.lean`, `Hidden/Align*.lean`, `Glue/Containment.lean` |
| H6 | the stage-one guess: a stage-1 query touches a hidden garbler entry with probability at most the per-query charge (`crtEntry_stageOneGuess_of`: the never-hot casts, the bridge key, the reachability of the conversion and body tags) | `Hidden/StageOne*.lean`, `Hidden/Reach.lean` |
| H7 | the stage-two guess, split by the family of the touched tag (`crtEntry_stageTwoGuess_of`), with the curve-window term | `Hidden/StageTwo*.lean`, `Hidden/Case*.lean`, `Flags/CurveWindow.lean` |
| H5 to H7 | the hidden deletion from the guesses (`crt_hidden_of_guess`) | `Hidden/Reduction.lean`, `Hidden/GuessCore.lean` |
| H8 | `G1U → HW`, the public-first hop: the core (solve inversion of the conversion, the wrap-hint coupling, the body, masks and rows, `crtLiftCore_of_factors`), the coincidence guess (`crtCoincidenceGuess_of`), the flag mass (`crtFlagMass_crt`, from the stage-1 touch guess `Flags.crtTouchGuess`), the third swap | `PublicFirst/`, `Core/`, `Laws/`, `Paths/`, `Flags/` |
| H9 | `HW → H`, the opening | `Glue/Instance.lean` (`crt_opening_of_rows`), with `Proof/Privacy/Phase3/OpeningBound.lean` |
| H10 | `H → I`, the refill | `Refill/` (`crt_refill_of_layout`) |
| H11 | `I → M`, the machine law (`crtEntry_machineHop_of`) | `Glue/MachineCrt.lean`, with `Proof/Simulator/CRT/` |
| budget | the error terms and `chainError_budget` | `Glue/Budget.lean`, `Glue/BudgetData.lean`, `Glue/BudgetFacts.lean` |

## 4. The simulator machine (`Construction/Simulator/CRT/`, `Proof/Simulator/CRT/`)

The machine's code is under `Construction/Simulator/CRT/`: the layout, stage 1 (`Stage1.lean`), the replay
blocks (`Replay*.lean`), the arithmetic (`Arith.lean`, `Garner.lean`), the solve, the preimages, the
programs, the top-level design with its cost bound `size + 1 + firstFuel + secondFuel ≤ 2^60`
(`Design.lean`) and the valid arm (`Simulator.lean`). The closed simulator `CrtTop.crtSimulator` is defined
in `Proof/Simulator/CRT/Machine.lean` with its cost bound `crt_within`. Its law is proved under
`Proof/Simulator/CRT/`: stage 1's law (`Stage1Law.lean`, `Stage1LawFinal.lean`) and what stage 1 leaves in
memory (`Stage1Retained.lean`), the replay's agreement with the evaluator block by block (`Replay*.lean`),
the word arithmetic (`Barrett.lean`, `Limbs.lean`, `FracDigits.lean`), the solve, the preimages and the
programs.

## 5. Parts of xinshu's proof used unchanged

`Proof/Privacy/Phase3/` supplies the lazy-oracle glue (`Glue/OracleLaw.lean`, `Glue/LazyIdeal.lean`), the
hybrid shapes and the until-bad lemmas, the union bounds of the hidden hop, and the opening
(`Opening.lean`, `OpeningBound.lean`); `Proof/Simulator/` supplies the semantics of the machine's assembly
language, its compiler-correctness theorem, and the sampler and preimage laws. The rows' correctness is
`Proof/Correctness/JacobianMixed.lean`.
