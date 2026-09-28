# Local verification report — H1 (two-unit budget, modulus 17 dropped)

Scope: **local** Lean verification of this repository's proofs against the pinned challenge library. It is not a
hosted Kriterion result.

## Source

* Base: dnctse `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05` (130,122 B / 988,438 / 981,506).
* Proof source verified: `42a1b4bd84be1cfa9c3e2418752beed4072dc9b9`. The commit that adds this report changes
  documentation, `evidence/` logs and `Scratch/opus_run.py` only (no `.lean` file), so the Lean results below
  apply to it unchanged.
* Pinned configuration: `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` byte-identical to `e37c4db`
  (`evidence/h1-pins-unchanged.log`, `git diff --exit-code`, exit 0). Challenge
  `aaf278948a4127f99ee6752c7cec4b9f9bd43615`, Lean 4.33.1 (`819816b`), Mathlib `0df444a`. The dependency packages
  are clones of the ones used for the baseline reproduction (`../logs/opus-dependency-copy.json`, 14 revisions
  matching the lockfile); this project's own `.lake/build` was built from scratch.
* `Scratch/Audit.lean` and `Scratch/ProofAudit.lean` are unchanged from `e37c4db`.

## Results (raw logs and exit statuses in `evidence/`)

| check | command | result |
|---|---|---|
| full build | `lake build` (run by the coordinator in a persistent session) | exit 0, **3,844 jobs**, no `sorry`, no error; 428.3 s (`h1-build-2.*`) |
| audit dependency | `lake build Benchmark` | exit 0 (`h1-benchmark-build.*`) |
| candidate audit | `lake env lean Scratch/OpusH1Audit.lean` | exit 0; all `#guard`s pass (`h1-audit.*`) |
| whole-tree axioms | `lake env lean Scratch/ProofAudit.lean` | exit 0; **23,730** declarations, union `[Quot.sound, Classical.choice, propext]` (`h1-proof-audit.*`) |
| budget generator | `python3 Scratch/opus_gen_budget.py check` | exit 0; byte-identical to `e37c4db`'s `BudgetData.lean` (`h1-generator-check.*`) |
| static re-derivation | `python3 Scratch/opus_check_h1.py` | exit 0 (`h1-static-check.*`) |
| core-only kernel check | `lean Proof/Privacy/CRT/Glue/BudgetData.lean` | no errors (before the full build) |

`h1-build-1.log` is an incomplete earlier build attempt that was killed when a session ended; it is kept for
completeness and is not evidence of anything.

## Metrics: model versus Lean

| metric | independent model (`Scratch/opus_budget_model.py`) | Lean (`Kriterion.Benchmark` via `OpusH1Audit.lean`) |
|---|---:|---:|
| `ciphertextBytes` | 129,628 | **129,628** |
| `garbleQueries` | 985,094 | **985,094** |
| `evaluateQueries` | 978,204 | **978,204** |

The model reproduces the pinned 130,122 / 988,438 / 981,506 before modelling the change. The audit also checks:
the encoded length of an all-zero and an all-maximal `Public` value is 129,628 bytes and both decode;
`bn254Moduli` has 84 entries and no 17, equals `BudgetData.moduli`, and its product equals `BudgetData.M`;
`2B ≤ M + 1`; `2M ≤ 256^78`; `log2 M = 618`; `convBlocks = convCount = 2937`; both budgets ≥ 500 below their gates;
the statement of `chainError_budget` (`… ≤ first + second + 2`); and that `Submission.solution`,
`chainError_budget`, `chain_oracleAdaptivePrivacy`, `smudgeError_le`, `BudgetData.chainConstant_le_two`,
`encoding_length`, both budget equalities, `bn254Table_record_fits` and `bn254_correctTable` use only
`propext`, `Classical.choice`, `Quot.sound`.

## Declaration count

23,730 versus the baseline's 23,735. My source-level accounting is −3: removed `padQ_17`, `padTerm_17_367`,
`padTerm_17_275`, `chainConstant_le_unit`, `chainConstant_room`; added `chainConstant_le_two`, `frac_share_le`.
I attribute the other −2 to kernel-decided auxiliary lemmas of the removed/added `decide +kernel` theorems; this
attribution is an inference and was not checked name by name.

## What the change relies on

The challenge's `OracleAdaptivePrivacy` requires `advantage · 2^100 ≤ machine.steps + 1` and defines
`steps = size + 1 + firstFuel + secondFuel`, so `steps + 1 ≥ firstFuel + secondFuel + 2` for every adversary
machine. It does not assume `steps ≥ 2`. The constant error of the chain is 1.2719 units exactly (Python, both
smudge copies) and is closed in Lean by shares summing to 1.408 ≤ 2.
