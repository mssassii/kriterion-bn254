# Local verification: selective width-9 A1

Verified on 2026-09-28. This report accompanies the locally proved candidate source. No hosted verification or submission has been performed for A1.

## Provenance and fixed inputs

- Base: dnctse `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05`.
- Delta: OpenAI GPT-6 Astra under Souhail's direction; independent arithmetic checks by Claude Opus 5.5 and the coordinator. Upstream history and README credits retained.
- Challenge: `aaf278948a4127f99ee6752c7cec4b9f9bd43615`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Toolchain: `leanprover/lean4:v4.33.1`; local Lean reports version 4.33.1, arm64-apple-darwin24.6.0, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are unchanged from the base. All 14 dependency checkouts match their exact locked commits and have clean source trees (`candidate-width9/dependencies.json`). No challenge source or security definition is modified.

## Results

| Check | Baseline | A1 |
|---|---:|---:|
| Ciphertext bytes | 130,122 | **128,822** |
| Garbling queries | 988,438 | **1,062,022** |
| Evaluation queries | 981,506 | **1,055,144** |
| Concrete encoded public length | 130,122 | **128,822** |
| Full-build exit status | 0 | 0 |
| Metric/encoding audit exit status | 0 | 0 |
| Whole-tree axiom audit exit status | 0 | 0 |
| Audited declarations | 23,735 | **23,747** |

A1 saves **1,300 bytes**. Garbling rises by 73,584 queries and evaluation by 73,638; the remaining query headroom is 697,945 and 735 respectively. Both complete axiom unions are exactly `propext`, `Classical.choice`, `Quot.sound`. The metric audit evaluates the challenge's `Benchmark` accessors, independently recomputes query budgets, and checks a concrete encoding and decoder. The universal encoding length, correctness and adaptive privacy claims are proved in the compiled `Submission.solution`; the concrete audit is an additional consistency check.

## Exact commands and logs

All commands run from the repository root. Thread counts affect local scheduling only.

Baseline source was unchanged for all baseline checks:

```sh
lake exe cache get
env LEAN_NUM_THREADS=6 lake build
lake build Benchmark
lake env lean Scratch/Audit.lean
lake env lean Scratch/ProofAudit.lean
```

All successful baseline outputs and acquisition history are in `baseline-e37c4db/`. The baseline build completed 3,845 jobs. A stalled initial cache download was stopped, its failure retained, and acquisition retried with a curl wrapper adding connection/transfer timeouts. The retry fetched all 8,690 artifacts. A shallow Mathlib checkout uses the identical lockfile commit. Neither workaround changes dependencies or source. See `baseline-e37c4db/commands.txt` and the raw acquisition logs.

After implementing A1:

```sh
python3 -B Scratch/check_width9.py
env LEAN_NUM_THREADS=6 lake build
env LEAN_NUM_THREADS=3 lake env lean Scratch/CandidateAudit.lean
env LEAN_NUM_THREADS=3 lake env lean Scratch/ProofAudit.lean
```

The final successful build is `candidate-width9/build-third.log` (3,844 jobs). Successful audits are `candidate-width9/audit.log` and `candidate-width9/proof-audit.log`. The cost-model output is `width9-cost-model.json` and `width9-cost-model.stdout`. Baseline-specific `Scratch/Audit.lean` remains unchanged; candidate expectations are independently derived in a separate file.

Failed intermediate attempts are retained for transparency:

1. `build-first.log`: finite proposition checks through a matched row kind did not synthesize a decider. Replaced with explicit kernel-checked selected-row predicates and a separate proof by cases on the kind.
2. `build-second.log`: the reach proof's subtraction identity lacked the actual row-width sum. Added the existing wellformedness equality from `SliceC.bn254_odd`; the schedule's arithmetic was valid.
3. `audit-first.log`: all printed metrics were correct, but a doc comment before `#guard` was parsed as an incomplete declaration. Changed it to an ordinary comment and reran successfully.

## Scope and proof changes

`selectiveWidth0` widens 25 chosen odd rows from 8 to 9 bits; all other rows remain width 8. Each widening removes one join and one half-pin label per coordinate. The 85 moduli, chunk width, 104-bit internal labels, 128-bit external labels, 642 records, pad slack and privacy error data are identical to baseline.

Updated proofs establish nonempty extraction stages and complete selected-row wellformedness; kernel-evaluate exact budgets and vector counts; prove widened stage-zero targets lie inside existing reach certificates; retain the stage-one and growth reach arguments using explicit row facts; and recompute simulator join/piece counts and finite-machine bounds. No reachability certificate was changed. The independent script rechecks all 84 certificates, with minimum slack 112.

Files with semantic/proof changes: `Construction/CRT/{Params,Entry,Public,BudgetFacts}.lean`, `Proof/Correctness/CRT/RealTable.lean`, `Proof/Privacy/CRT/{Core/Conversion,Hidden/Reach}.lean`, `Proof/Simulator/CRT/{Stage1Stored,Stage1Size}.lean`. Other tracked source edits are comments; `Submission.solution` retains the same field assignments. New research/audit files are `Scratch/check_width9.py` and `Scratch/CandidateAudit.lean`.

This is a local proof result. Hosted acceptance, current leaderboard position and any global optimality claim remain outside this report. The independent Opus modulus-removal experiment is not included in A1.
