# Combined A1 + H1: local verification

All local checks passed on 2026-09-28. This combination has not been submitted to the hosted verifier by the implementation agent. Baseline, A1 and H1 remain preserved in Git and in their individual evidence reports.

## Provenance and review

- Base: dnctse `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05`.
- A1: `719b09effea8b5ef544b8243dd9cd840636f963c`, selected width-9 extraction by OpenAI GPT-6 Astra under Souhail's direction. Full build and audits passed before integration. Independently reviewed by Claude Opus 5.5; no blockers. Coordinator also reviewed the semantic source diff.
- H1 proof source: `42a1b4bd84be1cfa9c3e2418752beed4072dc9b9`, modulus-17 removal and valid two-unit privacy closure by Claude Opus 5.5 under Souhail's direction.
- H1 verified checkpoint: **`a020614bc1ba5271c0e4d3522365a8b1fbbad447`**, the same proof source plus documentation and full passing evidence. Astra's independent review applies to this exact checkpoint: its Lean source is byte-identical to the reviewed `42a1b4b` source.
- Integration: Astra, on `codex/integrate-h1`, started from A1 and applied both verified H1 commits with no-commit cherry-picks. Numeric conflicts were resolved using an independent combined model; modulus 397 became the 26th width-9 row. No integration commit was made before all checks passed.

All inherited authors and research are credited in the root README. This report claims no global optimality and no hosted acceptance.

## Reproduced results

| Source | Bytes | Garbling | Evaluation | Audited declarations |
|---|---:|---:|---:|---:|
| Baseline | 130,122 | 988,438 | 981,506 | 23,735 |
| A1 | 128,822 | 1,062,022 | 1,055,144 | 23,747 |
| H1 | 129,628 | 985,094 | 978,204 | 23,730 |
| **Combined** | **128,276** | **1,061,622** | **1,054,788** | **23,742** |

The combined saving is **1,846 bytes** from baseline and **546 bytes** from A1. Evaluation has **1,091 queries** of headroom; garbling has **698,345**. The full combined build succeeded on its first attempt, exit 0, 3,844 jobs. Both combined audits exited 0. The axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.

The metric audit evaluates all three challenge `Benchmark` accessors, recomputes both budgets directly, checks 84 moduli and 26 selected rows, and checks the 619-bit product, wrap bound, full record width, pin/join/piece counts and named proof axioms. Both zero and maximal public values encode to **128,276 bytes** and decode successfully. The compiled solution separately proves the universal complete encoding length, every-input correctness and finite-machine adaptive privacy; sample encodings do not replace those theorems.

## Commands and source binding

From the repository root, with the exact pinned dependencies already acquired:

```sh
python3 -B Scratch/check_combined.py
python3 -B Scratch/source_manifest.py write
env LEAN_NUM_THREADS=6 lake build
env LEAN_NUM_THREADS=3 lake env lean Scratch/CombinedAudit.lean
env LEAN_NUM_THREADS=3 lake env lean Scratch/ProofAudit.lean
python3 -B Scratch/source_manifest.py check
```

The manifest was captured while the combined build was running, before both audits. No Lean source changed during the build or audits. The `write` command should be used to record a new experiment, not to overwrite the evidence before checking a reproduced checkout. On this committed source, run `check` directly.

`source-manifest.json` records SHA-256 for **446 Lean source, configuration and audit/model files**, with aggregate digest:

`b302e8d44cbfdaf85544a5c2ae1ae886c3f9ba6560d53a77ab0c555a8235729b`

The manifest is rechecked after the integration commit to bind the source to that immutable SHA. Documentation, evidence logs and Git metadata are outside the source digest. `checks.json` records observed exit statuses, metrics and provenance. Raw logs are `build-first.log`, `audit.log`, `proof-audit.log`, `cost-model.log` and `source-manifest.log` in this directory.

All 14 dependencies match their exact lockfile revisions and have clean source trees (`dependencies.json`). `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Scratch/Audit.lean` and `Scratch/ProofAudit.lean` are unchanged from baseline. The pinned challenge is `aaf278948a4127f99ee6752c7cec4b9f9bd43615`; Lean is `v4.33.1`; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. No challenge or security definition was changed.

## Independent arithmetic and proof scope

`Scratch/check_combined.py` first reproduces baseline and both individual candidates. Equal per-row savings make sorting by evaluation cost optimal for the restricted width-8/9 family; the cheapest 27 widenings would cost **1,057,734** evaluation queries and fail the gate. The selected 26 yield 2,885 conversion labels per coordinate: 1,692 half-pin labels and 1,193 modulus joins. There are 198 pins and 1,415 joins including unused chunk joins per coordinate, and 44,579 serialized pieces.

All 83 remaining reach certificates are the original list with only modulus 17's entry removed; the model replays them with minimum slack 112. It also rechecks all stage targets. The generated H1 budget data equals the reviewed generator's output, and that generator reproduces baseline data byte-for-byte in legacy mode. Independent exact-rational recomputation counts both smudge terms and every other constant error, giving about **1.2718635395647524** units of `2^-100`, within the unchanged challenge's two-unit allowance.

The proofs cover selected-row wellformedness/nonempty stages; exact source-program budgets; byte codecs and record bounds; all-input CRT delivery; hidden-tag reachability; the tightened valid privacy closure; pad layouts and finite simulator sampling, storage, serialization, replay and cost bounds. The external 508 selected 128-bit Lamport labels, 104-bit internal label width, pad slack, record count and universal target remain fixed.
