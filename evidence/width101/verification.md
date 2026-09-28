# Local verification — P1b width-101 conversion labels (Opus)

Local Lean verification only; no hosted result. Base: Astra's `dc6aa07014645d3bc1a2846d4521c17b8c3d93af` (refined
charge at 104 bits, on the submitted combined `32f1fb34884ca33a84ac9dd4db687ca30187aeed`).

## Results (raw logs and exit statuses: `evidence/w101-*.log` / `.status.json`)

| check | command | result |
|---|---|---|
| full build (final source) | `lake build` | exit 0, 3,845 jobs, no `sorry`, no error (`w101-build-final`) |
| audit dependency | `lake build Benchmark` | exit 0 (`w101-benchmark-build`) |
| metric/encoding audit | `lake env lean Scratch/Width101Audit.lean` | exit 0, all guards (`w101-audit-final`) |
| whole-tree axioms | `lake env lean Scratch/ProofAudit.lean` | exit 0, **23,777** declarations, `[Quot.sound, Classical.choice, propext]` (`w101-proof-audit-final`) |
| independent model | `python3 Scratch/opus_check_w101.py` | exit 0 (`w101-model-check`) |
| dependencies | `python3 Scratch/opus_w101_manifest.py deps` | all 14 at locked revisions, clean (`w101-deps`) |
| pins, baseline audits | `git diff --exit-code e37c4db -- lakefile.toml lake-manifest.json lean-toolchain Scratch/Audit.lean Scratch/ProofAudit.lean` | exit 0 (`w101-pins-unchanged`) |
| source manifest | `python3 Scratch/opus_w101_manifest.py write`, then `check <commit>` | 436 files (`source-manifest.json`) |

Metrics (Lean `Benchmark` = independent model): **126,114 bytes / 1,061,622 garbling / 1,054,788 evaluation**.
The audit also checks `labelBits = laneCount = 101`, `packedBytes 2885 = 36,424`, `convPad = 7`, 84 moduli without
17, product = `BudgetData.M`, `2B ≤ M + 1`, `2M ≤ 256^78`, 26 width-9 rows, 1,415 joins, 198 pins, 43,393
serializer pieces; zero and maximal public values encode to 126,114 bytes and decode; a varied 2,885-label vector and
an all-ones vector round-trip exactly through `packedLabels`; and 19 named theorems use only the three axioms.
Earlier passes (`w101-build-1..3`) show the repair history: a `field_simp` closing early, literal `2^104` lane bounds,
a `List.ofFn` normalization, and a wrong piece count (the kernel rejected 44,581; the true count is 43,393 because
pins now have 101 lanes).

## Exact security inequality

`chainError(q₁, q₂)·2^100 ≤ C + (q₁+q₂)·c·2^100 + q₁·c·2^100` with `c = 2^-101 + 1/(p−1)`, `C = 1.271864` (exact
rational, both smudge copies). `crtHiddenCharge_le`: `c·2^100 ≤ 1/2 + 2^-152` (kernel: `2^252 ≤ p − 1`). For
`q₁ + q₂ < 2^100` the proof bounds the excess `(2q₁ + q₂)·2^-152 ≤ 1/1000`, so the total is at most
`q₁ + q₂/2 + 1.408 + 0.001 ≤ q₁ + q₂ + 2 ≤ steps + 1`. Worst vertex margin (exact): 0.728136 unit.

## Limitations

- Local only; not submitted or published.
- The 13-byte single-label codec `Narrow.labelEncoding` is retained but no longer used by the public encoding.
- The conversion vectors are packed separately (7 padding bits each); a joint stream would save 1 more byte.
