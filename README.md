> **P1 research branch — byte-neutral proof refinement.** This branch tests the tighter hidden/touch
> charge `1/2^104 + 1/(p−1)` on the submitted combined source `32f1fb34884ca33a84ac9dd4db687ca30187aeed`.
> Labels remain 104 bits; construction, encoding and all three metrics are unchanged. The full build
> and both audits passed locally. The remainder of this README describes the submitted combined construction.
> See [P1 evidence](evidence/privacy-charge-p1/verification.md). No P1 publication or submission is planned.

# CRT-residue ArgoMAC with selected width-9 extraction and 84 moduli

This entry implements garbled BN254 scalar multiplication for Kriterion's `scalar-multiplication`
challenge. The challenge, Lean toolchain and dependency lock remain pinned to
`aaf278948a4127f99ee6752c7cec4b9f9bd43615`, Lean `v4.33.1` and the inherited Mathlib revision.

Starting from dnctse's **130,122-byte** entry, Astra's selected extraction schedule and Opus's removal
of modulus 17 combine to save **1,846 bytes**. The first extraction has width 9 on 26 selected odd
moduli, and width 8 on the other 57. The remaining modulus 256 reuses the first chunk.

**All combined local checks passed on 2026-09-28: full build, metric/encoding audit, and whole-tree
axiom audit. No hosted result is claimed for this combined candidate.**

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **128,276** | ranked, lower is better |
| `garbleQueries` | **1,061,622** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **1,054,788** `≤ 1,055,879` | acceptance gate; **1,091** headroom |

## 1. Provenance and construction changes

The base is dnctse's `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05`, itself built on Lazar's
`f79c96a`, psivesely's CRT-residue delivery `de8f397`, and xinshu's Plan B framework `bf53ea4`.
The 91 base-`(2−ω)` digits, X/Z and sign rows, curve check, exception digest and CRT-residue construction
are inherited. Upstream history and credits are retained.

| step | change | bytes |
|---|---|---:|
| — | Lazar's entry `f79c96a` | 173,472 |
| 1 | dnctse: 104-bit internal conversion labels and initial width-8 selection | 148,712 |
| 2 | dnctse: one-byte exception entries | 147,711 |
| 3 | dnctse: first extraction width 8 on every odd modulus | 146,827 |
| 4 | dnctse: parity casts publishing halved pins | 141,627 |
| 5 | dnctse: chunk joins absorbed into Lamport labels | 135,855 |
| 6 | dnctse: normalized Z/sign rows represented by flags | 130,122 |
| 7 | Astra A1: selected first extraction width 9 on 25 moduli | 128,822 |
| 8 | Opus H1 plus integration: remove modulus 17 and widen modulus 397 | **128,276** |

The independently proved checkpoints are:

- **A1** `719b09effea8b5ef544b8243dd9cd840636f963c`: 128,822 bytes / 1,062,022 garbling / 1,055,144 evaluation.
- **H1** source `42a1b4bd84be1cfa9c3e2418752beed4072dc9b9`, with verified documentation/evidence at
  `a020614bc1ba5271c0e4d3522365a8b1fbbad447`: 129,628 bytes / 985,094 / 978,204.

The combined schedule widens `59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397`. Each widening removes one join and one
half-pin label per coordinate, saving 52 bytes. Dropping modulus 17 removes 494 bytes and frees query
budget for the 26th widening. The word widths, chunk width, 104-bit internal labels, 128-bit external
Lamport labels, 120-bit pad slack, 642 records and all row/exception codecs are retained.

`Scratch/check_combined.py` reproduces baseline, A1 and H1 before computing this combination. It
selects the cheapest 26 widenings by evaluation cost, replays all 83 remaining reach certificates,
and independently computes the privacy constants. A 27th widening would cost at least 1,057,734
evaluation queries and violate the gate. This is a result for the explored width-8/9 family, not a
global lower bound on ciphertext size.

## 2. Privacy and proof changes

Astra's schedule proofs establish nonempty extraction stages, the complete row conditions, exact
budgets and conversion lengths. `ConvReach.stageZero_bound` places every widened stage-zero target
inside the existing reachability certificate. The second stage shrinks, and growth still uses at most
nine bits. H1 removes only modulus 17's certificate; every remaining certificate is unchanged.

Opus's H1 uses a tighter consequence of the **unchanged** challenge work allowance:
`steps + 1 = size + 2 + firstFuel + secondFuel ≥ firstFuel + secondFuel + 2`.
The smaller CRT product has 619 bits. The two smudge terms together, plus all other constant errors,
cost about **1.27186354** units of `2^-100`. The Lean proof bounds each smudge term by `7/10`, the other
constant terms by `1/1000` shares, and closes the constant against two units. The per-query bounds are
unchanged. `Glue/Shapes.lean` connects this to the original `steps + 1` target for every adversary.

The product still satisfies the universal wrap bound, and every record fits the existing 78-byte
public type. The simulator draws 84 residue digits per record and proves the complete finite-machine
implementation. Its current counts are 1,415 joins (including 222 unused chunk joins) and 198 pins
per coordinate, and 44,579 serialized pieces. The full construction, perfect correctness and adaptive
privacy remain fields of `Submission.solution` with proof terms.

## 3. Complete public bytes and queries

| field | contents | bytes |
|---|---|---:|
| `curve` | 3 constants × 32 B | 96 |
| `rows` | 91 digits × (32 B constant + 1 B flags) | 3,003 |
| `exception` | 91 digits × 1 B | 91 |
| `crtX`, `crtY` | 2 × 2,885 labels × 13 B (1,692 half-pin labels + 1,193 modulus joins per coordinate) | 75,010 |
| `recX`, `recY` | 642 records × 78 B | 50,076 |
| **total** | | **128,276** |

| part | garbling | evaluation |
|---|---:|---:|
| coordinate `x`: chunks 55,936 / 55,522; extraction/growth/folds 281,535 / 279,641; body 217,831 / 216,864 | 555,302 | 552,027 |
| coordinate `y`: same chunks/extraction; body 166,558 / 165,815 | 504,029 | 500,978 |
| mask key, masks, exception digest | 2,291 | 1,783 |
| **total** | **1,061,622** | **1,054,788** |

The budgets are exact sums over the 84-modulus table, certified by `decide +kernel` in
`Construction/CRT/BudgetFacts.lean`. `Entry.Wire.encoding_length` states the fixed length for every
public value, not only honest garbler outputs.

## 4. Build and evidence

```sh
lake exe cache get
lake build
lake build Benchmark
python3 -B Scratch/check_combined.py
lake env lean Scratch/CombinedAudit.lean
lake env lean Scratch/ProofAudit.lean
python3 -B Scratch/source_manifest.py check
```

The combined full build passed (exit 0, 3,844 jobs). The metric/encoding audit passed (exit 0), including
zero and maximal public values. The whole-tree axiom audit passed (exit 0): **23,742 declarations**,
using only `propext`, `Classical.choice`, `Quot.sound`.
[Combined evidence](evidence/combined-width9-h1/verification.md) records exact commands, results,
source hashes, source provenance and the independent arithmetic model. The source manifest covers
all Lean source, pinned configuration and current audit/model files; it is checked again after commit.

Historical evidence is preserved: [A1](evidence/verification.md),
[H1](evidence/h1-verification.md), and unchanged baseline logs in `evidence/baseline-e37c4db/`.
Baseline reproduced 130,122 / 988,438 / 981,506 and 23,735 audited declarations. A1 audited 23,747;
H1 audited 23,730. All three axiom unions are exactly `propext`, `Classical.choice`, `Quot.sound`.
The baseline, A1 and H1 audit files retain their original expectations and must be run at their
respective source commits. Use `CombinedAudit.lean` for this tree.

`Scratch/` is outside the Lean library and is ignored by the hosted verifier. Local verification is
separate from hosted acceptance and leaderboard position.

## 5. Proof map

| `Solution` obligation | where |
|---|---|
| programs, budgets, program equalities | `Construction/CRT/Entry.lean`, `Bounds.lean`, `BudgetFacts.lean`; `Submission.lean` |
| every public encoding has the declared size | `Construction/CRT/Public.lean`: `Entry.Wire.encoding_length` |
| Lamport compatibility | `Proof/LamportCompatibility/Labels.lean` |
| intended function | `rfl` in `Submission.lean` |
| perfect correctness | `Proof/Correctness/CRT/EntryCorrect.lean` |
| adaptive privacy | `Proof/Privacy/CRT/Final.lean`, with the finite simulator under `Proof/Simulator/CRT/` |

`Proof/README.md` maps the full proof tree. `Intuition.md` describes this delta and preserves the
inherited design explanation, explicitly labeled as the original baseline.

## 6. Credits

* **dnctse** (`dnctse/kriterion-bn254`, `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05`): the starting
  130,122-byte entry, its six optimizations, construction, correctness/privacy proofs, simulator and audits.
* **Lazar** (`Lazar955/bn254-planb`, `f79c96a`; `Lazar955/argomac-lean`): the sign row, the coefficient
  cut, the second exceptional case, and the entry dnctse built on.
* **psivesely** (`psivesely/kriterion-bn254-crt`, `de8f397`): the CRT-residue delivery layer, the curve-value
  masks, the hash-digest exception gadget, the hash-only oracle, and the proof and simulator machine of the
  CRT entry.
* **xinshu** (`xinshudong/bn254-entry`, `bf53ea4`): the Plan B framework — the chain of games, the
  public-first hop, the opening, the simulator machine and its assembly language, the curve check, the
  exception gadget and the decoder.
* **liucheng**: the 91-digit decomposition. **Runchao Han** (`Kriterion-cc/argomac-lean`): the challenge's
  ArgoMAC baseline.
* **Nakul Khambhati, Anwesh Bhattacharya and David Heath**, *Duty-Free Bits* (ePrint 2026/476);
  **Khambhati, Feickert, Lewe and Tiwari** (ePrint 2026/2100); **David Heath** (ePrint 2024/139);
  **Liam Eagen and Ying Tong Lai**, *Argo MAC* (ePrint 2026/049); **Garg, Kolonelos, Sergeevitch, Sridhar
  and Tse**, *BABE* (ePrint 2026/065).

The first six optimizations and their proofs are inherited. Astra developed the selected width-9 schedule
and its Lean integration under Souhail's direction. Claude Opus 5.5 developed H1's modulus removal,
generated budget data and two-unit privacy closure, and independently reviewed A1. Astra reviewed the
verified H1 source and completed this combination; the coordinator supplied independent arithmetic checks.

AI involvement is explicit: OpenAI GPT-6 Astra and Anthropic Claude Opus 5.5 assisted under Souhail's
direction. The original entry disclosed Claude and GPT assistance as well. The pinned verifier checks
the proof terms, permitted axioms and metrics independently of those attributions.
