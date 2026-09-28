> **P1a research candidate — complete public bit packing.** Based on the proved P1 checkpoint
> `dc6aa07014645d3bc1a2846d4521c17b8c3d93af`, this branch packs the full public value into one bit stream.
> Full build and both audits passed locally. The actual complete size is **127,875 bytes** at unchanged
> 104-bit labels and unchanged query budgets. See [P1a evidence](evidence/packed-public/verification.md).
> The earlier `32f1fb34884ca33a84ac9dd4db687ca30187aeed` entry was hosted verified at 128,276 bytes;
> this research candidate has not been published or submitted.

# CRT-residue ArgoMAC with complete public bit packing

This entry implements garbled BN254 scalar multiplication for Kriterion's `scalar-multiplication`
challenge. The challenge, Lean toolchain and dependency lock remain pinned to
`aaf278948a4127f99ee6752c7cec4b9f9bd43615`, Lean `v4.33.1` and the inherited Mathlib revision.

Starting from dnctse's **130,122-byte** entry, Astra's selected extraction schedule and Opus's removal
of modulus 17 save 1,846 bytes. P1a's complete bit packing removes another 401 bytes, for a total
saving of **2,247 bytes**. The first extraction has width 9 on 26 selected odd
moduli, and width 8 on the other 57. The remaining modulus 256 reuses the first chunk.

**P1a local verification passed on 2026-09-28:** full build, metric/encoding checks, and an audit of **23,800 declarations** with only the three permitted axioms. Earlier successful builds and hosted results remain historical evidence for their exact source commits.

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **127,875** | ranked, lower is better |
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
| 8 | Opus H1 plus integration: remove modulus 17 and widen modulus 397 | 128,276 |
| 9 | P1: hidden/touch charge numerator 4→1, unchanged 104-bit labels | 128,276 |
| 10 | Astra P1a: whole-public bit packing, field254/flags3/record620 | **127,875** |

The independently proved checkpoints are:

- **A1** `719b09effea8b5ef544b8243dd9cd840636f963c`: 128,822 bytes / 1,062,022 garbling / 1,055,144 evaluation.
- **H1** source `42a1b4bd84be1cfa9c3e2418752beed4072dc9b9`, with verified documentation/evidence at
  `a020614bc1ba5271c0e4d3522365a8b1fbbad447`: 129,628 bytes / 985,094 / 978,204.

The combined schedule widens `59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397`. Each widening removes one join and one
half-pin label per coordinate, saving 52 bytes. Dropping modulus 17 removes 494 bytes and frees query
budget for the 26th widening. The word widths, chunk width, 104-bit internal labels, 128-bit external
Lamport labels, 120-bit pad slack and 642 records are retained. P1a replaces the full public byte codec.

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

P1 refines the hidden/touch charge to `1/2^104 + 1/(p−1)` with complete generic case proofs;
it does not change the target security definition or either query budget.

The product still satisfies the universal wrap bound. P1a proves every honest record is below
`2 M ≤ 2^620` and changes the public record type to `Fin (2^620)`. The codec round-trips every
inhabitant of that type, independently of the honest-record bound. The simulator draws 84 residue digits per record and proves the complete finite-machine
implementation. Its current counts are 1,415 joins (including 222 unused chunk joins) and 198 pins
per coordinate, and 44,579 serialized pieces. The full construction, perfect correctness and adaptive
privacy remain fields of `Submission.solution` with proof terms.

## 3. Complete public bytes and queries

| field | contents | bits |
|---|---|---:|
| `curve` | 3 constants × 254 | 762 |
| `rows` | 91 digits × (254-bit constant + 3 flags) | 23,387 |
| `exception` | 91 digits × 2 four-bit nibbles | 728 |
| `crtX`, `crtY` | 2 × 2,885 labels × 104 bits | 600,080 |
| `recX`, `recY` | 642 records × 620 bits | 398,040 |
| **public data** | concatenated before byte conversion | **1,022,997** |
| final padding | canonical zeros | 3 |
| **total** | **127,875 bytes** | **1,023,000** |

`BitPacking` composes fixed-width vectors of bits, proves an all-values inverse, and converts to
bytes once. Its generic width supports later label-width changes. `CrtWire.wire_bits` proves exact
bit equality, including final padding. The finite machine emits field254/flags3/record620 and the
same final zero run; its unchanged fuel bounds are proved again. No per-field byte padding remains.

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
lake env lean Scratch/PackedAudit.lean
lake env lean Scratch/ProofAudit.lean
python3 -B Scratch/check_packed.py
python3 -B Scratch/PackedSourceManifest.py check
```

P1a verification and source binding are recorded in
[P1a evidence](evidence/packed-public/verification.md). The full build passed (3,846 jobs); the
metric/encoding audit and the whole-tree audit passed (23,800 declarations). Zero and maximal
public values encode to 127,875 bytes; maximal values decode and re-encode exactly while preserving
an arbitrary byte tail. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The source
manifest covers 453 Lean source, configuration and audit/model files, and is checked after commit.

Historical evidence is preserved: [A1](evidence/verification.md),
[H1](evidence/h1-verification.md), and unchanged baseline logs in `evidence/baseline-e37c4db/`.
Baseline reproduced 130,122 / 988,438 / 981,506 and 23,735 audited declarations. A1 audited 23,747;
H1 audited 23,730. All three axiom unions are exactly `propext`, `Classical.choice`, `Quot.sound`.
The baseline, A1 and H1 audit files retain their original expectations and must be run at their
respective source commits. Combined and P1 reports also remain historical; use `PackedAudit.lean` for this tree.

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
verified H1 source and completed that combination; the coordinator supplied independent arithmetic checks.
P1's charge-refinement idea came from Opus and was implemented and proved by Astra. Astra implemented
P1a's generic bit codec, complete public packing, record bounds and finite simulator serialization.
Opus independently researches the next label-width proof; P1a retains 104-bit labels.

AI involvement is explicit: OpenAI GPT-6 Astra and Anthropic Claude Opus 5.5 assisted under Souhail's
direction. The original entry disclosed Claude and GPT assistance as well. The pinned verifier checks
the proof terms, permitted axioms and metrics independently of those attributions.
