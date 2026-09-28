> **125,450 bytes is hosted verified and first as checked on 28 September 2026 at 15:42 UTC.**
> The [W1 submission](https://kriterion.cc/s/f35df4f4-af76-4e42-8dbc-0e0de872937c)
> passed all five hosted checks; automated review is CLEAR.
> Its exact submitted checkpoint is `684c3d826c4b54c6f5d501dff6489b49ebf6f97b`;
> construction source was committed at `88fcad833697e37993c66b25e40eac04d872cf54`.
> See [hosted results](HOSTED_RESULTS.md) and [W1 local evidence](evidence/w1/verification.md).
> Under 100,000 bytes remains an open research target, not an achieved score.

# CRT-residue ArgoMAC with complete public bit packing

This entry implements garbled BN254 scalar multiplication for Kriterion's `scalar-multiplication`
challenge. The challenge, Lean toolchain and dependency lock remain pinned to
`aaf278948a4127f99ee6752c7cec4b9f9bd43615`, Lean `v4.33.1` and the inherited Mathlib revision.

Starting from dnctse's **130,122-byte** entry, Astra's selected extraction schedule and Opus's removal
of modulus 17 save 1,846 bytes. P1a's complete bit packing removes another 401 bytes, for a total
saving of 2,247 bytes. Opus101 removes a further 2,164 bytes, for a total saving of 4,411 bytes; Opus W1 removes
261 more (**4,672 bytes** in total). The first extraction has width 9 on 26 selected odd
moduli, and width 8 on the other 57. The remaining modulus 256 reuses the first chunk.

**W1 local verification passed on 2026-09-28:** full build, `lake build Benchmark`, actual metrics/encoding
(`Scratch/W1Audit.lean`) and the whole-tree audit of **23,805 declarations**, using only the three permitted axioms.
Earlier successful builds and hosted results remain historical evidence for their exact source commits.

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **125,450** | ranked, lower is better |
| `garbleQueries` | **1,060,976** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **1,054,152** `≤ 1,055,879` | acceptance gate; **1,727** headroom |

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
| 10 | Astra P1a: whole-public bit packing, field254/flags3/record620 | 127,875 |
| 11 | Opus101 + Astra integration: 101-bit internal labels and tighter privacy closure | 125,711 |
| 12 | Opus W1: proved curve-window charge, modulus 41 → 17, 618-bit records | **125,450** |

The independently proved checkpoints are:

- **A1** `719b09effea8b5ef544b8243dd9cd840636f963c`: 128,822 bytes / 1,062,022 garbling / 1,055,144 evaluation.
- **H1** source `42a1b4bd84be1cfa9c3e2418752beed4072dc9b9`, with verified documentation/evidence at
  `a020614bc1ba5271c0e4d3522365a8b1fbbad447`: 129,628 bytes / 985,094 / 978,204.

The combined schedule widens `59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397`. Each widening removes one join and one
half-pin label per coordinate, saving 52 bytes in the earlier byte-aligned 104-bit format. Dropping modulus 17 removes 494 bytes and frees query
budget for the 26th widening. The word widths, chunk width, 128-bit external Lamport labels, 120-bit pad slack and 642 records are retained. P1a replaces the full public byte codec; Opus101 narrows internal labels to 101 bits.

**W1 (Opus).** The hidden hop's window term `hiddenWindowError` was charged at `smudgeError`, about 86 times its
proved size: `Flags/CurveWindow.lean` bounds the event by `15 ((p − 1)^2 + 1)/M` (five curve encodings, `3B/M`
each). Charging that value lowers the exact constant at the 857e88b table from `1.2719` (proved bound `1.408`) to `0.6435`, enough to restore modulus 17 (`ell = 10`) in place
of 41 (`ell = 11`). The product falls from 619 to 617 bits (`log2 M = 616.90`), so records fit 618 bits. The table
has 84 moduli, all 26 width-9 widenings are unchanged, and the only reach-certificate change restores 17's certificate
(from `de8f397`) and removes 41's. The construction is otherwise unchanged. `Scratch/opus_window_model.py` evaluated
single swaps: 43, 47 and 49 → 17 give the same bytes; 37 → 17 gives 125,530.

For the historical pre-W1 combination, `Scratch/check_combined.py` reproduces baseline, A1 and H1. It
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

P1 refines the hidden/touch charge to `1/2^104 + 1/(p−1)` with complete generic case proofs.
Opus101 generalizes that charge to `1/2^labelBits + 1/(p−1)` and sets `labelBits = 101`.
Its scaled charge is at most `1/2 + 2^-152`. For fewer than `2^100` adversary queries,
the accumulated excess fits inside the second constant unit: `1.408 + 2^-51 < 2`. Under W1 the constant is
approximately `1.551578`; its proved upper bound is `1.568` (smudge `≤ 77/50`, window `≤ 1/50`, all others `≤ 8/1000`), still `< 2 − 2^-51`.
The target security definition, 508 selected external 128-bit labels and both query budgets are unchanged.

The product still satisfies the universal wrap bound. P1a proves every honest record is below
`2 M ≤ 2^620` and changes the public record type to `Fin (2^620)`; W1 tightens both to `2^618`. The codec round-trips every
inhabitant of that type, independently of the honest-record bound. The simulator draws 84 residue digits per record and proves the complete finite-machine
implementation. Its current counts are 1,413 joins (including 222 unused chunk joins) and 198 pins
per coordinate, and 43,387 serialized pieces. The full construction, perfect correctness and adaptive
privacy remain fields of `Submission.solution` with proof terms.

## 3. Complete public bytes and queries

| field | contents | bits |
|---|---|---:|
| `curve` | 3 constants × 254 | 762 |
| `rows` | 91 digits × (254-bit constant + 3 flags) | 23,387 |
| `exception` | 91 digits × 2 four-bit nibbles | 728 |
| `crtX`, `crtY` | 2 × 2,881 labels × 101 bits | 581,962 |
| `recX`, `recY` | 642 records × 618 bits | 396,756 |
| **public data** | concatenated before byte conversion | **1,003,595** |
| final padding | canonical zeros | 5 |
| **total** | **125,450 bytes** | **1,003,600** |

`BitPacking` composes fixed-width vectors of bits, proves an all-values inverse, and converts to
bytes once. Its generic width supports the integrated 101-bit labels without per-label or per-vector padding. `CrtWire.wire_bits` proves exact
bit equality, including final padding. The finite machine emits 254-bit fields, 3-bit flags and 618-bit records and the
same final zero run; its unchanged fuel bounds are proved again. No per-field byte padding remains.

| part | garbling | evaluation |
|---|---:|---:|
| coordinate `x`: chunks 55,936 / 55,522 (unchanged); extraction, growth, folds and body over the W1 table | 554,955 | 551,685 |
| coordinate `y`: same chunks and extraction; body at `S = 275` | 503,730 | 500,684 |
| mask key, masks, exception digest | 2,291 | 1,783 |
| **total** | **1,060,976** | **1,054,152** |

The budgets are exact sums over the 84-modulus table, certified by `decide +kernel` in
`Construction/CRT/BudgetFacts.lean`. `Entry.Wire.encoding_length` states the fixed length for every
public value, not only honest garbler outputs.

## 4. Build and evidence

```sh
lake exe cache get
lake build
lake build Benchmark
lake env lean Scratch/W1Audit.lean
lake env lean Scratch/ProofAudit.lean
python3 -B Scratch/opus_check_w1.py
python3 -B Scratch/opus_w1_manifest.py check
```

`Scratch/Packed101Audit.lean` and `Scratch/check_packed101.py` keep their 125,711-byte expectations and must be
run at `857e88b`.

Current verification and source binding are recorded in [W1 evidence](evidence/w1/verification.md).
The audit measures the actual complete ciphertext, checks zero and maximal public values, and checks exact
decode/re-encode with a byte tail. The universal inverse covers every public value, including arbitrary
618-bit records. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. The current manifest
covers 439 production/configuration and selected audit/model files. The coordinator also checked all
459 inherited files against Astra's independently reviewed snapshot; historical Scratch audits outside
the current manifest remain unchanged. The earlier [packed-101 evidence](evidence/packed-101/verification.md)
refers to its own immutable 125,711-byte source.

The exact P1a checkpoint and its [report](evidence/packed-public/verification.md) remain immutable.
The independent Opus101 checkpoint and [report](evidence/width101/verification.md) describe its
126,114-byte labels-only codec. Integration retains the whole-public codec and omits that unused
standalone codec; its historical audit must be run at the Opus checkpoint.
Historical evidence is preserved: [A1](evidence/verification.md),
[H1](evidence/h1-verification.md), and unchanged baseline logs in `evidence/baseline-e37c4db/`.
Baseline reproduced 130,122 / 988,438 / 981,506 and 23,735 audited declarations. A1 audited 23,747;
H1 audited 23,730. All three axiom unions are exactly `propext`, `Classical.choice`, `Quot.sound`.
The baseline, A1 and H1 audit files retain their original expectations and must be run at their
respective source commits. Combined and P1 reports also remain historical; use `W1Audit.lean` for this tree.

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
Opus developed and independently proved the 101-bit label, generic replay and tighter privacy
closure at `2f7b9ca70f7a9c72ac4a24e98ddb97cb606e7ee8`. Astra integrated that exact delta
with P1a, preserved the all-values whole-public codec, and re-proved the finite serialization bridge
with 43,391 pieces and one final padding bit. Opus developed W1 on `claude/structural-research`: charging
the curve window at the size the inherited `CurveWindow` proof (psivesely `de8f397`, Lazar `f79c96a`) already establishes, the 41 → 17 swap, and the
618-bit record width through Astra's packed codec and serializer proofs (whose structure is unchanged).

AI involvement is explicit: OpenAI GPT-6 Astra and Anthropic Claude Opus 5.5 assisted under Souhail's
direction. The original entry disclosed Claude and GPT assistance as well. The pinned verifier checks
the proof terms, permitted axioms and metrics independently of those attributions.

## Research toward fewer than 100,000 bytes

This target remains unresolved. Research is preserved separately from the submitted entry:

- [Astra's isolated algebra and 9-bit chunk feasibility](https://github.com/mssassii/kriterion-bn254/tree/codex/structural-research/evidence): mathematical experiments and migration requirements; the projected new formats are not complete entries.
- [Claude's carry-range and joint cost models](https://github.com/mssassii/kriterion-bn254/tree/claude/structural-research/Scratch): conditional arithmetic models; they do not establish a construction, its query totals or its privacy.

Promising questions concern larger scalar-digit alphabets and cheaper authenticated carry reduction.
Their combined cost budgets can fall below 100,000 bytes under unproved assumptions. Those projections are
not scores, and no global lower bound is claimed. W1 still needs another 25,451-byte reduction to reach 99,999 bytes.
