# The sign row on psivesely's CRT-residue delivery of ArgoMAC

This is an entry for the Kriterion `scalar-multiplication` challenge: garbled BN254 scalar
multiplication `f_k(u) = k·u`, targeting the challenge library
`Kriterion-cc/kriterion-challenge` at commit `aaf2789` (Lean `v4.33.1`).

The schedule uses width 8 for 67 odd moduli and width 7 for the other 17, using 104-bit internal conversion labels and 128-bit external Lamport labels and digest keys.

It is psivesely's CRT entry (`psivesely/kriterion-bn254-crt`, commit `de8f397`, 182,936 bytes) with Lazar's
sign row (`Lazar955/bn254-planb`) in the `Y` slot of every digit:

* **the rows**: the sign row `S = τ²·S0` replaces Lazar's four-encoding `Y` row, which `de8f397` uses. It
  reads three encodings instead of four, and Lazar's coefficient cut leaves it one published constant
  instead of two, so a digit reads 7 affine encodings and publishes 3 constants instead of 8 and 4 (§1.5);
* **the exception gadget**: the sign row vanishes at a second exceptional input, `Q = 2K`, so the gadget's
  entry has one byte per digit and the hash digest two final sites per digit (§1.6).

psivesely's entry is xinshu's entry (`xinshudong/bn254-entry`, commit `bf53ea4`, 3,363,376 bytes) with the
delivery of the affine encodings replaced:

* **the delivery layer**: the switch systems are replaced by the CRT-residue projectivization of Duty-Free
  Bits (Khambhati, Bhattacharya and Heath), applied to Argo MAC encodings as in ePrint 2026/2100: per coordinate, one conversion of the 254 input bits into
  one-hot labels of the residues modulo 85 small moduli (3,378 published blocks), then one 78-byte record
  per encoding;
* **the gating**: the rows are masked by hash outputs keyed by the curve check's value, in place of the
  second switch system on labels whitened by EncPRF pads;
* **the exception gadget**: xinshu's per-digit gadget (`91·508 = 46,228` permutation queries on each side)
  is keyed by a hash digest of the input's labels: 1,016 label hashes and one final hash per exceptional
  input;
* **the oracle**: every query is to the field hash; the two permutation families are unused.

The curve check, the `X` and `Z` rows, the decoder's doubling and identity cases and the proof architecture
are xinshu's.

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **146,827** `= 96 + 91·96 + 91·1 + 2·43,914 + 642·78` | ranked, lower is better |
| `garbleQueries` | **988,438** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **981,506** `≤ 1,055,879` (74,373 below) | acceptance gate |

The baseline supplied proofs for every field of `Kriterion.Solution`, with no `sorry`, and its
axiom audits reported only `propext`, `Classical.choice` and `Quot.sound`. This branch preserves the
proof structure and introduces no admitted proofs; its updated certificates and audits remain to be
checked (`Scratch/Audit.lean`, `Scratch/ProofAudit.lean`).

`Intuition.md` explains the construction and the proof.

## Credit

* **psivesely** (`psivesely/kriterion-bn254-crt`, `de8f397`): the CRT-residue delivery layer, the
  curve-value masks of the rows, the hash-digest exception gadget, the hash-only oracle, and the whole proof
  and simulator machine of the base entry. This entry keeps all of it; it changes the rows and the gadget
  (§1.5, §1.6) and the parts of the proof and the machine that read them.
* **xinshu** (`xinshudong/bn254-entry`, `bf53ea4`): the entry the CRT entry builds on: the rows' proof
  architecture, the decoder, the curve check and the simulator machine's framework.
* **Nakul Khambhati, Anwesh Bhattacharya and David Heath**, Duty-Free Bits (ePrint 2026/476), and
  **Khambhati, Feickert, Lewe and Tiwari** (ePrint 2026/2100): the CRT-residue projectivization and its
  use for Argo MAC encodings.
* **Lazar** (`Lazar955/argomac-lean`, `Lazar955/bn254-planb`): the four-encoding `Y` row and the
  coefficient cut that the base entry uses, and in this entry the sign row, its coefficient cut, the second
  exceptional case, and their proofs and machine port.
* **The challenge's ArgoMAC baseline** (`Kriterion-cc/argomac-lean`, Runchao Han).

§7 gives the full provenance.

## 1. What changed, and why

§1.1 to §1.4 are psivesely's changes from `bf53ea4`; §1.5 and §1.6 are this entry's changes from
`de8f397`.

### 1.1 The delivery layer

xinshu's switch systems publish, per chunk of input bits, one field element per encoding, so the size is
about `chunks · encodings · 32` bytes. The CRT delivery separates the two factors. Per coordinate: 32
chunks (31 of 8 bits, one of 6) are turned by one-hot trees into leaf labels, cast into arithmetic labels
over `Z_{2^14}` (128 lanes); a free linear map gives, for each odd modulus `m`, a word congruent to `v`
modulo `m` (per-modulus truth tables); a three-stage extraction, a kept one-hot, growth, reindexing and
folds give a one-hot vector over `Z_m` hot at `v mod m`. Per encoding and modulus, every slot's pad vector
and one published residue join give the evaluator `a_e·v + O_e mod m`; the Chinese remainder theorem and a
published wrap hint give `a_e·v + O_e` exactly, hence `a_e·v + (O_e mod p)`. The moduli are the 79 primes
from 17 to 439, the prime powers 49, 81, 121, 125, 169, and 256 (`log2 M = 622.26`), with one closed-form
schedule per odd modulus.

### 1.2 The gating

The five curve encodings pass through the same layer. The evaluator computes the curve check's value `t'`,
queries the mask key `K` at the low 128 bits of `t'` (a labelled query), and reads a mask for each of the
637 row encodings by xinshu's three-block rule; the garbler's row offsets include the masks. Off the curve
`t' ≠ t` and every row value is masked. This removes xinshu's curve-lane switch system and the EncPRF
whitening.

### 1.3 The exception digest

Each of the 508 labels is hashed with its bit in the tag; the key of an exceptional input is the XOR of the
hashes at its bits, and the mask byte of its slot in the entry is the low byte of the hash of the key
(§1.6).

### 1.4 The hash-only oracle

`FixedIndex` and `EncIndex` are `Empty`. Every query is at `label + 2^128·tag` with a tag below `2^40`
that names its site, so distinct sites never share an input.

### 1.5 The sign row

Write `K = (a, b)` for a digit's offset, `Q = (u, v)` for its image of the input and `R = Q + K` for its
MAC point. The `X` and `Z` rows are the Jacobian `X` and `Z` of `R`, with the randomiser `ρ` as Jacobian
weight, and `x_R = X/Z²` fixes `y_R` up to sign. So the `Y` slot carries only the sign: the sign row
`S = τ²·S0` (`Coordinates.signCoefficients`), with
`S0 = 4b³v² + 3ab(27 − b²)u² + (b⁴ + 54b² − 243)v − 36b³`. On the curve and for `u ≠ a`, `S0 = L²·y_R`,
where `L = 2bv + 3a²u + 9 − b²` is the tangent at `−K` scaled by `2b` (`Coordinates.evaluateSign`). When
`L ≠ 0`, `S` has the quadratic character of `y_R`, and the decoder takes
`y_R = S^((p−1)/2)·(x_R³ + 3)^((p+1)/4)`: since `p ≡ 3 (mod 4)`, the second factor is a square root of
`y_R²` and the first is `±1` (`JacobianMixed.signRoot`). `τ` is a new nonzero randomiser per digit,
independent of `ρ`, so that the opening's two scales are independent (§4).

The sign row is `S = s0 + s2·y + s4·x² + s5·y²`, with no `x` and no `xy` term, so it reads three
encodings: `rowY_cubic` (of `x`, read with `x²`), `rowY_y8` (read with `y`) and `rowY_y10` (read with 1).
A digit reads 7 encodings (`rowX_x7`, `rowX_x9`, `rowY_cubic`, `rowZ_x9` of `x`; `rowX_y10`, `rowY_y8`,
`rowY_y10` of `y`), so with the curve check's five there are 642: 367 of `x` and 275 of `y`. The
coefficient cut on the sign row publishes only `s4` minus the offset of `rowY_cubic`, so a digit publishes
3 constants (`RowGamma`: `xC0`, `yC4`, `zC0`). The slope of `rowY_cubic` is `−t`, with
`t = (s0 − b_{y10})/3` (`Biquadratic.signShift`, `b_{y10}` the offset of `rowY_y10`). It contributes
`−t·x³ = t·(3 − y²)` on the curve; the slope `t + s5` of `rowY_y8` absorbs the `y²` part, and `3t` plus
`b_{y10}` is the constant `s0`. So the row is exact on the curve (`Biquadratic.evaluateEncodedY`) and off
by `t·(y² − x³ − 3)` elsewhere, where the evaluator refuses the input before its first query. The privacy
proof inverts the cut digit by digit (`BMR.rowEquiv`): the slopes of `rowY_y8` and `rowY_y10` read each
other's offset, and the inverse divides by `3 − y²`, which is never zero because 3 is not a square
modulo `p` (`signDet_ne_zero`).

### 1.6 The second exceptional case

A row decodes through `x_R = X/Z²` and the sign row except where `Z = 0` or `L = 0`. With `P` the input
point and `φ(P) = Q` its image under the digit, `Garbling.decodeHomogeneous` reads a row `(X, S, Z)` as
follows:

| row | case | decoded point |
|---|---|---|
| `Z = 0`, `X = 0` | `Q = K`, the doubling case | `2·φ(P)`, digit from the gadget's kind 0 |
| `Z = 0`, `X ≠ 0` | `Q = −K` | the identity |
| `Z ≠ 0`, `S = 0` | `Q = 2K`: the tangent at `−K` meets the curve again at `2K` (`JacobianMixed.tangentZero_double`) | `(3/2)·φ(P)`, `3/2` in the scalar field, digit from the gadget's kind 1 |
| otherwise | | `x = X/Z²`, `y = S^((p−1)/2)·(x³ + 3)^((p+1)/4)` |

The gadget's entry has one byte per digit: kind `k` in nibble `k` (`Exception.slotOf`), kind 0 for
the input at `Q = K` (`Exception.exceptionalInput`) and kind 1 for the input at `Q = 2K`
(`Exception.tripleInput`). Each exceptional input of a nonzero digit `o` has its own digest key and its own
final site `s = 2o + k`, so the digest has 182 final sites. The garbler asks the final of each site at its
exceptional input's key; the evaluator asks both sites of every digit at its own key, and at an exceptional
input of either kind the nibble of that kind unmasks (`DigestUnlock.digestUnlock_exceptional`,
`digestUnlock_triple`). The digest asks 1,198 garbling queries (`4·254 + 2·91`, a bound: a zero digit asks
no final) and 690 evaluation queries (`2·254 + 2·91`), 91 more on each side than with one final per digit.

### 1.7 Construction

| file | content |
|---|---|
| `Construction/CRT/Interface.lean`, `Params.lean`, `Query.lean` | the frozen definitions (tags, hash inputs, one-block and long hashes, block-aligned cast lanes, pin codec, fraction reading, pad counts, wrap hint), the modulus table `CrtTable` and its 85-row instance, the query language `FreeQuery CrtSpec` and `liftHash` |
| `Construction/CRT/Lanes.lean`, `Tree.lean`, `Chunk.lean` | arithmetic labels; the one-hot tree step; chunk trees, casts, pins and truth-table words |
| `Construction/CRT/ExtractSpec.lean`, `Extract.lean`, `Fold.lean` | the fused extraction stage (garbler by node recursion, evaluator by rounds); the kept one-hot, reindex and folds |
| `Construction/CRT/Body.lean`, `Coord.lean` | pads, residues and joins; one coordinate: conversion, body, CRT offsets with the wrap hint, records, the evaluator's reconstruction, the flat layout |
| `Construction/CRT/Mask.lean`, `Digest.lean` | the mask key and the 1,092 mask answers; the exception digest with two final sites per digit |
| `Construction/CRT/Entry.lean`, `Public.lean`, `Bounds.lean`, `BudgetFacts.lean` | the scheme, the garbler and evaluator programs at their exact budgets, the public value and its codec, the query bounds, the budgets evaluated by the kernel |
| `Construction/CRT/Layout.lean` | the public value in source form, for the simulator |
| `Construction/Simulator/CRT/` | the simulator machine: layout, stage 1, the replay blocks, Garner, the solve (the sign row's collector `rowY_cubic`, with its target scaled by `(x·x)⁻¹`), the preimages and programs, the design and its cost bound, the valid arm (`Simulator.lean`) |
| `Construction/ArgoMAC/`, `Garbling.lean`, `Scheme.lean`, `QueryMonad.lean` | the rows (the sign row and its cut in `Coordinates.lean` and `Biquadratic.lean`), the curve check, the one-byte gadget entry (`Exception.lean`), the decoder (`Garbling.decodeHomogeneous`) and the coins (with the sign row's `τ`) |

### 1.8 Proof

| directory | content |
|---|---|
| `Proof/Correctness/CRT/` | perfect correctness wire by wire for every hash function: trees, chunks, words, extraction stages, folds, the body, records and the wrap hint, the flat layout, the digest unlock of both exceptional kinds, and the assembly `EntryCorrect.perfectCorrectness`; the rows' decode with the sign row is `Proof/Correctness/JacobianMixed.lean` |
| `Proof/Privacy/CRT/` | the chain `G0 → G0T → G0U → G1U → HW → H → I → M` at the entry: the statements and the named rows (`Named.lean`, `Statements.lean`), the pad and mask swap (`Swap/`), the hidden hop (`Hidden/`), the public-first core (`Core/`, `Laws/`, `Paths/`, `PublicFirst/`, `Flags/`), the refill (`Refill/`), the budget and the assembly (`Glue/`), and `Final.lean` |
| `Proof/Simulator/CRT/` | the closed simulator `CrtTop.crtSimulator` and its law: stage 1, what stage 1 leaves in memory, the replay's agreement with the evaluator block by block, Barrett, Garner, the fraction reading, the solve and the programs |
| `Proof/Privacy/Phase3/`, `Proof/Simulator/`, `Proof/LamportCompatibility/` | xinshu's generic parts that the CRT chain uses (the lazy-oracle glue, the hybrid shapes, the opening, here with the sign row's two-scale lift, the assembly language's semantics), and Lamport compatibility |

## 2. The bytes

| field | contents | bytes |
|---|---|---:|
| `curve` | 3 curve-check constants | 96 |
| `rows` | 91 digits × 3 constants × 32 B | 8,736 |
| `exception` | 91 digits × one-byte entry | 91 |
| `crtX`, `crtY` | 3,378 labels × 13 B per coordinate | 87,828 |
| `recX`, `recY` | 642 records × 78 B (367 of `x`, 275 of `y`) | 50,076 |
| **total** | | **146,827** |

A record is `h_e·M + Σ_i J_{e,i}·Π_{i'<i} m_{i'}`, below `2M < 2^624`. Every field has a fixed width, so
every public value encodes to the same length (`Entry.Wire.encoding_length`). Against `de8f397`, the sign
row saves 91 records (7,098 B) and 91 row constants (2,912 B), and the second exceptional case adds 6
bytes per digit (546 B) in the original layout: 9,464 B less. The fallback schedule saves another 4,288 B,
first extraction width 8 on every odd row saves 884 B more, and compacting both exceptional kinds into one byte saves 1,001 B, and 104-bit conversion labels save 20,472 B, for 36,109 B less in total.

## 3. Query accounting

| part | garbling | evaluation |
|---|---:|---:|
| coordinate `x` (chunks 55,936 / 55,522; conversions 244,841 / 242,904; body 217,950 / 216,976) | 518,727 | 515,402 |
| coordinate `y` (chunks and conversions as `x`; body 166,643 / 165,895) | 467,420 | 464,321 |
| mask key | 1 | 1 |
| masks | 1,092 | 1,092 |
| exception digest | 1,198 | 690 |
| **total** | **988,438** | **981,506** |

The budgets are term-by-term sums over the 85 moduli (`Entry.garbleBudgetOf`, `Entry.evaluateBudgetOf`),
with certificates using `decide +kernel` in `Construction/CRT/BudgetFacts.lean`. The evaluator's count is the same for
every input. Against `de8f397`, the body of `x` (367 encodings instead of 458) asks 49,966 garbling and
49,745 evaluation queries fewer, the masks 137 fewer on each side, and the digest 91 more on each side.

## 4. Privacy

The obligation, the lazy oracle and the chain's shape are xinshu's. The chain is
`G0 → G0T → G0U → G1U → HW → H → I → M` (`Proof/Privacy/CRT/Glue/Budget.lean`): the table-planted game, the
pad and mask swap, the hidden deletion, the public-first hop, xinshu's opening, the refill, and the
machine law. The core of the public-first hop is that the map from the hidden answers to the published
conversion material is a bijection whose inverse is the evaluator's own solve; the wrap hint is coupled to
the ideal integer except on `O > M − B`; the simulator programs only the 273 collectors' masks (546 hash
answers). The constant part is about `2^-103.74`, 0.075 of the unit `2^-100`: the wrap-hint term
`(1284·(p − 1)² + 273·p)/M ≈ 2^-104.74` is charged twice (in the public-first hop, and in the hidden hop
for the curve encodings' wrap window) and dominates. The linear part is `2^-125` per stage-1 query and
`2^-126` per stage-2 query, so `Adv · 2^100 ≤ q₁ + q₂ + 1` (`chainError_budget`).

The sign row and the second exceptional case change four parts of the chain and nothing in the CRT layer.
The rows' bijection of the public-first core maps a digit's 7 offsets to its 3 constants and its 4
non-collector values, dividing by `3 − y²` (§1.5; `BMR.rowEquiv`, with `bmrEquiv` on the curve and
`bmrEquivOff` off it). The exceptional event is a digit point `Q + K` equal to `2Q`, `0` or `(3/2)Q`: three
targets per digit, `364/(r − 1)` (`RowsDoubling.threeTargets_real_le`; the sign row vanishes at `2K`,
`BmrEntry.sign_double`). The opening lifts a digit point with two scales, `(λ²x, t²y, λ)` (`(λ², 0, 0)` at
the identity); off the exceptional inputs a real row is such a lift with `λ = ρ·(u − a)` and `t = τ·L`, and
the output kernel is `455/(r − 1)` (`Instance.crtEntry_opening`). The 182 final sites of the digest
bound a hidden final's coincidence by `182/2^128` (`FinalCoincide.crtEntry_finalCoincide`), so the
coincidence term is `185/2^128`.

The simulator is one closed machine, `CrtTop.crtSimulator` (`Proof/Simulator/CRT/Machine.lean`), written
in xinshu's structured assembly with his two-stage layout. Its cost bound `size + 1 + firstFuel +
secondFuel ≤ 2^60` follows from per-block bounds of `2^55` (`Design.blocks_totalCost_le`), and its law
(stage 1, the two arms of stage 2, the sampler cutoff `2^-128`) gives the machine row
`crtEntry_machineHop_of` (`Proof/Privacy/CRT/Glue/MachineCrt.lean`). The sign row's collector is
`rowY_cubic`, read with `x²`, so the machine's solve scales its target by `(x·x)⁻¹` (`x ≠ 0` on the curve),
and its opening draws 91 lift pairs `(λ, t)`.

## 5. Proof map

| `Solution` field | where | status |
|---|---|---|
| `garbleProgram`, `evaluateProgram`, `garbleQueries`, `evaluateQueries`, `garbleProgramCorrect`, `evaluateProgramCorrect` | `Construction/CRT/Entry.lean`, `Bounds.lean`, `BudgetFacts.lean`; `Submission.lean` | proof supplied; draft unbuilt |
| `ciphertextSize` | `Construction/CRT/Public.lean` (`Entry.Wire.encoding_length`) | proof supplied; draft unbuilt |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` | proof supplied; draft unbuilt |
| `functionCorrect` | `rfl` | proof supplied; draft unbuilt |
| `perfectCorrectness` | `Proof/Correctness/CRT/EntryCorrect.lean` (`EntryCorrect.perfectCorrectness`) | proof supplied; draft unbuilt |
| `adaptivePrivacy` | `Proof/Privacy/CRT/Final.lean` (`Final.crtEntry_adaptivePrivacy`, from `Assembly.crtPrivacy`), `Proof/Privacy/CRT/Glue/Instance.lean` (`crtEntry_privacy_of_table`), `Proof/Privacy/CRT/Glue/MachineCrt.lean` (`crtEntry_machineHop_of`) | proof supplied; draft unbuilt |

## 6. Build and audit

The static fallback audit runs without Lean and checks the frozen schedule, cost numerals,
and the existing reachability certificates. It does not check proof elaboration:

```sh
python3 Scratch/check_fallback.py
```

```sh
lake exe cache get                      # Mathlib build cache
lake build                              # Construction, Proof, Submission
lake env lean Scratch/Audit.lean        # metrics, budgets recomputed, bytes of an encoded value, axioms
lake env lean Scratch/ProofAudit.lean   # the three axioms over every declaration of the entry
```

`Scratch/` is not a Lean library and the verifier ignores it. `Scratch/Audit.lean` fails if the bytes
(146,827, from the metric and from encoding an all-zero public value), the garbling budget (988,438) or
the evaluation budget (981,506) differ, or if a budget comes within 500 queries of its gate, and it checks
the axioms of the solution and of the privacy field. Build time depends strongly on available
memory; this fallback draft has not been built, and no build-time estimate is claimed here.

## 7. Provenance

The CRT-residue projectivization (one-hot trees, casts and pins, extraction, folds, the body), the switch
systems and the Embryo masking are from Duty-Free Bits (Khambhati, Bhattacharya and Heath, ePrint
2026/476); arithmetic labels and per-modulus truth tables from Heath (ePrint 2024/139). The delivery of
Argo MAC field encodings through the Duty-Free Bits CRT residues, a fixed conversion per input plus a cost
per encoding, is from Khambhati, Feickert, Lewe and Tiwari (ePrint 2026/2100). The ArgoMAC entries start
from the challenge's baseline `Kriterion-cc/argomac-lean` (Runchao Han). The Plan B framework this tree
descends from, a switch-system entry with a complete proof whose privacy proof structure and simulator
machine the CRT entry extends, is xinshu's (`xinshudong/bn254-entry`, `bf53ea4`). The CRT entry is
psivesely's (`psivesely/kriterion-bn254-crt`, `de8f397`): its contest tunings (the modulus set and its
closed-form schedule, block-aligned casts, the fraction reading with 120 bits of slack, the wrap hint and
per-encoding records, the labelled mask key, the hash digest for the exception gadget, the hash-only oracle)
and its Lean construction and proofs, which this entry keeps. The coefficient cut and the proof that 3 is a
quadratic non-residue modulo `p` (so no point of BN254 has `x = 0`) are Lazar's (`Lazar955/argomac-lean`,
`d9a8327`), who also published the four-encoding `Y` row first (`9516948`). The sign row, its coefficient
cut, the second exceptional case, and their correctness, privacy and machine proofs on the CRT entry are
Lazar's (`Lazar955/bn254-planb`). The 91-digit decomposition is liucheng's. Argo MAC is by Eagen and Lai (ePrint 2026/049), and
BABE, whose ArgoMAC garbling of BN254 scalar multiplication the challenge baseline follows, by Garg,
Kolonelos, Sergeevitch, Sridhar and Tse (ePrint 2026/065).

This entry was written with AI coding agents under human direction and review. That changes nothing
that is checked: the verifier builds the tree against the pinned public library, rejects `sorry` and every
axiom beyond the three above, and evaluates the three metrics.

## 8. Layout

| path | content |
|---|---|
| `Construction/CRT/`, `Construction/Simulator/CRT/` | the CRT construction and the simulator machine's code |
| `Construction/ArgoMAC/`, `Garbling.lean`, `Scheme.lean`, `QueryMonad.lean` | the rows with the sign row, curve check, gadget entry, decoder and coins |
| `Proof/Correctness/CRT/`, `Proof/LamportCompatibility/` | the proved fields |
| `Proof/Privacy/CRT/`, `Proof/Simulator/CRT/` | the privacy proof and the machine law |
| `Submission.lean` | the `Kriterion.Solution` instance |
| `Proof/README.md` | the proof map: which module proves which obligation |
| `Scratch/` | the two audit files of §6 |
| `Intuition.md` | the public design rationale the challenge requires |

The tree holds exactly the modules that `Submission` imports (394 files under `Construction/` and `Proof/`,
and the three roots): the switch-system entry's modules that the CRT entry does not use are removed
relative to `bf53ea4`, and the 27 modules of xinshu's switch-system simulator machine that the CRT machine
does not use are removed relative to `de8f397`. Some of xinshu's switch-system
construction is still imported, through his privacy glue (`Proof/Privacy/Phase3/Glue/RandomnessSplit.lean`
imports `Construction/PGS/`, `Construction/OraclePrograms.lean` and `Construction/Simulator.lean`, which is
now only the root of the CRT machine). Module
headers inherited from `bf53ea4` cite xinshu's internal design notes by file name (`2026-09-17-planB.md`
and others), and some CRT headers refer to the design's decision labels (`D7`, `D11`), lemma labels
(`L1` to `L20`) and the labels of the parts of the privacy proof (`P1` to `P10`, `P45`); the notes they
come from are not part of this repository.
