# CRT-residue delivery of the affine encodings of ArgoMAC, on xinshu's switch-system entry

This is an entry for the Kriterion `scalar-multiplication` challenge: garbled BN254 scalar
multiplication `f_k(u) = k·u`, checked in Lean against the challenge library
`Kriterion-cc/kriterion-challenge` at commit `aaf2789` (Lean `v4.33.1`).

It is xinshu's entry (`xinshudong/bn254-entry`, commit `bf53ea4`, 3,363,376 bytes) with the delivery of
the affine encodings replaced:

* **the delivery layer**: the switch systems are replaced by the CRT-residue projectivization of Duty-Free
  Bits (Khambhati, Bhattacharya and Heath), applied to Argo MAC encodings as in ePrint 2026/2100: per coordinate, one conversion of the 254 input bits into
  one-hot labels of the residues modulo 85 small moduli (3,546 published blocks), then one 78-byte record
  per encoding;
* **the gating**: the rows are masked by hash outputs keyed by the curve check's value, in place of the
  second switch system on labels whitened by EncPRF pads;
* **the exception gadget**: xinshu's per-digit gadget (`91·508 = 46,228` permutation queries on each side)
  is keyed by a hash digest of the input's labels: 1,016 label hashes and one final hash per digit, 1,107
  garbling and 599 evaluation queries, the same 6-byte entry per digit;
* **the oracle**: every query is to the field hash; the two permutation families are unused;
* **the rows**: 8 affine encodings and 4 published constants per digit (Lazar's four-encoding `Y` row,
  garbled with the curve equation, and Lazar's coefficient cut).

The curve check, the rows' algebra, the decoder and the proof architecture are xinshu's.

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **182,936** `= 12,290 + 2·56,736 + 733·78` | ranked, lower is better |
| `garbleQueries` | **995,088** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **987,209** `≤ 1,055,879` (68,670 below) | acceptance gate |

Every field of `Kriterion.Solution` is proved, and there is no `sorry` in the tree.
`#print axioms Submission.solution` reports exactly `propext`, `Classical.choice` and `Quot.sound`,
and so does every declaration under `Construction/`, `Proof/` and `Submission.lean`
(`Scratch/Audit.lean`, `Scratch/ProofAudit.lean`).

`Intuition.md` explains the construction and the proof.

## 1. What changed from `bf53ea4`, and why

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
728 row encodings by xinshu's three-block rule; the garbler's row offsets include the masks. Off the curve
`t' ≠ t` and every row value is masked. This removes xinshu's curve-lane switch system and the EncPRF
whitening.

### 1.3 The exception digest

Each of the 508 labels is hashed with its bit in the tag; a digit's key is the XOR of the hashes at its
exceptional input's bits, and the entry's mask byte is the low byte of the hash of the key.

### 1.4 The hash-only oracle

`FixedIndex` and `EncIndex` are `Empty`. Every query is at `label + 2^128·tag` with a tag below `2^40`
that names its site, so distinct sites never share an input.

### 1.5 Construction

| file | content |
|---|---|
| `Construction/CRT/Interface.lean`, `Params.lean`, `Query.lean` | the frozen definitions (tags, hash inputs, one-block and long hashes, block-aligned cast lanes, pin codec, fraction reading, pad counts, wrap hint), the modulus table `CrtTable` and its 85-row instance, the query language `FreeQuery CrtSpec` and `liftHash` |
| `Construction/CRT/Lanes.lean`, `Tree.lean`, `Chunk.lean` | arithmetic labels; the one-hot tree step; chunk trees, casts, pins and truth-table words |
| `Construction/CRT/ExtractSpec.lean`, `Extract.lean`, `Fold.lean` | the fused extraction stage (garbler by node recursion, evaluator by rounds); the kept one-hot, reindex and folds |
| `Construction/CRT/Body.lean`, `Coord.lean` | pads, residues and joins; one coordinate: conversion, body, CRT offsets with the wrap hint, records, the evaluator's reconstruction, the flat layout |
| `Construction/CRT/Mask.lean`, `Digest.lean` | the mask key and the 1,229 mask answers; the exception digest |
| `Construction/CRT/Entry.lean`, `Public.lean`, `Bounds.lean`, `BudgetFacts.lean` | the scheme, the garbler and evaluator programs at their exact budgets, the public value and its codec, the query bounds, the budgets evaluated by the kernel |
| `Construction/CRT/Layout.lean` | the public value in source form, for the simulator |
| `Construction/Simulator/CRT/` | the simulator machine: layout, stage 1, the replay blocks, Garner, the solve, the preimages and programs, the design and its cost bound, the valid arm (`Simulator.lean`) |
| `Construction/ArgoMAC/`, `Garbling.lean`, `Scheme.lean`, `QueryMonad.lean` | the rows, the curve check, the gadget entry, the decoder and the coins, unchanged except the rows of §1 |

### 1.6 Proof

| directory | content |
|---|---|
| `Proof/Correctness/CRT/` | perfect correctness wire by wire for every hash function: trees, chunks, words, extraction stages, folds, the body, records and the wrap hint, the flat layout, the digest unlock, and the assembly `EntryCorrect.perfectCorrectness` |
| `Proof/Privacy/CRT/` | the chain `G0 → G0T → G0U → G1U → HW → H → I → M` at the entry: the statements and the named rows (`Named.lean`, `Statements.lean`), the pad and mask swap (`Swap/`), the hidden hop (`Hidden/`), the public-first core (`Core/`, `Laws/`, `Paths/`, `PublicFirst/`, `Flags/`), the refill (`Refill/`), the budget and the assembly (`Glue/`), and `Final.lean` |
| `Proof/Simulator/CRT/` | the closed simulator `CrtTop.crtSimulator` and its law: stage 1, what stage 1 leaves in memory, the replay's agreement with the evaluator block by block, Barrett, Garner, the fraction reading, the solve and the programs |
| `Proof/Privacy/Phase3/`, `Proof/Simulator/`, `Proof/LamportCompatibility/` | xinshu's generic parts that the CRT chain uses (the lazy-oracle glue, the hybrid shapes, the opening, the assembly language's semantics), and Lamport compatibility |

## 2. The bytes

| field | contents | bytes |
|---|---|---:|
| `curve` | 3 curve-check constants | 96 |
| `rows` | 91 digits × 4 constants × 32 B | 11,648 |
| `exception` | 91 digits × 6-byte entry | 546 |
| `crtX`, `crtY` | 3,546 blocks × 16 B per coordinate | 113,472 |
| `recX`, `recY` | 733 records × 78 B (458 of `x`, 275 of `y`) | 57,174 |
| **total** | | **182,936** |

A record is `h_e·M + Σ_i J_{e,i}·Π_{i'<i} m_{i'}`, below `2M < 2^624`. Every field has a fixed width, so
every public value encodes to the same length (`Entry.Wire.encoding_length`).

## 3. Query accounting

| part | garbling | evaluation |
|---|---:|---:|
| coordinate `x` (chunks 71,936 / 71,458; conversions 207,160 / 204,924; body 267,916 / 266,721) | 547,012 | 543,103 |
| coordinate `y` (chunks and conversions as `x`; body 166,643 / 165,895) | 445,739 | 442,277 |
| mask key | 1 | 1 |
| masks | 1,229 | 1,229 |
| exception digest | 1,107 | 599 |
| **total** | **995,088** | **987,209** |

The budgets are term-by-term sums over the 85 moduli (`Entry.garbleBudgetOf`, `Entry.evaluateBudgetOf`),
evaluated by `decide +kernel` in `Construction/CRT/BudgetFacts.lean`. The evaluator's count is the same for
every input.

## 4. Privacy

The obligation, the lazy oracle and the chain's shape are xinshu's. The chain is
`G0 → G0T → G0U → G1U → HW → H → I → M` (`Proof/Privacy/CRT/Glue/Budget.lean`): the table-planted game, the
pad and mask swap, the hidden deletion, the public-first hop, xinshu's opening, the refill, and the
machine law. The core of the public-first hop is that the map from the hidden answers to the published
conversion material is a bijection whose inverse is the evaluator's own solve; the wrap hint is coupled to
the ideal integer except on `O > M − B`; the simulator programs only the 273 collectors' masks (546 hash
answers). The constant part is about `2^-103.54`, 0.086 of the unit `2^-100`: the wrap-hint term
`(1466·(p − 1)² + 273·p)/M ≈ 2^-104.55` is charged twice (in the public-first hop, and in the hidden hop
for the curve encodings' wrap window) and dominates. The linear part is `2^-125` per stage-1 query and
`2^-126` per stage-2 query, so `Adv · 2^100 ≤ q₁ + q₂ + 1` (`chainError_budget`).

The simulator is one closed machine, `CrtTop.crtSimulator` (`Proof/Simulator/CRT/Machine.lean`), written
in xinshu's structured assembly with his two-stage layout. Its cost bound `size + 1 + firstFuel +
secondFuel ≤ 2^60` follows from per-block bounds of `2^55` (`Design.blocks_totalCost_le`), and its law
(stage 1, the two arms of stage 2, the sampler cutoff `2^-128`) gives the machine row
`crtEntry_machineHop_of` (`Proof/Privacy/CRT/Glue/MachineCrt.lean`).

## 5. Proof map

| `Solution` field | where | status |
|---|---|---|
| `garbleProgram`, `evaluateProgram`, `garbleQueries`, `evaluateQueries`, `garbleProgramCorrect`, `evaluateProgramCorrect` | `Construction/CRT/Entry.lean`, `Bounds.lean`, `BudgetFacts.lean`; `Submission.lean` | proved |
| `ciphertextSize` | `Construction/CRT/Public.lean` (`Entry.Wire.encoding_length`) | proved |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` | proved |
| `functionCorrect` | `rfl` | proved |
| `perfectCorrectness` | `Proof/Correctness/CRT/EntryCorrect.lean` (`EntryCorrect.perfectCorrectness`) | proved |
| `adaptivePrivacy` | `Proof/Privacy/CRT/Final.lean` (`Final.crtEntry_adaptivePrivacy`, from `Assembly.crtPrivacy`), `Proof/Privacy/CRT/Glue/Instance.lean` (`crtEntry_privacy_of_table`), `Proof/Privacy/CRT/Glue/MachineCrt.lean` (`crtEntry_machineHop_of`) | proved |

## 6. Build and audit

```sh
lake exe cache get                      # Mathlib build cache
lake build                              # Construction, Proof, Submission
lake env lean Scratch/Audit.lean        # metrics, budgets recomputed, bytes of an encoded value, axioms
lake env lean Scratch/ProofAudit.lean   # the three axioms over every declaration of the entry
```

`Scratch/` is not a Lean library and the verifier ignores it. `Scratch/Audit.lean` fails if the bytes
(182,936, from the metric and from encoding an all-zero public value), the garbling budget (995,088) or
the evaluation budget (987,209) differ, or if a budget comes within 500 queries of its gate, and it checks
the axioms of the solution and of the privacy field. A clean build of the entry's 424 modules (with
Mathlib and the challenge library prebuilt) takes about 3 minutes on an 18-core machine; the slowest module
takes 14 s.

## 7. Provenance

The CRT-residue projectivization (one-hot trees, casts and pins, extraction, folds, the body), the switch
systems and the Embryo masking are from Duty-Free Bits (Khambhati, Bhattacharya and Heath, ePrint
2026/476); arithmetic labels and per-modulus truth tables from Heath (ePrint 2024/139). The delivery of
Argo MAC field encodings through the Duty-Free Bits CRT residues, a fixed conversion per input plus a cost
per encoding, is from Khambhati, Feickert, Lewe and Tiwari (ePrint 2026/2100). The ArgoMAC entries start
from the challenge's baseline `Kriterion-cc/argomac-lean` (Runchao Han). The Plan B framework this tree
descends from, a switch-system entry with a complete proof whose privacy proof structure and simulator
machine this entry extends, is xinshu's (`xinshudong/bn254-entry`, `bf53ea4`). The contest tunings (the modulus set and its closed-form schedule,
block-aligned casts, the fraction reading with 120 bits of slack, the wrap hint and per-encoding records,
the labelled mask key, the hash digest for the exception gadget, the hash-only oracle) and the Lean
construction and proofs are this entry's authors' own work. The coefficient cut and the proof that 3 is a
quadratic non-residue modulo `p` (so no point of BN254 has `x = 0`) are Lazar's (`Lazar955/argomac-lean`,
`d9a8327`), who also published the four-encoding `Y` row first (`9516948`). The 91-digit decomposition is liucheng's. Argo MAC is by Eagen and Lai (ePrint 2026/049), and
BABE, whose ArgoMAC garbling of BN254 scalar multiplication the challenge baseline follows, by Garg,
Kolonelos, Sergeevitch, Sridhar and Tse (ePrint 2026/065).

This entry was written with AI coding agents under human direction and review. That changes nothing
that is checked: the verifier builds the tree against the pinned public library, rejects `sorry` and every
axiom beyond the three above, and evaluates the three metrics.

## 8. Layout

| path | content |
|---|---|
| `Construction/CRT/`, `Construction/Simulator/CRT/` | the CRT construction and the simulator machine's code |
| `Construction/ArgoMAC/`, `Garbling.lean`, `Scheme.lean`, `QueryMonad.lean` | the rows, curve check, gadget entry, decoder and coins |
| `Proof/Correctness/CRT/`, `Proof/LamportCompatibility/` | the proved fields |
| `Proof/Privacy/CRT/`, `Proof/Simulator/CRT/` | the privacy proof and the machine law |
| `Submission.lean` | the `Kriterion.Solution` instance |
| `Proof/README.md` | the proof map: which module proves which obligation |
| `Scratch/` | the two audit files of §6 |
| `Intuition.md` | the public design rationale the challenge requires |

The tree holds exactly the modules that `Submission` imports (421 files under `Construction/` and `Proof/`,
and the three roots): the switch-system entry's modules that the CRT entry does not use are removed
relative to `bf53ea4`. Some of xinshu's switch-system
construction is still imported, through his privacy glue (`Proof/Privacy/Phase3/Glue/RandomnessSplit.lean`
imports `Construction/PGS/`, `Construction/OraclePrograms.lean` and `Construction/Simulator.lean`). Module
headers inherited from `bf53ea4` cite xinshu's internal design notes by file name (`2026-09-17-planB.md`
and others), and some CRT headers refer to the design's decision labels (`D7`, `D11`), lemma labels
(`L1` to `L20`) and the labels of the parts of the privacy proof (`P1` to `P10`, `P45`); the notes they
come from are not part of this repository.
