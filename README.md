# Selective width-9 extraction on the CRT-residue ArgoMAC entry

This is an entry for the Kriterion `scalar-multiplication` challenge: garbled BN254 scalar
multiplication `f_k(u) = k·u`, checked in Lean against the challenge library
`Kriterion-cc/kriterion-challenge` at commit `aaf2789` (Lean `v4.33.1`, Mathlib `v4.33.1`). The build
configuration (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) is unchanged from the entry it
builds on.

This fork starts at dnctse's `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05` (130,122 B).
Its sole construction change is first-stage width 9 on 25 selected odd moduli. Each substitution saves
one join and one half-pin label per coordinate: **1,300 bytes** in total. All moduli, 104-bit internal
labels, 128-bit external labels, pad slack, records and privacy error parameters are unchanged.

**All local build, metric, encoding and axiom checks passed on 2026-09-28.
Hosted verification has not been run for this candidate.**

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **128,822** | ranked, lower is better |
| `garbleQueries` | **1,062,022** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **1,055,144** `≤ 1,055,879` (735 below) | acceptance gate |

The unchanged starting commit was reproduced locally: full build, exact metric and encoding audit,
and a whole-tree axiom audit over 23,735 declarations. Its axiom union is exactly `propext`,
`Classical.choice` and `Quot.sound`. Candidate results are recorded in §4.

## 1. What this entry changes

dnctse's starting point builds on Lazar's entry (`Lazar955/bn254-planb`, commit `f79c96a`, 173,472 B), itself psivesely's
CRT-residue delivery (`psivesely/kriterion-bn254-crt`, `de8f397`) of ArgoMAC on xinshu's Plan B framework
(`xinshudong/bn254-entry`, `bf53ea4`). The ArgoMAC structure (91 base-`(2−ω)` digits, the X/Z rows and the sign
row, the curve check, the exception digest) and the CRT-residue conversion are theirs. The first six
steps below are inherited from dnctse; step 7 is this fork’s schedule refinement:

| step | change | bytes |
|---|---|---:|
| — | Lazar's entry `f79c96a` | 173,472 |
| 1 | **104-bit internal conversion labels** (and first extraction width 8 on 67 of the 84 odd moduli) | 148,712 |
| 2 | **one-byte exception entries** (two masked 4-bit digit codes per digit instead of 12 bytes) | 147,711 |
| 3 | **first extraction width 8 on every odd modulus** | 146,827 |
| 4 | **parity casts**: every pin is even and is published halved | 141,627 |
| 5 | **no chunk joins**: the chunk-tree joins are absorbed into the Lamport labels | 135,855 |
| 6 | **normalized rows**: the Z and sign-row constants become flag bits | 130,122 |
| 7 | **selected first extraction width 9** on 25 odd moduli | **128,822** |

1. **Narrow labels.** The challenge's privacy requirement is `Adv · 2^100 ≤ T + 1`, i.e. about 100 bits of
   security per unit of adversary work. The conversion layer's labels, joins and arithmetic lanes are
   therefore 104 bits (`Kriterion.CRT.Narrow`: `Label = BitVec 104`, `clip`/`embed`); the external Lamport
   labels, the digest and mask keys and all raw oracle answers stay 128 bits. Conversion queries are
   related by the projected offset `embed (clip Δ)` and digest queries by the full `Δ` (the mixed relation
   `queryShift`); a hidden conversion label is guessed with probability `2^-104` per query
   (`Hidden/CaseConv`, `StageOneCast`), and the budget allots each hidden/touch charge
   `4/2^104 + 1/(p−1) ≤ 1/3` units. Every conversion block shrinks from 16 to 13 bytes.
2. **Exception entries.** The per-input digest key already singles out the one exceptional input, so the
   six orbit-indexed slots per kind were unnecessary: each kind is a 4-bit digit code masked by the low bits
   of its own final hash, packed two per byte (`Construction/ArgoMAC/Exception.lean`,
   `ExceptionEncoding.lean`).
3. **Width 8 (inherited step).** At this step every odd modulus extracts 8 bits in its first stage (one join and one pin label fewer),
   paid for with evaluation queries freed by step 1.
4. **Parity casts.** A cast lane's low bit is the corresponding bit of its control label
   (`A(L)_i = bit_i(L) + 2·H_i`). Because the leaves of a tree XOR to `Δ`, every pin
   `P = Σ_α A(L_α) + Δ` is even in every lane, so the entry publishes `P/2` (one label fewer per pin, 400
   pins) and the evaluator doubles it back. Privacy: the extraction injectivity theorem with the hot tree
   materials and the upper bits of the hot cast as the hidden data.
5. **No chunk joins.** A chunk tree's higher bit masks enter only through its joins, so the actual zero
   label of coordinate bit `8c + n` (`n ≥ 1`) is `Z ⊕ embed(J_{c,n})`: the 222 chunk joins per coordinate are
   not published and the evaluator runs its chunk trees on the join `0`. The digest and the returned key use
   the derived labels. Privacy: the XOR bijection between the hot chunk-tree answers and the selected
   labels (`Proof/Privacy/CRT/NoJoins/`), a re-cut core split (`H8.restHidden`, `H8.hotPayloadTag`) and a
   fine view that carries the selected labels (`Hidden/DeltaView*`).
6. **Normalized rows.** The Z row is scaled by `ρ = (K_z + ε_Z)/z₀` and the sign row by
   `κ = (K_c + ε_S)/s₄` (not necessarily a square), so their published constants become the bits `ε_Z`, `ε_S`
   and `ν = [χ(κ) = −1]`; digit zero's sign polynomial becomes `b·x²`. Per digit the entry publishes `xC0`
   and one flag byte (`NormRow`) instead of three field constants. Privacy: a bijection on the coins through
   the field scales with a sign split, the zero-offset case paid on the ideal side
   (`Proof/Privacy/CRT/Core/BmrNorm.lean`, `NormRows`, `NormFlag`); `exceptionalError` becomes `546/(r−1)`.

7. **Selective width 9.** `selectiveWidth0` chooses `59, 61, 257, 263, 269, 271, 277, 281, 283, 293,
   307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389`. The word width stays fixed;
   the second extraction stage shrinks by one bit. Kernel-checked row facts establish the complete
   conversion conditions. `ConvReach.stageZero_bound` puts every widened first-stage target inside the
   existing reachability certificates; second-stage targets shrink, and growth still has at most nine
   bits. The simulator keeps 400 pins and emits 50 fewer joins across the two coordinates, with the new
   lane widths and wire length checked by its existing generic proofs. `Scratch/check_width9.py`
   independently computes the byte/query tradeoff and rechecks all 84 reachability certificates.

## 2. The bytes

| field | contents | bytes |
|---|---|---:|
| `curve` | 3 curve-check constants × 32 | 96 |
| `rows` | 91 digits × (`xC0` 32 B + flags 1 B) | 3,003 |
| `exception` | 91 digits × one byte | 91 |
| `crtX`, `crtY` | 2 × 2,906 labels × 13 B (1,703 half-pin labels and 1,203 modulus joins per coordinate) | 75,556 |
| `recX`, `recY` | 642 records × 78 B (367 of `x`, 275 of `y`) | 50,076 |
| **total** | | **128,822** |

## 3. Queries

| part | garbling | evaluation |
|---|---:|---:|
| coordinate `x` (chunks 55,936 / 55,522; extraction, growth, folds 281,633 / 279,723; body 217,950 / 216,976) | 555,519 | 552,221 |
| coordinate `y` (chunks and extraction as `x`; body 166,643 / 165,895) | 504,212 | 501,140 |
| mask key, masks, exception digest | 2,291 | 1,783 |
| **total** | **1,062,022** | **1,055,144** |

The budgets are exact sums over the 85 moduli (`Construction/CRT/Entry.lean`), certified by
`decide +kernel` in `Construction/CRT/BudgetFacts.lean`.

## 4. Build and audit

```sh
lake exe cache get                      # Mathlib build cache
lake build                              # Construction, Proof, Submission
lake build Benchmark                    # audit dependency
lake env lean Scratch/CandidateAudit.lean # candidate metrics, budgets, encoding, axioms
lake env lean Scratch/ProofAudit.lean   # the three axioms over every declaration of the entry
```

Baseline logs are preserved under `evidence/baseline-e37c4db/`: build (3,845 jobs), the unchanged
`Scratch/Audit.lean` (130,122 / 988,438 / 981,506), and `Scratch/ProofAudit.lean` (23,735 declarations).
The pinned `Benchmark` module must be built explicitly for the metric audit on a fresh checkout.

Candidate verification passed, with raw logs under `evidence/candidate-width9/`:

- Full build: exit 0, 3,844 jobs (`build-third.log`), including `Submission.solution` and the finite simulator.
- Metric/encoding audit: exit 0 (`audit.log`), **128,822 / 1,062,022 / 1,055,144**. Both budgets are
  recomputed from their definitions; the concrete public encoding is **128,822 bytes** and decodes successfully.
- Whole-tree axiom audit: exit 0 (`proof-audit.log`), **23,747 declarations**, with union exactly
  `propext`, `Classical.choice`, `Quot.sound`.

`Scratch/CandidateAudit.lean` retains separate expectations derived from the independent cost model,
checks both gates with at least 500 queries of headroom, and audits affected proof declarations.
`Scratch/ProofAudit.lean` audits all construction/proof declarations. The baseline audit is intentionally
unchanged and is expected to fail its old numeric guards on this candidate. The complete command and
repair record is in [the verification report](evidence/verification.md).

`Scratch/` is not a Lean library and the hosted verifier ignores it. Local verification does not assert
hosted acceptance, leaderboard position, or a lower bound on achievable size.

## 5. Proof map

| `Solution` field | where |
|---|---|
| programs, budgets, program equalities | `Construction/CRT/Entry.lean`, `Bounds.lean`, `BudgetFacts.lean`; `Submission.lean` |
| `ciphertextSize` | `Construction/CRT/Public.lean` (`Entry.Wire.encoding_length`) |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` |
| `functionCorrect` | `rfl` |
| `perfectCorrectness` | `Proof/Correctness/CRT/EntryCorrect.lean` (`EntryCorrect.perfectCorrectness`) |
| `adaptivePrivacy` | `Proof/Privacy/CRT/Final.lean` (`Final.crtEntry_adaptivePrivacy`), the closed simulator `CrtTop.crtSimulator` (`Proof/Simulator/CRT/`) |

`Intuition.md` describes this delta and preserves the inherited design background.

## 6. Credits

* **dnctse** (`dnctse/kriterion-bn254`, `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05`): the starting
  130,122-byte entry, its six optimizations, construction, correctness/privacy proofs, simulator and audits.
* **Lazar** (`Lazar955/bn254-planb`, `f79c96a`; `Lazar955/argomac-lean`): the sign row, the coefficient
  cut, the second exceptional case, and the entry this one starts from.
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

The first six optimizations above and their proofs are inherited. This fork contributes only the selected
width-9 schedule, its integration proofs and audits. The git history preserves every prior author's commits.

The inherited entry disclosed development with Anthropic's Claude and OpenAI's GPT under human direction.
This fork's schedule implementation and Lean proof integration were developed with OpenAI GPT-6 Astra under
Souhail's direction; independent arithmetic checks were supplied by Claude Opus 5.5 and the coordinator. The verifier builds the
tree against the pinned public library, rejects `sorry` and every axiom beyond the three above, and evaluates
the three metrics.
