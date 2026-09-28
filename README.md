# Narrow labels, parity pins, absorbed joins and normalized rows on the CRT-residue ArgoMAC entry

This is an entry for the Kriterion `scalar-multiplication` challenge: garbled BN254 scalar
multiplication `f_k(u) = k·u`, checked in Lean against the challenge library
`Kriterion-cc/kriterion-challenge` at commit `aaf2789` (Lean `v4.33.1`, Mathlib `v4.33.1`). The build
configuration (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) is unchanged from the entry it
builds on.

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **130,122** | ranked, lower is better |
| `garbleQueries` | **988,438** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **981,506** `≤ 1,055,879` (74,373 below) | acceptance gate |

Every field of `Kriterion.Solution` is proved; there is no `sorry`, and `#print axioms
Submission.solution` reports exactly `propext`, `Classical.choice` and `Quot.sound` (so does every one of the
23,735 declarations under `Construction/`, `Proof/` and `Submission.lean`; see §4).

## 1. What this entry changes

It builds on Lazar's entry (`Lazar955/bn254-planb`, commit `f79c96a`, 173,472 B), itself psivesely's
CRT-residue delivery (`psivesely/kriterion-bn254-crt`, `de8f397`) of ArgoMAC on xinshu's Plan B framework
(`xinshudong/bn254-entry`, `bf53ea4`). The ArgoMAC structure (91 base-`(2−ω)` digits, the X/Z rows and the sign
row, the curve check, the exception digest) and the CRT-residue conversion are theirs. This entry changes six
things; each step was built and audited on its own:

| step | change | bytes |
|---|---|---:|
| — | Lazar's entry `f79c96a` | 173,472 |
| 1 | **104-bit internal conversion labels** (and first extraction width 8 on 67 of the 84 odd moduli) | 148,712 |
| 2 | **one-byte exception entries** (two masked 4-bit digit codes per digit instead of 12 bytes) | 147,711 |
| 3 | **first extraction width 8 on every odd modulus** | 146,827 |
| 4 | **parity casts**: every pin is even and is published halved | 141,627 |
| 5 | **no chunk joins**: the chunk-tree joins are absorbed into the Lamport labels | 135,855 |
| 6 | **normalized rows**: the Z and sign-row constants become flag bits | **130,122** |

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
3. **Width 8.** Every odd modulus extracts 8 bits in its first stage (one join and one pin label fewer),
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

## 2. The bytes

| field | contents | bytes |
|---|---|---:|
| `curve` | 3 curve-check constants × 32 | 96 |
| `rows` | 91 digits × (`xC0` 32 B + flags 1 B) | 3,003 |
| `exception` | 91 digits × one byte | 91 |
| `crtX`, `crtY` | 2 × 2,956 labels × 13 B (1,728 half-pin labels and 1,228 modulus joins per coordinate) | 76,856 |
| `recX`, `recY` | 642 records × 78 B (367 of `x`, 275 of `y`) | 50,076 |
| **total** | | **130,122** |

## 3. Queries

| part | garbling | evaluation |
|---|---:|---:|
| coordinate `x` (chunks 55,936 / 55,522; extraction, growth, folds 244,841 / 242,904; body 217,950 / 216,976) | 518,727 | 515,402 |
| coordinate `y` (chunks and extraction as `x`; body 166,643 / 165,895) | 467,420 | 464,321 |
| mask key, masks, exception digest | 2,291 | 1,783 |
| **total** | **988,438** | **981,506** |

The budgets are exact sums over the 85 moduli (`Construction/CRT/Entry.lean`), certified by
`decide +kernel` in `Construction/CRT/BudgetFacts.lean`.

## 4. Build and audit

```sh
lake exe cache get                      # Mathlib build cache
lake build                              # Construction, Proof, Submission
lake env lean Scratch/Audit.lean        # metrics, budgets, bytes of an encoded value, axioms
lake env lean Scratch/ProofAudit.lean   # the three axioms over every declaration of the entry
```

We verified this commit from a clean tree (no reused build artifacts of the entry): `lake build` completes
(3,844 jobs, no `sorry`); `Scratch/ProofAudit.lean` audits 23,735 declarations with axioms exactly `propext`,
`Classical.choice`, `Quot.sound`; an independent audit prints `Submission.solution : Kriterion.Solution`, its
axioms, the three metrics above, and checks both gates by `decide +kernel`. `Scratch/` is not a Lean
library and the verifier ignores it; it also holds the audit files of the individual steps
(`NarrowPhaseA`, `NarrowPrivacyCore`, `NarrowSimulatorAudit`, `NarrowParityCorrectness`, `NoJoinsAudit`,
`NoJoinsPrivacyIntegrated`, …) and independent Python cost checkers.

## 5. Proof map

| `Solution` field | where |
|---|---|
| programs, budgets, program equalities | `Construction/CRT/Entry.lean`, `Bounds.lean`, `BudgetFacts.lean`; `Submission.lean` |
| `ciphertextSize` | `Construction/CRT/Public.lean` (`Entry.Wire.encoding_length`) |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` |
| `functionCorrect` | `rfl` |
| `perfectCorrectness` | `Proof/Correctness/CRT/EntryCorrect.lean` (`EntryCorrect.perfectCorrectness`) |
| `adaptivePrivacy` | `Proof/Privacy/CRT/Final.lean` (`Final.crtEntry_adaptivePrivacy`), the closed simulator `CrtTop.crtSimulator` (`Proof/Simulator/CRT/`) |

`Intuition.md` explains the construction and the proof in detail.

## 6. Credits

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

The six changes above, their proofs and their audits are this entry's. The git history keeps every prior
author's commits.

This entry was developed with AI agents (Anthropic's Claude and OpenAI's GPT via Codex) under human
direction and review. That changes nothing that is checked: the verifier builds the tree against the pinned
public library, rejects `sorry` and every axiom beyond the three above, and evaluates the three metrics.
