# P1a: whole-public bit packing, locally verified

Date: 2026-09-28. Base: P1 `dc6aa07014645d3bc1a2846d4521c17b8c3d93af`, itself based on submitted combined `32f1fb34884ca33a84ac9dd4db687ca30187aeed`. Branch: `codex/packed-public`. All checks below passed before committing. No publication, hosted verification or leaderboard change is claimed for P1a.

## Actual results

| Measurement | Actual |
|---|---:|
| Complete ciphertext | **127875 bytes** |
| Garbling queries | **1061622** |
| Evaluation queries | **1054788** |
| Evaluation headroom | 1091 |
| Full public bits before padding | 1022997 |
| Final zero padding | 3 bits |
| Internal label width | 104 bits |
| Whole-tree declarations audited | 23800 |

The independently calculated stream is curve 762 + rows 23387 + exception 728 + conversion 600080 + records 398040 = 1022997 bits. After three final zero bits: 1023000/8 = 127875 bytes. Relative to 128276 bytes this removes 401 bytes, and relative to the pinned 130122-byte baseline, 2247 bytes. Query budgets are unchanged. At 101-bit labels the model predicts 1005687 bits plus **one** final zero bit, or 125711 bytes ; 101-bit labels are not part of this milestone.

## Construction and proof

`Construction/CRT/BitPacking.lean` implements generic fixed-width bit codecs using `Vector Bool`, with map/pair/vector composition, bounded-natural conversion and a direct byte-vector codec. Each codec has an inverse for every inhabitant. The complete byte codec preserves arbitrary appended byte tails. Packing uses one cached padded bit vector, then byte conversion; it avoids giant-natural packing and deeply nested byte encoders.

`Public.lean` uses 254-bit fields, 3-bit flags, unchanged 104-bit conversion labels and `Record := Fin (2^620)`. The honest-record bound `2*M ≤ 2^620` is separately kernel-checked from the actual table product; correctness never relies on truncating a too-large honest record. All eight flag triples and every 620-bit record inhabitant round-trip, including values outside the honest source range.

The generic byte-bit theorem is proved in `Proof/Simulator/CRT/BitPacking.lean`. `Stage1Wire.wire_bits` identifies all public bits plus final padding. The finite machine emits 254-bit fields, 3-bit flags and 620-bit records (the fifth 128-bit limb contributes 108 bits). `serialize` first emits final zeros, then runs its existing pieces in reverse. `Stage1Pieces`, `Stage1Serial`, `Stage1Tail`, `Stage1Law` and the complete simulator assembly prove exact output, memory behavior, no oracle calls, and the original fuel bounds. Final padding adds at most 22 instructions to the serialization bound and no Piece constructor; pieces remain 44579 at 104 bits.

All challenge definitions, `Submission.lean`, query programs, query budgets, external 128-bit Lamport labels, pad slack, modulus/schedule choices, security closure and pinned dependencies are unchanged from P1. The only changed privacy module updates the record range used by `BmrIdealOff.publish_recX/Y_val`.

## Checks and source binding

- `env LEAN_NUM_THREADS=6 lake build`: **exit0**, 3846 jobs, successful final run 24.4 seconds (incremental); `build-fourth.log` and status.
- `lake build Benchmark`: **exit0**; `benchmark-build.log` and status.
- `lake env lean Scratch/PackedAudit.lean`: **exit0**, 14.1 seconds; `audit-second.log` and status. Actual Benchmark metrics, table/record bounds, query gates, exact bit/padding guards, formula-derived piece count, universal codec inverse, zero/maximal lengths and maximal decode/re-encode with tail `[137,42]` all pass.
- `lake env lean Scratch/ProofAudit.lean`: **exit0**, 43.4 seconds ; 23800 declarations; axiom union exactly `propext`, `Classical.choice`, `Quot.sound`.
- `python3 -B Scratch/check_packed.py`: independent integer model reproduces baseline/A1/H1/combined before computing the complete packed layout.
- `dependencies.json`: all 13 dependency checkouts match pinned revisions with no tracked changes; Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

Final source/configuration/audit manifest: **ea76922a04a00ae3cf705bcf9f0b58d1db28ec65d5021a4a3c4b2798aa38063a**, 453 files. The full-build manifest is preserved separately. `build-source-binding.json` checks that the only later source-file change was in the separate `Scratch/PackedAudit.lean`: its maximal-record witness uses `Nat.sub_lt` instead of brute-force power reduction, and its piece-count check also states the derived formula. Every construction, proof, solution and pin is byte-identical to the successful full build. Recheck the final manifest at the committed HEAD with `python3 -B Scratch/PackedSourceManifest.py check`.

## Preserved repair history

All failed/interrupted runs are retained without overwriting their logs:

1. `build-first`: ordinary proof failures in the old 78-byte record-bound use and the zero-padding simp lemma; both repaired.
2. `build-second`: the remaining `noOracle_serialize` obligation failed. Its `Stage1Size` process was separately **terminated with SIGTERM** (exit143) after spending roughly 3 minutes expanding the concrete serializer in a size tactic. This was an intentional cancellation, not a mathematical counterexample or accepted check. A generic abstract-program size lemma avoids that expansion.
3. `build-third`: ordinary exact-cost failure from the obsolete 112-bit top-limb numeral; corrected to 108.
4. `build-fourth`: the complete build passed and all processes finished normally.
5. First `audit`: two maximal-record proof witnesses exceeded Lean's default recursion-depth reduction. No metric mismatch was reported. Replacing those test witnesses with the general strict-subtraction lemma produced the successful second audit.

## Attribution

Retains dnctse, Lazar955, psivesely, xinshudong, liucheng, ArgoMAC and research credits in README/history. Opus proposed charge refinement, narrower labels and complete bit packing in the shared research note. OpenAI GPT-6 Astra implemented P1a's Vector Bool codec, universal inverse, exact public type/widths and simulator/proof integration under Souhail's direction. The coordinator supplied independent arithmetic review. Claude Opus 5.5 independently owns the subsequent 101-bit label/privacy implementation; none of that unpublished delta is included here.
