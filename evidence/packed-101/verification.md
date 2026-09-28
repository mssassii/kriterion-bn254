# Locally verified P1a + Opus101 integration

**125,711 bytes / 1,061,622 garbling queries / 1,054,788 evaluation queries.**
This is a locally proved candidate; hosted submission and acceptance are separate.

## Exact provenance

- Integration base: P1a documentation tip `76f7589ed25f909373d11700f4c0ac4b2dd70f00`.
- Immutable P1a source: `cc221c36a4f8e991d2c983b4ec748d40805ea064`, itself based on P1 `dc6aa07014645d3bc1a2846d4521c17b8c3d93af` and combined A1/H1 `32f1fb34884ca33a84ac9dd4db687ca30187aeed`.
- Exact independently verified Opus101 checkpoint: `2f7b9ca70f7a9c72ac4a24e98ddb97cb606e7ee8`, fetched from the sibling Claude repository and integrated without rewriting either checkpoint.
- Source/configuration/audit manifest: **459 files**, SHA-256 **`3396d0568b3d7f061aafd9ba4a860668c115eac1e948d228c758fa4a0b9f99a9`**. The final commit is identified by the commit containing this report; the manifest is checked against that commit after creation. Pre-commit logs accurately record the base HEAD and staged changes.

`build-source-binding.json` binds the successful build and audits to exactly the same manifest. No source or audit files changed between these checks or afterward. Only README and evidence documentation changed after the build.

## Verification

All commands ran in this checkout. `Scratch/opus_run.py` preserves raw logs, complete commands, timings and exit statuses in this directory.

| check | command | result |
|---|---|---|
| full build | `env LEAN_NUM_THREADS=6 lake build` | exit 0, 3,846 jobs, 181.9 seconds; first attempt |
| benchmark dependency | `env LEAN_NUM_THREADS=6 lake build Benchmark` | exit 0, 1.7 seconds |
| actual metrics and encoding | `env LEAN_NUM_THREADS=3 lake env lean Scratch/Packed101Audit.lean` | exit 0, 12.0 seconds; every guard passes |
| whole-tree axiom audit | `env LEAN_NUM_THREADS=3 lake env lean Scratch/ProofAudit.lean` | exit 0, 27.6 seconds; **23,803 declarations** |
| independent arithmetic | `python3 -B Scratch/check_packed101.py` | exact metrics, bit count, padding, piece count and privacy inequalities agree |
| source binding | `python3 -B Scratch/Packed101SourceManifest.py check` | all 459 file hashes match |

The axiom union is exactly `Quot.sound`, `Classical.choice`, `propext`. Perfect correctness, adaptive privacy, actual bounded simulator, exact encoding size and challenge solution all retain proof terms. No proof holes, axiom additions or challenge changes are introduced. All **14** dependencies match their locked revisions with clean tracked trees (`dependencies.json`). The challenge remains `aaf278948a4127f99ee6752c7cec4b9f9bd43615`; Lean remains `leanprover/lean4:v4.33.1`; Mathlib remains `0df444a360eaa60ab8c11dca51a86af692955474`. Lockfiles/toolchain are byte-identical to the original baseline. `Submission.lean` is byte-identical to P1a; its earlier comments retain historical sizes (`pins.json`).

## Integration and complete bytes

Opus101 supplies 101-bit labels, generic lane/replay lemmas, the regenerated arithmetic budget and a tighter closing proof. Astra retains P1a's complete fixed-bit-vector codec, 254-bit fields, 3-bit flags, 620-bit records and final-padding serializer. The standalone Opus labels-only `PackedLabels` codec is omitted; its raw historical audit and report remain intact and should be reproduced at its own immutable checkpoint.

The integration adjusts the two literal lane/piece-count bridges: 43,391 pieces, comprising 1,009 base pieces, 2,386 modulus-join labels and 39,996 pin lanes. Padding is emitted once outside that piece list. No per-label or per-vector padding remains.

| public component | bits |
|---|---:|
| three curve constants | 762 |
| 91 normalized rows | 23,387 |
| 91 exception entries | 728 |
| 5,770 conversion labels × 101 | 582,770 |
| 642 records × 620 | 398,040 |
| **before padding** | **1,005,687** |
| final canonical zero padding | **1** |
| **complete bytes × 8** | **1,005,688 = 125,711 × 8** |

The codec theorem round-trips **every** `Public` inhabitant with every byte tail. This includes all flags and arbitrary records throughout `Fin (2^620)`, independently of the honest bound `2M ≤ 2^620`. Actual zero and maximal values have the declared length; maximal values decode and re-encode exactly while retaining `[137, 42]`. Guards explicitly check the bit total, single padding bit, 26 widened rows, 84 moduli, 2,885 labels per coordinate and 43,391 pieces.

Queries remain unchanged, with 1,091 evaluation queries of headroom. The independent model reproduces the original baseline and computes the current counts separately; every used cast width has the same rounded answer count at 101 and 104 bits.

## Security closure and review

The common hidden/touch charge is now `2^-101 + 1/(p−1)`. Opus proves its scaled value at most `1/2 + 2^-152`, using `2^252 ≤ p−1`. The chain's constant bound is 1.408 units. For fewer than `2^100` queries, the excess `(2q₁+q₂)·2^-152` fits below `1/1000`; the unchanged challenge permits `q₁+q₂+2` units. Independent exact rational arithmetic verifies the worst vertex has about 0.728136 unit of room. Full-width external labels, adversary model and security target are unchanged.

Astra reviewed this privacy and machine delta at exact `2f7b9ca70f7a9c72ac4a24e98ddb97cb606e7ee8`. The coordinator independently checked its committed production manifest and preserved the public checkpoint. Final independent integration review is coordinator-owned.

## Attribution and historical evidence

Opus proposed and proved the 101-bit/privacy changes. Astra implemented P1a and this combined serializer/codec integration, derived independent counts and ran the integrated checks. Both worked under Souhail's direction; AI assistance is explicit. dnctse, Lazar955, psivesely, xinshudong, liucheng, ArgoMAC and cited research credits and upstream history remain preserved. All earlier reports and raw logs refer to their own immutable sources, not this integrated tree.
