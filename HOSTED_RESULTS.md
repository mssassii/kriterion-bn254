# Kriterion hosted results

Updated 28 September 2026 at 13:52 UTC. GitHub/Kriterion identity: `mssassii`.

**Both submissions passed hosted verification. The improved combined submission currently ranks first at 128,276 bytes.** It saves 1,846 bytes (about 1.42%) from the previous 130,122-byte record. Rankings can change before the 3 October 2026, 03:00 UTC closing time.

| Submission | Commit | Ciphertext bytes | Garbling queries | Evaluation queries | Hosted outcome |
|---|---|---:|---:|---:|---|
| [A1](https://kriterion.cc/s/dcdf2b68-3328-480f-8c1a-0a6f5a209476) | `719b09effea8b5ef544b8243dd9cd840636f963c` | 128,822 | 1,062,022 | 1,055,144 | Verified; all checks pass; review CLEAR |
| [Combined](https://kriterion.cc/s/89e2b245-1673-4476-a71b-7a4eb84bcc77) | `32f1fb34884ca33a84ac9dd4db687ca30187aeed` | 128,276 | 1,061,622 | 1,054,788 | Verified; all checks pass; review CLEAR |

The fixed limits are 1,759,967 garbling queries and 1,055,879 evaluation queries. Both candidates satisfy them in the hosted measurements. The combined entry has 1,091 evaluation queries of headroom. Hosted checks cover axioms, build, layout, lint and obligations. Both accepted entries’ axiom list is exactly `propext`, `Classical.choice`, `Quot.sound`.

The work builds on dnctse's `e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05` (130,122 bytes), with its complete upstream history and credits retained. Astra developed selective width-9 extraction; Opus developed the modulus-17 removal with a tighter valid privacy closure. Astra integrated both and one further width-9 row. Implementation, arithmetic checks and reviews used GPT-6 Astra and Claude Opus 5.5 under Souhail's direction. Formal and hosted verification, rather than agreement between models, determines admission.

Public source: [mssassii/kriterion-bn254](https://github.com/mssassii/kriterion-bn254).
Live ranking: [Kriterion scalar multiplication](https://kriterion.cc/c/scalar-multiplication).

No global-optimality or final-prize claim is made. Research targets for smaller encodings remain separate from these measured results.

The first submission is now marked SUPERSEDED because the same account submitted the better combined entry. Its checks and measurements remain verified. The current combined state is ON_BOARD, position 1, as observed at 13:52 UTC.
