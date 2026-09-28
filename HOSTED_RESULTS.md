# Kriterion hosted results

Updated 2026-09-28 15:23 UTC. Account: `mssassii`.

**Best confirmed hosted result from this work: 125,711 bytes.** The requested 125,711-byte target has passed hosted verification. Consult the live leaderboard for the current rank; a current rank does not establish the final outcome.

| Candidate | Submitted commit | Complete bytes | Garbling / evaluation queries | Verification |
|---|---|---:|---:|---|
| [A1](https://kriterion.cc/s/dcdf2b68-3328-480f-8c1a-0a6f5a209476) | `719b09effea8b5ef544b8243dd9cd840636f963c` | 128,822 | 1,062,022 / 1,055,144 | All five hosted checks pass; review CLEAR |
| [Astra + Opus](https://kriterion.cc/s/89e2b245-1673-4476-a71b-7a4eb84bcc77) | `32f1fb34884ca33a84ac9dd4db687ca30187aeed` | 128,276 | 1,061,622 / 1,054,788 | All five hosted checks pass; review CLEAR |
| [Packed public](https://kriterion.cc/s/115fcdd2-6760-4648-811e-65d00c39382c) | `cc221c36a4f8e991d2c983b4ec748d40805ea064` | 127,875 | 1,061,622 / 1,054,788 | All five hosted checks pass; review CLEAR |
| [Packed + 101-bit labels](https://kriterion.cc/s/8e10e0d6-d6fe-4a45-969f-95c76cda5ce8) | `857e88b66f91ce0c61ab0e86ff6d8b9e9bf91790` | 125,711 | 1,061,622 / 1,054,788 | All five hosted checks pass; review CLEAR |
| [W1 window refinement](https://kriterion.cc/s/f35df4f4-af76-4e42-8dbc-0e0de872937c) | `684c3d826c4b54c6f5d501dff6489b49ebf6f97b` | 125,450 (local) | 1,060,976 / 1,054,152 (local) | Hosted pending; local checks pass |

The 125,711-byte checkpoint passed at 15:17:34.910 UTC on 28 September 2026 and ranked first on the board refreshed immediately afterward. Raw snapshots are preserved under `evidence/hosted/`. Earlier accepted entries may be marked SUPERSEDED when a smaller submission from the same account is admitted; their successful checks remain valid for their exact commits.

Current challenge revision 16 limits garbling to 1,759,967 queries and evaluation to 1,055,879. The W1 local counts leave 1,727 evaluation queries of headroom. The original challenge, function, adversary model, 128-bit external labels, dependency pins and permitted axioms are unchanged.

Astra implemented the selected extraction schedule, complete public bit packing and integration. Claude Opus supplied the CRT-factor changes, 101-bit labels, tighter privacy closure and the refined curve-window curve-window charge. Both cross-reviewed immutable source; the coordinator independently checked arithmetic, reviewed source manifests, published and submitted the commits. Original authors and upstream history are retained. Model agreement does not substitute for the Lean proofs and hosted checks.

[Public source](https://github.com/mssassii/kriterion-bn254) · [Live leaderboard](https://kriterion.cc/c/scalar-multiplication)

Under 100,000 bytes remains unresolved. The best verified result is not a global minimum. Research projections are separate from the measurements above. Challenge closes 2026-10-03 at 03:00 UTC.
