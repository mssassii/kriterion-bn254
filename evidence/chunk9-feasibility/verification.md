# Nine-bit chunk feasibility, before production migration

Base construction: `857e88b66f91ce0c61ab0e86ff6d8b9e9bf91790` (125,711 bytes). This is a separate research table and exact model, **not a complete solution or a measured 125,261-byte public ciphertext**. Production files remain unchanged.

## Checked results

`Scratch/chunk9_feasibility.py` constructs 29 chunks (28 of width9, last width2), replaces modulus256 with512, and uses first extraction width7 on `73,79,81,83,89,97,101`, width8 on the other76 odd rows. The kept width is `max width0 (bitLength (m-1))`. This last change matters: for moduli above256 the kept width must be9 even when `ell-5=8`.

| quantity | exact checked value |
|---|---:|
| proposed complete bytes | 125,261 |
| proposed bit count | 1,002,087 + 1 padding bit |
| actual generic Lean garbling budget at research table | 1,062,388 |
| actual generic Lean evaluation budget at research table | 1,055,556 |
| evaluation headroom | 323 |
| conversion labels / coordinate | 2,864 |
| record bits | 621 |
| pins / coordinate | 195 |
| total joins / coordinate | 1,427 (225 unpublished chunk joins) |
| published joins / coordinate | 1,202 |
| proposed serializer pieces | 42,803 |

Exact rational arithmetic gives total constant error **0.6360604892571928** units of `2^-100`; the worst vertex of the current101-bit query-charge inequality leaves **1.363939510742807** units. This recomputes all pad biases and both smudge terms; the earlier approximate0.635932 figure omitted the unchanged small remainder. Exact fractions are in `model.json`.

`Scratch/Chunk9Feasibility.lean` passes in isolation, initially12.3 seconds and5.3 seconds with the added actual-budget guards. It proves:

- `correctTable`: positivity, pairwise coprimality, wrap bound, power-of-two row and every selected odd-row condition for the explicit research table;
- `records_fit`: honest records fit621 bits;
- `rows_ok`: all83 new reach certificates pass the kernel;
- `word_target`: every required odd-row conversion target is the word value of an actual input below the field modulus;
- exact equality of the generic `Entry.garbleBudgetOf` and `evaluateBudgetOf` counts to the numbers above, and agreement of `table.convBlocks`;
- product equals twice the current product and the current conservative smudge share remains valid.

The certificate recurrence and its soundness proofs are adapted from the inherited `Hidden/Reach.lean`. Radix512 exceeds all odd moduli, so each of the first28 chunks can contribute every residue. The final witness chunk is zero; the admissibility bound is3 and `3*512^28 ≤ p`. The minimum proved certificate slack is96. Named axiom checks show only `propext`, `Classical.choice`, `Quot.sound`.

Raw commands and exit statuses: `model-second.*`, `lean-first.*`, `lean-metrics.*`. The first model invocation had a Python syntax typo (`else512`); it performed no arithmetic and is preserved as the failed `model.*` run. No build is left running.

## Production migration surface

1. **Schedule and arithmetic.** Introduce the exact table/width selector, new kept-width formula, kernel facts, regenerated budget data and pad layouts. Replace84-row power-of-two facts about256 with512, and bounds439 with512 where appropriate. Tag slots remain below65536 and answer indices below64; these facts must still be re-proved at the new table.
2. **Reachability.** Integrate the checked radix512/29-chunk certificate walk and field-input construction into `Proof/Privacy/CRT/Hidden/Reach.lean`. Update the chunk witness proof and the last-chunk/never-hot classification. All four last-chunk values are now realizable: `3*2^252 < p`. The existing width8/9 shape lemma's formula `keep=max width0 (ell-5)` is unsuitable for this schedule; use the explicit checked facts.
3. **Replay RAM.** `Construction/Simulator/CRT/ReplayChunks.lean` currently reserves256 leaves and32768 cast cells per chunk. Nine-bit chunks need512 and65536 respectively. `ReplayMachine.coordCells` also has256-cell tree/material scratch blocks. Grow the scratch offsets and move `leafBase`/`modBase` apart; prove the changed frame/disjointness contracts in `ReplayChunks`, `ReplayCoord`, `ReplayWords`, `ReplayDispatch`, `ReplayMachine` and their callers. A literal width change alone would create overlapping memory regions.
4. **Finite size/cost bounds.** `ReplayCost` and `ChunkShape.widthSmall` use `≤8`; generalize to9 and redo conservative bounds. The overall machine allowance is much larger than these local changes, but the actual proof still needs completion. Exact generic oracle query counts above do not establish those machine fuel/size proofs.
5. **Public codec and stage1.** Set2,864 labels,195 pins,1,427 joins and621-bit records. The top record limb grows108→109 bits. Recompute42,803 pieces and retain the generic all-public codec with one final pad bit. Update record, source-reading, wire, serialization and machine proofs.
6. **Complete candidate checks.** Full build, actual `Submission` metric/encoding roundtrips, complete declaration axiom audit, independent arithmetic, pins and exact source binding. The 323-query headroom is real but narrow; no500-query discretionary reserve fits this modeled optimum.

Estimated work before inspecting the full repair frontier: roughly1–3 hours for production migration and proof/build cycles. This estimate is not a completion guarantee. The coordinator requested this feasibility checkpoint and explicitly deferred the full production migration; no production migration was started. The modeled450-byte saving is useful incrementally but does not resolve the25.7KB structural gap to100,000 bytes.
