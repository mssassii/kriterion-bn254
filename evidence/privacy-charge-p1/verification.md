# P1: byte-neutral privacy-charge refinement

Base: submitted combined source `32f1fb34884ca33a84ac9dd4db687ca30187aeed`.
Research branch: `codex/privacy-charge-p1`; the submitted branch `codex/integrate-h1` remains intact.
Idea: Opus's source analysis in `coordination/next-ideas.md`; implementation and proof integration by Astra under Souhail's direction.

Status: **full build and both audits passed**, all observed complete by 2026-09-28 13:34:38 UTC. The bounded experiment began at 13:30:36 UTC: about four minutes to full verification, one build attempt, no repair cycle. No width or codec experiment is included.

## Change and rationale

The hidden-hop and stage-one-touch charge changes from `4/2^104 + 1/(p−1)` to **`1/2^104 + 1/(p−1)`**. Each query has a fixed tag family, so the generic stage-one and stage-two case assembly uses a common maximum charge rather than adding charges across families.

The conversion/never-hot cases cost at most `1/2^104`. The digest, mask, final and touch-tail cases cost at most `1/2^128`. The key cases cost at most `2/2^128 + 1/(p−1)`, which is below the refined charge at 104 bits. The six affected case/tail comparison proofs are tightened, and the readable budget equalities and closed arithmetic share are updated. The final chain retains its conservative 1/3 per-charge share and the same valid two-unit constant allowance.

Seven existing proof files change: `Glue/Budget.lean`, `Hidden/CaseConv.lean`, `Hidden/CaseDigest.lean`, `Hidden/CaseKeyOff.lean`, `Hidden/StageOneKey.lean`, `Hidden/StageTwoTable.lean`, and `Flags/Touch.lean`, all under `Proof/Privacy/CRT/`.

`BudgetData.lean` remains unchanged: its historical closed query inequalities with numerators 8 and 4 remain true, looser arithmetic facts; they are not used to assert the new charge equality. The actual refined charge/share are proved directly in `Budget.lean`. No smudge, window or other constant error changes.

## Fixed construction and checks

`Construction/`, `Submission.lean`, all pinned configuration files, the challenge/security definition and `BudgetData.lean` are byte-identical to the base. Thus P1 is **not a ciphertext-size improvement**. Expected metrics remain **128276 bytes / 1061622 garbling / 1054788 evaluation**. `P1Audit.lean` checks those metrics, zero/maximal encodings, table/simulator counts and the exact refined charge equality. Whole-tree audit separately checks every construction/proof declaration.

All 14 dependency checkouts match their locked commits and have clean source trees (`dependencies.json`). P1's own source manifest preserves the submitted candidate's manifest unchanged; it records the new proof/audit files before the full build and is checked again after committing.

Commands from the repository root:

```sh
python3 -B Scratch/P1SourceManifest.py write
env LEAN_NUM_THREADS=6 lake build
lake env lean Scratch/P1Audit.lean
lake env lean Scratch/ProofAudit.lean
python3 -B Scratch/P1SourceManifest.py check
```

Use `check`, not `write`, when reproducing a committed source manifest. No publication or hosted verification is part of this experiment.

## Observed results and immutable source binding

- Full build: exit 0 on the first attempt, 3,844 jobs, including every affected generic case assembly, complete adaptive privacy, finite simulator and `Submission.solution` (`build-first.log`).
- P1 audit: exit 0; exact refined charge equality checked; metrics **128276 / 1061622 / 1054788**; zero and maximal encoding/decode guards pass (`audit.log`).
- Whole-tree axiom audit: exit 0; **23,742 declarations**, union exactly `Quot.sound`, `Classical.choice`, `propext` (`proof-audit.log`).
- Source manifest: **448 files**, SHA-256 **`8ac97107f82c0ee1f3860b68c5c6c06247a1eb3121e9559338c32557202aeafc`**. No Lean source changed during or after verification. The manifest is rechecked after committing this experiment.
- Every construction file, the solution field assignments, complete public codec, query/byte declarations, security definition and pinned configuration are unchanged. All 14 dependency checkouts remain at their exact locked revisions with clean source trees.

This proves that the factor-4 slack can be removed at the existing 104-bit width. It is **byte-neutral groundwork**, not an additional size improvement. This experiment stops here; no label-width change, packed codec, publication or submission is included.
