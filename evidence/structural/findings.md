# Structural row research after the 125,711-byte checkpoint

Base: `857e88b66f91ce0c61ab0e86ff6d8b9e9bf91790`. These experiments do not change the construction or claim another ciphertext improvement.

`Scratch/StructuralAlgebra.lean` passes Lean in 2.4 seconds. For a nonzero digit, let the hidden point be `(a,b)` and the projective scale be `rho`. Reusing the Z-row delivery `rho(phi^4 x-a)` in a product with a second affine delivery factors the X quadratic exactly when its offset equals `2 rho a^2 = -2a K_z`. The file proves the exact residual and the necessary-and-sufficient relation for nonzero scales/input. Existing independent CRT/body offsets do not supply that relation; enforcing it needs a new construction and a privacy argument. This rules out merely reusing those independent offsets in this one expression, not all possible row sharing. The conditional factorization is useful groundwork, not a record-removal theorem for Submission.

`Scratch/structural_rows_model.py` reproduces the verified metrics, then models hypothetical record removals under the same moduli and a reoptimized shared two-stage schedule. It does not establish that any removed record can be recovered, nor validate the resulting privacy and simulator obligations.

| Hypothetical removed affine records per digit | Best modeled bytes in tested placements |
|---|---:|
| 0 | 125,711 |
| 1 | 117,800 |
| 2 | 109,940 |
| 3 | 102,180 |
| 4 | 94,572 |
| 5 | 87,166 |

The arithmetic clarifies the scale of change needed; it is neither an existence proof nor a global lower bound. See `record-removal-costs.json` for counts, query budgets and every tested placement. The allowed axiom union of the algebraic lemmas is the same three standard axioms. Production source, challenge pins and the verified candidate are unchanged.
