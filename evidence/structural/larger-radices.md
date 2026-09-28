# Larger digit alphabets: a concrete structural axis

This is an assessment, not a new scalar decomposition, row construction or privacy proof. `Scratch/digit_radix_research.py` verifies finite quotient arithmetic for Eisenstein pairs `(a,b)` representing `a+bω`, with `ω²+ω+1=0` and norm `a²-ab+b²`.

Let `U={±1,±ω,±ω²}`. The following explicit alphabets cover their quotient exactly once:

| radix | norm | complete residue alphabet | information count | optimistic bytes |
|---|---:|---|---:|---:|
| `2−ω` | 7 | `{0} ∪ U` | 91 | 125,711 |
| `4+ω` | 13 | `{0} ∪ U ∪ 2U` | 69 | 113,048 |
| `5+2ω` | 19 | `{0} ∪ U ∪ 2U ∪ (1−ω)U` | 60 | 107,867 |
| `(2−ω)² = 3−5ω` | 49 | `D7+(2−ω)D7` | 46 | 99,808 |

The information count is the least `d` with `norm^d ≥ r`. It is **not** a proved bounded representation length: the existing lattice reduction, digit recursion, termination and reconstruction certificates would need replacement. The finite checks use `ω=2,9,7,30` modulo7,13,19,49 respectively. The49 alphabet has digit norms0,1,3,4,7,9,12,13.

The byte column makes a strong optimistic assumption: retain exactly seven affine records and265 public bits per digit, all existing conversion material, and five curve records. It does not include additional feature/conversion data or the cost of the new row formulas. Norm49's nominal99,808 bytes leaves only192 bytes of room: one additional affine record per digit would cost3,565 bytes before query-driven schedule changes.

The norm13 case is the most concrete next algebraic test. It introduces only one extra unit orbit, `2U`, so its evaluator needs either a unit transform ofP or of2P. The original rows assume only unit endomorphisms, which act by multiplyingx/y by fixed powers of a root of unity. Doubling instead introduces a rational map: on the curve `x(2P)=(x^4−24x)/(4y²)`. A common denominator can make both alternatives polynomial, but expands the feature support. Merely computing2P publicly does not provide hidden affine deliveries of its coordinates from the508 existing Lamport labels; a construction must either derive those deliveries from shared features or supply additional conversion data. Selection of the digit's orbit is also secret.

For norm19, the `(1−ω)U` orbit introduces another non-unit map. Grouping two current norm7 digits gives the49-symbol alphabet directly, but evaluating the two original rows and combining them retains essentially their original record cost. Savings require a new joint row representation, not only changing the radix in the Horner decoder.

Promising next experiment: derive the norm13 mixed-unit/doubling row polynomials after common denominator clearing, then find an affine-delivery schedule that shares input features and count both its records and new conversion requirements. It must account for digit zero, exceptional inputs, normalization, curve membership and the adaptive privacy simulator. Neither failure of the current offset-sharing expression nor these optimistic counts proves a global size lower bound. Under100,000 bytes remains unresolved.
