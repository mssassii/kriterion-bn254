# Intuition: the sign row on psivesely's CRT-residue delivery of ArgoMAC

**Draft status:** the fallback schedule has not been built in Lean. Its independently computed
target is **169,184 bytes** of public ciphertext; updated proof terms and audit expectations remain
to be checked on the build VM. This document describes the intended construction and existing proof
architecture, not a completed verification of this branch.

This entry garbles BN254 scalar multiplication at that target size.
Garbling makes at most **1,062,038** oracle queries (gate 1,759,967) and evaluation at most
**1,054,570** (gate 1,055,879). Both figures are the expected exact bounds to be checked against the types of
`garbleProgram` and `evaluateProgram`.

It is psivesely's CRT entry (`psivesely/kriterion-bn254-crt`, commit `de8f397`, 182,936 bytes)
with Lazar's sign row in the `Y` slot of every digit. The sign row reads three affine encodings
instead of four and, with the coefficient cut, publishes one constant instead of two, so a digit
reads 7 encodings and publishes 3 constants (section 1.1). It also vanishes at a second exceptional
input, which the exception gadget covers with a 12-byte entry per digit (sections 1.2 and 6).
Sections 1.1, 1.2, 6 and 11.6 describe the sign-row change. This branch additionally retunes the
first extraction width to 8 for 67 odd moduli, retaining width 7 for the other 17 (section 3.6).

psivesely's entry keeps the ArgoMAC structure of xinshu's entry (`xinshudong/bn254-entry`, commit
`bf53ea4`, 3,363,376 bytes): 91 digit MACs whose rows read affine encodings of the input
coordinates. It changes how the evaluator obtains those encodings. xinshu's entry delivers them
through switch systems whose published size grows with the number of encodings times the number of
chunks. psivesely's entry delivers them through the CRT-residue projectivization of Duty-Free Bits
(Khambhati, Bhattacharya and Heath), as ePrint 2026/2100 (Khambhati, Feickert, Lewe and Tiwari) does
for the field encodings of Argo MAC: each input coordinate is turned once into one-hot labels of its
residues modulo 85 small moduli, and each encoding then costs one 78-byte record. The conversion of
a coordinate is 54,592 bytes whatever the number of encodings. The rows are gated by masks keyed by
the curve check, the exception gadget is a hash digest, and the oracle is the field hash alone. The
proof architecture (the obligation, the lazy oracle, the chain of games, the public-first hop, the
opening and the closed simulator machine) is xinshu's, adapted to the CRT layer.

The baseline had proofs for every field of the challenge's `Solution` record, with no `sorry`, and
only `propext`, `Classical.choice` and `Quot.sound` in its axiom audits. The modified branch still
needing build and audit validation supplies proof terms without new admissions.

---

## 1. What the evaluator must learn

ArgoMAC (Eagen and Lai) turns the evaluator's 508 Lamport labels (254 bits of `x`, 254 of `y`) into
91 elliptic-curve MACs, one per digit of the secret scalar in base `2 − ω` (liucheng's 91-digit
decomposition). Each digit's MAC is three rows, low-degree polynomials in the input `(x, y)` whose
coefficients depend on the digit: the Jacobian `X` and `Z`, and in the `Y` slot the sign row `S`.
The rows read *affine encodings*: values `a_e·v + b_e` with `v = x` or `v = y`, a secret slope `a_e`
and a secret offset `b_e`, which the evaluator learns without learning `a_e` or `b_e`.

The `X` and `Z` rows are the Jacobian rows of BABE as Lazar introduced them to the contest. The `Y`
slot carries Lazar's sign row instead of the Jacobian `Y` (section 1.1). It reads three encodings,
where psivesely's entry, with Lazar's four-encoding `Y` row, read four. Lazar's coefficient cut puts
each coefficient into a slope instead of publishing it; on the sign row it leaves one published
constant, so a digit publishes 3 constants. Per digit the rows read 4 encodings of `x` and 3 of `y`.
With the 5 encodings of the curve check (`x3, x5, x7` of `x`, `y4, y6` of `y`) there are 642
encodings: `S_x = 367` of `x` and `S_y = 275` of `y`.

In xinshu's entry each coordinate is cut into chunks, and each chunk publishes one join holding one
field element per encoding. The size is about `chunks · encodings · 32` bytes. The CRT delivery
separates the two factors: the chunks are converted once per coordinate, and the encodings are paid
per encoding.

### 1.1 The sign row

Write `K = (a, b)` for a digit's offset, `Q = (u, v)` for its image of the input and `R = Q + K`
for its MAC point. The `X` and `Z` rows are the Jacobian `X` and `Z` of `R`, with a randomiser `ρ`
as Jacobian weight. The decoder does not need the whole Jacobian `Y`: `x_R = X/Z²` fixes `y_R` up
to sign, so the `Y` slot only has to carry the sign. It carries the sign row `S = τ²·S0`, with

```
S0 = 4b³v² + 3ab(27 − b²)u² + (b⁴ + 54b² − 243)v − 36b³
```

On the curve and for `u ≠ a`, `S0 = L²·y_R`, where `L = 2bv + 3a²u + 9 − b²` is the tangent at
`−K` scaled by `2b`. `L²` and `τ²` are squares, so when `L ≠ 0` the sign row has the quadratic
character of `y_R`, and the decoder recovers

```
y_R = S^((p−1)/2) · (x_R³ + 3)^((p+1)/4)
```

by Fermat: `p ≡ 3 (mod 4)`, so the second factor is a square root of `y_R²`, and the first is
`±1`, the character of `y_R`. `τ` is a new nonzero randomiser per digit, independent of `ρ`
(section 11.6 says why).

The sign row is `S = s0 + s2·y + s4·x² + s5·y²`: it has no `x` and no `xy` term, so it reads three
encodings, `cubic` (of `x`, read with `x²`), `y8` (read with `y`) and `y10` (read with 1). The
coefficient cut publishes only `s4` minus the offset of `cubic`; the slopes carry the rest. The
`cubic` slope is `−t` with `t = (s0 − b_{y10})/3`, the `y8` slope is `t + s5` and the `y10` slope is
`s2 − b_{y8}`. The `cubic` slope contributes `−t·x³`. On the curve `x³ = y² − 3`, so that term is
`t·(3 − y²)`: the `y8` slope absorbs the `y²` part, and `3t` plus the offset `b_{y10}` is the
constant `s0`. So the row is exact on the curve. Off the curve it would be off by
`t·(y² − x³ − 3)`, but the evaluator refuses an off-curve input before its first query. Against the
four-encoding `Y` row, the mixed encoding, which carried the `xy` term, is gone; and where that row
shifted by a uniform randomiser and published its constant, the sign row shifts by `t`, which the
constant determines, so the constant is not published.

### 1.2 Three degenerate inputs

A row cannot be decoded where `Z = 0` or `L = 0`:

- `Q = K`, the doubling case: `X = Z = 0`, and the MAC is `2Q`;
- `Q = −K`: `Z = 0 ≠ X`, and the MAC is the identity, which the decoder returns directly;
- `Q = 2K`: the tangent at `−K` meets the curve again at `2K`, so `L = 0` and `S = 0 ≠ Z`, and
  the MAC is `3K = (3/2)·Q`.

With `P` the input point and `φ(P) = Q` its image under the digit, the decoder reads the first case
as `2·φ(P)` and the third as `(3/2)·φ(P)`, with `3/2` in the scalar field. In both it needs the
digit, which the exception gadget releases (section 6). psivesely's entry, which decodes `y_R` from
the Jacobian `Y`, has only the first.

---

## 2. The CRT idea

Let `M = m_1 · ... · m_85` be the product of 85 pairwise coprime moduli (section 3.6). If the
evaluator holds, for each modulus `m`, the residue `(a_e·v + O_e) mod m` of an integer
`a_e·v + O_e` below `M`, the Chinese remainder theorem gives the integer, and its value modulo `p`
is the encoding `a_e·v + (O_e mod p)`.

The construction obtains those residues in two layers.

1. **Conversion** (per coordinate, independent of the encodings). From the Lamport labels of `v`,
   the evaluator obtains, for each odd modulus `m`, a *one-hot vector* of `m` labels indexed by
   `Z_m` whose *hot* index is `v mod m`. For `m = 256` the one-hot vector is the leaf vector of the
   lowest 8-bit chunk. Section 3.
2. **Body** (per modulus, all encodings at once). Each slot `ρ` of a one-hot vector hashes to a
   *pad vector*: one digit modulo `m` for each encoding. The garbler publishes, per encoding and
   modulus, one residue join. The evaluator can hash every slot except the hot one, and the join
   supplies what it misses. Section 4.

The conversion of a coordinate publishes 3,412 blocks (54,592 bytes). The body publishes, per
encoding, the 85 residue joins and one hint bit, packed into a 78-byte record.

---

## 3. The conversion

### 3.1 Labels

A label is a 128-bit block. Each coordinate has one global offset `Δ`. For an input bit `b` with
garbler label (mask) `Z`, the evaluator holds `Z ⊕ b·Δ` (free XOR). A *one-hot vector* of `N` labels
for a value `α < N` has the garbler's masks at every index and the evaluator's labels equal to them
except at the hot index `α`, where they differ by `Δ`. The evaluator can hash the *cold* labels but
never the hot one.

An *arithmetic label* for a value `w` in `Z_{2^l}` is a vector of 128 *lanes* in `Z_{2^l}`: garbler
mask `A`, evaluator label `A + w·Δ⃗`, where `Δ⃗` is `Δ` read lane by lane as 0 or 1 (Heath's word
labels). Sums of arithmetic labels and products by public integers need no queries and publish
nothing.

A *cast* hashes a boolean leaf label into `128·l` bits and reads them as the lanes of an arithmetic
label over `Z_{2^l}`. The lanes are aligned to the 128-bit blocks of the answers: `⌊128/l⌋` lanes per
block, so no lane straddles two blocks. A *pin* of `l` blocks gives the evaluator the cast of the hot
leaf: `P = Σ_α A_α + Δ⃗`, from which the evaluator subtracts the casts of all cold leaves.

### 3.2 Chunks and trees

Each coordinate `v` (its 254 little-endian bits) is cut into 32 chunks: 31 of 8 bits and one of 6.
Per chunk, a *tree* turns the chunk's bit labels into a one-hot vector over its `2^k` values. A level
of `2^n` labels grows by one bit as in xinshu's `bin-to-hot`: every slot `s` hashes to a material
`y_s`; the new level has `G_s ⊕ y_s` at `s` and `y_s` at `s + 2^n`; the garbler publishes one join,
`(⊕_s y_s) ⊕ z` with `z` the mask of the new bit. The evaluator hashes every slot except the active
one and solves the active material from the join. A tree over `k` bits starts from the free pair
`(z_0 ⊕ Δ, z_0)` and publishes `k − 1` joins.

Every leaf of a chunk is then cast to an arithmetic label over `Z_{2^14}` (8 answers per leaf), and
the chunk publishes a 14-block pin. The evaluator ends with the arithmetic labels
`A_{c,α} + [α = α_c]·Δ⃗` of every leaf `α` of chunk `c`, where `α_c` is the chunk's value.

### 3.3 Truth-table words

For each odd modulus `m` the garbler and the evaluator form the same free linear combination of the
chunk casts, with public coefficients `T_{c,m}(α) = (α·2^{8c}) mod m`:

```
W_m = Σ_c Σ_α T_{c,m}(α) · A_{c,α}      (reduced to ℓ_m bits)
```

Since exactly one leaf per chunk is hot, the evaluator's word is an arithmetic label of
`σ_m = Σ_c T_{c,m}(α_c)`, and `σ_m ≡ v (mod m)` with `σ_m ≤ 32·(m − 1) < 2^{ℓ_m}`, where
`ℓ_m = bitlen(32·(m − 1))` is 10 to 14 bits. These per-modulus tables (Heath's) keep the words short.
They cost nothing.

### 3.4 Extraction

The word `W_m` must become boolean labels of the bits of `σ_m`. Extraction does this in three
*stages*, as in the Duty-Free Bits reference code: stage 0 extracts bits `0..w0 − 1` (width
`w0 ∈ {7,8}`, casts of width `ℓ`); stage 1 extracts bits `w0..ℓ − 2` (width `ℓ − w0 − 1`, casts
of width `ℓ − w0`); stage 2 takes
the top bit for free. A stage over `w` bits reduces the remaining word to `w` bits, takes its low
lane bit as the first bit label, builds a tree over `w` bits, casts every leaf, and publishes the
tree's `w − 1` joins and a pin. The evaluator's order is forced by data dependencies: at level `n` it
reads the class sums of the leaves below the active node from the pin, peels bit `n` from them, and
only then solves the level's join. The remaining word is then divided by `2^w` (exact, since the
extracted part is subtracted first).

### 3.5 From bits to a one-hot vector over `Z_m`

- **Kept one-hot.** Stage 0's leaf vector is a one-hot vector of `σ_m mod 2^w0`.
- **Growth.** It grows by `k0 − w0` bits from stage 1, with the tree step and one join per bit,
  to `k0 = max(w0, ℓ − 5)` bits. The fallback needs at most one growth bit.
- **Reindex.** Slot `ρ < m` of the new vector is the XOR of the kept slots `α ≡ ρ (mod m)`. Since
  `2^{k0} ≥ m` for every modulus, no class is empty, and the hot slot is `(σ_m mod 2^{k0}) mod m`.
  Free.
- **Folds.** Each remaining bit `j = k0..ℓ − 1` rotates the hot index by `b_j · (2^j mod m)`: every
  slot hashes to a material, the garbler publishes one join, the evaluator solves the hot material,
  and the new vector is `h'[ρ] = h[ρ] ⊕ u_ρ ⊕ u_{ρ − s_j}` (the fold of the Duty-Free Bits code).

The result is a one-hot vector over `Z_m` whose hot index is `σ_m mod m = v mod m`. The active slot at
a tree level of `2^n` entries is `value mod 2^n` at every level; the construction states it that way
throughout (a reference evaluator that read the second grown level from the low 7 bits failed at
`v = p − 1`).

### 3.6 The table

The moduli are every prime from 17 to 439 (79 primes), the prime powers 49, 81, 121, 125, 169, and
256: 85 pairwise coprime moduli whose product `M` has 623 bits (`log2 M = 622.26`). Every odd modulus
uses `ℓ = bitlen(32·(m − 1))`, stage widths `(w0, ℓ − w0 − 1, 1)`, and
`k0 = max(w0, ℓ − 5)`, with `k0 − w0` growth bits and `ℓ − k0` folds. The real table chooses
`w0 = 8` for 67 odd moduli and `w0 = 7` for 17; the generic T9 definition remains unchanged.
A modulus publishes `4ℓ − 2w0 − 3` blocks (21 to 37 in the selected table). The odd rows
publish 2,742 blocks and the chunks 670, giving 3,412 blocks per coordinate. Compared with all
width-7 rows, this saves `2 × 67 = 134` blocks per coordinate while retaining 1,309 queries of
evaluator headroom. Using width 8 for all odd rows would exceed the evaluator gate at 128 bits.

---

## 4. The body, the records and the wrap hint

### 4.1 Pad vectors and residues

For each modulus `m` and each slot `ρ` of its one-hot vector, the slot's label is hashed into a pad
integer of `256·q` bits (`q` answers), read as `S` digits modulo `m` (one per encoding of the
coordinate) by the *fraction reading*: digit `e` is `⌊u·m^S/2^{256q}⌋ / m^e mod m`. The number of
answers is `q = ⌈(bitlen(m^S) + 120)/256⌉` for odd `m` (120 bits of slack; the largest pad is 3,584
bits) and `q = ⌈S/32⌉` for 256 (one byte per encoding).

The garbler's residue of encoding `e` is `R_{e,m} = Σ_ρ ρ·V_ρ[e] mod m`, and it publishes the join
`J_{e,m} = Σ_ρ V_ρ[e] + a_e mod m`. The evaluator hashes the `m − 1` cold slots and computes

```
L_{e,m} = Σ_{ρ≠hot} ρ·V_ρ[e] + hot · (J_{e,m} − Σ_{ρ≠hot} V_ρ[e])  =  R_{e,m} + (v mod m)·a_e   (mod m)
```

This is xinshu's scale-hot evaluation over `Z_m` instead of `F_p`.

### 4.2 Reconstruction and the wrap hint

The garbler's CRT offset is `O_e = crt(R_{e,·})`, uniform below `M`; the evaluator's CRT value is
`w = crt(L_{e,·}) = (a_e·v + O_e) mod M`. The integer `a_e·v` is at most `(p − 1)²`, so `a_e·v + O_e`
exceeds `M` only when `O_e > M − B` with `B = (p − 1)² + 1`. The garbler publishes the *wrap hint*
`h_e = [O_e > M − B]`, and the evaluator adds `M` to `w` when `h_e = 1` and `w < B`. Since `2B ≤ M`,
this recovers `a_e·v + O_e` exactly as a natural (`wrapHint_exact`), and its value modulo `p` is the
delivered encoding `a_e·v + (O_e mod p)`. The hint is set with probability `(p − 1)²/M`, about `2^-115`, so it is
nearly always 0; it costs no bytes because it shares the record (section 4.3).

### 4.3 Records

The record of encoding `e` is `h_e·M + Σ_i J_{e,i}·Π_{i'<i} m_{i'}` (mixed radix in modulus order),
a natural below `2M < 2^624`, published in 78 bytes. The evaluator reads `h_e = ⌊record/M⌋` and the
joins by division.

---

## 5. Gating the rows: masks keyed by the curve check

The point rows are correct only on the curve. The curve check (xinshu's) turns the 5 curve
encodings into a value `t'` that equals the garbler's secret `t` exactly when the input is on the
curve. The evaluator hashes the low 128 bits of `t'` under a key tag into a mask key `K`, and reads
from `K` a mask `π_e` for each of the 637 row encodings (the curve encodings carry no mask). The
garbler sets the row offset to `b_e = (O_e mod p) − π_e`; the evaluator's row value is its delivered
encoding minus `π_e`. Off the curve `t' ≠ t`, the evaluator cannot compute `K`, and every row value
is masked. This is the masking of Duty-Free Bits' Embryo construction, with the curve check as the
validity test. It replaces xinshu's gating, in which the point encodings' switch system runs on
labels whitened by pads keyed on `H(t)`.

Masks are read by xinshu's three-block rule `sampleFp` (three 128-bit blocks, reduced modulo `p`).
Per digit, the three *collectors* (the `X` row's `x9`, the sign row's `cubic` and the `Z` row's
`x9`, 273 in all) each take two answers of their own; the other 364 row encodings are paired, three
answers per pair: 1,092 answers.

---

## 6. The exception digest

A digit's MAC fails at two *exceptional* inputs of the curve, which the garbler knows: the input at
`Q = K` and the input at `Q = 2K` (section 1.2). xinshu's gadget lets the evaluator detect the first
through a 6-byte entry per digit. Here the entry has 12 bytes, six slots per exceptional input: kind
`k` (0 for `Q = K`, 1 for `Q = 2K`) at slot `6k + index`. The entry is unlocked by a hash digest of
the input's own labels: each of the 508 labels `Z_{κ,i} ⊕ b·Δ_κ` is hashed with the bit `b` in the
tag, the key of an exceptional input is the XOR of the 508 hashes at its bits, and the mask byte of
its slot is the low byte of the hash of that key at its *final site* `s = 2o + k` (digit `o`). The
garbler hashes both labels of every position (1,016 queries) and one final per exceptional input of a
nonzero digit (at most 182); the evaluator hashes its 508 labels and asks both final sites of every
digit at its own key (690 queries). At an exceptional input of either kind the evaluator's key equals
that input's key, and the slot of that kind unmasks.

---

## 7. One random function

Every query of the entry is to the challenge's field hash. The two permutation families are unused,
and the entry's index types for them are `Empty`. A query is made at `label + 2^128·tag`, where the
tag names the site: family (chunk tree, chunk cast, extraction tree, extraction cast, growth, fold,
body, masks, digest labels, digest finals, key), coordinate, modulus index, stage, level, slot and
part. Tags are below `2^40`, so the inputs are below `p` and distinct sites never share an input.
Correctness does not use this; privacy does (section 11).

---

## 8. Why the ciphertext is 169,184 bytes

| Field | Contents | Bytes |
|---|---|---:|
| `curve` | 3 curve-check constants × 32 | 96 |
| `rows` | 91 digits × 3 constants × 32 | 8,736 |
| `exception` | 91 digits × 12-byte entry | 1,092 |
| `crtX` | conversion of `x`: 3,412 blocks × 16 | 54,592 |
| `crtY` | conversion of `y`: 3,412 blocks × 16 | 54,592 |
| `recX` | 367 records × 78 | 28,626 |
| `recY` | 275 records × 78 | 21,450 |
| **total** | | **169,184** |

Every field has a fixed width and there is no tag, so every public value encodes to the same
length (`Wire.encoding_length`). The conversion blocks are 65 percent of the total and do not depend
on the number of encodings; each further encoding would cost 78 bytes. Against psivesely's entry,
the sign row saves 91 records (7,098 bytes) and one row constant per digit (2,912 bytes), and the
second exceptional case adds 6 bytes per digit (546 bytes). The fallback schedule then saves
another 4,288 bytes across the two coordinates.

---

## 9. Query counts

Per coordinate, the garbler hashes every slot of every structure and the evaluator every slot but
the hot one:

| Part | Garbling `x` | Garbling `y` | Evaluation `x` | Evaluation `y` |
|---|---:|---:|---:|---:|
| chunk trees and casts | 71,936 | 71,936 | 71,458 | 71,458 |
| extraction, growth, folds (84 odd moduli) | 265,641 | 265,641 | 263,500 | 263,500 |
| body pads (85 moduli) | 217,950 | 166,643 | 216,976 | 165,895 |
| **coordinate** | **555,527** | **504,220** | **551,934** | **500,853** |

| Fixed part | Garbling | Evaluation |
|---|---:|---:|
| mask key | 1 | 1 |
| masks | 1,092 | 1,092 |
| exception digest | 1,198 | 690 |

Totals: 1,062,038 garbling and 1,054,570 evaluation queries. The evaluation count is the same for every
input, since every one-hot vector has exactly one hot slot. The budgets are sums over the 85 moduli
in `Construction/CRT/Entry.lean`; their `decide +kernel` certificates in
`Construction/CRT/BudgetFacts.lean` await a build for this draft.

---

## 10. Perfect correctness

Correctness holds for every tape, every hash function and every input on the curve (the evaluator
refuses an off-curve input before its first query). It is stated wire by wire for an arbitrary hash
function, with the answers at the hot positions as free parameters:

- every tree, growth and fold level gives the evaluator `mask ⊕ bit·Δ` at every slot and the solved
  hot material;
- every cast and pin gives `A + [hot]·Δ⃗`; every word is an arithmetic label of `σ_m`;
- every extraction stage gives the bit labels of its bits and the exact remainder;
- the body gives `R_{e,m} + (v mod m)·a_e mod m`, and `wrapHint_exact` gives `a_e·v + O_e`;
- the curve check releases `t`, the key and masks match the garbler's, the rows are the Jacobian `X`
  and `Z` rows and the sign row at every on-curve input, the digest unlocks every exceptional digit
  of either kind, and the decoder's chain (the sign row's character, the two gadget cases, the
  identity at `Q = −K`) gives the scalar multiple.

Nothing in the chain depends on the tags, the pad slack or the oracle's values. The statement over an
arbitrary hash function also serves the privacy proof, which runs the garbler on answer tables with
the hot positions overridden.

---

## 11. The privacy argument

### 11.1 The chain

The obligation, the lazy oracle and the shape of the chain are xinshu's. The chain is

```
G0 → G0T → G0U → G1U → HW → H → I → M
```

- `G0 → G0T`: the mask key's input is a labelled query, so the real game is the game on an answer
  table indexed by tags. The budget conservatively retains `1,759,967/p`, using the fixed
  garbler-query gate instead of the smaller actual count 1,062,038; the current table-hop proof
  in fact establishes zero cost.
- `G0T → G0U`: every pad vector and every mask, read from a uniform integer by a slightly biased
  reading, is swapped for an exactly uniform value (the pad-slack and `sampleFp` biases).
- `G0U → G1U`: the garbler's hidden entries (the hot slot of every one-hot structure, the other
  bit's digest positions and the finals of the exceptional inputs other than the input, and off the
  curve the key and the masks) are deleted from the oracle. The adversary finds one only by guessing
  a label `E ⊕ Δ` or a field
  element, `4/2^128 + 1/(p − 1)` per query. One event is charged once instead of per query: a curve
  encoding's CRT offset in the wrap window, where its hint could pin the curve mask; its mass is below
  the wrap-hint term of section 11.3.
- `G1U → HW`: the public-first hop. The published value is drawn first, uniform, and the view is
  reconstructed from it (sections 11.2 to 11.5).
- `HW → H`: the rows are replaced by the lift sampler; xinshu's opening and kernel bound, with the
  sign row's second scale (section 11.6).
- `H → I`: the pads are swapped back.
- `I → M`: the closed simulator machine (section 12).

### 11.2 The conversion core: solving inverts garbling

Fix the input. Every join and pin of the conversion and every residue join of the body is a hidden
answer (the hot slot's material, the hot leaf's cast or the hot pad vector) combined with values
the evaluator can compute. The map from the hidden answers to the published conversion material is
a bijection between sets of equal size, and its inverse is the honest evaluator's own solving
procedure, which recovers every hidden answer from the published values. This is the correctness
statement of section 10 read with the hot answers as free parameters. A bijection sends the uniform
law to the uniform law, so the published conversion material is exactly uniform and independent of
everything else the evaluator sees. The fused extraction, whose evaluator uses a pin before the join
of the same level, needs no special treatment: the argument uses only that the procedure is a function
of the published values that recovers every hidden answer.

In the random-oracle model this replaces the circular correlation robustness that Duty-Free Bits
assumes: the hidden answers are never installed, the view does not involve `Δ`, and a query at a
hidden label succeeds with probability `2^-128`.

### 11.3 The wrap hint in the proof

After the pad swap the CRT offset `O` is uniform below `M`. The map `O ↦ w = (a·v + O) mod M` is a
bijection, and off the event `O > M − B` the real hint is 0, the real integer is `w` and the row
offset is `(w − a·v) mod p`: exactly the ideal values with `w` uniform. The event has probability
`(p − 1)²/M` per encoding. The chain charges it for all 642 encodings, twice, because the proof flags
the two-sided window `[0, B − 1) ∪ (M − B, M)` of the CRT values (it cannot see `a_e·v`, so a value
with the hint set may land at either end), plus `273·p/M` for the collectors' constants:
`smudgeError = (1284·(p − 1)² + 273·p)/M ≈ 2^-104.74`.

### 11.4 What the simulator programs

In the ideal game the simulator learns the output only after the adversary's input. It replays the
honest evaluator on the lazy oracle up to and including the non-collector masks, reconstructs every
row value, solves the target of each digit's three collectors from the output (the target rows are
the opening's lifts, section 11.6), and programs each collector's mask: 546 hash answers, each pair a
uniform `sampleFp` preimage of the needed field element (xinshu's preimage machinery). The CRT layer
itself is never programmed. This works because
each row is affine in its collector's value with a nonzero coefficient (1, `x²` or 1; `x ≠ 0` on
BN254, because 3 is a quadratic non-residue modulo `p`), and the collector's mask pays for the row's
constant: for a fixed delivered value, the map from the constant to the mask is a bijection of `F_p`.

### 11.5 Off the curve

Off the curve the evaluator evaluates the whole CRT layer on its raw labels, and by sections 11.2
and 11.3 everything it obtains there is uniform. It cannot compute `K`, so every mask is hidden, the
row offsets contain hidden masks, and the row constants are uniform. The curve check's delivered
value is uniform. The simulator returns labels only.

### 11.6 The sign row and the second exceptional case

They change four places in the chain, and nothing in the CRT layer.

- **The rows' bijection.** The public-first core maps a digit's seven row offsets to its three
  published constants and its four non-collector row values (`BMR.rowEquiv`). With the coefficient
  cut, the `y8` and `y10` slopes of the sign row read each other's offset, and the inverse solves
  that block by dividing by `3 − y²`. That is never zero, because 3 is not a square modulo `p`, so
  the bijection holds at every input. Off the curve, where the masks are hidden, the residual holds
  the offsets of the four encodings that no constant absorbs, and no division occurs
  (`bmrEquivOff`).
- **The exceptional inputs.** At `Q = K` and `Q = 2K` the real rows are not a lift, and the real
  gadget unlocks the true digit, while the simulator's gadget bytes are uniform. The public-first hop
  flags a target row with `Z = 0` or `S = 0`: some digit point `Q + K` is `2Q`, `0` or `(3/2)·Q`.
  That is three targets per digit, `273/#Point`, and with `91/#Point` for the law of the tail points
  it is `364/(r − 1)`.
- **The opening.** A lift has two scales, `(λ²x, t²y, λ)` (`(λ², 0, 0)` at the identity). Off the
  exceptional inputs a real row is such a lift with `λ = ρ·(u − a)` and `t = τ·L`, nonzero multiples
  of `ρ` and of `τ`, so uniform `ρ` and `τ` give uniform, independent `λ` and `t`. That is why `τ`
  must not be `ρ`: the two scales would be tied. The exceptional inputs have mass at most
  `273/#Point`, and the two point laws add `182/#Point`, so the output kernel is `455/(r − 1)`.
- **The digest's finals.** There are 182 final sites, one per exceptional input. A hidden final that
  the evaluator's path reaches needs an exceptional input other than the input with the same digest
  key, `2^-128` per site: `182/2^128` in all. With the two `Δ = 0` events the coincidence guess is
  `184/2^128`, within the budget's `185/2^128`.

### 11.7 The budget

The error terms, as stated in `Proof/Privacy/CRT/Glue/Budget.lean`:

| Hop | Term | Value |
|---|---|---:|
| `G0 → G0T` | `1,759,967/p` | `2^-232.85` |
| `G0T → G0U`, `G1U → HW`, `H → I` | pad and mask swap, three times | `2^-113.51` each |
| `G0U → G1U` | per query `4/2^128 + 1/(p − 1)` | `2^-126` per query |
| `G0U → G1U` | the curve encodings' wrap window (section 11.1) | `2^-104.74` |
| `G1U → HW` | stage-1 touches, per stage-1 query | `2^-126` per query |
| `G1U → HW` | wrap hint and collectors (section 11.3) | `2^-104.74` |
| `G1U → HW` | exceptional inputs `364/(r − 1)`, coincidences `185/2^128` (section 11.6) | `2^-245.1`, `2^-120.5` |
| `HW → H` | output kernel `455/(r − 1)` | `2^-244.8` |
| `I → M` | sampler cutoff | `2^-128` |

The constant part is about `2^-103.74`, 0.075 of the unit `2^-100` (the two wrap-hint terms are
almost all of it), and the linear part is `2^-125` per stage-1 query (the hidden hop's charge and the
stage-1 touch) and `2^-126` per stage-2 query, so `Adv · 2^100 ≤ q₁ + q₂ + 1`, which is at most the
adversary's step count plus one. Each share is one closed inequality of naturals decided by the
kernel (`chainError_budget`).

---

## 12. The simulator machine

The machine is written in xinshu's structured assembly (`Prog`, compiled to the library's flat code
table with a compiler-correctness theorem, one cost on every non-aborting path) with his two-stage
layout.

- **Stage 1** draws the public value: the curve and row constants (276 field cells) as field
  elements by bounded rejection, the 1,092 exception bytes, the joins and pins as coin words, the 85
  residue digits of each of the 642 records by bounded rejection below `m_i` (so the record is
  uniform below `M`, with hint 0), and the Lamport key; it serializes them with `Wire.encoding`,
  computing each 624-bit record by Horner's rule over 128-bit limbs.
- **Stage 2** replays the honest CRT evaluator on the shared lazy oracle: 936,182 queries (the
  conversion and body of both coordinates, the key and the 546 non-collector mask answers). The
  machine has 256-bit words and no division; it reads pad digits by the fraction reading with one
  multi-limb multiply-add primitive and a Barrett reduction, and reconstructs with Garner's method,
  the hint and the reduction modulo `p`. It then draws the opening's digit points and 91 lift pairs
  `(λ, t)`, solves the collectors (the sign row's collector `cubic` is read with `x²`, so its target
  is scaled by `(x·x)⁻¹`), samples their preimages and makes the 546 programs.

The machine is one closed `BoundedMachine.Simulator` (`CrtTop.crtSimulator`). Its law has xinshu's
three parts: stage 1's law (the drawn value has exactly the law of the public-first source), stage 2's
law (each arm computes what the abstract simulator computes, from the memory stage 1 leaves), and the
sampler cutoff (`2^-128`). The cost bound `size + 1 + firstFuel + secondFuel ≤ 2^60` is proved from
per-block bounds (every block's size and cost is at most `2^55`); the proofs about the machine keep the
sizes and costs of stage 1 and of the replay as variables, so no kernel check evaluates those programs.
The machine reuses xinshu's generic blocks and laws; the files of his switch-system machine that it
does not use are removed from the tree.

---

## 13. Status

The following obligations have supplied proof terms, adapted from the verified baseline and
awaiting a build and audit for the fallback schedule:

* computable garbling, with query programs at exact budgets and their equality proofs;
* Lamport compatibility;
* perfect correctness;
* function correctness;
* the fixed byte count;
* adaptive privacy, with the closed simulator machine and its `2^60` cost bound.

The baseline `#print axioms Submission.solution` reported exactly `propext`, `Classical.choice`
and `Quot.sound`; rerun this audit for the fallback branch after it builds.

---

## 14. Credits

* **psivesely** (`psivesely/kriterion-bn254-crt`, `de8f397`): the CRT entry this entry is built on,
  with its CRT-residue delivery layer, the curve-value masks of the rows, the hash-digest exception
  gadget, the hash-only oracle, and the whole proof and simulator machine; this entry keeps all of it
  and changes the rows and the gadget (sections 1.1, 1.2, 6 and 11.6).
* **Nakul Khambhati, Anwesh Bhattacharya and David Heath**, *Duty-Free Bits: Projectivizing Garbling
  Schemes* (ePrint 2026/476): the CRT-residue projectivization (one-hot trees, casts and pins,
  extraction, folds, the body), the switch systems, and the Embryo masking.
* **David Heath**, *Efficient Arithmetic in Garbled Circuits* (ePrint 2024/139): arithmetic labels
  and per-modulus truth tables.
* **Nakul Khambhati, Aaron Feickert, Christian Lewe and Mukesh Tiwari**, *Garbling Groth16 with
  Native Group Operations* (ePrint 2026/2100): the delivery of Argo MAC field encodings through the
  Duty-Free Bits CRT residues, with a fixed conversion per input and a cost per encoding, which the
  CRT entry's delivery layer follows.
* **The challenge's ArgoMAC baseline** (`Kriterion-cc/argomac-lean`, Runchao Han): the first ArgoMAC
  garbling of the challenge in Lean, the starting point of the ArgoMAC entries.
* **xinshu** (`xinshudong/bn254-entry`, `bf53ea4`): the Plan B framework this tree descends from, a
  switch-system entry with a complete proof, whose architecture the CRT entry extends: the obligation's
  reduction, the lazy oracle, the chain of games and the structure of the privacy proof, the
  public-first hop, the opening, the simulator machine and its assembly language, the curve check,
  the exception gadget and the decoder.
* **Lazar** (`Lazar955/argomac-lean`, `Lazar955/bn254-planb`): the Jacobian rows in the contest, the
  coefficient cut, the four-encoding `Y` row (published first), and the proof that 3 is a quadratic
  non-residue modulo `p`, so that no point of BN254 has `x = 0`; and in this entry the sign row, its
  coefficient cut, the second exceptional case, and their proofs and machine port.
* **liucheng** (`liuchengxu/kriterion-scalar-multiplication-honest`): the 91-digit decomposition.
* **Liam Eagen and Ying Tong Lai**, *Argo MAC: Garbling with Elliptic Curve MACs* (ePrint 2026/049).
* **Sanjam Garg, Dimitris Kolonelos, Mikhail Sergeevitch, Srivatsan Sridhar and David Tse**, *BABE:
  Verifying Proofs on Bitcoin Made 1000x Cheaper* (ePrint 2026/065): the Jacobian rows.

The contest tunings are psivesely's: the modulus set and the closed-form schedule, the
block-aligned casts, the fraction reading with 120 bits of slack, the wrap hint and the per-encoding
records, the labelled mask key, the hash digest for the exception gadget, the hash-only oracle, and
the Lean construction and proofs, including the conversion core by solve inversion, the wrap-hint
coupling, the route that programs only the collectors' masks, and the simulator machine. This
entry's own part is the sign row, its coefficient cut, the second exceptional case, and their
correctness, privacy and machine proofs on the CRT entry.

This entry was written with AI coding agents under human direction and review.
