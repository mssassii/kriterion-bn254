/-
The modulus table of the CRT delivery layer, as data: one record `CrtTable` that every definition
of `Construction/CRT/` is generic in (the real 85-row table, the reduced tables of the differential
test, and a toy field).

A table fixes the coordinate width and the chunking, the cast width of the chunk step, the moduli
in index order with one conversion schedule each (an odd row of `Interface.OddRow`, or the power
of two `2 ^ (chunk 0 width)` read from chunk 0's leaves), the pad slack and the wrap bound. The
product `M`, the prefix products (the mixed radix of the records) and the CRT idempotents are
computable functions of the table.

Kernel rules: `product`, `radix`, `idempotent` and the pad counts of the real table are never
unfolded or decided in a proof; facts about them are stated symbolically or closed by
kernel-accelerated `Nat` arithmetic on small closed data.
-/

import Construction.CRT.Interface

namespace Kriterion.CRT

/-- The conversion kind of one modulus. -/
inductive Kind where
  /-- The modulus `2 ^ (chunk 0 width)`: its one-hot is chunk 0's leaf vector, no conversion. -/
  | chunkZero
  /-- An odd modulus with its extraction, growth and fold schedule. -/
  | odd (row : OddRow)
deriving Repr, DecidableEq

/-- A modulus table. -/
structure CrtTable where
  /-- Bits of the coordinate (254 for BN254). -/
  inputBits : Nat
  /-- Width of every chunk but the last. -/
  chunkBits : Nat
  /-- Cast width `L` of the chunk step (the largest `ell`). -/
  castWidth : Nat
  /-- Number of moduli. -/
  count : Nat
  /-- The moduli in index order (the order of tags, records and the flat layout). -/
  modulus : Fin count → Nat
  /-- The conversion kind of each modulus. -/
  kind : Fin count → Kind
  /-- Pad slack (D5): 120. -/
  slack : Nat
  /-- Wrap bound `B` (D7): `(p - 1) ^ 2 + 1`. -/
  wrapBound : Nat

namespace CrtTable

variable (T : CrtTable)

/-! ### Chunks -/

/-- `⌈inputBits / chunkBits⌉` chunks. -/
def chunkCount : Nat := (T.inputBits + T.chunkBits - 1) / T.chunkBits

/-- The first coordinate bit of chunk `c`. -/
def chunkOffset (c : Nat) : Nat := T.chunkBits * c

/-- The width of chunk `c`: `chunkBits`, except the last chunk, which takes what is left. -/
def chunkWidth (c : Nat) : Nat := min T.chunkBits (T.inputBits - T.chunkBits * c)

/-- The value of chunk `c` of a coordinate value `v`. -/
def chunkValue (v c : Nat) : Nat := (v >>> T.chunkOffset c) % 2 ^ T.chunkWidth c

/-- The truth table of modulus `m` at chunk `c`: `T_{c,m}(α) = (α * 2 ^ offset) mod m`. -/
def truth (m c α : Nat) : Nat := α * 2 ^ T.chunkOffset c % m

/-- The word value of an odd modulus `m`: `σ_m = Σ_c T_{c,m}(α_c)`, congruent to `v` mod `m`
and below `2 ^ ell` (L5). -/
def wordValue (m v : Nat) : Nat :=
  ∑ c : Fin T.chunkCount, T.truth m c.val (T.chunkValue v c.val)

/-! ### Moduli -/

/-- `M`, the product of the moduli. Never unfolded in a proof on the real table. -/
def product : Nat := ∏ i : Fin T.count, T.modulus i

/-- The mixed radix of modulus `i`: the product of the moduli before it. -/
def radix (i : Fin T.count) : Nat :=
  ∏ j : Fin i.val, T.modulus ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- The inverse of `a` modulo `m`, as a natural below `m` (extended gcd, computable). -/
def inverseMod (a m : Nat) : Nat := ((a : ZMod m)⁻¹).val

/-- The CRT idempotent `ε_i = (M / m_i) * ((M / m_i)⁻¹ mod m_i) mod M`. -/
def idempotent (i : Fin T.count) : Nat :=
  let cofactor := T.product / T.modulus i
  cofactor * inverseMod cofactor (T.modulus i) % T.product

/-- CRT reconstruction `crt(r) = (Σ_i r_i * ε_i) mod M` (L16). -/
def crt (residues : Fin T.count → Nat) : Nat :=
  (∑ i : Fin T.count, residues i * T.idempotent i) % T.product

/-- Pad answers per slot of modulus `i` for `S` encodings (D5). -/
def padAnswers (S : Nat) (i : Fin T.count) : Nat :=
  match T.kind i with
  | .chunkZero => padAnswersPow2 S (T.chunkWidth 0)
  | .odd _ => padAnswersOdd T.slack S (T.modulus i)

end CrtTable

/-! ### Building tables from a list of moduli -/

/-- The table of the given moduli with the given kinds. -/
def CrtTable.ofModuli (inputBits chunkBits castWidth : Nat) (moduli : Array Nat)
    (kindOf : Nat → Kind) (slack wrapBound : Nat) : CrtTable where
  inputBits := inputBits
  chunkBits := chunkBits
  castWidth := castWidth
  count := moduli.size
  modulus i := moduli[i]
  kind i := kindOf moduli[i]
  slack := slack
  wrapBound := wrapBound

/-- The T9 kinds for the BN254 chunking (32 chunks of 8 bits, the last of 6): 256 is chunk 0's
one-hot, every other modulus gets `t9Row 32 m`. -/
def t9Kind (m : Nat) : Kind := if m = 256 then .chunkZero else .odd (t9Row 32 m)

/-- A T9 BN254 table on the given moduli, retained for reduced tests and the original
schedule's lemmas. The real table below uses `selectiveTableOf`. -/
def bn254TableOf (moduli : Array Nat) : CrtTable :=
  CrtTable.ofModuli 254 8 14 moduli t9Kind padSlack (wrapBound BN254.baseFieldModulus)

/-- First extraction width of the 128-bit fallback. These 17 real odd moduli retain
width 7; the other 67 use width 8. The exact schedule is recorded in
`Scratch/fallback_schedule.json`; the power-of-two modulus bypasses this selector. -/
def fallbackWidth0 (m : Nat) : Nat :=
  if m ∈ ([167, 169, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251] : List Nat) then 7 else 8

theorem fallbackWidth0_lower (m : Nat) : 7 ≤ fallbackWidth0 m := by
  unfold fallbackWidth0
  split <;> decide

theorem fallbackWidth0_upper (m : Nat) : fallbackWidth0 m ≤ 8 := by
  unfold fallbackWidth0
  split <;> decide

/-- The fallback changes the first extraction width, keeping the same word width as T9.
The second width and kept one-hot follow the same width-parametric formulas. -/
def fallbackRow (chunks m : Nat) : OddRow :=
  let ell := bitLength (chunks * (m - 1))
  let width0 := fallbackWidth0 m
  { ell, width0, width1 := ell - width0 - 1, keep := max width0 (ell - 5) }

@[simp] theorem fallbackRow_ell (chunks m : Nat) :
    (fallbackRow chunks m).ell = (t9Row chunks m).ell := rfl

/-- As in T9, modulus 256 is read directly from chunk 0. -/
def fallbackKind (m : Nat) : Kind :=
  if m = 256 then .chunkZero else .odd (fallbackRow 32 m)

/-- A BN254 table with the fallback schedule. Kept separate from `bn254TableOf` so
the existing T9 reduced fixture and generic T9 statements retain their meaning. -/
def fallbackTableOf (moduli : Array Nat) : CrtTable :=
  CrtTable.ofModuli 254 8 14 moduli fallbackKind padSlack (wrapBound BN254.baseFieldModulus)

/-- Width-8 extraction on every odd modulus; the word width is unchanged from T9. -/
def width8Row (chunks m : Nat) : OddRow :=
  let ell := bitLength (chunks * (m - 1))
  { ell, width0 := 8, width1 := ell - 8 - 1, keep := max 8 (ell - 5) }

@[simp] theorem width8Row_ell (chunks m : Nat) :
    (width8Row chunks m).ell = (t9Row chunks m).ell := rfl

/-- Modulus 256 reuses chunk 0; every odd modulus uses first extraction width 8. -/
def width8Kind (m : Nat) : Kind :=
  if m = 256 then .chunkZero else .odd (width8Row 32 m)

/-- A BN254 table with width 8 for every odd row. -/
def width8TableOf (moduli : Array Nat) : CrtTable :=
  CrtTable.ofModuli 254 8 14 moduli width8Kind padSlack (wrapBound BN254.baseFieldModulus)

/-- First-stage width 9 on the 25 rows selected by the exact cost experiment;
all other odd rows retain width 8. The power-of-two modulus bypasses this selector. -/
def selectiveWidth0 (m : Nat) : Nat :=
  if m ∈ ([59, 61, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389] : List Nat) then 9 else 8

theorem selectiveWidth0_lower (m : Nat) : 8 ≤ selectiveWidth0 m := by
  unfold selectiveWidth0
  split <;> decide

theorem selectiveWidth0_upper (m : Nat) : selectiveWidth0 m ≤ 9 := by
  unfold selectiveWidth0
  split <;> decide

/-- The selected schedule preserves the word width, with a smaller second stage. -/
def selectiveRow (chunks m : Nat) : OddRow :=
  let ell := bitLength (chunks * (m - 1))
  let width0 := selectiveWidth0 m
  { ell, width0, width1 := ell - width0 - 1, keep := max width0 (ell - 5) }

@[simp] theorem selectiveRow_ell (chunks m : Nat) :
    (selectiveRow chunks m).ell = (t9Row chunks m).ell := rfl

/-- Modulus 256 reuses chunk 0; odd moduli use the selected schedule. -/
def selectiveKind (m : Nat) : Kind :=
  if m = 256 then .chunkZero else .odd (selectiveRow 32 m)

/-- BN254 conversion with the selected width-8/9 schedule. -/
def selectiveTableOf (moduli : Array Nat) : CrtTable :=
  CrtTable.ofModuli 254 8 14 moduli selectiveKind padSlack (wrapBound BN254.baseFieldModulus)

/-- **The real table**: 85 moduli, 25 odd rows at width 9 and 59 at width 8, slack 120. -/
def bn254Table : CrtTable := selectiveTableOf bn254Moduli

/-- The reduced table of the differential test: growth 0, 1 and 2 and
the power of two. -/
def reducedTable : CrtTable := bn254TableOf #[17, 131, 256, 257]

end Kriterion.CRT
