/-
**The CRT simulator's word-model arithmetic**.

The machine has 256-bit words, `mul` modulo `2 ^ 256` and no division. Every multi-precision
step of the CRT simulator is built from two blocks:

* `mulSmallAdd base count`: `X ← X · m + c` over `count` little-endian 128-bit limbs stored at
  `RAM[base] … RAM[base + count - 1]`, with the small multiplier `m` in `rM`, the carry in and out
  in `rC` (7 instructions a limb);
* `barrett src dst m width`: `dst ← src mod m` for `src < 2 ^ width`, by one multiplication with
  the constant `⌊2 ^ width / m⌋`, one shift and one constant-time correction (12 instructions).

On top of them: `fracPass` and `fracDigits` (the fraction reading of a pad integer: the digits of
`⌊u · m ^ S / 2 ^ B⌋`, top digit first, one `mulSmallAdd` pass per digit), and, in
`Construction/Simulator/CRT/Garner.lean`, Garner's reconstruction with the wrap hint and the
reduction modulo `p`.

Register use (a block's scratch, never live across an oracle instruction): `rA`, `rB`, `rC`, `rD`,
`rE`, `rF`, `rAddr` as scratch; `rM`, `rMask`, `rK128` hold the block constants `m`,
`2 ^ 128 - 1` and `128`. These three are xinshu's oracle operand registers `R12 … R14`
(`Layout.lean`), free while no query is being issued.
-/

import Construction.Simulator.Blocks
import Construction.Simulator.CRT.Frame

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks

/-! ### Registers and constants -/

/-- The small multiplier of `mulSmallAdd` (xinshu's `rIndex`, free outside queries). -/
abbrev rM : Register := 12
/-- The limb mask `2 ^ 128 - 1` (xinshu's `rInput`, free outside queries). -/
abbrev rMask : Register := 13
/-- The shift `128` (xinshu's `rFirst`, free outside queries). -/
abbrev rK128 : Register := 14

/-- The limb mask. -/
def limbMask : Nat := 2 ^ 128 - 1

/-- Load the three block constants: `rM := m`, `rMask := 2 ^ 128 - 1`, `rK128 := 128`. -/
def setupConsts (m : Nat) : Prog :=
  .seq (cst rM m) (.seq (cst rMask limbMask) (cst rK128 128))

/-! ### `mulSmallAdd` -/

/-- One limb: `v = RAM[base + k] · m + carry`; `RAM[base + k] := v mod 2 ^ 128`;
`carry := v / 2 ^ 128`. -/
def mulSmallAddLimb (base k : Nat) : Prog :=
  .seq (cst rAddr (base + k))
    (.seq (.op (.load rA rAddr))
    (.seq (ar .mul rA rA rM)
    (.seq (ar .add rA rA rC)
    (.seq (ar .and rB rA rMask)
    (.seq (.op (.store rAddr rB))
      (ar .shiftRight rC rA rK128))))))

/-- `X ← X · R[rM] + R[rC]` over `count` limbs at `base`, the carry out in `rC`. -/
def mulSmallAdd (base count : Nat) : Prog := Prog.rep count (mulSmallAddLimb base)

/-! ### The fraction reading -/

/-- One digit of the fraction reading: `carry := 0`, one `mulSmallAdd` pass, store the carry (the
next digit) at `dst`. -/
def fracPass (base count dst : Nat) : Prog :=
  .seq (cst rC 0) (.seq (mulSmallAdd base count) (storeAt dst rC))

/-- `digits` digits of the fraction reading of the `count`-limb integer at `base`, top digit
first; pass `j` stores its digit at `dst j`. -/
def fracDigits (base count digits : Nat) (dst : Nat → Nat) : Prog :=
  Prog.rep digits fun j => fracPass base count (dst j)

/-! ### Barrett reduction -/

/-- `dst ← R[src] mod m` for `R[src] < 2 ^ width`: `q = (x · ⌊2 ^ width / m⌋) >> width`,
`r = x - q · m`, then subtract `m` once if `r ≥ m`. Clobbers `rD`, `rE`, `rF`. -/
def barrett (src dst : Register) (m width : Nat) : Prog :=
  .seq (cst rE (2 ^ width / m))
    (.seq (ar .mul rE src rE)
    (.seq (cst rF width)
    (.seq (ar .shiftRight rE rE rF)
    (.seq (cst rF m)
    (.seq (ar .mul rE rE rF)
    (.seq (ar .sub dst src rE)
    (.seq (ar .less rE dst rF)
    (.seq (cst rD 1)
    (.seq (ar .sub rE rD rE)
    (.seq (ar .mul rE rE rF)
      (ar .sub dst dst rE)))))))))))

/-! ### Frames (the schema of `Construction/Simulator/CRT/Frame.lean`) -/

/-- `mulSmallAdd` writes its limbs. -/
def mulSmallAddWrites (base count : Nat) : Writes := Writes.region ⟨base, count⟩

/-- `mulSmallAdd`, `fracPass` and `fracDigits` clobber `rA`, `rB`, `rC`, `rAddr`. -/
def limbClobbers : Clobbers := Clobbers.ofList [rA, rB, rC, rAddr]

/-- `fracDigits` writes its limbs and its digit cells. -/
def fracDigitsWrites (base count digits : Nat) (dst : Nat → Nat) : Writes :=
  (Writes.region ⟨base, count⟩).union (Writes.iUnion digits fun j => Writes.cell (dst j))

/-- `barrett` writes no RAM. -/
def barrettWrites : Writes := Writes.none

/-- `barrett` clobbers its destination and `rD`, `rE`, `rF`. -/
def barrettClobbers (dst : Register) : Clobbers := Clobbers.ofList [dst, rD, rE, rF]

/-! ### Sizes and costs -/

theorem size_setupConsts (m : Nat) : (setupConsts m).size = 3 := rfl
theorem cost_setupConsts (m : Nat) : (setupConsts m).cost = 3 := rfl
theorem size_mulSmallAddLimb (base k : Nat) : (mulSmallAddLimb base k).size = 7 := rfl
theorem cost_mulSmallAddLimb (base k : Nat) : (mulSmallAddLimb base k).cost = 7 := rfl

theorem size_mulSmallAdd (base count : Nat) : (mulSmallAdd base count).size = 7 * count := by
  unfold mulSmallAdd
  rw [Prog.size_rep count _ 7 (fun _ _ => rfl), Nat.mul_comm]

theorem cost_mulSmallAdd (base count : Nat) : (mulSmallAdd base count).cost = 7 * count := by
  unfold mulSmallAdd
  rw [Prog.cost_rep count _ 7 (fun _ _ => rfl), Nat.mul_comm]

theorem size_fracPass (base count dst : Nat) : (fracPass base count dst).size = 3 + 7 * count := by
  simp only [fracPass, Prog.size, size_mulSmallAdd, cst, size_storeAt]; omega

theorem cost_fracPass (base count dst : Nat) : (fracPass base count dst).cost = 3 + 7 * count := by
  simp only [fracPass, Prog.cost, cost_mulSmallAdd, cst, cost_storeAt]; omega

theorem size_fracDigits (base count digits : Nat) (dst : Nat → Nat) :
    (fracDigits base count digits dst).size = digits * (3 + 7 * count) := by
  unfold fracDigits
  rw [Prog.size_rep digits _ _ (fun j _ => size_fracPass base count (dst j))]

theorem cost_fracDigits (base count digits : Nat) (dst : Nat → Nat) :
    (fracDigits base count digits dst).cost = digits * (3 + 7 * count) := by
  unfold fracDigits
  rw [Prog.cost_rep digits _ _ (fun j _ => cost_fracPass base count (dst j))]

theorem size_barrett (src dst : Register) (m width : Nat) : (barrett src dst m width).size = 12 := rfl
theorem cost_barrett (src dst : Register) (m width : Nat) : (barrett src dst m width).cost = 12 := rfl

end Kriterion.CRT.SimMachine
