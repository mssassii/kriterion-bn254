/-
The release-r1 opening blocks that the CRT machine's valid arm runs (`Construction/Simulator/CRT/Design.lean`,
`rowsProgram`; `Construction/Simulator/CRT/Preimages.lean`), in the order of the abstract simulator's rows kernel:

1. `tail`: `90` uniform finite curve points `D_d = (x, ±√(x³ + 3))`, `d = 1 .. 90`: `x` by
   bounded rejection over `254` coins, accepted when `x < p` and `x³ + 3` is a square (the
   candidate `(x³ + 3) ^ ((p + 1) / 4)` squares back; `p ≡ 3 mod 4`), then a fair sign — the
   construction's own offset law (P3's `coinOffsetsLaw`), with no group-order fact;
2. `horner`: `H = pointHorner β (D_1 … D_90)` by `P ← D_d + β · P` from `d = 90` down, with the
   constant multiple `β · P` unrolled over the `192` bits of `β`; the head clamp
   `D_0 = Q − β · H`, aborting when `β · H = O` (no clamped offset exists);
3. `lambdas`: `91` randomiser pairs `(λ_d, t_d) ∈ [1, p)²`, `λ_d` then `t_d` for each digit;
4. `lifts`: `W_d = (λ² x', t² y, tag · λ)` with `x' = 1 + tag · (x − 1)` (the identity's words are
   `(0, 0, 0)`, so its sign row is `0`), i.e. `liftRow`;
5. `preimageOne`: for a collector site `(d, c)`, `m < q + [y* < ρ]` by bounded rejection over `131` coins and the
   limbs of `y* + p · m`.

`rowCell d k` is the published row constant `k` of digit `d` (`xC0, yC4, zC0`).
-/

import Construction.Simulator.Blocks

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks Prog

namespace Opening

/-- Point register moves: `target ← source`, one coordinate at a time. -/
def copyPoint (target source : PointRegisters) : Prog :=
  seqList [ar .and target.tag source.tag source.tag, ar .and target.x source.x source.x,
    ar .and target.y source.y source.y]

/-- Load a stored point (tag, x, y) into a point register. -/
def loadPoint (target : PointRegisters) (address : Nat) : Prog :=
  seqList [loadAt target.tag address, loadAt target.x (address + 1), loadAt target.y (address + 2)]

/-- Store a point register. -/
def storePoint (address : Nat) (source : PointRegisters) : Prog :=
  seqList [storeAt address source.tag, storeAt (address + 1) source.x,
    storeAt (address + 2) source.y]

/-- `P ← O`. -/
def clearP : Prog := seqList [cst 6 0, cst 7 0, cst 8 0]

/-- One round of `s ← s² · a^bit` of the square-root exponentiation (`s` in `rB`, `a` in `rA`);
a one-instruction skip when the exponent bit is clear, so every round costs two. -/
def sqrtRound (bit : Nat) : Prog :=
  .seq (ar .fieldMul rB rB rB)
    (if sqrtExponent.testBit bit then ar .fieldMul rB rB rA else .skip 1)

/-- `rB ← (x³ + 3) ^ ((p + 1) / 4)` and `rA ← x³ + 3`, for `x` in register `source`
(clobbers `rAddr`). -/
def curveRoot (source : Register) : Prog :=
  seqList [ar .fieldMul rA source source, ar .fieldMul rA rA source, cst rAddr 3,
    ar .fieldAdd rA rA rAddr, cst rB 1, rep 252 fun round => sqrtRound (251 - round)]

/-- The acceptance test of the curve-point sampler, on `x = rAcc`: `x < p` and `x³ + 3` is a
square (the candidate root squares back to it). Sets `rBit`; clobbers `rAddr`, `rA` … `rD`. -/
def testCurveX : Prog :=
  seqList [cst rAddr pNat, ar .less rBit rAcc rAddr, curveRoot rAcc,
    ar .fieldMul rC rB rB, ar .xor rC rC rA, cst rD 1, ar .less rC rC rD,
    ar .and rBit rBit rC]

/-- One uniform finite point of the curve into the point cell of digit `d`: an accepted `x`
(in `rOut`), its root recomputed, and a fair sign. -/
def storeCurvePoint (digit : Nat) : Prog :=
  seqList [curveRoot rOut, coinBit rBit, cst rAcc 0, ar .fieldSub rC rAcc rB,
    ar .sub rC rC rB, ar .mul rC rC rBit, ar .add rC rC rB,
    cst rD 1, storeAt (openPoint digit) rD, storeAt (openPoint digit + 1) rOut,
    storeAt (openPoint digit + 2) rC]

/-- One tail digit `d ∈ 1 .. 90`: a uniform finite point (the construction's offset law). -/
def tailOne (digit : Nat) : Prog :=
  seqList [bounded fieldWidth testCurveX attempts (storeCurvePoint digit),
    zeroRegs [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB, rC, rD]]

/-- The `90` tail digits. -/
def tail : Prog := rep 90 fun index => tailOne (index + 1)

/-- One round of `P ← β · P` at bit `bit` of `β`: double, then add `Q` iff the bit is set (a
one-instruction skip otherwise, so every round costs two). -/
def betaRound (bit : Nat) : Prog :=
  .seq (.op (.pointAdd pointP pointP pointP))
    (if betaNat.testBit bit then .op (.pointAdd pointP pointP pointQ) else .skip 1)

/-- `P ← β · P` (clobbers `Q`). -/
def betaMul : Prog :=
  seqList [copyPoint pointQ pointP, clearP, rep 192 fun round => betaRound (191 - round)]

/-- One Horner step `P ← D_d + β · P`. -/
def hornerStep (digit : Nat) : Prog :=
  seqList [betaMul, loadPoint pointQ (openPoint digit), .op (.pointAdd pointP pointQ pointP)]

/-- The head clamp `D_0 = Q − β · H`, `H` in `P`; the tail is valid (the construction's clamped
offsets exist) only when `β · H ≠ O`, and the run aborts otherwise. -/
def head : Prog :=
  seqList [betaMul, .ite 6
    (seqList [cst rAcc 0, ar .fieldSub 8 rAcc 8, loadAt 9 reqTag0, loadAt 10 reqQX,
      loadAt 11 reqQY, .op (.pointAdd pointP pointQ pointP), storePoint (openPoint 0) pointP,
      zeroRegs [0, 4, 6, 7, 8, 9, 10, 11]])
    (.abort rSel)]

/-- `H`, then the head clamp. -/
def horner : Prog := seqList [clearP, rep 90 fun index => hornerStep (90 - index), head]

/-- One randomiser in `[1, p)`, stored at `address`. -/
def nonZeroCell (address : Nat) : Prog :=
  .seq (bounded fieldWidth (testPositiveBelow pNat) attempts (storeAt address rOut))
    (zeroRegs samplerScratch)

/-- The randomiser pair of digit `d`: `λ_d` (the `X` and `Z` rows), then `t_d` (the sign row). -/
def lambdaOne (digit : Nat) : Prog :=
  .seq (nonZeroCell (openLambda digit)) (nonZeroCell (openTau digit))

def lambdas : Prog := rep 91 lambdaOne

/-- `W_d = liftRow D_d λ_d t_d`. -/
def liftOne (digit : Nat) : Prog :=
  seqList [loadAt rA (openLambda digit), ar .fieldMul rB rA rA, loadAt rC (openTau digit),
    ar .fieldMul rC rC rC, loadPoint ⟨rD, rE, rF⟩ (openPoint digit), cst rAcc 1,
    ar .fieldSub rE rE rAcc, ar .fieldMul rE rE rD, ar .fieldAdd rE rE rAcc,
    ar .fieldMul rE rE rB, ar .fieldMul rF rF rC, ar .fieldMul rD rD rA,
    storeAt (openRow digit) rE, storeAt (openRow digit + 1) rF, storeAt (openRow digit + 2) rD,
    zeroRegs [rAcc, rAddr, rA, rB, rC, rD, rE, rF]]

def lifts : Prog := rep 91 liftOne

/-- The row-constant cell `k` of digit `d` (`xC0, yC4, zC0`). -/
def rowCell (digit slot : Nat) : Nat := fieldBase + curveCellCount + 3 * digit + slot

/-- `target ← source >> 128` (clobbers `rAddr`). -/
def shr128 (target source : Register) : Prog := .seq (cst rAddr 128) (ar .shiftRight target source rAddr)

/-- The limbs of `y + p · m`: `m` in `tmpM`, `y` at the target cell, limbs to `openLimb d c ·`. -/
def limbsOf (digit collector : Nat) : Prog :=
  seqList [loadAt rA tmpM, loadAt rB (openTarget digit collector), cst rC mask128,
    ar .and rD rA rC, shr128 rE rA, cst rF pLow, cst rSel pHigh,
    ar .mul rAcc rF rD, ar .mul rOut rF rE, ar .mul rFlag rSel rD, ar .mul rBit rSel rE,
    -- s0 = y_lo + t0_lo
    ar .and rD rB rC, ar .and rE rAcc rC, ar .add rD rD rE,
    ar .and rE rD rC, storeAt (openLimb digit collector 0) rE, shr128 rD rD,
    -- s1 = c0 + y_hi + t0_hi + t1_lo + t2_lo
    shr128 rE rB, ar .add rD rD rE, shr128 rE rAcc, ar .add rD rD rE,
    ar .and rE rOut rC, ar .add rD rD rE, ar .and rE rFlag rC, ar .add rD rD rE,
    ar .and rE rD rC, storeAt (openLimb digit collector 1) rE, shr128 rD rD,
    -- s2 = c1 + t1_hi + t2_hi + t3
    shr128 rE rOut, ar .add rD rD rE, shr128 rE rFlag, ar .add rD rD rE, ar .add rD rD rBit,
    storeAt (openLimb digit collector 2) rD,
    zeroRegs [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB, rC, rD, rE, rF]]

/-- The preimage of collector target `(d, c)`: `M = q + [y* < ρ]` in `rB`, then `m < M`. -/
def preimageOne (digit collector : Nat) : Prog :=
  seqList [loadAt rC (openTarget digit collector), cst rAddr preimageRemainder,
    ar .less rD rC rAddr, cst rAddr preimageQuotient, ar .add rB rD rAddr,
    bounded multiplierWidth (testBelowRegister rB) attempts (storeAt tmpM rOut),
    zeroRegs samplerScratch, limbsOf digit collector]

/-! ### Sizes and costs -/

section Sizes

/-- The simp set for straight-line blocks. -/
macro "prog_size" : tactic => `(tactic| simp only [seqList, Prog.size_seq, Prog.cost_seq,
  size_cst, cost_cst, size_loadAt, cost_loadAt, size_storeAt, cost_storeAt, size_zeroRegs,
  cost_zeroRegs, ar, Prog.size, Prog.cost, List.length_cons, List.length_nil])

theorem size_sqrtRound (bit : Nat) : (sqrtRound bit).size = 2 := by
  unfold sqrtRound; split <;> rfl
theorem cost_sqrtRound (bit : Nat) : (sqrtRound bit).cost = 2 := by
  unfold sqrtRound; split <;> rfl

theorem size_curveRoot (source : Register) : (curveRoot source).size = 509 := by
  unfold curveRoot; prog_size; rw [size_rep _ _ _ fun _ _ => size_sqrtRound _]
theorem cost_curveRoot (source : Register) : (curveRoot source).cost = 509 := by
  unfold curveRoot; prog_size; rw [cost_rep _ _ _ fun _ _ => cost_sqrtRound _]

theorem size_testCurveX : testCurveX.size = 516 := by
  unfold testCurveX; prog_size; rw [size_curveRoot]
theorem cost_testCurveX : testCurveX.cost = 516 := by
  unfold testCurveX; prog_size; rw [cost_curveRoot]

theorem size_storeCurvePoint (digit : Nat) : (storeCurvePoint digit).size = 526 := by
  unfold storeCurvePoint coinBit; prog_size; rw [size_curveRoot]
theorem cost_storeCurvePoint (digit : Nat) : (storeCurvePoint digit).cost = 524 := by
  unfold storeCurvePoint coinBit; prog_size; rw [cost_curveRoot]

theorem size_tailOne (digit : Nat) : (tailOne digit).size = 589865 := by
  unfold tailOne
  simp only [seqList, Prog.size_seq, size_zeroRegs, List.length_cons, List.length_nil, Prog.size]
  rw [size_bounded _ _ _ _ (by rw [cost_storeCurvePoint]; omega), size_testCurveX,
    size_storeCurvePoint, cost_storeCurvePoint]
  rfl
theorem cost_tailOne (digit : Nat) : (tailOne digit).cost = 459290 := by
  unfold tailOne
  simp only [seqList, Prog.cost_seq, cost_zeroRegs, List.length_cons, List.length_nil, Prog.cost]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeCurvePoint]; omega), cost_testCurveX,
    cost_storeCurvePoint]
  rfl

theorem size_tail : tail.size = 90 * 589865 := size_rep _ _ _ fun _ _ => size_tailOne _
theorem cost_tail : tail.cost = 90 * 459290 := cost_rep _ _ _ fun _ _ => cost_tailOne _

theorem size_betaRound (bit : Nat) : (betaRound bit).size = 2 := by
  unfold betaRound; split <;> rfl
theorem cost_betaRound (bit : Nat) : (betaRound bit).cost = 2 := by
  unfold betaRound; split <;> rfl

theorem size_betaMul : betaMul.size = 390 := by
  unfold betaMul copyPoint clearP
  prog_size
  rw [size_rep _ _ _ fun _ _ => size_betaRound _]
theorem cost_betaMul : betaMul.cost = 390 := by
  unfold betaMul copyPoint clearP
  prog_size
  rw [cost_rep _ _ _ fun _ _ => cost_betaRound _]

theorem size_hornerStep (digit : Nat) : (hornerStep digit).size = 397 := by
  unfold hornerStep loadPoint; prog_size; rw [size_betaMul]
theorem cost_hornerStep (digit : Nat) : (hornerStep digit).cost = 397 := by
  unfold hornerStep loadPoint; prog_size; rw [cost_betaMul]

theorem size_head : head.size = 439 := by
  unfold head storePoint; prog_size; rw [size_betaMul]; simp only [Prog.padSet, Prog.padClear]
  prog_size; norm_num
theorem cost_head : head.cost = 415 := by
  unfold head storePoint; prog_size; rw [cost_betaMul]; norm_num

theorem size_horner : horner.size = 3 + 90 * 397 + 439 := by
  unfold horner clearP; prog_size
  rw [size_rep _ _ _ fun _ _ => size_hornerStep _, size_head]
theorem cost_horner : horner.cost = 3 + 90 * 397 + 415 := by
  unfold horner clearP; prog_size
  rw [cost_rep _ _ _ fun _ _ => cost_hornerStep _, cost_head]

theorem size_nonZeroCell (address : Nat) : (nonZeroCell address).size = 457743 := by
  unfold nonZeroCell
  simp only [Prog.size_seq, size_zeroRegs, samplerScratch, List.length_cons, List.length_nil]
  rw [size_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testPositiveBelow, Prog.size_seq, size_cst, ar, Prog.size, size_storeAt, cost_storeAt,
    fieldWidth, attempts]
theorem cost_nonZeroCell (address : Nat) : (nonZeroCell address).cost = 327692 := by
  unfold nonZeroCell
  simp only [Prog.cost_seq, cost_zeroRegs, samplerScratch, List.length_cons, List.length_nil]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testPositiveBelow, Prog.cost_seq, cost_cst, ar, Prog.cost, cost_storeAt,
    fieldWidth, attempts]

theorem size_lambdaOne (digit : Nat) : (lambdaOne digit).size = 2 * 457743 := by
  unfold lambdaOne; rw [Prog.size_seq, size_nonZeroCell, size_nonZeroCell]
theorem cost_lambdaOne (digit : Nat) : (lambdaOne digit).cost = 2 * 327692 := by
  unfold lambdaOne; rw [Prog.cost_seq, cost_nonZeroCell, cost_nonZeroCell]

theorem size_lambdas : lambdas.size = 91 * (2 * 457743) :=
  size_rep _ _ _ fun _ _ => size_lambdaOne _
theorem cost_lambdas : lambdas.cost = 91 * (2 * 327692) :=
  cost_rep _ _ _ fun _ _ => cost_lambdaOne _

theorem size_liftOne (digit : Nat) : (liftOne digit).size = 33 := by
  unfold liftOne loadPoint; prog_size
theorem cost_liftOne (digit : Nat) : (liftOne digit).cost = 33 := by
  unfold liftOne loadPoint; prog_size

theorem size_lifts : lifts.size = 91 * 33 := size_rep _ _ _ fun _ _ => size_liftOne _
theorem cost_lifts : lifts.cost = 91 * 33 := cost_rep _ _ _ fun _ _ => cost_liftOne _

theorem size_limbsOf (digit collector : Nat) : (limbsOf digit collector).size = 58 := by
  unfold limbsOf shr128; prog_size
theorem cost_limbsOf (digit collector : Nat) : (limbsOf digit collector).cost = 58 := by
  unfold limbsOf shr128; prog_size

theorem size_preimageOne (digit collector : Nat) : (preimageOne digit collector).size = 236623 := by
  unfold preimageOne
  simp only [seqList, Prog.size_seq, size_zeroRegs, size_limbsOf, size_loadAt, size_cst, ar,
    samplerScratch, List.length_cons, List.length_nil, Prog.size]
  rw [size_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testBelowRegister, ar, Prog.size, size_storeAt, cost_storeAt, multiplierWidth,
    attempts]
theorem cost_preimageOne (digit collector : Nat) : (preimageOne digit collector).cost = 169548 := by
  unfold preimageOne
  simp only [seqList, Prog.cost_seq, cost_zeroRegs, cost_limbsOf, cost_loadAt, cost_cst, ar,
    samplerScratch, List.length_cons, List.length_nil, Prog.cost]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testBelowRegister, ar, Prog.cost, cost_storeAt, multiplierWidth, attempts]

end Sizes

end Opening

end Kriterion.ArgoMAC.PlanB.SimMachine
