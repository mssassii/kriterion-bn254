/-
The fixed register, RAM and stack layout of release-r1's simulator blocks, and the numeric
constants their code embeds (the CRT machine adds its own regions above `2 ^ 51`,
`Construction/Simulator/CRT/Layout.lean`).

**Registers.** `R0`–`R5` are sampler / arithmetic scratch, `R6`–`R8` and `R9`–`R11` are the two
point registers of `pointAdd`, `R12`–`R15` are the fixed oracle operands (index, input, first
answer, second answer).

**RAM.** Disjoint regions at `2 ^ 40 .. 2 ^ 50`: the published field cells and exception nibbles, the
parsed request, the selected labels, scalar temporaries, the opening's cells and the Lamport key.

**Stacks.** Stack `0` is the protocol request, stack `1` the private coin stack (every coin is
pushed and immediately popped, so it is empty between instructions blocks), stack `3` the
protocol response. Stack `2` is unused.
-/

import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine

/-! ### Registers -/

/-- Sampler accumulator and general scratch. -/
abbrev rAcc : Register := 0
/-- The accepted candidate of a rejection sampler. -/
abbrev rOut : Register := 1
/-- The accepted flag of a rejection sampler; the stage-2 validity flag. -/
abbrev rFlag : Register := 2
/-- The coin bit and the acceptance test. -/
abbrev rBit : Register := 3
/-- Address scratch of every constant-address load and store. -/
abbrev rAddr : Register := 4
/-- Select scratch and the abort scratch. -/
abbrev rSel : Register := 5
/-- General-purpose registers outside the samplers. -/
abbrev rA : Register := 6
abbrev rB : Register := 7
abbrev rC : Register := 8
abbrev rD : Register := 9
abbrev rE : Register := 10
abbrev rF : Register := 11
/-- The first point register (`R6`, `R7`, `R8`). -/
abbrev pointP : PointRegisters := ⟨6, 7, 8⟩
/-- The second point register (`R9`, `R10`, `R11`). -/
abbrev pointQ : PointRegisters := ⟨9, 10, 11⟩
/-- The third point register (`R0`, `R1`, `R2`), used only by the variable scalar multiple. -/
abbrev pointT : PointRegisters := ⟨0, 1, 2⟩
/-- The fixed oracle operands. -/
abbrev rIndex : Register := 12
abbrev rInput : Register := 13
abbrev rFirst : Register := 14
abbrev rSecond : Register := 15

/-! ### RAM regions -/

/-- The public field cells, in `Wire.encoding` order: curve (3), rows (`91 · 3`). -/
def fieldBase : Nat := 2 ^ 40
/-- The `182` exception nibbles. -/
def exceptionBase : Nat := 2 ^ 41
/-- The parsed request: `u.x`, `u.y`, the two output tag bits, `Q.x`, `Q.y`. -/
def requestBase : Nat := 2 ^ 43
/-- The `508` labels selected in stage 2. -/
def labelBase : Nat := 2 ^ 44
/-- Scalar temporaries (see `tmpM`). -/
def tmpBase : Nat := 2 ^ 48
/-- The opening: digit points, randomisers, lifted rows, targets. -/
def openBase : Nat := 2 ^ 49
/-- The Lamport key: `keyBase + 2 i` is the false label of input bit `i`, `+ 1` the true one
(bits `0 .. 253` are `x`, `254 .. 507` are `y`). Sampled in stage 1. -/
def keyBase : Nat := 2 ^ 50

/-- Field-cell counts: the curve constants, then the row constants (`91 · 3`: `xC0, yC4, zC0`). -/
def curveCellCount : Nat := 3
def rowCellCount : Nat := 91 * 3
/-- The exception nibble cells: `2` per digit, packed as one byte on the wire. -/
def exceptionCellCount : Nat := 91 * 2
def labelCount : Nat := 508
def keyBlockCount : Nat := 2 * 508

/-! ### Request cells -/

def reqX : Nat := requestBase
def reqY : Nat := requestBase + 1
def reqTag0 : Nat := requestBase + 2
def reqTag1 : Nat := requestBase + 3
def reqQX : Nat := requestBase + 4
def reqQY : Nat := requestBase + 5

/-! ### Temporaries -/

/-- The preimage multiplier `m` of the current collector site. -/
def tmpM : Nat := tmpBase + 15

/-! ### Opening cells -/

/-- Digit point `d` (tag, x, y). -/
def openPoint (digit : Nat) : Nat := openBase + 3 * digit
/-- The lift randomiser `λ_d` of digit `d` (the `X` and `Z` rows). -/
def openLambda (digit : Nat) : Nat := openBase + 400 + digit
/-- The sign-row randomiser `t_d` of digit `d`. -/
def openTau (digit : Nat) : Nat := openBase + 800 + digit
/-- The lifted row target `W_d` (X, Y, Z). -/
def openRow (digit : Nat) : Nat := openBase + 500 + 3 * digit
/-- The collector mask of (digit, collector), which the preimage sampler reads. -/
def openTarget (digit collector : Nat) : Nat := openBase + 1000 + 3 * digit + collector
/-- Limb `b` of the preimage of (digit, collector). -/
def openLimb (digit collector block : Nat) : Nat := openBase + 2000 + 9 * digit + 3 * collector + block

/-! ### Numeric constants -/

/-- The BN254 base-field modulus `p`. -/
def pNat : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
/-- The BN254 scalar-field modulus `r`. -/
def rNat : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617
/-- `2 ^ 256 mod p`, the weight of the third block in `sampleFp`. -/
def c256 : Nat := 2 ^ 256 % pNat
/-- `⌊2 ^ 384 / p⌋` and `2 ^ 384 mod p`: the preimage count of `y` is `q + [y < ρ]`. -/
def preimageQuotient : Nat := 2 ^ 384 / pNat
def preimageRemainder : Nat := 2 ^ 384 % pNat
/-- The two 128-bit limbs of `p`. -/
def pLow : Nat := pNat % 2 ^ 128
def pHigh : Nat := pNat / 2 ^ 128
/-- The 128-bit mask. -/
def mask128 : Nat := 2 ^ 128 - 1

/-- `radix.val = (2 − ω).val`, the Horner radix `β` as a natural number (192 bits). -/
def betaNat : Nat := 4407920970296243842393367215006156084916469457145843978464

/-- `(p + 1) / 4`: since `p ≡ 3 (mod 4)`, `a ^ ((p + 1) / 4)` is a square root of every square
`a` (252 bits). -/
def sqrtExponent : Nat := 5472060717959818805561601436314318772174077789324455915672259473661306552146

/-- A word constant. -/
abbrev word (value : Nat) : Word := BitVec.ofNat 256 value

/-! ### Sampling parameters -/

/-- Every bounded rejection sampler makes this many constant-time attempts. -/
def attempts : Nat := 256
/-- Field cells, scalars and randomisers are drawn from 254 coins per attempt. -/
def fieldWidth : Nat := 254
/-- The preimage multiplier `m < q + 1 < 2 ^ 131` is drawn from 131 coins per attempt. -/
def multiplierWidth : Nat := 131

end Kriterion.ArgoMAC.PlanB.SimMachine
