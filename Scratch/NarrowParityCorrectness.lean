/-
Round-7 parity audit: the wire codec is a bijection at every stored width,
including zero, and honest full pins are even for all hashes and offsets.
-/
import Proof.Correctness.CRT.ChunkStep
import Proof.Correctness.CRT.ParityCast
import Lean

open Kriterion.CRT

#check Parity.HalfPin.codecEquiv
#check SliceC.treeGarbleM_xor
#check SliceC.chunkGarbleM_pin_even
#check SliceC.extStageGarbleM_pin_even

#print axioms Parity.HalfPin.ofBlocks_blocks
#print axioms Parity.HalfPin.blocks_ofBlocks
#print axioms SliceC.treeGarbleM_xor
#print axioms SliceC.chunkGarbleM_pin_even
#print axioms SliceC.extStageGarbleM_pin_even

run_cmd do
  for name in [`Kriterion.CRT.Parity.HalfPin.ofBlocks_blocks,
      `Kriterion.CRT.Parity.HalfPin.blocks_ofBlocks,
      `Kriterion.CRT.SliceC.treeGarbleM_xor,
      `Kriterion.CRT.SliceC.chunkGarbleM_pin_even,
      `Kriterion.CRT.SliceC.extStageGarbleM_pin_even] do
    let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
      !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
    unless illegal.isEmpty do
      Lean.throwError m!"disallowed axioms in {name}: {illegal}"
  Lean.logInfo "Parity correctness axiom check passed: only propext, Classical.choice, Quot.sound"

example (width : Nat) (wire : Fin width → Label) :
    (Parity.HalfPin.ofBlocks width wire).blocks = wire := Parity.HalfPin.blocks_ofBlocks wire

example (width : Nat) (pin : Parity.HalfPin width) :
    Parity.HalfPin.ofBlocks width pin.blocks = pin := Parity.HalfPin.ofBlocks_blocks pin

example (width : Nat) (label : Label) (tagOf : Nat → Nat) :
    (Parity.parityCastM width label tagOf).Bounded (castAnswers width) :=
  Parity.bounded_parityCastM width label tagOf
