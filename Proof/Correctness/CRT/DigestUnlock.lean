/-
C7 part C: the per-label hash digest unlocks the digit of an exceptional input (`Construction/CRT/Digest.lean`). With honest labels (the zero label XOR the bit times `Δ`), the
evaluator's key is the garbler's key of its input (`digestKey_honest`); at either exceptional input of
a nonzero digit the published entry holds the masked digit code at the input's slot of that kind, so the
unlock of that kind returns the digit (`digestUnlock_exceptional`, `digestUnlock_triple`), for every hash.
-/

import Construction.CRT.Digest

namespace Kriterion.CRT.DigestUnlock

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.CRT

/-- Honest labels: the zero label, XOR `Δ` where the input's bit is set. -/
def Honest {bits : Nat} (zero : Fin 2 → Fin bits → Block) (delta : Fin 2 → Block)
    (labels : Fin 2 → Fin bits → Block) (u : AffineInput) : Prop :=
  ∀ coord position, labels coord position =
    zero coord position ^^^ (if coordBit u coord position.val = 1 then delta coord else 0)

theorem digestKey_honest (H : HashN) (bits : Nat) (zero : Fin 2 → Fin bits → Block)
    (delta : Fin 2 → Block) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (honest : Honest zero delta labels u) :
    digestKey H bits labels u = garblerKey (digestTable H bits zero delta) u := by
  unfold digestKey garblerKey
  congr 1
  funext coord
  congr 1
  funext position
  rw [honest coord position]
  unfold digestTable
  by_cases bit : coordBit u coord position.val = 1
  · rw [if_pos bit, if_pos bit, bit]
  · have zeroBit : coordBit u coord position.val = 0 := by
      unfold coordBit at bit ⊢
      split at bit <;> simp_all
    rw [if_neg bit, if_neg bit, zeroBit,
      show zero coord position ^^^ (0 : Block) = zero coord position from BitVec.xor_zero]

/-- **The digest unlocks the digit at its doubling input** (the first half of the pair). -/
theorem digestUnlock_exceptional (H : HashN) (bits digits : Nat) (zero : Fin 2 → Fin bits → Block)
    (delta : Fin 2 → Block) (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput)
    (padOf : Fin digits → Exception.Entry) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (honest : Honest zero delta labels u) (o : Fin digits) (phi : BaseField)
    (selected : digitEndomorphismBase (digitOf o) = some phi)
    (exceptional : u = Exception.exceptionalInput phi (offsetOf o)) :
    (digestUnlock H bits digits labels u (digestEntries H bits digits zero delta digitOf offsetOf padOf) o).1 =
      digitOf o := by
  unfold digestUnlock digestEntries garbleEntry
  rw [digestKey_honest H bits zero delta labels u honest]
  simp only [selected]
  rw [Exception.unlock_writeEntry_ne _ _ _ _ _ _ (Exception.slotOf_ne _ _).symm, ← exceptional]
  exact Exception.unlock_writeEntry _ _ _ _ _

/-- **The digest unlocks the digit at its second exceptional input** `φ⁻¹(2K)` (the second half). -/
theorem digestUnlock_triple (H : HashN) (bits digits : Nat) (zero : Fin 2 → Fin bits → Block)
    (delta : Fin 2 → Block) (digitOf : Fin digits → Digit) (offsetOf : Fin digits → AffineInput)
    (padOf : Fin digits → Exception.Entry) (labels : Fin 2 → Fin bits → Block) (u : AffineInput)
    (honest : Honest zero delta labels u) (o : Fin digits) (phi : BaseField)
    (selected : digitEndomorphismBase (digitOf o) = some phi)
    (triple : u = Exception.tripleInput phi (offsetOf o)) :
    (digestUnlock H bits digits labels u (digestEntries H bits digits zero delta digitOf offsetOf padOf) o).2 =
      digitOf o := by
  unfold digestUnlock digestEntries garbleEntry
  rw [digestKey_honest H bits zero delta labels u honest]
  simp only [selected]
  rw [← triple]
  exact Exception.unlock_writeEntry _ _ _ _ _

end Kriterion.CRT.DigestUnlock
