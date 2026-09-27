/-
**The memory after stage 1's draws** (M2): `readDraw` reads the draws back from RAM, and `readDraw_stored` says the
storedMem memory holds exactly the draws (every block writes its own region: field cells at `2^40`, bytes at `2^41`,
zero labels at `2^50`, joins at `2^51`, lanes at `2^52`, digits at `2^53`, offsets at `2^55`).
-/

import Proof.Simulator.CRT.Stage1Draws

namespace Kriterion.CRT.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
  Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.Blocks
open Kriterion.CRT.Entry (joinCount pinCount)
open CrtStage1 CrtDraws

namespace CrtStored

noncomputable section

/-! ### Counts -/

theorem joinCount_eq : joinCount = 1534 := by decide +kernel

theorem pinCount_eq : pinCount = 200 := CrtConv.pinCount_eq

theorem recordCount_eq : recordCount = 642 := rfl

/-! ### Reading the draws back -/

/-- **The draws a memory holds.** -/
def readDraw (ram : Word → Word) : Draw where
  fields index := ((ram (word (fieldBase + index.val))).toNat : BaseField)
  bytes n := (ram (word (exceptionBase + n.val))).toNat
  joins n := (ram (word (joinAddr n.val))).toNat
  pins n := (ram (word (pinAddr n.val))).toNat
  digits n := (ram (word (digitAddr n.val))).toNat
  zeros j := (ram (word (keyBase + 2 * j.val))).toNat
  deltas κ := (ram (word (Layout.deltaCell κ.val))).toNat

/-- Every drawn natural fits a word. -/
structure DrawSmall (d : Draw) : Prop where
  bytes : ∀ n, d.bytes n < 2 ^ 256
  joins : ∀ n, d.joins n < 2 ^ 256
  pins : ∀ n, d.pins n < 2 ^ 256
  digits : ∀ n, d.digits n < 2 ^ 256
  zeros : ∀ n, d.zeros n < 2 ^ 256
  deltas : ∀ n, d.deltas n < 2 ^ 256

/-! ### The regions -/

theorem word_ne_lt {first second : Nat} (firstSmall : first < 2 ^ 256) (secondSmall : second < 2 ^ 256)
    (below : first < second) : word first ≠ word second :=
  word_ne firstSmall secondSmall (by omega)

theorem joinAddr_range (n : Nat) (small : n < 2 * joinCount) :
    2 ^ 51 ≤ joinAddr n ∧ joinAddr n < 2 ^ 51 + 2 ^ 25 := by
  unfold joinAddr Layout.sourceJoin
  rw [joinCount_eq] at *
  constructor <;> omega

theorem pinAddr_range (n : Nat) (small : n < 2 * (pinCount * 128)) :
    2 ^ 52 ≤ pinAddr n ∧ pinAddr n < 2 ^ 52 + 2 ^ 25 := by
  unfold pinAddr pinCoord pinOf Layout.sourcePin
  rw [pinCount_eq] at *
  constructor <;> omega

theorem digitAddr_range (n : Nat) (small : n < recordCount * moduliCount) :
    2 ^ 53 ≤ digitAddr n ∧ digitAddr n < 2 ^ 53 + 2 ^ 25 := by
  unfold digitAddr recordCoord recordIndex Layout.residueCell
  simp only [show recordCount = 642 from rfl, show moduliCount = 85 from rfl, show Entry.xCount = 367 from rfl] at *
  constructor <;> split_ifs <;> omega

theorem joinAddr_injective (first second : Nat) (firstSmall : first < 2 * joinCount)
    (secondSmall : second < 2 * joinCount) (different : first ≠ second) :
    word (joinAddr first) ≠ word (joinAddr second) := by
  apply word_ne
  · have := joinAddr_range first firstSmall; omega
  · have := joinAddr_range second secondSmall; omega
  · unfold joinAddr Layout.sourceJoin
    rw [joinCount_eq] at *
    omega

theorem pinAddr_injective (first second : Nat) (firstSmall : first < 2 * (pinCount * 128))
    (secondSmall : second < 2 * (pinCount * 128)) (different : first ≠ second) :
    word (pinAddr first) ≠ word (pinAddr second) := by
  apply word_ne
  · have := pinAddr_range first firstSmall; omega
  · have := pinAddr_range second secondSmall; omega
  · unfold pinAddr pinCoord pinOf Layout.sourcePin
    rw [pinCount_eq] at *
    omega

theorem digitAddr_injective (first second : Nat) (firstSmall : first < recordCount * moduliCount)
    (secondSmall : second < recordCount * moduliCount) (different : first ≠ second) :
    word (digitAddr first) ≠ word (digitAddr second) := by
  apply word_ne
  · have := digitAddr_range first firstSmall; omega
  · have := digitAddr_range second secondSmall; omega
  · unfold digitAddr recordCoord recordIndex Layout.residueCell
    simp only [show recordCount = 642 from rfl, show moduliCount = 85 from rfl,
      show Entry.xCount = 367 from rfl] at *
    split_ifs <;> omega

/-! ### The stores -/

variable [FieldCertificate]

theorem wordStore_ram (address : Nat) (memory : Memory) (value : Nat) :
    (wordStore address memory value).ram = Function.update memory.ram (word address) (BitVec.ofNat 256 value) := by
  simp only [wordStore, (clearRegs_other _ _).1, storeRam]

theorem cellStore_ram (address : Nat) (memory : Memory) (value : Nat) :
    (cellStore address memory value).ram = Function.update memory.ram (word address) (BitVec.ofNat 256 value) := by
  simp only [cellStore, (clearRegs_other _ _).1, storeRam]

/-- A cell outside the offsets, the zero labels, the digits and the lanes is as the joins left it. -/
theorem stored_ram_upto_joins (memory : Memory) (d : Draw) (target : Nat) (small : target < 2 ^ 256)
    (offDeltas : target < 2 ^ 55 ∨ 2 ^ 55 + 2 ≤ target)
    (offZeros : target < keyBase ∨ keyBase + 2 * labelCount ≤ target)
    (offDigits : target < 2 ^ 53 ∨ 2 ^ 53 + 2 ^ 25 ≤ target)
    (offPins : target < 2 ^ 52 ∨ 2 ^ 52 + 2 ^ 25 ≤ target) :
    (storedMem memory d).ram (word target) =
      (foldStore (fun n => wordStore (joinAddr n)) (2 * joinCount)
        (foldStore (wordStep exceptionBase) exceptionByteCount
          (foldStore (cellStep fieldBase) fieldCount memory d.fields) d.bytes) d.joins).ram (word target) := by
  unfold storedMem
  rw [foldStore_ram_off _ (fun n => word (Layout.deltaCell n)) _ (fun n => wordStore_ram _) 2 _ _ _
      (fun n bound => word_ne small (by unfold Layout.deltaCell; omega) (by unfold Layout.deltaCell; omega)),
    foldStore_ram_off _ (fun n => word (keyBase + 2 * n)) _ (fun n => wordStore_ram _) labelCount _ _ _
      (fun n bound => word_ne small (by unfold keyBase labelCount at *; omega)
        (by unfold keyBase labelCount at *; omega)),
    foldStore_ram_off _ (fun n => word (digitAddr n)) _ (fun n => cellStore_ram _) (recordCount * moduliCount) _ _ _
      (fun n bound => by have := digitAddr_range n bound; exact word_ne small (by omega) (by omega)),
    foldStore_ram_off _ (fun n => word (pinAddr n)) _ (fun n => wordStore_ram _) (2 * (pinCount * 128)) _ _ _
      (fun n bound => by have := pinAddr_range n bound; exact word_ne small (by omega) (by omega))]

theorem stored_deltas (memory : Memory) (d : Draw) (κ : Fin 2) :
    (storedMem memory d).ram (word (Layout.deltaCell κ.val)) = BitVec.ofNat 256 (d.deltas κ) := by
  unfold storedMem
  exact foldStore_ram_at _ (fun n => word (Layout.deltaCell n)) _ (fun n => wordStore_ram _) 2
    (fun first second fb sb ne => word_ne (by unfold Layout.deltaCell; omega) (by unfold Layout.deltaCell; omega)
      (by unfold Layout.deltaCell; omega)) _ _ κ

theorem stored_zeros (memory : Memory) (d : Draw) (j : Fin labelCount) :
    (storedMem memory d).ram (word (keyBase + 2 * j.val)) = BitVec.ofNat 256 (d.zeros j) := by
  have jSmall : j.val < 508 := j.isLt
  unfold storedMem
  rw [foldStore_ram_off _ (fun n => word (Layout.deltaCell n)) _ (fun n => wordStore_ram _) 2 _ _ _
      (fun n bound => word_ne (by unfold keyBase; omega) (by unfold Layout.deltaCell; omega)
        (by unfold keyBase Layout.deltaCell; omega))]
  exact foldStore_ram_at _ (fun n => word (keyBase + 2 * n)) _ (fun n => wordStore_ram _) labelCount
    (fun first second fb sb ne => word_ne (by unfold keyBase labelCount at *; omega)
      (by unfold keyBase labelCount at *; omega) (by omega)) _ _ j

set_option maxRecDepth 400000 in
theorem stored_digits (memory : Memory) (d : Draw) (n : Fin (recordCount * moduliCount)) :
    (storedMem memory d).ram (word (digitAddr n.val)) = BitVec.ofNat 256 (d.digits n) := by
  have range := digitAddr_range n.val n.isLt
  unfold storedMem
  rw [foldStore_ram_off _ (fun n => word (Layout.deltaCell n)) _ (fun n => wordStore_ram _) 2 _ _ _
      (fun k bound => word_ne (by omega) (by unfold Layout.deltaCell; omega) (by unfold Layout.deltaCell; omega)),
    foldStore_ram_off _ (fun n => word (keyBase + 2 * n)) _ (fun n => wordStore_ram _) labelCount _ _ _
      (fun k bound => word_ne (by omega) (by unfold keyBase labelCount at *; omega)
        (by unfold keyBase labelCount at *; omega))]
  exact foldStore_ram_at _ (fun n => word (digitAddr n)) _ (fun n => cellStore_ram _) (recordCount * moduliCount)
    digitAddr_injective _ _ n

set_option maxRecDepth 400000 in
theorem stored_pins (memory : Memory) (d : Draw) (n : Fin (2 * (pinCount * 128))) :
    (storedMem memory d).ram (word (pinAddr n.val)) = BitVec.ofNat 256 (d.pins n) := by
  have range := pinAddr_range n.val n.isLt
  unfold storedMem
  rw [foldStore_ram_off _ (fun n => word (Layout.deltaCell n)) _ (fun n => wordStore_ram _) 2 _ _ _
      (fun k bound => word_ne (by omega) (by unfold Layout.deltaCell; omega) (by unfold Layout.deltaCell; omega)),
    foldStore_ram_off _ (fun n => word (keyBase + 2 * n)) _ (fun n => wordStore_ram _) labelCount _ _ _
      (fun k bound => word_ne (by omega) (by unfold keyBase labelCount at *; omega)
        (by unfold keyBase labelCount at *; omega)),
    foldStore_ram_off _ (fun n => word (digitAddr n)) _ (fun n => cellStore_ram _) (recordCount * moduliCount) _ _ _
      (fun k bound => by have := digitAddr_range k bound; exact word_ne (by omega) (by omega) (by omega))]
  exact foldStore_ram_at _ (fun n => word (pinAddr n)) _ (fun n => wordStore_ram _) (2 * (pinCount * 128))
    pinAddr_injective _ _ n

theorem stored_joins (memory : Memory) (d : Draw) (n : Fin (2 * joinCount)) :
    (storedMem memory d).ram (word (joinAddr n.val)) = BitVec.ofNat 256 (d.joins n) := by
  have range := joinAddr_range n.val n.isLt
  rw [stored_ram_upto_joins memory d _ (by omega) (by omega) (by unfold keyBase labelCount; omega) (by omega)
    (by omega)]
  exact foldStore_ram_at _ (fun n => word (joinAddr n)) _ (fun n => wordStore_ram _) (2 * joinCount)
    joinAddr_injective _ _ n

theorem stored_bytes (memory : Memory) (d : Draw) (n : Fin exceptionByteCount) :
    (storedMem memory d).ram (word (exceptionBase + n.val)) = BitVec.ofNat 256 (d.bytes n) := by
  have small : n.val < 1092 := n.isLt
  rw [stored_ram_upto_joins memory d _ (by unfold exceptionBase; omega) (by unfold exceptionBase; omega)
      (by unfold exceptionBase keyBase labelCount; omega) (by unfold exceptionBase; omega) (by unfold exceptionBase; omega),
    foldStore_ram_off _ (fun n => word (joinAddr n)) _ (fun n => wordStore_ram _) (2 * joinCount) _ _ _
      (fun k bound => by
        have := joinAddr_range k bound
        exact word_ne (by unfold exceptionBase; omega) (by omega) (by unfold exceptionBase; omega))]
  exact foldStore_ram_at _ (fun n => word (exceptionBase + n)) _ (fun n => wordStep_ram exceptionBase n) exceptionByteCount
    (fun first second fb sb ne => word_ne (by unfold exceptionBase exceptionByteCount at *; omega)
      (by unfold exceptionBase exceptionByteCount at *; omega) (by omega)) _ _ n

theorem stored_fields (memory : Memory) (d : Draw) (n : Fin fieldCount) :
    (storedMem memory d).ram (word (fieldBase + n.val)) = BitVec.ofNat 256 (d.fields n).val := by
  have small : n.val < 276 := n.isLt
  rw [stored_ram_upto_joins memory d _ (by unfold fieldBase; omega) (by unfold fieldBase; omega)
      (by unfold fieldBase keyBase labelCount; omega) (by unfold fieldBase; omega) (by unfold fieldBase; omega),
    foldStore_ram_off _ (fun n => word (joinAddr n)) _ (fun n => wordStore_ram _) (2 * joinCount) _ _ _
      (fun k bound => by
        have := joinAddr_range k bound
        exact word_ne (by unfold fieldBase; omega) (by omega) (by unfold fieldBase; omega)),
    foldStore_ram_off _ (fun n => word (exceptionBase + n)) _ (fun n => wordStep_ram exceptionBase n)
      exceptionByteCount _ _ _
      (fun k bound => word_ne (by unfold fieldBase; omega) (by unfold exceptionBase exceptionByteCount at *; omega)
        (by unfold fieldBase exceptionBase exceptionByteCount at *; omega))]
  exact foldStore_ram_at _ (fun n => word (fieldBase + n)) _ (fun n => cellStep_ram fieldBase n) fieldCount
    (fun first second fb sb ne => word_ne (by unfold fieldBase fieldCount curveCellCount rowCellCount at *; omega)
      (by unfold fieldBase fieldCount curveCellCount rowCellCount at *; omega) (by omega)) _ _ n

theorem toNat_ofNat_small (value : Nat) (small : value < 2 ^ 256) : (BitVec.ofNat 256 value).toNat = value := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

/-- **The stored memory holds exactly the draws.** -/
theorem readDraw_stored (memory : Memory) (d : Draw) (small : DrawSmall d) :
    readDraw (storedMem memory d).ram = d := by
  obtain ⟨f, b, j, p, g, z, dl⟩ := d
  simp only [readDraw, Draw.mk.injEq]
  refine ⟨funext fun n => ?_, funext fun n => ?_, funext fun n => ?_, funext fun n => ?_, funext fun n => ?_,
    funext fun n => ?_, funext fun n => ?_⟩
  · rw [stored_fields, toNat_ofNat_small _ (lt_trans (f n).val_lt (by unfold baseFieldModulus; norm_num))]
    exact ZMod.natCast_zmod_val _
  · rw [stored_bytes, toNat_ofNat_small _ (small.bytes n)]
  · rw [stored_joins, toNat_ofNat_small _ (small.joins n)]
  · rw [stored_pins, toNat_ofNat_small _ (small.pins n)]
  · rw [stored_digits, toNat_ofNat_small _ (small.digits n)]
  · rw [stored_zeros, toNat_ofNat_small _ (small.zeros n)]
  · rw [stored_deltas, toNat_ofNat_small _ (small.deltas n)]

end

end CrtStored

end Kriterion.CRT.SimMachine
