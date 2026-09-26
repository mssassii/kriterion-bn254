/-
**The flat indices of the source are small** (M5b): `chunkJoinBase`, `modJoinBase`,
`modPinBase` and the rows `rowAt` of the real table are bounded, so every source cell the replay
reads lies in its region, below the replay's scratch.
-/

import Proof.Simulator.CRT.ReplayTableFacts
import Construction.CRT.Layout

namespace Kriterion.CRT.SimMachine

open Kriterion.CRT Finset

namespace IndexFacts

theorem chunkJoinBase_le (c : Nat) : Entry.chunkJoinBase c ≤ 8 * c := by
  unfold Entry.chunkJoinBase
  calc ∑ c' : Fin c, (Entry.table.chunkWidth c'.val - 1) ≤ ∑ _c' : Fin c, 8 :=
        sum_le_sum fun c' _ => by rw [TableFacts.chunkWidth]; omega
    _ = 8 * c := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

theorem rowAt_eq (i : Nat) (h : i < Entry.table.count) (row : OddRow)
    (kind : Entry.table.kind ⟨i, h⟩ = .odd row) : Entry.rowAt i = row := by
  unfold Entry.rowAt CrtTable.kindAt
  rw [dif_pos h, kind]

/-- Every row the table's `rowAt` returns has width at most 14 and its stages inside. -/
theorem rowAt_bounds (i : Nat) :
    (Entry.rowAt i).ell ≤ 14 ∧ (Entry.rowAt i).width0 ≤ 12 ∧ (Entry.rowAt i).width1 ≤ 12 ∧
      (Entry.rowAt i).keep ≤ (Entry.rowAt i).ell ∧ (Entry.rowAt i).width0 ≤ (Entry.rowAt i).keep := by
  unfold Entry.rowAt
  split
  · rename_i row kindAt
    unfold CrtTable.kindAt at kindAt
    split at kindAt
    · rename_i h
      simp only [Option.some.injEq] at kindAt
      obtain ⟨w0, w1, ellEq, keepGe, keepLe, ellLe, _⟩ := TableFacts.odd_facts ⟨i, h⟩ row kindAt
      omega
    · cases kindAt
  · simp

theorem modJoins_kind_le (i : Fin Entry.table.count) : Entry.modJoins (Entry.table.kind i) ≤ 64 := by
  cases hk : Entry.table.kind i with
  | chunkZero => simp [Entry.modJoins]
  | odd row =>
      obtain ⟨w0, w1, ellEq, keepGe, keepLe, ellLe, _⟩ := TableFacts.odd_facts i row hk
      simp only [Entry.modJoins]
      omega

theorem kindAt_eq (i : Nat) (h : i < Entry.table.count) :
    Entry.table.kindAt i = some (Entry.table.kind ⟨i, h⟩) := by
  unfold CrtTable.kindAt
  rw [dif_pos h]

theorem kindAt_none (i : Nat) (h : ¬ i < Entry.table.count) : Entry.table.kindAt i = none := by
  unfold CrtTable.kindAt
  rw [dif_neg h]

theorem modJoinBase_le (i : Nat) : Entry.modJoinBase i ≤ 256 + 64 * i := by
  unfold Entry.modJoinBase
  have chunks := chunkJoinBase_le Entry.table.chunkCount
  rw [TableFacts.chunkCount] at chunks ⊢
  refine le_trans (add_le_add chunks (sum_le_sum fun i' _ => (?_ : _ ≤ 64))) ?_
  · by_cases h : i'.val < Entry.table.count
    · rw [kindAt_eq _ h]
      exact modJoins_kind_le _
    · rw [kindAt_none _ h]
      exact Nat.zero_le _
  · rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    omega

theorem modPinBase_le (i : Nat) : Entry.modPinBase i ≤ 32 + 2 * i := by
  unfold Entry.modPinBase
  rw [TableFacts.chunkCount]
  refine le_trans (add_le_add le_rfl (sum_le_sum fun i' _ => (?_ : _ ≤ 2))) ?_
  · by_cases h : i'.val < Entry.table.count
    · rw [kindAt_eq _ h]
      cases Entry.table.kind ⟨i'.val, h⟩ <;> simp [Entry.modPinWidths]
    · rw [kindAt_none _ h]
      exact Nat.zero_le _
  · rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    omega

end IndexFacts

end Kriterion.CRT.SimMachine
