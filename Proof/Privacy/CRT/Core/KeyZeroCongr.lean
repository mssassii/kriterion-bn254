/-
**No chunk joins: the actual Lamport key is a function of the coins' label keys and the coordinates' in-range
chunk joins.**

The actual zero label of bit `j` of coordinate `κ` is `Z_j ⊕ embed (chunkShift J j)` (`Entry.keyZeroOf`,
`Entry.absorbedOf`), and every chunk join it absorbs is an in-range one (`J c n` with `j = 8 c + n`, `1 ≤ n < w_c`,
`j < 254`; `chunkShift_congr`). So two garblings whose coins agree on the label keys and whose coordinate garblings
have the same in-range chunk joins (`JoinsAgree`) return the same actual zero labels (`keyZero_congr`) and the same key
(`keyOf_congr`). (The conversion payload's in-range reading `Conv.readPub` no longer carries the chunk joins.) This is a functional-dependence fact only; it says nothing about the
law of the labels.
-/

import Proof.Privacy.CRT.Core.Conversion
import Proof.Correctness.CRT.EntryCorrect

namespace Kriterion.CRT.Privacy.KeyZero

open Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Conv (readPub)

theorem table_chunkBits : table.chunkBits = 8 := rfl

theorem table_inputBits : table.inputBits = 254 := rfl

/-- The in-range chunk joins of a material (`1 ≤ n < w_c`, `c` a chunk): the ones the actual key absorbs. -/
def JoinsAgree (p q : ConvPublic) : Prop :=
  ∀ c < table.chunkCount, ∀ n, 1 ≤ n → n < table.chunkWidth c → p.chunkJoin c n = q.chunkJoin c n

/-- **The absorbed chunk joins are the in-range ones**: materials with the same in-range chunk joins give equal
chunk shifts on the coordinate's bits. -/
theorem chunkShift_congr (p q : ConvPublic) (h : JoinsAgree p q) (j : ℕ) (hj : j < 254) :
    table.chunkShift p.chunkJoin j = table.chunkShift q.chunkJoin j := by
  unfold CrtTable.chunkShift
  rw [table_chunkBits]
  split
  · rfl
  · rename_i n0
    have hc : j / 8 < table.chunkCount := by
      unfold CrtTable.chunkCount
      rw [table_inputBits, table_chunkBits]
      omega
    have hn : j % 8 < table.chunkWidth (j / 8) := by
      unfold CrtTable.chunkWidth
      rw [table_inputBits, table_chunkBits]
      omega
    exact h (j / 8) hc (j % 8) (by omega) hn

/-- **The actual zero labels read the coins' zero labels and the coordinates' in-range chunk joins.** -/
theorem keyZero_congr {H H' : HashN} {c1 c2 : Coins} (hZ : c1.inputZero = c2.inputZero)
    (hx : JoinsAgree (EntryCorrect.gxOf H c1).pub (EntryCorrect.gxOf H' c2).pub)
    (hy : JoinsAgree (EntryCorrect.gyOf H c1).pub (EntryCorrect.gyOf H' c2).pub) :
    EntryCorrect.keyZero H c1 = EntryCorrect.keyZero H' c2 := by
  funext coord pos
  unfold EntryCorrect.keyZero keyZeroOf absorbedOf zeroOf
  rw [hZ]
  by_cases h0 : coord = 0
  · simp only [if_pos h0]
    rw [chunkShift_congr _ _ hx pos.val pos.isLt]
  · simp only [if_neg h0]
    rw [chunkShift_congr _ _ hy pos.val pos.isLt]

/-- **The actual key reads the coins' label keys and the coordinates' in-range chunk joins.** -/
theorem keyOf_congr {H H' : HashN} {c1 c2 : Coins} (hZ : c1.inputZero = c2.inputZero)
    (hD : c1.inputDelta = c2.inputDelta)
    (hx : JoinsAgree (EntryCorrect.gxOf H c1).pub (EntryCorrect.gxOf H' c2).pub)
    (hy : JoinsAgree (EntryCorrect.gyOf H c1).pub (EntryCorrect.gyOf H' c2).pub) :
    EntryCorrect.keyOf H c1 = EntryCorrect.keyOf H' c2 := by
  unfold EntryCorrect.keyOf deltaOf
  rw [keyZero_congr hZ hx hy, hD]

end Kriterion.CRT.Privacy.KeyZero
