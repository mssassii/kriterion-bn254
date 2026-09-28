/-
**No chunk joins: the actual Lamport key is a function of the coins' label keys and the coordinates' in-range
conversion readings.**

The actual zero label of bit `j` of coordinate `κ` is `Z_j ⊕ embed (chunkShift J j)` (`Entry.keyZeroOf`,
`Entry.absorbedOf`), and every chunk join it absorbs (`J c n` with `j = 8 c + n`, `1 ≤ n < w_c`, `j < 254`) is a
component of the in-range reading `Conv.readPub table pub` (`chunkShift_readPub`). So two garblings whose coins agree on
the label keys and whose coordinate garblings have the same in-range readings return the same actual zero labels
(`keyZero_congr`) and the same key (`keyOf_congr`). This is a functional-dependence fact only; it says nothing about the
law of the labels.
-/

import Proof.Privacy.CRT.Core.Conversion
import Proof.Correctness.CRT.EntryCorrect

namespace Kriterion.CRT.Privacy.KeyZero

open Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Conv (readPub)

theorem table_chunkBits : table.chunkBits = 8 := rfl

theorem table_inputBits : table.inputBits = 254 := rfl

/-- **The absorbed chunk joins are read in range**: equal in-range readings give equal chunk shifts on the
coordinate's bits. -/
theorem chunkShift_readPub (p q : ConvPublic) (h : readPub table p = readPub table q) (j : ℕ) (hj : j < 254) :
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
    have hn : j % 8 - 1 < table.chunkWidth (j / 8) - 1 := by
      unfold CrtTable.chunkWidth
      rw [table_inputBits, table_chunkBits]
      omega
    have e := congrFun (congrFun (congrArg (fun v => v.1.1) h) ⟨j / 8, hc⟩) ⟨j % 8 - 1, hn⟩
    simp only [readPub] at e
    rwa [Nat.sub_add_cancel (by omega)] at e

/-- **The actual zero labels read the coins' zero labels and the coordinates' in-range readings.** -/
theorem keyZero_congr {H H' : HashN} {c1 c2 : Coins} (hZ : c1.inputZero = c2.inputZero)
    (hx : readPub table (EntryCorrect.gxOf H c1).pub = readPub table (EntryCorrect.gxOf H' c2).pub)
    (hy : readPub table (EntryCorrect.gyOf H c1).pub = readPub table (EntryCorrect.gyOf H' c2).pub) :
    EntryCorrect.keyZero H c1 = EntryCorrect.keyZero H' c2 := by
  funext coord pos
  unfold EntryCorrect.keyZero keyZeroOf absorbedOf zeroOf
  rw [hZ]
  by_cases h0 : coord = 0
  · simp only [if_pos h0]
    rw [chunkShift_readPub _ _ hx pos.val pos.isLt]
  · simp only [if_neg h0]
    rw [chunkShift_readPub _ _ hy pos.val pos.isLt]

/-- **The actual key reads the coins' label keys and the coordinates' in-range readings.** -/
theorem keyOf_congr {H H' : HashN} {c1 c2 : Coins} (hZ : c1.inputZero = c2.inputZero)
    (hD : c1.inputDelta = c2.inputDelta)
    (hx : readPub table (EntryCorrect.gxOf H c1).pub = readPub table (EntryCorrect.gxOf H' c2).pub)
    (hy : readPub table (EntryCorrect.gyOf H c1).pub = readPub table (EntryCorrect.gyOf H' c2).pub) :
    EntryCorrect.keyOf H c1 = EntryCorrect.keyOf H' c2 := by
  unfold EntryCorrect.keyOf deltaOf
  rw [keyZero_congr hZ hx hy, hD]

end Kriterion.CRT.Privacy.KeyZero
