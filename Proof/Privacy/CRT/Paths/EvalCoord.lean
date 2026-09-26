/-
**The evaluator's coordinates and `Entry.replayConv` are `Tagged`**: the conversion of an odd modulus
(two round-ordered extraction stages, growth, folds), a modulus (conversion and body), a coordinate (chunks and
moduli), and the conversion part of the replay (both coordinates). The body keys are kept exact (`modEvalKeys`,
`coordEvalKeys`): a pad key of coordinate `κ` and modulus index `i` has its residue below `m_i` and its part below the
pad count of `i`, which places it among the layout's sites and their tags.
-/

import Proof.Privacy.CRT.Paths.Extract
import Proof.Privacy.CRT.Paths.Table
import Construction.CRT.Entry

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC

/-! ### One odd modulus -/

/-- **The evaluator's conversion** of an odd modulus. -/
theorem conversionEvalM_tagged (coord idx : Nat) (row : OddRow) (m : Nat) (coordLt : coord < 2)
    (idxLt : idx < 128) (ranges : RowRanges row) (mSmall : m ≤ 65536) (value : Nat) (word : Lanes row.ell)
    (pub : ConvPublic) :
    Tagged (convKeys coord idx) (conversionEvalM coord idx row m value word pub) := by
  unfold conversionEvalM
  have growFields : Fields 4 coord idx 0 := ⟨by norm_num, coordLt, idxLt, by norm_num, by norm_num, by norm_num⟩
  have ranges' := ranges
  obtain ⟨w0, w1, keep, ell, cast0, cast1⟩ := ranges'
  refine Tagged.bind' (extStageEvalM_tagged coord idx 0 row.width0 coordLt idxLt (by norm_num) w0 cast0 word _ _ _)
    (S' := pairKeys 2 3 coord idx 1 ∪ (growKeys 4 coord idx 0 row.width0 (row.keep - row.width0) ∪
      foldKeys coord idx row.keep (row.ell - row.keep) m)) (fun e0 => ?_) ?_ ?_ ?_
  · refine Tagged.bind' (extStageEvalM_tagged coord idx 1 row.width1 coordLt idxLt (by norm_num) w1 cast1 e0.next
      _ _ _) (S' := growKeys 4 coord idx 0 row.width0 (row.keep - row.width0) ∪
        foldKeys coord idx row.keep (row.ell - row.keep) m) (fun e1 => ?_) ?_ ?_ le_rfl
    · refine Tagged.bind' (growEvalM_tagged 4 coord idx 0 growFields value _ _ row.width0 _ (row.keep - row.width0)
        (by omega)) (fun grown => foldsEvalM_tagged coord idx m coordLt idxLt mSmall value _ _
          (row.ell - row.keep) row.keep _ _ (by omega)) ?_ ?_ le_rfl
      · refine Set.disjoint_left.mpr fun k inG inF => ?_
        simp only [growKeys, foldKeys, Set.mem_setOf_eq] at inG inF
        omega
      · exact siteDisjoint_of_fam fun k inS => by
          simp only [growKeys, Set.mem_setOf_eq] at inS
          rw [inS.1]; exact ⟨by norm_num, by norm_num⟩
    · refine Set.disjoint_left.mpr fun k inA inB => ?_
      simp only [pairKeys, growKeys, foldKeys, Set.mem_union, Set.mem_setOf_eq] at inA inB
      omega
    · exact siteDisjoint_of_fam fun k inS => by
        simp only [pairKeys, Set.mem_setOf_eq] at inS
        omega
  · refine Set.disjoint_left.mpr fun k inA inB => ?_
    simp only [pairKeys, growKeys, foldKeys, Set.mem_union, Set.mem_setOf_eq] at inA inB
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [pairKeys, Set.mem_setOf_eq] at inS
      omega
  · intro k inside
    simp only [pairKeys, growKeys, foldKeys, convKeys, Set.mem_union, Set.mem_setOf_eq] at inside ⊢
    omega

/-! ### One modulus -/

/-- The keys of the evaluator at one modulus: its conversion (families 2 to 5) and its body's pads, exact. -/
def modEvalKeys (T : CrtTable) (S coord : Nat) (i : Fin T.count) : Set TagKey :=
  convKeys coord i.val ∪ bodyKeys coord i.val (T.modulus i) (T.padAnswers S i)

/-- **The evaluator of one modulus.** -/
theorem modEvalM_tagged (T : CrtTable) (S coord : Nat) (ranges : TableRanges T S) (coordLt : coord < 2)
    (pub : ConvPublic) (joins : Fin T.count → Fin S → Nat) (v : Nat) (chunks : Nat → ChunkEval T.castWidth)
    (i : Fin T.count) :
    Tagged (modEvalKeys T S coord i) (modEvalM T S coord pub joins v chunks i) := by
  have idxLt : i.val < 128 := lt_of_lt_of_le i.isLt ranges.count
  unfold modEvalM
  split
  · exact (bodyEvalM_tagged coord i.val _ S _ coordLt idxLt (ranges.modulus i) (ranges.pads i) _ _ _).mono
      Set.subset_union_right
  · rename_i row kind
    refine Tagged.bind' (materializeM_tagged _) (S' := modEvalKeys T S coord i) (fun word => ?_)
      (Set.empty_disjoint _) (fun _ inside => absurd inside id) (by simp)
    exact Tagged.bind (conversionEvalM_tagged coord i.val row _ coordLt idxLt (ranges.rows i row kind)
      (ranges.modulus i) _ word pub) (fun conversion => bodyEvalM_tagged coord i.val _ S _ coordLt idxLt
        (ranges.modulus i) (ranges.pads i) _ _ _)
      (Set.disjoint_left.mpr fun k inC inB => by
        simp only [convKeys, bodyKeys, Set.mem_setOf_eq] at inC inB
        omega)
      (siteDisjoint_of_fam fun k inS => by
        simp only [convKeys, Set.mem_setOf_eq] at inS
        omega)

/-! ### One coordinate -/

/-- The keys of the evaluator at one coordinate: its chunks (families 0 and 1) and its moduli, exact. -/
def coordEvalKeys (T : CrtTable) (S coord : Nat) : Set TagKey :=
  {k | ∃ c < T.chunkCount, k ∈ pairKeys 0 1 coord c 0} ∪ {k | ∃ i : Fin T.count, k ∈ modEvalKeys T S coord i}

theorem coordEvalKeys_sub (T : CrtTable) (S coord : Nat) : coordEvalKeys T S coord ⊆ coordKeys coord := by
  rintro k (⟨c, _, inC⟩ | ⟨i, inC | inB⟩)
  · simp only [pairKeys, coordKeys, Set.mem_setOf_eq] at inC ⊢
    omega
  · simp only [convKeys, coordKeys, Set.mem_setOf_eq] at inC ⊢
    omega
  · simp only [bodyKeys, coordKeys, Set.mem_setOf_eq] at inB ⊢
    omega

/-- **The evaluator of one coordinate.** -/
theorem coordEvalM_tagged (T : CrtTable) (S coord : Nat) (ranges : TableRanges T S) (coordLt : coord < 2)
    (pub : ConvPublic) (records : Fin S → Nat) (v : Nat) (labels : Nat → Block) :
    Tagged (coordEvalKeys T S coord) (coordEvalM T S coord pub records v labels) := by
  unfold coordEvalM
  refine Tagged.bind (Tagged.tableM (S := fun c => pairKeys 0 1 coord c 0) T.chunkCount
    (fun c => chunkEvalM_tagged T coord labels v _ _ c.val coordLt
      (lt_of_lt_of_le c.isLt ranges.chunkCount) (ranges.chunkWidth c.val c.isLt) ranges.castAnswers)
    fun i j _ _ different => ⟨?_, ?_⟩) (fun chunkTable => ?_) ?_ ?_
  · refine Set.disjoint_left.mpr fun k inI inJ => ?_
    simp only [pairKeys, Set.mem_setOf_eq] at inI inJ
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      simp only [pairKeys, Set.mem_setOf_eq] at inS
      omega
  · refine Tagged.bind_pure ((Tagged.tableM (S := fun i => if h : i < T.count then modEvalKeys T S coord ⟨i, h⟩
      else ∅) T.count (fun i => ?_) fun i j _ _ different => ⟨?_, ?_⟩).mono ?_) _
    · rw [dif_pos i.isLt]
      exact modEvalM_tagged T S coord ranges coordLt pub _ v _ i
    · refine Set.disjoint_left.mpr fun k inI inJ => ?_
      rw [dif_pos ‹i < T.count›] at inI
      rw [dif_pos ‹j < T.count›] at inJ
      simp only [modEvalKeys, convKeys, bodyKeys, Set.mem_union, Set.mem_setOf_eq] at inI inJ
      omega
    · refine siteDisjoint_of_padField TagKey.idx padField_idx ?_ ?_ fun k inS k' inS' => ?_
      · intro k inS
        rw [dif_pos ‹i < T.count›] at inS
        simp only [modEvalKeys, convKeys, bodyKeys, Set.mem_union, Set.mem_setOf_eq] at inS
        omega
      · intro k inS
        rw [dif_pos ‹j < T.count›] at inS
        simp only [modEvalKeys, convKeys, bodyKeys, Set.mem_union, Set.mem_setOf_eq] at inS
        omega
      · rw [dif_pos ‹i < T.count›] at inS
        rw [dif_pos ‹j < T.count›] at inS'
        simp only [modEvalKeys, convKeys, bodyKeys, Set.mem_union, Set.mem_setOf_eq] at inS inS'
        omega
    · rintro k ⟨i, small, inside⟩
      rw [dif_pos small] at inside
      exact ⟨⟨i, small⟩, inside⟩
  · refine Set.disjoint_left.mpr fun k inC inM => ?_
    obtain ⟨c, _, inC⟩ := inC
    obtain ⟨i, inM⟩ := inM
    simp only [pairKeys, modEvalKeys, convKeys, bodyKeys, Set.mem_union, Set.mem_setOf_eq] at inC inM
    omega
  · exact siteDisjoint_of_fam fun k inS => by
      obtain ⟨c, _, inS⟩ := inS
      simp only [pairKeys, Set.mem_setOf_eq] at inS
      omega

/-! ### The conversion part of the replay -/

/-- The keys of `Entry.replayConv`: both coordinates' evaluators. -/
def replayConvKeys : Set TagKey :=
  coordEvalKeys Entry.table Entry.xCount 0 ∪ coordEvalKeys Entry.table Entry.yCount 1

theorem replayConvKeys_sub : replayConvKeys ⊆ coordKeys 0 ∪ coordKeys 1 :=
  Set.union_subset_union (coordEvalKeys_sub _ _ _) (coordEvalKeys_sub _ _ _)

/-- **`Entry.replayConv` is `Tagged`.** -/
theorem replayConv_tagged (pub : Entry.Public) (input : BN254.AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    Tagged replayConvKeys (Entry.replayConv pub input labels) := by
  unfold Entry.replayConv
  have ranges : ∀ S, S ≤ 1000 → TableRanges Entry.table S := bn254_ranges
  refine Tagged.bind (coordEvalM_tagged Entry.table Entry.xCount 0 (ranges _ (by decide)) (by norm_num) _ _ _ _)
    (fun ex => Tagged.bind_pure (coordEvalM_tagged Entry.table Entry.yCount 1 (ranges _ (by decide)) (by norm_num)
      _ _ _ _) _) ?_ ?_
  · refine Set.disjoint_left.mpr fun k inX inY => ?_
    have x := coordEvalKeys_sub _ _ _ inX
    have y := coordEvalKeys_sub _ _ _ inY
    simp only [coordKeys, Set.mem_setOf_eq] at x y
    omega
  · refine siteDisjoint_of_padField TagKey.coord padField_coord ?_ ?_ fun k inS k' inS' => ?_
    · intro k inS
      have x := coordEvalKeys_sub _ _ _ inS
      simp only [coordKeys, Set.mem_setOf_eq] at x
      omega
    · intro k inS
      have y := coordEvalKeys_sub _ _ _ inS
      simp only [coordKeys, Set.mem_setOf_eq] at y
      omega
    · have x := coordEvalKeys_sub _ _ _ inS
      have y := coordEvalKeys_sub _ _ _ inS'
      simp only [coordKeys, Set.mem_setOf_eq] at x y
      omega

end Kriterion.CRT.Paths
