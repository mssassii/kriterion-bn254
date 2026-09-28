/-
C7, the flat layout: the evaluator reads only the published cells of `ConvPublic` that `flatten`
writes, and `unflatten ∘ flatten` returns every one of them. Together: the evaluator run on the
material read back from the published blocks is the evaluator run on the garbler's material
(`coordEvalM_unflatten`), which lets `coord_delivery` apply to the published
value.

`ConvAgree T p q` says that `p` and `q` agree on every index the evaluator reads; the congruence
lemmas are program equalities (`coordEvalM T S coord p = coordEvalM T S coord q`), proved block by
block along the program's structure.
-/

import Construction.CRT.Coord
import Mathlib.Data.List.GetD
import Batteries.Data.List.Lemmas

namespace Kriterion.CRT.FlatLayout

open Cryptography Kriterion.CRT Kriterion.ArgoMAC

/-! ### Agreement on the read indices -/

/-- The published cells the evaluator reads for modulus `i` agree. -/
def ModAgree (row : OddRow) (i : Nat) (p q : ConvPublic) : Prop :=
  (∀ n, 1 ≤ n → n < row.width0 → p.stageJoin i 0 n = q.stageJoin i 0 n) ∧
  (∀ n, 1 ≤ n → n < row.width1 → p.stageJoin i 1 n = q.stageJoin i 1 n) ∧
  (∀ k < row.ell, p.stagePin i 0 k = q.stagePin i 0 k) ∧
  (∀ k < row.ell - row.width0, p.stagePin i 1 k = q.stagePin i 1 k) ∧
  (∀ j, row.width0 ≤ j → j < row.keep → p.growJoin i j = q.growJoin i j) ∧
  (∀ j, row.keep ≤ j → j < row.ell → p.foldJoin i j = q.foldJoin i j)

/-- Two published materials agree on every index the evaluator reads. -/
def ConvAgree (T : CrtTable) (p q : ConvPublic) : Prop :=
  (∀ c < T.chunkCount, ∀ n, 1 ≤ n → n < T.chunkWidth c → p.chunkJoin c n = q.chunkJoin c n) ∧
  (∀ c < T.chunkCount, ∀ k < T.castWidth, p.chunkPin c k = q.chunkPin c k) ∧
  (∀ (i : Fin T.count) (row : OddRow), T.kind i = .odd row → ModAgree row i.val p q)

/-! ### Congruence of the evaluator's blocks -/

theorem treeEvalM_congr (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel J₁ J₂ : Nat → Label)
    (levels : Nat) (agree : ∀ n, 1 ≤ n → n < levels → J₁ n = J₂ n) :
    treeEvalM tagOf value bitLabel J₁ levels = treeEvalM tagOf value bitLabel J₂ levels := by
  induction levels with
  | zero => rfl
  | succ n ih =>
      rw [treeEvalM, treeEvalM, ih fun k lower upper => agree k lower (by omega)]
      congr 1
      funext previous
      by_cases zero : n = 0
      · simp only [zero, if_true]
      · rw [if_neg zero, if_neg zero, agree n (by omega) (by omega)]

theorem growEvalM_congr (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel J₁ J₂ : Nat → Label)
    (start : Nat) (labels : Fin (2 ^ start) → Label) (count : Nat)
    (agree : ∀ k < count, J₁ (start + k) = J₂ (start + k)) :
    growEvalM tagOf value bitLabel J₁ start labels count =
      growEvalM tagOf value bitLabel J₂ start labels count := by
  induction count with
  | zero => rfl
  | succ k ih =>
      rw [growEvalM, growEvalM, ih fun j lower => agree j (by omega), agree k (by omega)]

theorem stageRoundsM_congr {rb : Nat} (w : Nat) (treeTag castTag : Nat → Nat → Nat) (sub : Lanes w)
    (value : Nat) (J₁ J₂ : Nat → Label) (pin : Lanes rb) (remaining : Nat) :
    ∀ (n : Nat), (∀ k < remaining, J₁ (n + k) = J₂ (n + k)) → ∀ (state : StageState rb),
      stageRoundsM w treeTag castTag sub value J₁ pin remaining n state =
        stageRoundsM w treeTag castTag sub value J₂ pin remaining n state := by
  induction remaining with
  | zero => intro n _ state; rfl
  | succ r ih =>
      intro n agree state
      rw [stageRoundsM, stageRoundsM]
      have here : J₁ n = J₂ n := by simpa using agree 0 (by omega)
      have round : stageRoundM w treeTag castTag sub value J₁ pin n state =
          stageRoundM w treeTag castTag sub value J₂ pin n state := by
        unfold stageRoundM
        rw [here]
      rw [round]
      congr 1
      funext next
      exact ih (n + 1) (fun k lower => by rw [show n + 1 + k = n + (k + 1) by omega]; exact agree _ (by omega)) next

theorem extStageEvalM_congr {rb : Nat} (w : Nat) (treeTag castTag : Nat → Nat → Nat)
    (remainder : Lanes rb) (value : Nat) (J₁ J₂ : Nat → Label) (pin : Lanes rb)
    (agree : ∀ n, 1 ≤ n → n < w → J₁ n = J₂ n) :
    extStageEvalM w treeTag castTag remainder value J₁ pin =
      extStageEvalM w treeTag castTag remainder value J₂ pin := by
  have rounds := stageRoundsM_congr w treeTag castTag (materialize (reduceTo w remainder)) value J₁ J₂
    pin (w - 1) 1 (fun k lower => agree (1 + k) (by omega) (by omega))
  unfold extStageEvalM
  simp only [rounds]

theorem foldsEvalM_congr (m : Nat) (tagOf : Nat → Nat → Nat) (value : Nat) (bitLabel J₁ J₂ : Nat → Label)
    (count : Nat) : ∀ (start hot : Nat) (labels : Fin m → Label),
      (∀ k < count, J₁ (start + k) = J₂ (start + k)) →
      foldsEvalM m tagOf value bitLabel J₁ count start hot labels =
        foldsEvalM m tagOf value bitLabel J₂ count start hot labels := by
  induction count with
  | zero => intro start hot labels _; rfl
  | succ count ih =>
      intro start hot labels agree
      rw [foldsEvalM, foldsEvalM]
      have here : J₁ start = J₂ start := by simpa using agree 0 (by omega)
      rw [here]
      congr 1
      funext next
      exact ih (start + 1) _ next fun k lower => by
        rw [show start + 1 + k = start + (k + 1) by omega]; exact agree _ (by omega)

theorem pinOfBlocks_congr (width : Nat) (f g : Fin width → Label) (agree : ∀ k : Fin width, f k = g k) :
    pinOfBlocks width f = pinOfBlocks width g := by
  rw [funext agree]

theorem conversionEvalM_congr (coord i : Nat) (row : OddRow) (m value : Nat) (word : Lanes row.ell)
    (p q : ConvPublic) (agree : ModAgree row i p q) :
    conversionEvalM coord i row m value word p = conversionEvalM coord i row m value word q := by
  obtain ⟨j0, j1, p0, p1, gJ, fJ⟩ := agree
  have s0 : ∀ (R : Lanes row.ell) v (pin : Lanes row.ell), extStageEvalM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) R v
      (p.stageJoin i 0) pin = extStageEvalM row.width0 (extTreeTag coord i 0) (extCastTag coord i 0) R v
      (q.stageJoin i 0) pin := fun R v pin => extStageEvalM_congr _ _ _ R v _ _ pin j0
  have s1 : ∀ (R : Lanes (row.ell - row.width0)) v (pin : Lanes (row.ell - row.width0)),
      extStageEvalM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) R v
      (p.stageJoin i 1) pin = extStageEvalM row.width1 (extTreeTag coord i 1) (extCastTag coord i 1) R v
      (q.stageJoin i 1) pin := fun R v pin => extStageEvalM_congr _ _ _ R v _ _ pin j1
  have pin0 : (fun k : Fin row.ell => p.stagePin i 0 k.val) = fun k => q.stagePin i 0 k.val :=
    funext fun k => p0 k.val k.isLt
  have pin1 : (fun k : Fin (row.ell - row.width0) => p.stagePin i 1 k.val) =
      fun k => q.stagePin i 1 k.val := funext fun k => p1 k.val k.isLt
  have grow : ∀ v bitLabel labels, growEvalM (growTag coord i) v bitLabel (p.growJoin i) row.width0
      labels (row.keep - row.width0) = growEvalM (growTag coord i) v bitLabel (q.growJoin i) row.width0
      labels (row.keep - row.width0) := fun v bitLabel labels =>
    growEvalM_congr _ _ _ _ _ _ _ _ fun k lower => gJ _ (by omega) (by omega)
  have folds : ∀ v bitLabel hot labels, foldsEvalM m (foldTag coord i) v bitLabel (p.foldJoin i)
      (row.ell - row.keep) row.keep hot labels = foldsEvalM m (foldTag coord i) v bitLabel (q.foldJoin i)
      (row.ell - row.keep) row.keep hot labels := fun v bitLabel hot labels =>
    foldsEvalM_congr _ _ _ _ _ _ _ _ _ _ fun k lower => fJ _ (by omega) (by omega)
  unfold conversionEvalM
  simp only [s0, s1, pin0, pin1, grow, folds]

theorem modEvalM_congr (T : CrtTable) (S coord : Nat) (p q : ConvPublic) (joins : Fin T.count → Fin S → Nat)
    (v : Nat) (chunks : Nat → ChunkEval T.castWidth) (i : Fin T.count)
    (agree : ∀ row, T.kind i = .odd row → ModAgree row i.val p q) :
    modEvalM T S coord p joins v chunks i = modEvalM T S coord q joins v chunks i := by
  unfold modEvalM
  split
  · rfl
  · rename_i row kind
    have conv : ∀ word, conversionEvalM coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v) word p =
        conversionEvalM coord i.val row (T.modulus i) (T.wordValue (T.modulus i) v) word q :=
      fun word => conversionEvalM_congr _ _ _ _ _ _ p q (agree row kind)
    simp only [conv]

/-- **The evaluator reads only the agreeing cells.** -/
theorem coordEvalM_congr (T : CrtTable) (S coord : Nat) (p q : ConvPublic) (records : Fin S → Nat)
    (v : Nat) (labels : Nat → Label) (agree : ConvAgree T p q) :
    coordEvalM T S coord p records v labels = coordEvalM T S coord q records v labels := by
  obtain ⟨cJ, cP, mA⟩ := agree
  have chunks : ∀ c : Fin T.chunkCount,
      chunkEvalM T coord labels v (p.chunkJoin c.val)
          (pinOfBlocks T.castWidth fun k => p.chunkPin c.val k.val) c.val =
        chunkEvalM T coord labels v (q.chunkJoin c.val)
          (pinOfBlocks T.castWidth fun k => q.chunkPin c.val k.val) c.val := by
    intro c
    have pins : (fun k : Fin T.castWidth => p.chunkPin c.val k.val) = fun k => q.chunkPin c.val k.val :=
      funext fun k => cP c.val c.isLt k.val k.isLt
    have tree := treeEvalM_congr (chunkTreeTag coord c.val) (T.chunkValue v c.val)
      (fun n => labels (T.chunkOffset c.val + n)) (p.chunkJoin c.val) (q.chunkJoin c.val)
      (T.chunkWidth c.val) fun n lower upper => cJ c.val c.isLt n lower upper
    unfold chunkEvalM
    simp only [pins, tree]
  have mods : ∀ joins chunks, modEvalM T S coord p joins v chunks = modEvalM T S coord q joins v chunks :=
    fun joins chunks => funext fun i => modEvalM_congr T S coord p q joins v chunks i
      fun row kind => mA i row kind
  unfold coordEvalM
  simp only [chunks, mods]

/-! ### Reading a concatenation back -/

theorem length_flatMap_range {α : Type} (f : Nat → List α) (len : Nat → Nat)
    (lengths : ∀ c, (f c).length = len c) (n : Nat) :
    ((List.range n).flatMap f).length = ∑ c ∈ Finset.range n, len c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
      simp [lengths]

theorem getD_flatMap_range {α : Type} (f : Nat → List α) (len : Nat → Nat)
    (lengths : ∀ c, (f c).length = len c) (d : α) :
    ∀ (n c j : Nat), c < n → j < len c →
      ((List.range n).flatMap f).getD ((∑ c' ∈ Finset.range c, len c') + j) d = (f c).getD j d := by
  intro n
  induction n with
  | zero => intro c j hc; omega
  | succ n ih =>
      intro c j hc hj
      rw [List.range_succ, List.flatMap_append]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with lower | same
      · have bound : (∑ c' ∈ Finset.range c, len c') + j < ((List.range n).flatMap f).length := by
          rw [length_flatMap_range f len lengths n]
          have split := Finset.sum_range_add_sum_Ico len (Nat.le_of_lt lower)
          have more : len c ≤ ∑ c' ∈ Finset.Ico c n, len c' :=
            Finset.single_le_sum (f := len) (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨le_refl c, lower⟩)
          omega
        rw [List.getD_append _ _ _ _ bound]
        exact ih c j lower hj
      · subst same
        have bound : ((List.range c).flatMap f).length ≤ (∑ c' ∈ Finset.range c, len c') + j := by
          rw [length_flatMap_range f len lengths c]
          omega
        rw [List.getD_append_right _ _ _ _ bound, length_flatMap_range f len lengths c]
        simp

theorem flatMap_finRange_eq {α : Type} (n : Nat) (g : Fin n → List α) :
    (List.finRange n).flatMap g =
      (List.range n).flatMap fun i => if h : i < n then g ⟨i, h⟩ else [] := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1
  funext i
  rw [dif_pos i.isLt]

/-! ### The sections of the flat layout -/

/-- Chunk `c`'s section: its joins, then its pin blocks. -/
def chunkSection (T : CrtTable) (pub : ConvPublic) (c : Nat) : List Label :=
  (List.range (T.chunkWidth c - 1)).map (fun n => pub.chunkJoin c (n + 1)) ++
    (List.range T.castWidth).map (pub.chunkPin c)

/-- Modulus `i`'s section. -/
def modSection (T : CrtTable) (pub : ConvPublic) (i : Fin T.count) : List Label :=
  match T.kind i with
  | .chunkZero => []
  | .odd row =>
    (List.range (row.width0 - 1)).map (fun n => pub.stageJoin i 0 (n + 1)) ++
    (List.range row.ell).map (pub.stagePin i 0) ++
    (List.range (row.width1 - 1)).map (fun n => pub.stageJoin i 1 (n + 1)) ++
    (List.range (row.ell - row.width0)).map (pub.stagePin i 1) ++
    (List.range (row.keep - row.width0)).map (fun n => pub.growJoin i (row.width0 + n)) ++
    (List.range (row.ell - row.keep)).map (fun n => pub.foldJoin i (row.keep + n))

/-- The modulus sections indexed by naturals (empty off range). -/
def modSectionNat (T : CrtTable) (pub : ConvPublic) (i : Nat) : List Label :=
  if h : i < T.count then modSection T pub ⟨i, h⟩ else []

/-- The block count of the modulus at a natural index. -/
def modBlocksNat (T : CrtTable) (i : Nat) : Nat :=
  match T.kindAt i with
  | some kind => modBlocks kind
  | none => 0

theorem flatten_eq (T : CrtTable) (pub : ConvPublic) :
    pub.flatten T = (List.range T.chunkCount).flatMap (chunkSection T pub) ++
      (List.range T.count).flatMap (modSectionNat T pub) := by
  unfold ConvPublic.flatten
  rw [flatMap_finRange_eq]
  rfl

theorem chunkSection_length (T : CrtTable) (pub : ConvPublic) (c : Nat) :
    (chunkSection T pub c).length = T.chunkBlocks c := by
  simp [chunkSection, CrtTable.chunkBlocks]

theorem modSectionNat_length (T : CrtTable) (pub : ConvPublic) (i : Nat) :
    (modSectionNat T pub i).length = modBlocksNat T i := by
  unfold modSectionNat modBlocksNat CrtTable.kindAt
  split
  · rename_i h
    simp only
    unfold modSection
    split <;> rename_i kind <;> simp [kind, modBlocks] <;> omega
  · rfl

theorem chunkBase_eq (T : CrtTable) (c : Nat) :
    T.chunkBase c = ∑ c' ∈ Finset.range c, T.chunkBlocks c' := by
  unfold CrtTable.chunkBase
  rw [Fin.sum_univ_eq_sum_range (fun c' => T.chunkBlocks c')]

theorem modBase_eq (T : CrtTable) (i : Nat) :
    T.modBase i = T.chunkBase T.chunkCount + ∑ i' ∈ Finset.range i, modBlocksNat T i' := by
  unfold CrtTable.modBase
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i' => modBlocksNat T i') i

theorem chunkPart_length (T : CrtTable) (pub : ConvPublic) :
    ((List.range T.chunkCount).flatMap (chunkSection T pub)).length = T.chunkBase T.chunkCount := by
  rw [length_flatMap_range _ _ (chunkSection_length T pub), chunkBase_eq]

/-- Read the flat list at a chunk position. -/
theorem flatten_chunk (T : CrtTable) (pub : ConvPublic) (c j : Nat) (hc : c < T.chunkCount)
    (hj : j < T.chunkBlocks c) :
    (pub.flatten T).getD (T.chunkBase c + j) 0 = (chunkSection T pub c).getD j 0 := by
  rw [flatten_eq]
  have inside : T.chunkBase c + j < ((List.range T.chunkCount).flatMap (chunkSection T pub)).length := by
    rw [chunkPart_length, chunkBase_eq, chunkBase_eq]
    have split := Finset.sum_range_add_sum_Ico (fun c' => T.chunkBlocks c') (Nat.le_of_lt hc)
    have more : T.chunkBlocks c ≤ ∑ c' ∈ Finset.Ico c T.chunkCount, T.chunkBlocks c' :=
      Finset.single_le_sum (f := fun c' => T.chunkBlocks c') (fun _ _ => Nat.zero_le _)
        (Finset.mem_Ico.mpr ⟨le_refl c, hc⟩)
    omega
  rw [List.getD_append _ _ _ _ inside, chunkBase_eq]
  exact getD_flatMap_range _ _ (chunkSection_length T pub) 0 _ c j hc hj

/-- Read the flat list at a modulus position. -/
theorem flatten_mod (T : CrtTable) (pub : ConvPublic) (i j : Nat) (hi : i < T.count)
    (hj : j < modBlocksNat T i) :
    (pub.flatten T).getD (T.modBase i + j) 0 = (modSectionNat T pub i).getD j 0 := by
  rw [flatten_eq, modBase_eq, Nat.add_assoc]
  rw [← chunkPart_length T pub, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact getD_flatMap_range _ _ (modSectionNat_length T pub) 0 _ i j hi hj

/-- The flat list's length is `convBlocks`. -/
theorem flatten_length (T : CrtTable) (pub : ConvPublic) : (pub.flatten T).length = T.convBlocks := by
  rw [flatten_eq, List.length_append, chunkPart_length,
    length_flatMap_range _ _ (modSectionNat_length T pub), CrtTable.convBlocks, chunkBase_eq,
    Fin.sum_univ_eq_sum_range (fun c => T.chunkBlocks c)]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => modBlocksNat T i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [modBlocksNat, CrtTable.kindAt, i.isLt]

/-! ### Round trip -/

theorem getD_left {α : Type} (a b : List α) (j : Nat) (d : α) (h : j < a.length) :
    (a ++ b).getD j d = a.getD j d := List.getD_append _ _ _ _ h

theorem getD_right {α : Type} (a b : List α) (j : Nat) (d : α) :
    (a ++ b).getD (a.length + j) d = b.getD j d := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem getD_map_range {α : Type} (f : Nat → α) (k j : Nat) (d : α) (h : j < k) :
    ((List.range k).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_right' {α : Type} (a b : List α) (n j : Nat) (d : α) (length : a.length = n) :
    (a ++ b).getD (n + j) d = b.getD j d := by
  rw [← length]; exact getD_right a b j d

theorem array_getD_toArray {α : Type} (l : List α) (i : Nat) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD]
  unfold Array.getD
  split
  · rename_i h
    simp only [List.size_toArray] at h
    simp [h]
  · rename_i h
    simp only [List.size_toArray, not_lt] at h
    simp [List.getElem?_eq_none h]

/-- The six parts of an odd modulus's section, right-associated. -/
theorem modSection_odd (T : CrtTable) (pub : ConvPublic) (i : Fin T.count) (row : OddRow)
    (kind : T.kind i = .odd row) :
    modSection T pub i =
      (List.range (row.width0 - 1)).map (fun n => pub.stageJoin i 0 (n + 1)) ++
      ((List.range row.ell).map (pub.stagePin i 0) ++
      ((List.range (row.width1 - 1)).map (fun n => pub.stageJoin i 1 (n + 1)) ++
      ((List.range (row.ell - row.width0)).map (pub.stagePin i 1) ++
      ((List.range (row.keep - row.width0)).map (fun n => pub.growJoin i (row.width0 + n)) ++
      (List.range (row.ell - row.keep)).map (fun n => pub.foldJoin i (row.keep + n)))))) := by
  unfold modSection
  rw [kind]
  simp only [List.append_assoc]

/-- **`unflatten ∘ flatten` agrees with the material on every cell the evaluator reads.** -/
theorem convAgree_unflatten (T : CrtTable) (pub : ConvPublic) :
    ConvAgree T (ConvPublic.unflatten T (pub.flatten T).toArray) pub := by
  refine ⟨fun c hc n lower upper => ?_, fun c hc k hk => ?_, fun i row kind => ?_⟩
  · show (pub.flatten T).toArray.getD (T.chunkBase c + (n - 1)) 0 = pub.chunkJoin c n
    rw [array_getD_toArray, flatten_chunk T pub c (n - 1) hc (by unfold CrtTable.chunkBlocks; omega),
      chunkSection, getD_left _ _ _ _ (by simp; omega), getD_map_range _ _ _ _ (by omega),
      Nat.sub_add_cancel lower]
  · show (pub.flatten T).toArray.getD (T.chunkBase c + (T.chunkWidth c - 1) + k) 0 = pub.chunkPin c k
    rw [array_getD_toArray, Nat.add_assoc, flatten_chunk T pub c _ hc (by unfold CrtTable.chunkBlocks; omega),
      chunkSection]
    have len : ((List.range (T.chunkWidth c - 1)).map (fun n => pub.chunkJoin c (n + 1))).length =
        T.chunkWidth c - 1 := by simp
    rw [getD_right' _ _ _ _ _ len, getD_map_range _ _ _ _ hk]
  · have hi := i.isLt
    have kindAt : T.kindAt i.val = some (.odd row) := by simp [CrtTable.kindAt, hi, kind]
    have blocks : modBlocksNat T i.val = modBlocks (.odd row) := by simp [modBlocksNat, kindAt]
    have section_ : modSectionNat T pub i.val = modSection T pub i := by simp [modSectionNat, hi]
    let J0 := (List.range (row.width0 - 1)).map (fun n => pub.stageJoin i 0 (n + 1))
    let P0 := (List.range row.ell).map (pub.stagePin i 0)
    let J1 := (List.range (row.width1 - 1)).map (fun n => pub.stageJoin i 1 (n + 1))
    let P1 := (List.range (row.ell - row.width0)).map (pub.stagePin i 1)
    let G := (List.range (row.keep - row.width0)).map (fun n => pub.growJoin i (row.width0 + n))
    let F := (List.range (row.ell - row.keep)).map (fun n => pub.foldJoin i (row.keep + n))
    have lJ0 : J0.length = row.width0 - 1 := by simp [J0]
    have lP0 : P0.length = row.ell := by simp [P0]
    have lJ1 : J1.length = row.width1 - 1 := by simp [J1]
    have lP1 : P1.length = row.ell - row.width0 := by simp [P1]
    have lG : G.length = row.keep - row.width0 := by simp [G]
    have lF : F.length = row.ell - row.keep := by simp [F]
    have whole : modSection T pub i = J0 ++ (P0 ++ (J1 ++ (P1 ++ (G ++ F)))) :=
      modSection_odd T pub i row kind
    have total : modBlocks (.odd row) = J0.length + (P0.length + (J1.length + (P1.length +
        (G.length + F.length)))) := by
      rw [lJ0, lP0, lJ1, lP1, lG, lF, modBlocks]; omega
    have at_ : ∀ j, j < modBlocks (.odd row) →
        (pub.flatten T).toArray.getD (T.modBase i.val + j) 0 =
          (J0 ++ (P0 ++ (J1 ++ (P1 ++ (G ++ F))))).getD j 0 := by
      intro j hj
      rw [array_getD_toArray, flatten_mod T pub i.val j hi (by rw [blocks]; exact hj), section_, whole]
    refine ⟨fun n lower upper => ?_, fun n lower upper => ?_, fun k hk => ?_, fun k hk => ?_,
      fun j lower upper => ?_, fun j lower upper => ?_⟩
    · simp only [ConvPublic.unflatten, ↓reduceIte]
      rw [at_ _ (by rw [total]; omega), getD_left _ _ _ _ (by rw [lJ0]; omega),
        getD_map_range _ _ _ _ (by omega), Nat.sub_add_cancel lower]
    · simp only [ConvPublic.unflatten, kindAt, ↓reduceIte, one_ne_zero]
      rw [Nat.add_assoc, Nat.add_assoc, at_ _ (by rw [total]; omega), getD_right' _ _ _ _ _ lJ0,
        getD_right' _ _ _ _ _ lP0, getD_left _ _ _ _ (by rw [lJ1]; omega),
        getD_map_range _ _ _ _ (by omega), Nat.sub_add_cancel lower]
    · simp only [ConvPublic.unflatten, kindAt, ↓reduceIte]
      rw [Nat.add_assoc, at_ _ (by rw [total]; omega), getD_right' _ _ _ _ _ lJ0,
        getD_left _ _ _ _ (by rw [lP0]; exact hk), getD_map_range _ _ _ _ hk]
    · simp only [ConvPublic.unflatten, kindAt, ↓reduceIte, one_ne_zero]
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, at_ _ (by rw [total]; omega),
        getD_right' _ _ _ _ _ lJ0, getD_right' _ _ _ _ _ lP0, getD_right' _ _ _ _ _ lJ1,
        getD_left _ _ _ _ (by rw [lP1]; exact hk), getD_map_range _ _ _ _ hk]
    · simp only [ConvPublic.unflatten, kindAt]
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, at_ _ (by rw [total]; omega),
        getD_right' _ _ _ _ _ lJ0, getD_right' _ _ _ _ _ lP0, getD_right' _ _ _ _ _ lJ1,
        getD_right' _ _ _ _ _ lP1, getD_left _ _ _ _ (by rw [lG]; omega),
        getD_map_range _ _ _ _ (by omega), Nat.add_sub_cancel' lower]
    · simp only [ConvPublic.unflatten, kindAt]
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
        at_ _ (by rw [total]; omega), getD_right' _ _ _ _ _ lJ0, getD_right' _ _ _ _ _ lP0,
        getD_right' _ _ _ _ _ lJ1, getD_right' _ _ _ _ _ lP1, getD_right' _ _ _ _ _ lG,
        getD_map_range _ _ _ _ (by omega), Nat.add_sub_cancel' lower]

end Kriterion.CRT.FlatLayout
