/-
**CRT privacy core: the flat bridge between the conversion values and the published vector.**

`Conversion.lean` and `ConvRead.lean` state the conversion core on the in-range reading `readPub table pub : ConvVals
table` of the published material (joins as blocks, pins decoded by the dense codec). The entry publishes the flat
vector `convVector pub` (`Construction/CRT/Entry.lean`), and the stage-1 source publishes `convVector (source.conv κ)`
from its joins and pins (`Construction/CRT/Layout.lean`). This file connects the two readings.

* **B1** (`convVector_eq_flatOf`): the flat vector reads only in-range cells, and the dense codec is a bijection
  (`pinOfBlocks_injective`), so `convVector pub = flatOf (readPub table pub)` for a fixed map `flatOf`.
* **B2** (`phi_bijective`, `phi_uniform`): the source's joins and pins of one coordinate are read back by `readPub` as
  a bijection `phi` onto `ConvVals table`. The join and pin positions of `ConvVals` are enumerated by sums and sigmas
  whose `finSigmaFinEquiv` offsets are the layout's bases (`jIdx_chunk`, `jIdx_mod`, `pIdx_mod`), so `phi` is
  injective; the two sides have `2 ^ (labelBits · 3178)` elements. **No chunk joins**: the source publishes zero
  chunk joins (`Source.conv`), so `phi` reads the *full* source material `srcConvFull` (the chunk joins from the
  retained, unpublished chunk-join cells); the flat vector omits the chunk joins, so it is the same for both
  (`convVector_srcConv`).
* `source_joins_pins_uniform`, `source_crt_law`: under a uniform source the joins and pins of coordinate `κ` are
  uniform, so the source's flat vector is `flatOf` of uniform conversion values.
-/

import Proof.Privacy.CRT.Core.Conversion
import Proof.Correctness.CRT.FoldChain
import Proof.Privacy.CRT.Core.TableSplit
import Construction.CRT.Layout

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.Flat

open Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy.Conv (ConvVals StageVals ChunkVals rowOf readPub readMod RowWF emptyRow rowOf_odd
  bn254Table_wf)

noncomputable section

theorem atNat_lt {α : Type} {count : ℕ} (family : Fin count → α) (default : α) {i : ℕ} (h : i < count) :
    atNat family default i = family ⟨i, h⟩ := by
  simp [atNat, h]

/-! ### Cardinalities -/

section Card

theorem natCard_block : Nat.card Label = 2 ^ labelBits := by
  rw [Nat.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ : Label ≃ Fin (2 ^ labelBits)),
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem natCard_blocks (n : ℕ) : Nat.card (Fin n → Label) = 2 ^ (labelBits * n) := by
  rw [Nat.card_fun, natCard_block, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]

theorem natCard_lanes (w : ℕ) : Nat.card (Lanes w) = 2 ^ (labelBits * w) := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

theorem natCard_prod {α β : Type} {a b : ℕ} (ha : Nat.card α = 2 ^ (labelBits * a)) (hb : Nat.card β = 2 ^ (labelBits * b)) :
    Nat.card (α × β) = 2 ^ (labelBits * (a + b)) := by
  rw [Nat.card_prod, ha, hb, ← pow_add, Nat.mul_add]

theorem natCard_pi {ι : Type} [Fintype ι] {β : ι → Type} (f : ι → ℕ) (h : ∀ i, Nat.card (β i) = 2 ^ (labelBits * f i)) :
    Nat.card (∀ i, β i) = 2 ^ (labelBits * ∑ i, f i) := by
  rw [Nat.card_pi, Finset.prod_congr rfl fun i _ => h i, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

end Card

/-! ### The dense pin codec is a bijection -/

section Codec

theorem pinBlocks_injective {w : ℕ} (hw : 0 < w) : Function.Injective (pinBlocks (width := w)) :=
  Function.LeftInverse.injective (g := pinOfBlocks w) fun P => SliceC.pinOfBlocks_pinBlocks hw P

theorem pinBlocks_bijective {w : ℕ} (hw : 0 < w) : Function.Bijective (pinBlocks (width := w)) :=
  bijective_of_injective_card (pinBlocks_injective hw) (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, natCard_lanes, natCard_blocks])

/-- **The dense codec reads blocks injectively.** -/
theorem pinOfBlocks_injective (w : ℕ) : Function.Injective (pinOfBlocks w) :=
  Function.LeftInverse.injective (g := pinBlocks) fun blocks => Narrow.pinBlocks_pinOfBlocks blocks

/-- Two lanes of a positive width `W = w` whose blocks read the same through the codec at width `w` are equal. -/
theorem lanes_eq_of_read {W w : ℕ} (hw : W = w) (hpos : 0 < W) (A B : Lanes W)
    (h : pinOfBlocks w (fun j : Fin w => atNat (pinBlocks A) 0 j.val) =
      pinOfBlocks w (fun j : Fin w => atNat (pinBlocks B) 0 j.val)) : A = B := by
  subst hw
  have e := pinOfBlocks_injective _ h
  apply pinBlocks_injective hpos
  funext j
  have := congrFun e j
  simpa only [atNat_lt _ _ j.isLt] using this

end Codec

/-! ### The table's rows -/

theorem rowOf_table (i : Fin table.count) (row : OddRow) (hk : table.kind i = .odd row) :
    rowOf (table.kind i) (table.modulus i) = row := by
  obtain ⟨wf, hm⟩ := bn254Table_wf.rows i row hk
  rw [hk]
  exact rowOf_odd row _ wf hm

theorem kindAt_lt (i : ℕ) (h : i < table.count) : table.kindAt i = some (table.kind ⟨i, h⟩) := by
  simp [CrtTable.kindAt, h]

/-- The normalised row of modulus `i`. -/
abbrev rowI (i : Fin table.count) : OddRow := rowOf (table.kind i) (table.modulus i)

/-- The layout's row of a modulus is the normalised row. -/
theorem rowAt_eq (i : Fin table.count) : rowAt i.val = rowI i := by
  unfold rowAt rowI
  rw [kindAt_lt i.val i.isLt]
  cases hk : table.kind i with
  | chunkZero => rfl
  | odd row =>
      have e := rowOf_table i row hk
      rw [hk] at e
      exact e.symm

/-! ### B1: the flat vector reads the in-range values -/

section B1

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.flatMap_cons]
      rw [h a (by simp), ih fun b hb => h b (by simp [hb])]

theorem readMod_parts {p q : ConvPublic} {i : ℕ} {row : OddRow} (h : readMod p i row = readMod q i row) :
    (∀ n, n < row.width0 - 1 → p.stageJoin i 0 (n + 1) = q.stageJoin i 0 (n + 1)) ∧
    (∀ k, k < row.ell - 1 → p.stagePin i 0 k = q.stagePin i 0 k) ∧
    (∀ n, n < row.width1 - 1 → p.stageJoin i 1 (n + 1) = q.stageJoin i 1 (n + 1)) ∧
    (∀ k, k < row.ell - row.width0 - 1 → p.stagePin i 1 k = q.stagePin i 1 k) ∧
    (∀ n, n < row.keep - row.width0 → p.growJoin i (row.width0 + n) = q.growJoin i (row.width0 + n)) ∧
    (∀ n, n < row.ell - row.keep → p.foldJoin i (row.keep + n) = q.foldJoin i (row.keep + n)) := by
  simp only [readMod, Prod.mk.injEq] at h
  obtain ⟨⟨h0j, h0p⟩, ⟨h1j, h1p⟩, hg, hf⟩ := h
  have p0 := pinOfBlocks_injective _ h0p
  have p1 := pinOfBlocks_injective _ h1p
  exact ⟨fun n hn => congrFun h0j ⟨n, hn⟩, fun k hk => congrFun p0 ⟨k, hk⟩, fun n hn => congrFun h1j ⟨n, hn⟩,
    fun k hk => congrFun p1 ⟨k, hk⟩, fun n hn => congrFun hg ⟨n, hn⟩, fun n hn => congrFun hf ⟨n, hn⟩⟩

/-- **The flat layout reads only in-range cells**: two published materials with the same in-range reading have the
same flat list. -/
theorem flatten_congr (p q : ConvPublic) (h : readPub table p = readPub table q) :
    p.flatten table = q.flatten table := by
  simp only [readPub, Prod.mk.injEq] at h
  obtain ⟨⟨_, hp⟩, hm⟩ := h
  unfold ConvPublic.flatten
  congr 1
  · apply flatMap_congr'
    intro c hc
    rw [List.mem_range] at hc
    have pins := pinOfBlocks_injective _ (congrFun hp ⟨c, hc⟩)
    exact List.map_congr_left fun k hk => congrFun pins ⟨k, List.mem_range.mp hk⟩
  · apply flatMap_congr'
    intro i _
    have hi := readMod_parts (congrFun hm i)
    split
    · rfl
    · rename_i row hk
      rw [rowOf_table i row hk] at hi
      obtain ⟨a, b, c, d, e, f⟩ := hi
      have e1 : (List.range (row.width0 - 1)).map (fun n => p.stageJoin i 0 (n + 1)) =
          (List.range (row.width0 - 1)).map (fun n => q.stageJoin i 0 (n + 1)) :=
        List.map_congr_left fun n hn => a n (List.mem_range.mp hn)
      have e2 : (List.range (row.ell - 1)).map (p.stagePin i 0) = (List.range (row.ell - 1)).map (q.stagePin i 0) :=
        List.map_congr_left fun n hn => b n (List.mem_range.mp hn)
      have e3 : (List.range (row.width1 - 1)).map (fun n => p.stageJoin i 1 (n + 1)) =
          (List.range (row.width1 - 1)).map (fun n => q.stageJoin i 1 (n + 1)) :=
        List.map_congr_left fun n hn => c n (List.mem_range.mp hn)
      have e4 : (List.range (row.ell - row.width0 - 1)).map (p.stagePin i 1) =
          (List.range (row.ell - row.width0 - 1)).map (q.stagePin i 1) :=
        List.map_congr_left fun n hn => d n (List.mem_range.mp hn)
      have e5 : (List.range (row.keep - row.width0)).map (fun n => p.growJoin i (row.width0 + n)) =
          (List.range (row.keep - row.width0)).map (fun n => q.growJoin i (row.width0 + n)) :=
        List.map_congr_left fun n hn => e n (List.mem_range.mp hn)
      have e6 : (List.range (row.ell - row.keep)).map (fun n => p.foldJoin i (row.keep + n)) =
          (List.range (row.ell - row.keep)).map (fun n => q.foldJoin i (row.keep + n)) :=
        List.map_congr_left fun n hn => f n (List.mem_range.mp hn)
      rw [e1, e2, e3, e4, e5, e6]

theorem convVector_congr (p q : ConvPublic) (h : readPub table p = readPub table q) : convVector p = convVector q := by
  unfold convVector
  rw [flatten_congr p q h]

open Classical in
/-- The flat vector of in-range conversion values (any material with that reading; the choice does not matter by
`convVector_congr`). -/
def flatOf (v : ConvVals table) : Vector Label convCount :=
  if h : ∃ p : ConvPublic, readPub table p = v then convVector h.choose else Vector.ofFn fun _ => 0

/-- **B1: the published flat vector is a function of the in-range reading.** -/
theorem convVector_eq_flatOf (p : ConvPublic) : convVector p = flatOf (readPub table p) := by
  have h : ∃ q : ConvPublic, readPub table q = readPub table p := ⟨p, rfl⟩
  unfold flatOf
  rw [dif_pos h]
  exact convVector_congr _ _ h.choose_spec.symm

end B1

/-! ### B2: the source's joins and pins of one coordinate -/

section B2

/-- The joins and pins of one coordinate of a source. -/
abbrev JP : Type := (Fin joinCount → Label) × ((k : Fin pinCount) → Lanes (pinWidth k))

/-- A source with the given joins and pins at both coordinates. -/
def srcOf (x : JP) : Source :=
  { (Classical.arbitrary Source) with joins := fun _ => x.1, pins := fun _ => x.2 }

/-- The conversion material that joins and pins publish (`Source.conv`: zero chunk joins). -/
def srcConv (x : JP) : ConvPublic := (srcOf x).conv 0

theorem source_conv_eq (s : Source) (κ : Fin 2) : s.conv κ = srcConv (s.joins κ, s.pins κ) := rfl

/-- The **full** conversion material of joins and pins: `srcConv` with the chunk joins read from the source's
(retained, unpublished) chunk-join cells. -/
def srcConvFull (x : JP) : ConvPublic :=
  { srcConv x with chunkJoin := fun c n => (srcOf x).joinAt 0 (chunkJoinBase c + (n - 1)) }

/-- The flat layout omits the chunk joins: a material and its chunk-join update flatten alike. -/
theorem flatten_chunkJoin (T : CrtTable) (p : ConvPublic) (f : ℕ → ℕ → Label) :
    ConvPublic.flatten T { p with chunkJoin := f } = ConvPublic.flatten T p := rfl

/-- The published flat vector of the source's material is that of its full material. -/
theorem convVector_srcConv (x : JP) : convVector (srcConv x) = convVector (srcConvFull x) := by
  unfold convVector srcConvFull
  rw [flatten_chunkJoin]

/-- **The in-range reading of the source's full conversion material.** -/
def phi (x : JP) : ConvVals table := readPub table (srcConvFull x)

/-! #### Join positions -/

/-- The joins of a modulus of row `row`. -/
def modJoinsOf (row : OddRow) : ℕ :=
  (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0) + (row.ell - row.keep)

/-- The join positions of a modulus: stage 0, stage 1, growth, folds. -/
abbrev ModJoinPos (row : OddRow) : Type :=
  ((Fin (row.width0 - 1) ⊕ Fin (row.width1 - 1)) ⊕ Fin (row.keep - row.width0)) ⊕ Fin (row.ell - row.keep)

def modJoinEquiv (row : OddRow) : ModJoinPos row ≃ Fin (modJoinsOf row) :=
  (Equiv.sumCongr ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv) (Equiv.refl _)).trans
    finSumFinEquiv

/-- The join positions of a coordinate: the chunks' tree levels, then the moduli's. -/
abbrev JoinPos : Type :=
  (Σ c : Fin table.chunkCount, Fin (table.chunkWidth c.val - 1)) ⊕ (Σ i : Fin table.count, ModJoinPos (rowI i))

def joinEquiv : JoinPos ≃ Fin ((∑ c : Fin table.chunkCount, (table.chunkWidth c.val - 1)) +
    ∑ i : Fin table.count, modJoinsOf (rowI i)) :=
  (Equiv.sumCongr finSigmaFinEquiv ((Equiv.sigmaCongrRight fun i => modJoinEquiv (rowI i)).trans finSigmaFinEquiv)).trans
    finSumFinEquiv

theorem modJoins_eq (i : Fin table.count) : modJoins (table.kind i) = modJoinsOf (rowI i) := by
  unfold rowI
  cases hk : table.kind i with
  | chunkZero => rfl
  | odd row =>
      rw [← hk, rowOf_table i row hk, hk]
      rfl

theorem joinCount_eq : joinCount = (∑ c : Fin table.chunkCount, (table.chunkWidth c.val - 1)) +
    ∑ i : Fin table.count, modJoinsOf (rowI i) := by
  unfold joinCount
  rw [Finset.sum_congr rfl fun i _ => modJoins_eq i]

/-- The flat join index of a position. -/
def jIdx (p : JoinPos) : ℕ := (joinEquiv p).val

theorem jIdx_lt (p : JoinPos) : jIdx p < joinCount := by
  rw [joinCount_eq]
  exact (joinEquiv p).isLt

theorem jIdx_chunk (c : Fin table.chunkCount) (k : Fin (table.chunkWidth c.val - 1)) :
    jIdx (.inl ⟨c, k⟩) = chunkJoinBase c.val + k.val := by
  simp only [jIdx, joinEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left,
    Fin.val_castAdd, finSigmaFinEquiv_apply, Fin.val_castLE, chunkJoinBase]

theorem modJoinBase_eq (i : Fin table.count) :
    modJoinBase i.val = (∑ c : Fin table.chunkCount, (table.chunkWidth c.val - 1)) +
      ∑ i' : Fin i.val, modJoinsOf (rowI (Fin.castLE i.isLt.le i')) := by
  unfold modJoinBase chunkJoinBase
  congr 1
  apply Finset.sum_congr rfl
  intro i' _
  rw [kindAt_lt i'.val (lt_trans i'.isLt i.isLt)]
  exact modJoins_eq _

theorem modJoinEquiv_val (row : OddRow) (r : ModJoinPos row) :
    (modJoinEquiv row r).val = match r with
      | .inl (.inl (.inl a)) => a.val
      | .inl (.inl (.inr b)) => (row.width0 - 1) + b.val
      | .inl (.inr c) => (row.width0 - 1) + (row.width1 - 1) + c.val
      | .inr d => (row.width0 - 1) + (row.width1 - 1) + (row.keep - row.width0) + d.val := by
  rcases r with ((a | b) | c) | d <;> rfl

theorem jIdx_mod (i : Fin table.count) (r : ModJoinPos (rowI i)) :
    jIdx (.inr ⟨i, r⟩) = modJoinBase i.val + (modJoinEquiv (rowI i) r).val := by
  rw [modJoinBase_eq]
  simp only [jIdx, joinEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right,
    Fin.val_natAdd, Equiv.sigmaCongrRight_apply, finSigmaFinEquiv_apply]
  omega

/-- A modulus's values read at a join position. -/
def modRead {row : OddRow} (x : StageVals row) : ModJoinPos row → Label
  | .inl (.inl (.inl a)) => x.1.1 a
  | .inl (.inl (.inr b)) => x.2.1.1 b
  | .inl (.inr c) => x.2.2.1 c
  | .inr d => x.2.2.2 d

/-- The conversion values read at a join position. -/
def jRead (v : ConvVals table) : JoinPos → Label
  | .inl ⟨c, k⟩ => v.1.1 c k
  | .inr ⟨i, r⟩ => modRead (v.2 i) r

theorem joinAt_eq (x : JP) (n : ℕ) : (srcOf x).joinAt 0 n = atNat x.1 0 n := rfl

/-- **Every join position reads its join.** -/
theorem jRead_phi (x : JP) (p : JoinPos) : jRead (phi x) p = atNat x.1 0 (jIdx p) := by
  rcases p with ⟨c, k⟩ | ⟨i, r⟩
  · rw [jIdx_chunk]
    show atNat x.1 0 (chunkJoinBase c.val + (k.val + 1 - 1)) = _
    rw [Nat.add_sub_cancel]
  · rw [jIdx_mod]
    have hrow := rowAt_eq i
    rcases r with ((a | b) | c) | d
    · show atNat x.1 0 (modJoinBase i.val + (a.val + 1 - 1)) = atNat x.1 0 (modJoinBase i.val + a.val)
      rw [Nat.add_sub_cancel]
    · show atNat x.1 0 (modJoinBase i.val + ((rowAt i.val).width0 - 1) + (b.val + 1 - 1)) =
        atNat x.1 0 (modJoinBase i.val + ((rowI i).width0 - 1 + b.val))
      rw [hrow, Nat.add_sub_cancel, Nat.add_assoc]
    · show atNat x.1 0 (modJoinBase i.val + ((rowAt i.val).width0 - 1) + ((rowAt i.val).width1 - 1) +
        ((rowI i).width0 + c.val - (rowAt i.val).width0)) =
        atNat x.1 0 (modJoinBase i.val + ((rowI i).width0 - 1 + ((rowI i).width1 - 1) + c.val))
      rw [hrow, Nat.add_sub_cancel_left]
      congr 1
      omega
    · show atNat x.1 0 (modJoinBase i.val + ((rowAt i.val).width0 - 1) + ((rowAt i.val).width1 - 1) +
        ((rowAt i.val).keep - (rowAt i.val).width0) + ((rowI i).keep + d.val - (rowAt i.val).keep)) =
        atNat x.1 0 (modJoinBase i.val + ((rowI i).width0 - 1 + ((rowI i).width1 - 1) +
          ((rowI i).keep - (rowI i).width0) + d.val))
      rw [hrow, Nat.add_sub_cancel_left]
      congr 1
      omega

theorem joins_eq_of_phi {x y : JP} (h : phi x = phi y) : x.1 = y.1 := by
  funext j
  let p := joinEquiv.symm (Fin.cast joinCount_eq j)
  have hp : jIdx p = j.val := by
    simp only [jIdx, p, Equiv.apply_symm_apply, Fin.val_cast]
  have e := jRead_phi x p
  rw [h, jRead_phi y p, hp, atNat_lt _ _ j.isLt, atNat_lt _ _ j.isLt] at e
  exact e.symm

/-! #### Pin positions -/

/-- The pins of modulus `i`. -/
abbrev modPins (i : Fin table.count) : ℕ := (modPinWidths (table.kind i)).length

/-- The pin positions of a coordinate: the chunks', then two per odd modulus. -/
abbrev PinPos : Type := Fin table.chunkCount ⊕ (Σ i : Fin table.count, Fin (modPins i))

theorem pinCount_eq : pinCount = table.chunkCount + ∑ i : Fin table.count, modPins i := by
  decide +kernel

def pinEquiv : PinPos ≃ Fin (table.chunkCount + ∑ i : Fin table.count, modPins i) :=
  (Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans finSumFinEquiv

theorem pIdx_chunk (c : Fin table.chunkCount) : (pinEquiv (.inl c)).val = c.val := by
  simp [pinEquiv]

theorem modPinBase_eq (i : Fin table.count) :
    modPinBase i.val = table.chunkCount + ∑ i' : Fin i.val, modPins (Fin.castLE i.isLt.le i') := by
  unfold modPinBase
  congr 1
  apply Finset.sum_congr rfl
  intro i' _
  rw [kindAt_lt i'.val (lt_trans i'.isLt i.isLt)]
  rfl

theorem pIdx_mod (i : Fin table.count) (s : Fin (modPins i)) :
    (pinEquiv (.inr ⟨i, s⟩)).val = modPinBase i.val + s.val := by
  rw [modPinBase_eq]
  simp only [pinEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right,
    Fin.val_natAdd, finSigmaFinEquiv_apply]
  omega

/-- The chunk pins have the cast width. -/
theorem pinWidth_chunk : ∀ k : Fin pinCount, k.val < table.chunkCount → pinWidth k = table.castWidth - 1 := by
  decide +kernel

/-- The two pins of an odd modulus have the widths of its two stages. -/
theorem pinWidth_mod : ∀ (i : Fin table.count) (s : Fin (modPins i)),
    pinWidths.getD (modPinBase i.val + s.val) 0 =
      if s.val = 0 then (rowI i).ell - 1 else (rowI i).ell - (rowI i).width0 - 1 := by
  decide +kernel

theorem pinWidth_eq_getD (k : Fin pinCount) : pinWidth k = pinWidths.getD k.val 0 := by
  unfold pinWidth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k.isLt]
  rfl

theorem modPins_odd (i : Fin table.count) (n : ℕ) (hn : n < modPins i) :
    ∃ row, table.kind i = .odd row ∧ n < 2 := by
  unfold modPins at hn
  cases hk : table.kind i with
  | chunkZero =>
      rw [hk] at hn
      exact absurd hn (Nat.not_lt_zero _)
  | odd row =>
      rw [hk] at hn
      exact ⟨row, rfl, hn⟩

theorem pinBlockAt_eq (x : JP) (k : ℕ) (hk : k < pinCount) (b : ℕ) :
    (srcOf x).pinBlockAt 0 k b = atNat (pinBlocks (x.2 ⟨k, hk⟩)) 0 b := by
  simp only [Source.pinBlockAt, dif_pos hk]
  rfl

/-- A pin is read back from the codec at its own width. -/
theorem pin_eq_of_read {x y : JP} (k : ℕ) (hk : k < pinCount) (w : ℕ) (hw : pinWidth ⟨k, hk⟩ = w) (hpos : 0 < w)
    (h : pinOfBlocks w (fun j : Fin w => (srcOf x).pinBlockAt 0 k j.val) =
      pinOfBlocks w (fun j : Fin w => (srcOf y).pinBlockAt 0 k j.val)) : x.2 ⟨k, hk⟩ = y.2 ⟨k, hk⟩ := by
  simp only [pinBlockAt_eq _ k hk] at h
  exact lanes_eq_of_read hw (hw ▸ hpos) _ _ h

theorem rowI_pos (i : Fin table.count) (row : OddRow) (hk : table.kind i = .odd row) :
    0 < (rowI i).ell - 1 ∧ 0 < (rowI i).ell - (rowI i).width0 - 1 := by
  obtain ⟨⟨h1, h2, h3, _, _⟩, _⟩ := bn254Table_wf.rows i row hk
  rw [show rowI i = row from rowOf_table i row hk]
  omega

theorem chunkPin_eq (x : JP) (c k : ℕ) : (srcConvFull x).chunkPin c k = (srcOf x).pinBlockAt 0 c k := by
  dsimp only [srcConvFull, srcConv, Source.conv]

theorem stagePin_eq (x : JP) (i s k : ℕ) :
    (srcConvFull x).stagePin i s k = (srcOf x).pinBlockAt 0 (modPinBase i + s) k := by
  dsimp only [srcConvFull, srcConv, Source.conv]

theorem pins_eq_of_phi {x y : JP} (h : phi x = phi y) : x.2 = y.2 := by
  funext k
  obtain ⟨kv, kh⟩ := k
  have hpins := congrArg (fun v : ConvVals table => v.1.2) h
  have hmods := congrArg Prod.snd h
  simp only [phi, readPub, readMod, chunkPin_eq, stagePin_eq] at hpins hmods
  obtain ⟨p, hp⟩ : ∃ p, (pinEquiv p).val = kv :=
    ⟨pinEquiv.symm (Fin.cast pinCount_eq ⟨kv, kh⟩), by simp only [Equiv.apply_symm_apply, Fin.val_cast]⟩
  rcases p with c | ⟨i, ⟨sv, hsv⟩⟩
  · rw [pIdx_chunk] at hp
    subst hp
    have e : pinOfBlocks (table.castWidth - 1) (fun j : Fin (table.castWidth - 1) => (srcOf x).pinBlockAt 0 c.val j.val) =
        pinOfBlocks (table.castWidth - 1) (fun j : Fin (table.castWidth - 1) => (srcOf y).pinBlockAt 0 c.val j.val) :=
      congrFun hpins c
    exact pin_eq_of_read c.val kh (table.castWidth - 1) (pinWidth_chunk ⟨c.val, kh⟩ c.isLt) (by decide) e
  · rw [pIdx_mod] at hp
    subst hp
    obtain ⟨row, hk, hs⟩ := modPins_odd i sv hsv
    have e := congrFun hmods i
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨_, e0⟩, ⟨_, e1⟩, _, _⟩ := e
    have hw := pinWidth_mod i ⟨sv, hsv⟩
    rw [← pinWidth_eq_getD ⟨_, kh⟩] at hw
    obtain ⟨pos0, pos1⟩ := rowI_pos i row hk
    obtain rfl | rfl : sv = 0 ∨ sv = 1 := by omega
    · rw [if_pos rfl] at hw
      exact pin_eq_of_read (modPinBase i.val + 0) kh _ hw pos0 e0
    · rw [if_neg (show ¬ ((⟨1, hsv⟩ : Fin (modPins i)).val = 0) from Nat.one_ne_zero)] at hw
      exact pin_eq_of_read (modPinBase i.val + 1) kh _ hw pos1 e1

/-- **`phi` is injective.** -/
theorem phi_injective : Function.Injective phi := fun _ _ h =>
  Prod.ext (joins_eq_of_phi h) (pins_eq_of_phi h)

/-! #### Cardinalities -/

/-- The blocks of a modulus's values. -/
def stageBlocks (row : OddRow) : ℕ :=
  ((row.width0 - 1) + (row.ell - 1)) + (((row.width1 - 1) + (row.ell - row.width0 - 1)) +
    ((row.keep - row.width0) + (row.ell - row.keep)))

theorem natCard_stageVals (row : OddRow) : Nat.card (StageVals row) = 2 ^ (labelBits * stageBlocks row) :=
  natCard_prod (natCard_prod (natCard_blocks _) (natCard_lanes _))
    (natCard_prod (natCard_prod (natCard_blocks _) (natCard_lanes _))
      (natCard_prod (natCard_blocks _) (natCard_blocks _)))

theorem natCard_convVals : Nat.card (ConvVals table) =
    2 ^ (labelBits * (((∑ c : Fin table.chunkCount, (table.chunkWidth c.val - 1)) +
      ∑ _c : Fin table.chunkCount, (table.castWidth - 1)) + ∑ i : Fin table.count, stageBlocks (rowI i))) :=
  natCard_prod (natCard_prod (natCard_pi _ fun _ => natCard_blocks _) (natCard_pi _ fun _ => natCard_lanes _))
    (natCard_pi _ fun _ => natCard_stageVals _)

theorem natCard_JP : Nat.card JP = 2 ^ (labelBits * (joinCount + ∑ k : Fin pinCount, pinWidth k)) :=
  natCard_prod (natCard_blocks _) (natCard_pi _ fun _ => natCard_lanes _)

theorem blocks_eq : ((∑ c : Fin table.chunkCount, (table.chunkWidth c.val - 1)) +
      ∑ _c : Fin table.chunkCount, (table.castWidth - 1)) + ∑ i : Fin table.count, stageBlocks (rowI i) =
    joinCount + ∑ k : Fin pinCount, pinWidth k := by
  decide +kernel

theorem card_JP : Fintype.card JP = Fintype.card (ConvVals table) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, natCard_JP, natCard_convVals, blocks_eq]

/-- **B2: the source's joins and pins of a coordinate are its conversion values, bijectively.** -/
theorem phi_bijective : Function.Bijective phi :=
  bijective_of_injective_card phi_injective card_JP

theorem phi_uniform : (PMF.uniformOfFintype JP).map phi = PMF.uniformOfFintype (ConvVals table) :=
  map_uniform_of_bijective phi_bijective

end B2

/-! ### The source's law -/

section SourceLaw

open Classical in
/-- **Under a uniform source the joins and pins of a coordinate are uniform.** -/
theorem source_joins_pins_uniform [Fintype Source] (κ : Fin 2) :
    (PMF.uniformOfFintype Source).map (fun s => ((s.joins κ, s.pins κ) : JP)) = PMF.uniformOfFintype JP := by
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun a b => ?_
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  exact {
    toFun := fun s => ⟨{ s.1 with joins := Function.update s.1.joins κ b1, pins := Function.update s.1.pins κ b2 },
      by simp⟩
    invFun := fun s => ⟨{ s.1 with joins := Function.update s.1.joins κ a1, pins := Function.update s.1.pins κ a2 },
      by simp⟩
    left_inv := fun s => by
      obtain ⟨s, hs⟩ := s
      apply Subtype.ext
      cases s
      simp only [Prod.mk.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      simp only [Function.update_idem, ← h1, ← h2, Function.update_eq_self]
    right_inv := fun s => by
      obtain ⟨s, hs⟩ := s
      apply Subtype.ext
      cases s
      simp only [Prod.mk.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      simp only [Function.update_idem, ← h1, ← h2, Function.update_eq_self] }

/-- The source's flat vector of coordinate `κ` read through `flatOf` (of its full material: the flat vector omits
the chunk joins). -/
theorem source_convVector (s : Source) (κ : Fin 2) :
    convVector (s.conv κ) = flatOf (phi (s.joins κ, s.pins κ)) := by
  rw [source_conv_eq, convVector_srcConv, convVector_eq_flatOf]
  rfl

/-- **The source's flat conversion vector of coordinate `κ` is `flatOf` of uniform conversion values.** -/
theorem source_crt_law [Fintype Source] (κ : Fin 2) :
    (PMF.uniformOfFintype Source).map (fun s => convVector (s.conv κ)) =
      (PMF.uniformOfFintype (ConvVals table)).map flatOf := by
  have factor : (fun s : Source => convVector (s.conv κ)) =
      (flatOf ∘ phi) ∘ fun s : Source => ((s.joins κ, s.pins κ) : JP) := by
    funext s
    exact source_convVector s κ
  rw [factor, ← PMF.map_comp, source_joins_pins_uniform, ← PMF.map_comp, phi_uniform]

theorem publish_crtX (s : Source) : (publish s).crtX = convVector (s.conv 0) := rfl

theorem publish_crtY (s : Source) : (publish s).crtY = convVector (s.conv 1) := rfl

end SourceLaw

end

end Kriterion.CRT.Privacy.Flat
