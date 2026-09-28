/-
**The source's labels are independent of its published value** (H8's
`CrtFlagMass`).

`Entry.Source` is a product: `publish` reads the curve, rows, exception entries, joins, pins and records,
and `labels` reads only the Lamport key (`zeros`, `deltas`). So under the uniform source the pair
`(publish s, labels s u)` is the product of the published law and the label law (`publish_labels_split`), and every
label position is uniform on `Block` (`labelLaw_position`).
-/

import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.EntrySplit

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open scoped ENNReal

noncomputable section

/-- The uniform law on a product is the product of the uniform laws (xinshu's `uniformOfFintype_productPMF`). -/
theorem uniform_prod_eq_bind {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    PMF.uniformOfFintype (A × B) =
      (PMF.uniformOfFintype A).bind fun a => (PMF.uniformOfFintype B).map fun b => (a, b) :=
  Kriterion.ArgoMAC.Security.Phase3.uniformOfFintype_productPMF

/-- The Lamport key of a source. -/
abbrev LabelKey := (Fin 2 → Fin coordinateBitCount → Block) × (Fin 2 → Block)

/-- The published cells of a source. Pin widths are the reduced stored widths;
the source contains no redundant zero parity plane. -/
abbrev Cells := (BaseField × BaseField × BaseField) × (Fin digitCount → RowGamma) ×
  (Fin digitCount → Exception.Entry) × (Fin 2 → Fin Entry.joinCount → Label) ×
  (Fin 2 → (k : Fin Entry.pinCount) → Lanes (Entry.pinWidth k)) × (Fin Entry.xCount → Fin Entry.table.product) ×
  (Fin Entry.yCount → Fin Entry.table.product)

/-- A source is its published cells and its Lamport key. -/
def split : Entry.Source ≃ Cells × LabelKey where
  toFun s := ((s.curve, s.rows, s.exception, s.joins, s.pins, s.recX, s.recY), (s.zeros, s.deltas))
  invFun p := ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance cellsKeyFinite : Finite (Cells × LabelKey) := Finite.of_equiv _ split

instance labelKeyNonempty : Nonempty LabelKey := ⟨(fun _ _ => 0, fun _ => 0)⟩

instance cellsFinite : Finite Cells :=
  Finite.of_surjective (Prod.fst : Cells × LabelKey → Cells) fun c => ⟨(c, Classical.arbitrary LabelKey), rfl⟩

instance cellsNonempty : Nonempty Cells := ⟨(split (Classical.arbitrary Entry.Source)).1⟩

instance cellsFintype : Fintype Cells := Fintype.ofFinite _

instance labelKeyFintype : Fintype LabelKey := Fintype.ofFinite _

/-- The label key of a source's labels, as a function of the key alone. -/
def labelsOfKey (k : LabelKey) (u : AffineInput) : GarbledCircuit.LamportSignature :=
  Entry.labels (split.symm ((split (Classical.arbitrary Entry.Source)).1, k)) u

/-- The label law at `u`: the labels of a uniform Lamport key. -/
def labelLaw (u : AffineInput) : PMF GarbledCircuit.LamportSignature :=
  (PMF.uniformOfFintype LabelKey).map fun k => labelsOfKey k u

/-- The published value of a source's cells. -/
def publishCells (c : Cells) : Entry.Public := Entry.publish (split.symm (c, Classical.arbitrary _))

theorem publish_split (c : Cells) (k : LabelKey) : Entry.publish (split.symm (c, k)) = publishCells c := rfl

theorem labels_split (c : Cells) (k : LabelKey) (u : AffineInput) :
    Entry.labels (split.symm (c, k)) u = labelsOfKey k u := rfl

/-- The uniform source is the uniform cells and the uniform key. -/
theorem uniform_source :
    (letI := Fintype.ofFinite Entry.Source; PMF.uniformOfFintype Entry.Source) =
      (PMF.uniformOfFintype (Cells × LabelKey)).map split.symm := by
  letI := Fintype.ofFinite Entry.Source
  exact (Kriterion.CRT.Privacy.BMR.uniform_map_equiv split.symm).symm

/-- **The published value and the labels are independent under the uniform source.** -/
theorem publish_labels_split (u : AffineInput) :
    (letI := Fintype.ofFinite Entry.Source
     (PMF.uniformOfFintype Entry.Source).map fun s => (Entry.publish s, Entry.labels s u)) =
      (letI := Fintype.ofFinite Entry.Source
       ((PMF.uniformOfFintype Entry.Source).map Entry.publish).bind fun p => (labelLaw u).map fun l => (p, l)) := by
  simp only [uniform_source, PMF.map_comp, uniform_prod_eq_bind, PMF.map_bind, PMF.bind_bind]
  refine congrArg (PMF.bind (PMF.uniformOfFintype Cells)) (funext fun c => ?_)
  simp only [labelLaw, PMF.map_comp, PMF.bind_map, Function.comp_def, publish_split, labels_split]
  rw [PMF.bind_const]

/-! ### Every label position is uniform -/

/-- The coordinate of Lamport block `j` (`x` for the first 254). -/
def keyCoord (j : Fin 508) : Fin 2 := if j.val < coordinateBitCount then 0 else 1

/-- The position of Lamport block `j` within its coordinate. -/
def keyPos (j : Fin 508) : Fin coordinateBitCount :=
  if inRange : j.val < coordinateBitCount then ⟨j.val, inRange⟩
  else ⟨j.val - coordinateBitCount, by have := j.isLt; simp only [coordinateBitCount] at *; omega⟩

/-- Flip the zero label of block `j` by `d`. -/
def flipKey (j : Fin 508) (d : Block) (k : LabelKey) : LabelKey :=
  (Function.update k.1 (keyCoord j) (Function.update (k.1 (keyCoord j)) (keyPos j) (k.1 (keyCoord j) (keyPos j) ^^^ d)),
    k.2)

theorem labelsOfKey_flip (j : Fin 508) (d : Block) (k : LabelKey) (u : AffineInput) :
    (labelsOfKey (flipKey j d k) u).get j = (labelsOfKey k u).get j ^^^ d := by
  unfold labelsOfKey flipKey
  simp only [Entry.labels, split, Equiv.coe_fn_symm_mk, Vector.get_ofFn]
  by_cases low : j.val < coordinateBitCount
  · have coord : keyCoord j = 0 := by simp [keyCoord, low]
    have pos : keyPos j = ⟨j.val, low⟩ := by simp [keyPos, low]
    rw [coord, pos]
    simp only [low, dif_pos, Function.update_self]
    split_ifs <;> simp [BitVec.xor_assoc, BitVec.xor_comm]
  · have coord : keyCoord j = 1 := by simp [keyCoord, low]
    have pos : keyPos j = ⟨j.val - coordinateBitCount, by have := j.isLt; simp only [coordinateBitCount] at *; omega⟩ := by
      simp [keyPos, low]
    rw [coord, pos]
    simp only [low, dif_neg, not_false_eq_true, Function.update_self]
    split_ifs <;> simp [BitVec.xor_assoc, BitVec.xor_comm]

theorem flipKey_flipKey (j : Fin 508) (d d' : Block) (k : LabelKey) :
    flipKey j d' (flipKey j d k) = flipKey j (d ^^^ d') k := by
  unfold flipKey
  simp only [Function.update_self, Function.update_idem, BitVec.xor_assoc]

theorem flipKey_zero (j : Fin 508) (k : LabelKey) : flipKey j 0#128 k = k := by
  obtain ⟨k1, k2⟩ := k
  unfold flipKey
  rw [BitVec.xor_zero, Function.update_eq_self, Function.update_eq_self]

theorem xor_cancel_pair (b b' : Block) : (b ^^^ b') ^^^ (b' ^^^ b) = 0#128 := by
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc b' b' b, BitVec.xor_self, BitVec.zero_xor, BitVec.xor_self]

/-- **Every label position is uniform** under the label law. -/
theorem labelLaw_position (u : AffineInput) (j : Fin 508) :
    (labelLaw u).map (fun l => l.get j) = PMF.uniformOfFintype Block := by
  classical
  unfold labelLaw
  rw [PMF.map_comp]
  refine Kriterion.ArgoMAC.Security.Phase3.uniform_map_of_fibre_equiv _ fun b b' => ?_
  exact
    { toFun := fun k => ⟨flipKey j (b ^^^ b') k.1, by
        have hk : (labelsOfKey k.1 u).get j = b := k.2
        show (labelsOfKey (flipKey j (b ^^^ b') k.1) u).get j = b'
        rw [labelsOfKey_flip, hk, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]⟩
      invFun := fun k => ⟨flipKey j (b' ^^^ b) k.1, by
        have hk : (labelsOfKey k.1 u).get j = b' := k.2
        show (labelsOfKey (flipKey j (b' ^^^ b) k.1) u).get j = b
        rw [labelsOfKey_flip, hk, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]⟩
      left_inv := fun k => Subtype.ext (by
        show flipKey j (b' ^^^ b) (flipKey j (b ^^^ b') k.1) = k.1
        rw [flipKey_flipKey, xor_cancel_pair, flipKey_zero])
      right_inv := fun k => Subtype.ext (by
        show flipKey j (b ^^^ b') (flipKey j (b' ^^^ b) k.1) = k.1
        rw [flipKey_flipKey, xor_cancel_pair, flipKey_zero]) }

end

end Kriterion.CRT.EntrySplit
