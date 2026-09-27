/-
**The coin split** (`BmrSplit.CoinsSplit`, row (S) of `CrtBmrSplit`).

The scheme's coins are, through an equivalence (`splitEquiv`), a pair of the rest (the clamped offsets, `ρ`, the
exception pad, the input labels) and P45's layer (`r4`, the seven unused randomizers of each digit, the bridge key
and the curve coins). The layer is `layerOf`, and the context part (`ctxPart`: the offsets and `ρ`) is read from the
rest. So under uniform coins the layer is uniform and independent of the context part (`coinsSplit`).
-/

import Proof.Privacy.CRT.Core.BmrSplit

namespace Kriterion.CRT.Privacy.BmrSplit

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate]

/-- The scheme's coins other than the layer: the clamped offsets, `(ρ, τ)`, the exception pad and the input labels. -/
abbrev Rest := {o : FieldMacToECMac.SuccessfulOffsets // ∀ [FieldCertificate] [GroupCertificate], o.IsClamped} ×
  (Fin 91 → NonZeroBase × NonZeroBase) × FieldMacToECMac.ExceptionPad ×
  (PlanB.Coord → Fin coordinateBitCount → Block) × (PlanB.Coord → Block)

/-- The row randomness of one digit from its `(ρ, τ)`, its `r4` and its seven unused randomizers. -/
def rowOf (scales : NonZeroBase × NonZeroBase) (r4 : BaseField) (unused : Fin 7 → BaseField) :
    FieldMacToECMac.RowRandomness where
  rho := scales.1
  tau := scales.2
  x := ⟨unused 0, unused 1, unused 2⟩
  y := ⟨unused 3, unused 4, r4, unused 5⟩
  z := ⟨unused 6⟩

/-- The seven unused randomizers of a row, in `bmrCoinsOf`'s order. -/
def unusedOf (row : FieldMacToECMac.RowRandomness) : Fin 7 → BaseField :=
  ![row.x.r1, row.x.r2, row.x.r4, row.y.r2, row.y.r3, row.y.r5, row.z.r1]

theorem unusedOf_rowOf (scales : NonZeroBase × NonZeroBase) (r4 : BaseField) (unused : Fin 7 → BaseField) :
    unusedOf (rowOf scales r4 unused) = unused := by
  funext k
  fin_cases k <;> rfl

theorem rowOf_parts (row : FieldMacToECMac.RowRandomness) :
    rowOf (row.rho, row.tau) row.y.r4 (unusedOf row) = row := rfl

/-- The rest and the layer of the scheme's coins. -/
def splitFun (c : Kriterion.ArgoMAC.Scheme.Coins) : Rest × Layer :=
  ((⟨c.offsets, c.offsetsClamped⟩, fun d => ((c.pointRandomness.get d).rho, (c.pointRandomness.get d).tau),
      c.exceptionPad, c.inputZero, c.inputDelta),
    layerOf c)

/-- The scheme's coins from the rest and the layer. -/
def joinFun (x : Rest × Layer) : Kriterion.ArgoMAC.Scheme.Coins where
  offsets := x.1.1.1
  offsetsClamped := x.1.1.2
  pointRandomness := Vector.ofFn fun d => rowOf (x.1.2.1 d) (x.2.1 d) (x.2.2.1 d)
  exceptionPad := x.1.2.2.1
  bridgeKey := x.2.2.2.1
  curveMask := ⟨x.2.2.2.2.1.1, x.2.2.2.2.1.2⟩
  curveR1 := x.2.2.2.2.2.1
  curveR2 := x.2.2.2.2.2.2
  inputZero := x.1.2.2.2.1
  inputDelta := x.1.2.2.2.2

theorem joinFun_row (x : Rest × Layer) (d : Fin 91) :
    (joinFun x).pointRandomness.get d = rowOf (x.1.2.1 d) (x.2.1 d) (x.2.2.1 d) := by
  unfold joinFun
  erw [Vector.get_ofFn]

theorem layerOf_eq (c : Kriterion.ArgoMAC.Scheme.Coins) :
    layerOf c = (fun d => (c.pointRandomness.get d).y.r4, fun d => unusedOf (c.pointRandomness.get d),
      (c.bridgeKey, ⟨c.curveMask.value, c.curveMask.nonzero⟩, c.curveR1, c.curveR2)) := rfl

theorem join_split (c : Kriterion.ArgoMAC.Scheme.Coins) : joinFun (splitFun c) = c := by
  obtain ⟨offsets, clamped, pr, pad, bridge, mask, r1, r2, zero, delta⟩ := c
  have rows : (Vector.ofFn fun d => rowOf ((pr.get d).rho, (pr.get d).tau) ((pr.get d).y.r4)
      (unusedOf (pr.get d))) = pr := by
    ext i hi
    simp only [Vector.getElem_ofFn, rowOf_parts]
    rfl
  unfold joinFun splitFun
  rw [layerOf_eq]
  dsimp only
  rw [rows]

theorem split_join (x : Rest × Layer) : splitFun (joinFun x) = x := by
  obtain ⟨⟨⟨offsets, clamped⟩, rho, pad, zero, delta⟩, r4, unused, bridge, ⟨mask, nonzero⟩, r1, r2⟩ := x
  have row := joinFun_row (((⟨offsets, clamped⟩, rho, pad, zero, delta), r4, unused, bridge, ⟨mask, nonzero⟩, r1, r2))
  dsimp only at row
  unfold splitFun
  rw [layerOf_eq]
  simp only [row, unusedOf_rowOf]
  rfl

/-- **The scheme's coins are the rest and the layer.** -/
def splitEquiv : Kriterion.ArgoMAC.Scheme.Coins ≃ Rest × Layer :=
  ⟨splitFun, joinFun, join_split, split_join⟩

theorem layerOf_symm (x : Rest × Layer) : layerOf (splitEquiv.symm x) = x.2 :=
  congrArg Prod.snd (splitEquiv.apply_symm_apply x)

theorem symm_apply (x : Rest × Layer) : splitEquiv.symm x = joinFun x := rfl

theorem ctxPart_splitFun (c : Kriterion.ArgoMAC.Scheme.Coins) :
    ctxPart c = ((splitFun c).1.1.1, (splitFun c).1.2.1) := rfl

theorem ctxPart_symm (x : Rest × Layer) : ctxPart (splitEquiv.symm x) = (x.1.1.1, x.1.2.1) := by
  rw [symm_apply, ctxPart_splitFun, split_join]

/-- **The layer is uniform and independent of the context part.** -/
theorem coinsSplit : CoinsSplit := by
  intro g invariant
  have swap : ∀ r l l', g (splitEquiv.symm (r, l)) l' = g (splitEquiv.symm (r, l')) l' :=
    fun r l l' => invariant _ _ _ (by rw [ctxPart_symm, ctxPart_symm])
  have uconst : ∀ l l' : Layer, PMF.uniformOfFintype Layer l = PMF.uniformOfFintype Layer l' := by
    intro l l'
    simp only [PMF.uniformOfFintype_apply]
  have key : ∑' c, g c (layerOf c) = ∑' c, ∑' l, PMF.uniformOfFintype Layer l * g c l := by
    calc ∑' c, g c (layerOf c)
        = ∑' x : Rest × Layer, g (splitEquiv.symm x) (layerOf (splitEquiv.symm x)) :=
          (splitEquiv.symm.tsum_eq fun c => g c (layerOf c)).symm
      _ = ∑' x : Rest × Layer, g (splitEquiv.symm (x.1, x.2)) x.2 := tsum_congr fun x => by rw [layerOf_symm]
      _ = ∑' r, ∑' l, g (splitEquiv.symm (r, l)) l := ENNReal.tsum_prod (f := fun r l => g (splitEquiv.symm (r, l)) l)
      _ = ∑' r, ∑' l0, ∑' l, PMF.uniformOfFintype Layer l * g (splitEquiv.symm (r, l0)) l := by
          refine tsum_congr fun r => ?_
          calc ∑' l, g (splitEquiv.symm (r, l)) l
              = (∑' l0, PMF.uniformOfFintype Layer l0) * ∑' l, g (splitEquiv.symm (r, l)) l := by
                rw [PMF.tsum_coe, one_mul]
            _ = ∑' l0, PMF.uniformOfFintype Layer l0 * ∑' l, g (splitEquiv.symm (r, l)) l :=
                ENNReal.tsum_mul_right.symm
            _ = ∑' l0, ∑' l, PMF.uniformOfFintype Layer l0 * g (splitEquiv.symm (r, l)) l := by
                simp only [ENNReal.tsum_mul_left]
            _ = _ := tsum_congr fun l0 => tsum_congr fun l => by rw [uconst l0 l, swap r l0 l]
      _ = ∑' x : Rest × Layer, ∑' l, PMF.uniformOfFintype Layer l * g (splitEquiv.symm x) l :=
          (ENNReal.tsum_prod (f := fun r l0 => ∑' l, PMF.uniformOfFintype Layer l *
            g (splitEquiv.symm (r, l0)) l)).symm
      _ = ∑' c, ∑' l, PMF.uniformOfFintype Layer l * g c l :=
          splitEquiv.symm.tsum_eq fun c => ∑' l, PMF.uniformOfFintype Layer l * g c l
  have hk : ∀ c, coinLaw c = coinLaw Kriterion.CRT.Entry.witness := by
    intro c
    simp only [coinLaw, PMF.uniformOfFintype_apply]
  calc ∑' c, coinLaw c * g c (layerOf c)
      = ∑' c, coinLaw Kriterion.CRT.Entry.witness * g c (layerOf c) := tsum_congr fun c => by rw [hk c]
    _ = coinLaw Kriterion.CRT.Entry.witness * ∑' c, g c (layerOf c) := ENNReal.tsum_mul_left
    _ = coinLaw Kriterion.CRT.Entry.witness * ∑' c, ∑' l, PMF.uniformOfFintype Layer l * g c l := by rw [key]
    _ = ∑' c, coinLaw Kriterion.CRT.Entry.witness * ∑' l, PMF.uniformOfFintype Layer l * g c l :=
        ENNReal.tsum_mul_left.symm
    _ = ∑' c, coinLaw c * ∑' l, PMF.uniformOfFintype Layer l * g c l := tsum_congr fun c => by rw [hk c]

end


end Kriterion.CRT.Privacy.BmrSplit
