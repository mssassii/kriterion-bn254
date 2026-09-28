/-
**P45 at the entry** (H8's `CrtBmrSplit`, parts (a) to (d); `Core/H8.lean` section 5).

* `rowsDoubling_of_doubling`: the doubling event of the real coins (either kind) shows in the true rows (a target row
  with `Z = 0` or `S = 0`), so route M's reveal `rowsDoubling` covers it when the rows kernel's coins are coupled with
  the garbler's.
* The real reading, part (a): the garbler's body on a tag table reads P45's pads (`bmrPadsOf`), and its CRT offsets
  are P45's (`gxOf_offset`, `gyOf_offset`).
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Core.BmrFlags
import Proof.Privacy.CRT.Swap.PadBridge
import Proof.Privacy.CRT.Core.ExtractStageHash
import Proof.Correctness.CRT.EntryCorrect
import Proof.Privacy.CRT.NormRows

namespace Kriterion.CRT.Privacy.BmrEntry

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

private theorem two_ne_zero_base : (2 : BaseField) ≠ 0 := by decide

/-- The sign row vanishes at `2K`: the tangent at `−K` passes through `2K` (a polynomial identity in the tangent
slope `s = 3 k_x² / (2 k_y)` and the curve equation). -/
theorem sign_double [FieldCertificate] (offset : AffineInput) (onCurve : OnCurve offset) (yNe : offset.y ≠ 0) :
    Coordinates.evaluate (Coordinates.signCoefficients offset) (Exception.doubleOffset offset) = 0 := by
  have curve : offset.y ^ 2 - offset.x ^ 3 - 3 = 0 := by
    have equation : offset.y ^ 2 = offset.x ^ 3 + 3 := onCurve
    linear_combination equation
  have two : (2 : BaseField) ≠ 0 := two_ne_zero_base
  have twoB : (2 : BaseField) * offset.y ≠ 0 := mul_ne_zero two yNe
  have hs : 2 * offset.y * (3 * offset.x ^ 2 * (2 * offset.y)⁻¹) - 3 * offset.x ^ 2 = 0 := by
    field_simp
    ring
  have key : (2 * offset.y) ^ 6 *
      Coordinates.evaluate (Coordinates.signCoefficients offset) (Exception.doubleOffset offset) = 0 := by
    simp only [Coordinates.evaluate, Coordinates.signCoefficients, Exception.doubleOffset]
    set a := offset.x
    set b := offset.y
    set s := 3 * a ^ 2 * (2 * b)⁻¹
    linear_combination (4*b^3*(243*a^10 + 162*a^8*b*s - 729*a^7*b^2 + 2187*a^7 + 108*a^6*b^2*s^2 -
        486*a^5*b^3*s + 1458*a^5*b*s + 702*a^4*b^4 + 72*a^4*b^3*s^3 - 4860*a^4*b^2 + 4374*a^4 -
        324*a^3*b^4*s^2 + 972*a^3*b^2*s^2 + 468*a^2*b^5*s + 48*a^2*b^4*s^4 - 3240*a^2*b^3*s +
        2916*a^2*b*s - 168*a*b^6 - 216*a*b^5*s^3 + 1296*a*b^4 + 648*a*b^3*s^3 - 5832*a*b^2 +
        56*b^6*s^2 + 32*b^5*s^5 - 432*b^4*s^2 + 1944*b^2*s^2)) * hs +
      (-12*b^3*(243*a^9 - 486*a^6*b^2 + 1458*a^6 + 216*a^3*b^4 - 1944*a^3*b^2 - 16*b^6 + 432*b^4)) * curve
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 6 twoB)

/-- **Doubling shows in the true rows**: at `u = exc_s` the row of digit `s / 2` has `Z = 0` (kind 0, the doubling
input, `Coordinates.exceptionalZ`) or `S = 0` (kind 1, the sign row's zero at `2K`, `sign_double`). -/
theorem rowsDoubling_of_doubling_old [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (doubling : ∃ o, Kriterion.CRT.Entry.exceptional scalar coins o = some u) :
    H8.rowsDoubling (Security.Phase3.trueRows scalar coins u) := by
  obtain ⟨o, hexc⟩ := doubling
  unfold Kriterion.CRT.Entry.exceptional at hexc
  by_cases inRange : o / 2 < digitCount
  swap
  · rw [dif_neg inRange] at hexc
    cases hexc
  rw [dif_pos inRange] at hexc
  generalize hkey : (Kriterion.CRT.Entry.outputKeysOf scalar coins).get ⟨o / 2, inRange⟩ = key at hexc
  dsimp only at hexc
  cases hphi : digitEndomorphismBase key.digit with
  | none => rw [hphi] at hexc; cases hexc
  | some phi =>
    rw [hphi] at hexc
    simp only [Option.some.injEq] at hexc
    refine ⟨⟨o / 2, inRange⟩, ?_⟩
    have six := digitEndomorphismBasePowSix key.digit phi hphi
    unfold Security.Phase3.trueRows FieldMacToECMac.evaluateRow
    simp only [FieldMacToECMac.rowsForOutputKeys, Vector.get_ofFn]
    unfold Kriterion.CRT.Entry.outputKeysOf at hkey
    rw [hkey, hphi]
    by_cases kind : o % 2 = 0
    · rw [if_pos kind] at hexc
      left
      rw [(Coordinates.evaluateRowsSome _ _ _ _ _).2.2, ← hexc, Exception.exceptionalInput_transform phi six]
      rw [Coordinates.exceptionalZ _ _ rfl, mul_zero]
    · rw [if_neg kind] at hexc
      right
      rw [(Coordinates.evaluateRowsSome _ _ _ _ _).2.1, ← hexc]
      unfold Exception.tripleInput
      rw [Exception.exceptionalInput_transform phi six,
        sign_double _ key.offset.onCurve (JacobianMixed.noAffineYZero _ key.offset.onCurve), mul_zero]

/-- At a nonzero digit the corrected true row is the old true row. -/
theorem normTrueRows_some [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput) (d : Fin 91) (phi : BaseField)
    (selected : digitEndomorphismBase ((Entry.outputKeysOf scalar coins).get d).digit = some phi) :
    NormRows.normTrueRows scalar coins u d = Security.Phase3.trueRows scalar coins u d := by
  unfold NormRows.normTrueRows BMR.nTargets Security.Phase3.trueRows
  simp only [NormRows.nctxOf, NormRows.scalesOf, Rows.unscaledOf]
  rw [FieldMacToECMac.rowsForOutputKeys, Vector.get_ofFn]
  show _ = FieldMacToECMac.evaluateRow (Coordinates.rows ((Entry.outputKeysOf scalar coins).get d).offset.coordinates
    (digitEndomorphismBase ((Entry.outputKeysOf scalar coins).get d).digit) _ _) u
  rw [selected]
  rw [← NormRows.nTargets_some]
  rfl

/-- **Doubling shows in the corrected true rows** (the exceptional digits are nonzero, where they are the old rows). -/
theorem rowsDoubling_of_doubling [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (doubling : ∃ o, Kriterion.CRT.Entry.exceptional scalar coins o = some u) :
    H8.rowsDoubling (NormRows.normTrueRows scalar coins u) := by
  obtain ⟨o, hexc⟩ := doubling
  obtain ⟨inRange, phi, selected, _⟩ := Entry.exceptional_cases scalar coins o u hexc
  obtain ⟨d, zero⟩ := rowsDoubling_of_doubling_old scalar coins u ⟨o, hexc⟩
  refine ⟨d, ?_⟩
  -- the old flag's digit is the exceptional one; it is nonzero, so the corrected row is the old row
  by_cases same : d = ⟨o / 2, inRange⟩
  · subst same
    rw [normTrueRows_some scalar coins u _ phi selected]
    exact zero
  · -- a digit other than the exceptional one flagged by the old rows: also nonzero or not, read through its own key
    cases sel : digitEndomorphismBase ((Entry.outputKeysOf scalar coins).get d).digit with
    | some psi =>
      rw [normTrueRows_some scalar coins u d psi sel]
      exact zero
    | none =>
      exfalso
      have rowsNone : Security.Phase3.trueRows scalar coins u d =
          FieldMacToECMac.evaluateRow (Coordinates.rows ((Entry.outputKeysOf scalar coins).get d).offset.coordinates
            none (coins.pointRandomness.get d).rho.value (coins.pointRandomness.get d).tau.value) u := by
        unfold Security.Phase3.trueRows
        rw [FieldMacToECMac.rowsForOutputKeys, Vector.get_ofFn, ← sel]
        rfl
      rw [rowsNone, FieldMacToECMac.evaluateRowsNone] at zero
      have onK := ((Entry.outputKeysOf scalar coins).get d).offset.onCurve
      rcases zero with z | y
      · exact (coins.pointRandomness.get d).rho.nonzero z
      · exact mul_ne_zero (pow_ne_zero 2 (coins.pointRandomness.get d).tau.nonzero)
          (JacobianMixed.noAffineYZero _ onK) y

/-- **Doubling shows in the corrected targets of every scales**: at an exceptional input the exceptional digit's
unscaled `Z` or sign row vanishes, whatever the scales. -/
theorem rowsDoubling_nTargets [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (coins : Kriterion.ArgoMAC.Scheme.Coins) (u : AffineInput)
    (doubling : ∃ o, Kriterion.CRT.Entry.exceptional scalar coins o = some u)
    (s : Fin 91 → NonZeroBase × NonZeroBase) :
    H8.rowsDoubling (BMR.nTargets (NormRows.nctxOf scalar coins) u s) := by
  let coins' : Kriterion.ArgoMAC.Scheme.Coins :=
    { coins with pointRandomness := Security.Phase3.setRho coins.pointRandomness s }
  have flagged := rowsDoubling_of_doubling scalar coins' u doubling
  have scales : NormRows.scalesOf coins' = s := Security.Phase3.rhoOf_setRho _ _
  unfold NormRows.normTrueRows at flagged
  rw [scales] at flagged
  exact flagged

/-! ### The real reading: pads and offsets -/

/-- A tag table answers a labelled input by its tag. -/
theorem tagHash_hashInput (table : TagTable) (G : Block) (tag : ℕ) :
    H8.tagHash table (Kriterion.CRT.hashInput G tag) =
      table ⟨tag % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ := by
  unfold H8.tagHash
  simp only [ExtractStage.hashInput_div]

/-- The pad digits of a body site on a tag table do not depend on the label. -/
theorem padVectorM_tagHash (table : TagTable) (m S q : ℕ) [NeZero m] (label : Label) (κ i ρ : ℕ) :
    (fun e => (((padVectorM m S q label (bodyTag κ i ρ)).eval (H8.tagHash table) e : ℕ) : ZMod m)) =
      padVector m S q (fun j => table ⟨bodyTag κ i ρ j.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩) := by
  rw [padVectorM_eq_padVector]
  simp only [tagHash_hashInput]

/-- Summing over `Fin m` through the cast is summing over `ZMod m`. -/
theorem sum_fin_cast {m : ℕ} [NeZero m] {M : Type*} [AddCommMonoid M] (f : ZMod m → M) :
    ∑ ρ : Fin m, f (ρ.val : ZMod m) = ∑ ρ : ZMod m, f ρ := by
  let e : Fin m ≃ ZMod m :=
    { toFun := fun ρ => (ρ.val : ZMod m)
      invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
      left_inv := fun ρ => Fin.ext (ZMod.val_cast_of_lt ρ.isLt)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- **The garbler's body on a tag table does not depend on the final labels.** -/
theorem bodyGarbleM_tagHash (table : TagTable) (m S q coord i : ℕ) (final : Fin m → Label) :
    (bodyGarbleM m S q coord i final).eval (H8.tagHash table) =
      (bodyGarbleM m S q coord i fun _ => 0).eval (H8.tagHash table) := by
  simp only [bodyGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, SliceC.eval_padVectorM, hlong,
    tagHash_hashInput]

/-- The body of a modulus on a tag table is the body at zero labels (either kind of modulus). -/
theorem modGarbleM_body (table : TagTable) (S coord : ℕ) (delta : Label) (chunks : ℕ → ChunkGarbled Entry.table.castWidth)
    (i : Fin Entry.table.count) :
    ((modGarbleM Entry.table S coord delta chunks i).eval (H8.tagHash table)).body =
      (bodyGarbleM (Entry.table.modulus i) S (Entry.table.padAnswers S i) coord i.val fun _ => 0).eval
        (H8.tagHash table) := by
  unfold modGarbleM
  split
  · simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]
    exact bodyGarbleM_tagHash _ _ _ _ _ _ _
  · simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]
    exact bodyGarbleM_tagHash _ _ _ _ _ _ _

/-- On the real table the layout's pad count is the garbler's. -/
theorem padCount_eq (κ : ℕ) (i : Fin Entry.table.count) :
    Layout.padCount κ i.val = Entry.table.padAnswers (Layout.padS κ) i := by
  unfold Layout.padCount
  rw [dif_pos i.isLt]

theorem packAnswers_congr {q q' : ℕ} (same : q = q') (g : ℕ → Block × Block) :
    packAnswers q (fun j => g j.val) = packAnswers q' (fun j => g j.val) := by
  subst same
  rfl

/-- `H8.padValues` at the garbler's pad count. -/
theorem padValues_eq (table : TagTable) (κ : ℕ) (i : Fin Entry.table.count) (ρ : ℕ) (e : Fin (Layout.padS κ)) :
    H8.padValues table κ i ρ e =
      ((digit (Entry.table.modulus i) (fractionValue (Entry.table.modulus i) (Layout.padS κ)
        (Entry.table.padAnswers (Layout.padS κ) i)
        (packAnswers (Entry.table.padAnswers (Layout.padS κ) i) fun j =>
          table ⟨bodyTag κ i ρ j.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩)) e.val : ℕ) :
        ZMod (Entry.table.modulus i)) := by
  unfold H8.padValues padVector
  rw [packAnswers_congr (padCount_eq κ i)
    (fun j => table ⟨tagCode Family.body κ i 0 0 ρ j % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩), padCount_eq]
  rfl

/-- **The garbler's CRT offsets on a tag table** are the CRT of its body residues. -/
theorem coordGarbleM_offset (table : TagTable) (S coord : ℕ) (delta : Label) (zero : ℕ → Label) (e : Fin S) :
    ((coordGarbleM Entry.table S coord delta zero).eval (H8.tagHash table)).offset e =
      Entry.table.crt fun i => ((bodyGarbleM (Entry.table.modulus i) S (Entry.table.padAnswers S i) coord i.val
        fun _ => 0).eval (H8.tagHash table)).residue e := by
  simp only [coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq, modGarbleM_body]
  rfl

/-- P45's pads of a tag table (encoding `e` of coordinate `κ` is entry `flat e` of the body site's pad vector). -/
def bmrPadsOf (table : TagTable) : BMR.Pads Entry.table := fun i ρ e =>
  match e with
  | .inl x => H8.padValues table 0 i ρ.val ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩
  | .inr y => H8.padValues table 1 i ρ.val ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩

/-- The body residue on a tag table, as a sum over slots. -/
theorem bodyGarbleM_residue (table : TagTable) (m S q coord i : ℕ) (e : Fin S) :
    ((bodyGarbleM m S q coord i fun _ => 0).eval (H8.tagHash table)).residue e =
      (∑ ρ : Fin m, (ρ.val : ZMod m) * ((digit m (fractionValue m S q (packAnswers q fun j =>
        table ⟨bodyTag coord i ρ.val j.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩)) e.val : ℕ) : ZMod m)).val := by
  simp only [bodyGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, SliceC.eval_padVectorM, hlong,
    tagHash_hashInput, stored_eq]

/-- **The garbler's `x` offsets on a tag table are P45's.** -/
theorem gx_offset (table : TagTable) (delta : Label) (zero : ℕ → Label) (x : BMR.XEnc) (c : BMR.Coins Entry.table)
    (pads : c.pads = bmrPadsOf table) :
    ((coordGarbleM Entry.table Entry.xCount 0 delta zero).eval (H8.tagHash table)).offset (BMR.xFlat x) =
      BMR.offset c (.inl x) := by
  rw [coordGarbleM_offset]
  unfold BMR.offset
  congr 1
  funext i
  rw [bodyGarbleM_residue]
  unfold BMR.readout
  rw [pads, ← sum_fin_cast]
  congr 2
  funext ρ
  simp only [bmrPadsOf, padValues_eq, ZMod.val_cast_of_lt ρ.isLt]
  rfl

/-- **The garbler's `y` offsets on a tag table are P45's.** -/
theorem gy_offset (table : TagTable) (delta : Label) (zero : ℕ → Label) (y : BMR.YEnc) (c : BMR.Coins Entry.table)
    (pads : c.pads = bmrPadsOf table) :
    ((coordGarbleM Entry.table Entry.yCount 1 delta zero).eval (H8.tagHash table)).offset (BMR.yFlat y) =
      BMR.offset c (.inr y) := by
  rw [coordGarbleM_offset]
  unfold BMR.offset
  congr 1
  funext i
  rw [bodyGarbleM_residue]
  unfold BMR.readout
  rw [pads, ← sum_fin_cast]
  congr 2
  funext ρ
  simp only [bmrPadsOf, padValues_eq, ZMod.val_cast_of_lt ρ.isLt]
  rfl

/-! ### The real reading: masks and element offsets -/

/-- On a tag table the masks do not depend on the key. -/
theorem maskValues_tagHash (table : TagTable) (K : Block) :
    maskValues (H8.tagHash table) K digitCount = maskValues (H8.tagHash table) 0 digitCount := by
  unfold maskValues siteAnswers
  simp only [tagHash_hashInput]

/-- P45's masks of a tag table, by row encoding. -/
def bmrMasksOf (table : TagTable) : BMR.RowEnc → BaseField
  | (d, .inl x) => maskOf (maskValues (H8.tagHash table) 0 digitCount) 0 (xElementIndex d x).val
  | (d, .inr y) => maskOf (maskValues (H8.tagHash table) 0 digitCount) 1 (yElementIndex d y).val

/-- The P45 coin reading of a table: pads and masks from the table, the rest from given coins. -/
structure Reads (table : TagTable) (c : BMR.Coins Entry.table) : Prop where
  pads : c.pads = bmrPadsOf table
  mask : c.mask = bmrMasksOf table

/-- **The garbler's `x` element offsets are P45's** (row encodings: `(O : F_p) − π`; curve encodings: `(O : F_p)`). -/
theorem offsetsX_eq (table : TagTable) (delta : Label) (zero : ℕ → Label) (K : Block) (c : BMR.Coins Entry.table)
    (reads : Reads table c) (x : BMR.XEnc) :
    Entry.offsetsX ((coordGarbleM Entry.table Entry.xCount 0 delta zero).eval (H8.tagHash table)).offset
        (maskValues (H8.tagHash table) K digitCount) (BMR.xFlat x) =
      match x with
      | .inl (d, element) => BMR.rowOffset c (d, .inl element)
      | .inr element => BMR.offsetF c (BMR.curveEnc (.inl element)) := by
  unfold Entry.offsetsX
  rw [gx_offset table delta zero x c reads.pads, maskValues_tagHash]
  rcases x with ⟨d, element⟩ | element
  · simp only [BMR.rowOffset, BMR.rowEnc, reads.mask, bmrMasksOf, BMR.offsetF, Entry.toField, BMR.xFlat]
  · have past : ¬ 364 + element.slot.val < 4 * digitCount := by
      have := element.slot.isLt; simp only [digitCount]; omega
    simp only [BMR.offsetF, BMR.curveEnc, Entry.toField, BMR.xFlat, maskOf, if_pos, past, if_false, sub_zero]

/-- **The garbler's `y` element offsets are P45's.** -/
theorem offsetsY_eq (table : TagTable) (delta : Label) (zero : ℕ → Label) (K : Block) (c : BMR.Coins Entry.table)
    (reads : Reads table c) (y : BMR.YEnc) :
    Entry.offsetsY ((coordGarbleM Entry.table Entry.yCount 1 delta zero).eval (H8.tagHash table)).offset
        (maskValues (H8.tagHash table) K digitCount) (BMR.yFlat y) =
      match y with
      | .inl (d, element) => BMR.rowOffset c (d, .inr element)
      | .inr element => BMR.offsetF c (BMR.curveEnc (.inr element)) := by
  unfold Entry.offsetsY
  rw [gy_offset table delta zero y c reads.pads, maskValues_tagHash]
  rcases y with ⟨d, element⟩ | element
  · simp only [BMR.rowOffset, BMR.rowEnc, reads.mask, bmrMasksOf, BMR.offsetF, Entry.toField, BMR.yFlat]
  · have past : ¬ 273 + element.slot.val < 3 * digitCount := by
      have := element.slot.isLt; simp only [digitCount]; omega
    simp only [BMR.offsetF, BMR.curveEnc, Entry.toField, BMR.yFlat, maskOf, past, if_false, sub_zero,
      one_ne_zero]

/-! ### The real reading: the coins, the element values, the curve and the rows -/

/-- The normalized layer's context of the scheme's coins: the unscaled rows of each digit. -/
abbrev bmrContextOf (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) : BMR.NContext :=
  NormRows.nctxOf scalar coins

/-- **P45's coins of a table tape**: pads and masks from the table; `r4`, the unused randomizers and the curve coins
from the scheme's coins. -/
def bmrCoinsOf (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) : BMR.Coins Entry.table :=
  (bmrPadsOf table, bmrMasksOf table, fun d => (coins.pointRandomness.get d).y.r4,
    fun d => ![(coins.pointRandomness.get d).x.r1, (coins.pointRandomness.get d).x.r2,
      (coins.pointRandomness.get d).x.r4, (coins.pointRandomness.get d).y.r2, (coins.pointRandomness.get d).y.r3,
      (coins.pointRandomness.get d).y.r5, (coins.pointRandomness.get d).z.r1],
    (coins.bridgeKey, ⟨coins.curveMask.value, coins.curveMask.nonzero⟩, coins.curveR1, coins.curveR2))

theorem bmrCoinsOf_reads (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) :
    Reads table (bmrCoinsOf coins table) := ⟨rfl, rfl⟩

/-- The garbler's `x` element offsets through the names. -/
theorem offXOf_eq (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc) :
    EntryCorrect.offXOf (H8.tagHash table) coins (BMR.xFlat x) =
      match x with
      | .inl (d, element) => BMR.rowOffset (bmrCoinsOf coins table) (d, .inl element)
      | .inr element => BMR.offsetF (bmrCoinsOf coins table) (BMR.curveEnc (.inl element)) := by
  unfold EntryCorrect.offXOf EntryCorrect.gxOf EntryCorrect.masksOf
  exact offsetsX_eq table _ _ _ _ (bmrCoinsOf_reads coins table) x

/-- The garbler's `y` element offsets through the names. -/
theorem offYOf_eq (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc) :
    EntryCorrect.offYOf (H8.tagHash table) coins (BMR.yFlat y) =
      match y with
      | .inl (d, element) => BMR.rowOffset (bmrCoinsOf coins table) (d, .inr element)
      | .inr element => BMR.offsetF (bmrCoinsOf coins table) (BMR.curveEnc (.inr element)) := by
  unfold EntryCorrect.offYOf EntryCorrect.gyOf EntryCorrect.masksOf
  exact offsetsY_eq table _ _ _ _ (bmrCoinsOf_reads coins table) y

/-- **The garbler's row values are P45's row offsets.** -/
theorem KOf_eq (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (d : Fin 91)
    (element : Biquadratic.Element) :
    EntryCorrect.KOf (H8.tagHash table) coins d element = BMR.rowOffset (bmrCoinsOf coins table) (d, element) := by
  unfold EntryCorrect.KOf
  rcases element with x | y
  · show Entry.pointPartX (EntryCorrect.offXOf (H8.tagHash table) coins) (xElementIndex d x) = _
    unfold Entry.pointPartX
    rw [show (⟨(xElementIndex d x).val, _⟩ : Fin Entry.xCount) = BMR.xFlat (.inl (d, x)) from rfl, offXOf_eq]
  · show Entry.pointPartY (EntryCorrect.offYOf (H8.tagHash table) coins) (yElementIndex d y) = _
    unfold Entry.pointPartY
    rw [show (⟨(yElementIndex d y).val, _⟩ : Fin Entry.yCount) = BMR.yFlat (.inl (d, y)) from rfl, offYOf_eq]

/-- **The garbler's curve values are P45's curve offsets.** -/
theorem curveKOf_eq (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) :
    EntryCorrect.curveKOf (H8.tagHash table) coins = BMR.curveK (bmrCoinsOf coins table) := by
  funext element
  unfold EntryCorrect.curveKOf
  rcases element with x | y
  · show Entry.curvePartX (EntryCorrect.offXOf (H8.tagHash table) coins) (curveXElementIndex x) = _
    unfold Entry.curvePartX
    rw [show (⟨pointElementCountX + (curveXElementIndex x).val, _⟩ : Fin Entry.xCount) = BMR.xFlat (.inr x)
      from rfl, offXOf_eq]
    rfl
  · show Entry.curvePartY (EntryCorrect.offYOf (H8.tagHash table) coins) (curveYElementIndex y) = _
    unfold Entry.curvePartY
    rw [show (⟨pointElementCountY + (curveYElementIndex y).val, _⟩ : Fin Entry.yCount) = BMR.yFlat (.inr y)
      from rfl, offYOf_eq]
    rfl

/-- **The published curve constants are P45's.** -/
theorem curve_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) :
    (EntryCorrect.pubOf (H8.tagHash table) scalar coins).curve = BMR.curveTable (bmrCoinsOf coins table) := by
  rw [EntryCorrect.pubOf_curve, curveKOf_eq]
  rfl

/-- **The published row constants are P45's.** -/
theorem rows_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (d : Fin 91) :
    (EntryCorrect.pubOf (H8.tagHash table) scalar coins).rows.get d =
      BMR.nGamma (bmrContextOf scalar coins) (bmrCoinsOf coins table) d := by
  rw [EntryCorrect.pubOf_rows]
  erw [Vector.get_ofFn]
  have values : EntryCorrect.KOf (H8.tagHash table) coins d =
      fun element => BMR.rowOffset (bmrCoinsOf coins table) (d, element) := funext (KOf_eq coins table d)
  rw [values]
  rfl

/-! ### The real reading: the slopes -/

/-- **The garbler's `x` slopes are P45's.** -/
theorem slXOf_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable)
    (x : BMR.XEnc) :
    EntryCorrect.slXOf (H8.tagHash table) scalar coins (BMR.xFlat x) =
      BMR.nSlope (bmrContextOf scalar coins) (bmrCoinsOf coins table) (.inl x) := by
  unfold EntryCorrect.slXOf Entry.slopesX Entry.joinX
  rcases x with ⟨d, element⟩ | element
  · have low : (BMR.xFlat (.inl (d, element))).val < pointElementCountX := (xElementIndex d element).isLt
    rw [dif_pos low]
    rw [show (⟨(BMR.xFlat (.inl (d, element))).val, low⟩ : Fin pointElementCountX) = xElementIndex d element
      from rfl]
    erw [Pipeline.pointXAssemble_digit]
    unfold EntryCorrect.pointOf Entry.pointSlopes EntryCorrect.rowsOf
    have values : EntryCorrect.KOf (H8.tagHash table) coins =
        fun d element => BMR.rowOffset (bmrCoinsOf coins table) (d, element) :=
      funext fun d => funext (KOf_eq coins table d)
    rw [values]
    rfl
  · have high : ¬ (BMR.xFlat (.inr element)).val < pointElementCountX := by
      show ¬ 364 + element.slot.val < pointElementCountX
      unfold pointElementCountX
      omega
    rw [dif_neg high]
    unfold Pipeline.curveXAssemble EntryCorrect.curveSlopesOf
    rw [curveKOf_eq]
    have idx : Pipeline.curveXElementOfSlot ((BMR.xFlat (.inr element)).val - pointElementCountX) = element := by
      cases element <;> simp [BMR.xFlat, pointElementCountX, Pipeline.curveXElementOfSlot, CurveXElement.slot]
    rw [idx]
    rfl

/-- **The garbler's `y` slopes are P45's.** -/
theorem slYOf_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable)
    (y : BMR.YEnc) :
    EntryCorrect.slYOf (H8.tagHash table) scalar coins (BMR.yFlat y) =
      BMR.nSlope (bmrContextOf scalar coins) (bmrCoinsOf coins table) (.inr y) := by
  unfold EntryCorrect.slYOf Entry.slopesY Entry.joinY
  rcases y with ⟨d, element⟩ | element
  · have low : (BMR.yFlat (.inl (d, element))).val < pointElementCountY := (yElementIndex d element).isLt
    rw [dif_pos low]
    rw [show (⟨(BMR.yFlat (.inl (d, element))).val, low⟩ : Fin pointElementCountY) = yElementIndex d element
      from rfl]
    erw [Pipeline.pointYAssemble_digit]
    unfold EntryCorrect.pointOf Entry.pointSlopes EntryCorrect.rowsOf
    have values : EntryCorrect.KOf (H8.tagHash table) coins =
        fun d element => BMR.rowOffset (bmrCoinsOf coins table) (d, element) :=
      funext fun d => funext (KOf_eq coins table d)
    rw [values]
    rfl
  · have high : ¬ (BMR.yFlat (.inr element)).val < pointElementCountY := by
      show ¬ 273 + element.slot.val < pointElementCountY
      unfold pointElementCountY
      omega
    rw [dif_neg high]
    unfold Pipeline.curveYAssemble EntryCorrect.curveSlopesOf
    rw [curveKOf_eq]
    have idx : Pipeline.curveYElementOfSlot ((BMR.yFlat (.inr element)).val - pointElementCountY) = element := by
      cases element <;> simp [BMR.yFlat, pointElementCountY, Pipeline.curveYElementOfSlot, CurveYElement.slot]
    rw [idx]
    rfl

/-! ### The real reading: pad sums, joins, hints and records -/

/-- The body pad sum on a tag table, as a sum over slots. -/
theorem bodyGarbleM_padSum (table : TagTable) (m S q coord i : ℕ) (e : Fin S) :
    ((bodyGarbleM m S q coord i fun _ => 0).eval (H8.tagHash table)).padSum e =
      (∑ ρ : Fin m, ((digit m (fractionValue m S q (packAnswers q fun j =>
        table ⟨bodyTag coord i ρ.val j.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩)) e.val : ℕ) : ZMod m)).val := by
  simp only [bodyGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, SliceC.eval_padVectorM, hlong,
    tagHash_hashInput, stored_eq]

/-- The garbler's pad sums on a tag table are its bodies' at zero labels. -/
theorem coordGarbleM_padSum (table : TagTable) (S coord : ℕ) (delta : Label) (zero : ℕ → Label)
    (i : Fin Entry.table.count) (e : Fin S) :
    ((coordGarbleM Entry.table S coord delta zero).eval (H8.tagHash table)).padSum i e =
      ((bodyGarbleM (Entry.table.modulus i) S (Entry.table.padAnswers S i) coord i.val
        fun _ => 0).eval (H8.tagHash table)).padSum e := by
  simp only [coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq, modGarbleM_body]

/-- The garbler's hints on a tag table are the wrap hints of its offsets. -/
theorem coordGarbleM_hint (table : TagTable) (S coord : ℕ) (delta : Label) (zero : ℕ → Label) (e : Fin S) :
    ((coordGarbleM Entry.table S coord delta zero).eval (H8.tagHash table)).hint e =
      wrapHint Entry.table.product Entry.table.wrapBound
        (((coordGarbleM Entry.table S coord delta zero).eval (H8.tagHash table)).offset e) := by
  simp only [coordGarbleM, FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq]

/-- **The garbler's `x` pad sums are P45's.** -/
theorem gx_padSum (table : TagTable) (delta : Label) (zero : ℕ → Label) (x : BMR.XEnc) (c : BMR.Coins Entry.table)
    (pads : c.pads = bmrPadsOf table) (i : Fin Entry.table.count) :
    ((coordGarbleM Entry.table Entry.xCount 0 delta zero).eval (H8.tagHash table)).padSum i (BMR.xFlat x) =
      (∑ ρ : ZMod (Entry.table.modulus i), c.pads i ρ (.inl x)).val := by
  rw [coordGarbleM_padSum, bodyGarbleM_padSum, pads, ← sum_fin_cast]
  congr 2
  funext ρ
  simp only [bmrPadsOf, padValues_eq, ZMod.val_cast_of_lt ρ.isLt]
  rfl

/-- **The garbler's `y` pad sums are P45's.** -/
theorem gy_padSum (table : TagTable) (delta : Label) (zero : ℕ → Label) (y : BMR.YEnc) (c : BMR.Coins Entry.table)
    (pads : c.pads = bmrPadsOf table) (i : Fin Entry.table.count) :
    ((coordGarbleM Entry.table Entry.yCount 1 delta zero).eval (H8.tagHash table)).padSum i (BMR.yFlat y) =
      (∑ ρ : ZMod (Entry.table.modulus i), c.pads i ρ (.inr y)).val := by
  rw [coordGarbleM_padSum, bodyGarbleM_padSum, pads, ← sum_fin_cast]
  congr 2
  funext ρ
  simp only [bmrPadsOf, padValues_eq, ZMod.val_cast_of_lt ρ.isLt]
  rfl

/-- A residue join, read as a natural. -/
theorem join_val (a : ZMod m) (slope : BaseField) [NeZero m] :
    (a + ((slope.val : ℕ) : ZMod m)).val = (a.val + slope.val) % m := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

theorem gxOf_unfold_offset (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc) :
    (EntryCorrect.gxOf (H8.tagHash table) coins).offset (BMR.xFlat x) =
      ((coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))).eval
        (H8.tagHash table)).offset (BMR.xFlat x) := by
  rw [EntryCorrect.gxOf]

/-- The `x` offsets through the names. -/
theorem gxOf_offset (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc) :
    (EntryCorrect.gxOf (H8.tagHash table) coins).offset (BMR.xFlat x) = BMR.offset (bmrCoinsOf coins table) (.inl x) := by
  rw [gxOf_unfold_offset]
  exact gx_offset table _ _ x (bmrCoinsOf coins table) rfl

theorem gxOf_unfold_hint (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc) :
    (EntryCorrect.gxOf (H8.tagHash table) coins).hint (BMR.xFlat x) =
      ((coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))).eval
        (H8.tagHash table)).hint (BMR.xFlat x) := by
  rw [EntryCorrect.gxOf]

/-- The `x` hints through the names. -/
theorem gxOf_hint (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc) :
    (EntryCorrect.gxOf (H8.tagHash table) coins).hint (BMR.xFlat x) = BMR.hint (bmrCoinsOf coins table) (.inl x) := by
  have step := coordGarbleM_hint table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j)) (BMR.xFlat x)
  rw [gx_offset table _ _ x (bmrCoinsOf coins table) rfl] at step
  rw [gxOf_unfold_hint, step]
  rfl

theorem gxOf_unfold_padSum (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc)
    (i : Fin Entry.table.count) :
    (EntryCorrect.gxOf (H8.tagHash table) coins).padSum i (BMR.xFlat x) =
      ((coordGarbleM Entry.table Entry.xCount 0 (clip (coins.inputDelta .x)) (fun j => clip (atNat (coins.inputZero .x) 0 j))).eval
        (H8.tagHash table)).padSum i (BMR.xFlat x) := by
  rw [EntryCorrect.gxOf]

/-- The `x` pad sums through the names. -/
theorem gxOf_padSum (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc)
    (i : Fin Entry.table.count) :
    (EntryCorrect.gxOf (H8.tagHash table) coins).padSum i (BMR.xFlat x) =
      (∑ ρ : ZMod (Entry.table.modulus i), (bmrCoinsOf coins table).pads i ρ (.inl x)).val := by
  rw [gxOf_unfold_padSum]
  exact gx_padSum table _ _ x (bmrCoinsOf coins table) rfl i

/-- The records of any coordinate garbling, spelled out. -/
theorem records_formula {S : ℕ} (g : CoordGarbled Entry.table S) (slopes : Fin S → ℕ) (e : Fin S) :
    g.records slopes e = (if g.hint e then Entry.table.product else 0) +
      ∑ i : Fin Entry.table.count, ((g.padSum i e + slopes e) % Entry.table.modulus i) * Entry.table.radix i := by
  unfold CoordGarbled.records CoordGarbled.join
  simp only [stored_eq]

/-- **The published `x` records are P45's** (hint and joins). -/
theorem recX_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (x : BMR.XEnc) :
    ((EntryCorrect.pubOf (H8.tagHash table) scalar coins).recX.get (BMR.xFlat x)).val =
      (if BMR.hint (bmrCoinsOf coins table) (.inl x) then Entry.table.product else 0) +
        ∑ i : Fin Entry.table.count,
          (BMR.nJoin (bmrContextOf scalar coins) (bmrCoinsOf coins table) (.inl x) i).val * Entry.table.radix i := by
  rw [EntryCorrect.pubOf_recX, records_formula, gxOf_hint]
  refine congrArg (HAdd.hAdd _) (Finset.sum_congr rfl fun i _ => ?_)
  rw [gxOf_padSum, slXOf_eq, BMR.nJoin, join_val]

theorem gyOf_unfold_offset (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc) :
    (EntryCorrect.gyOf (H8.tagHash table) coins).offset (BMR.yFlat y) =
      ((coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))).eval
        (H8.tagHash table)).offset (BMR.yFlat y) := by
  rw [EntryCorrect.gyOf]

theorem gyOf_unfold_hint (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc) :
    (EntryCorrect.gyOf (H8.tagHash table) coins).hint (BMR.yFlat y) =
      ((coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))).eval
        (H8.tagHash table)).hint (BMR.yFlat y) := by
  rw [EntryCorrect.gyOf]

theorem gyOf_unfold_padSum (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc)
    (i : Fin Entry.table.count) :
    (EntryCorrect.gyOf (H8.tagHash table) coins).padSum i (BMR.yFlat y) =
      ((coordGarbleM Entry.table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j))).eval
        (H8.tagHash table)).padSum i (BMR.yFlat y) := by
  rw [EntryCorrect.gyOf]

/-- The `y` offsets through the names. -/
theorem gyOf_offset (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc) :
    (EntryCorrect.gyOf (H8.tagHash table) coins).offset (BMR.yFlat y) = BMR.offset (bmrCoinsOf coins table) (.inr y) := by
  rw [gyOf_unfold_offset]
  exact gy_offset table _ _ y (bmrCoinsOf coins table) rfl

/-- The `y` hints through the names. -/
theorem gyOf_hint (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc) :
    (EntryCorrect.gyOf (H8.tagHash table) coins).hint (BMR.yFlat y) = BMR.hint (bmrCoinsOf coins table) (.inr y) := by
  have step := coordGarbleM_hint table Entry.yCount 1 (clip (coins.inputDelta .y)) (fun j => clip (atNat (coins.inputZero .y) 0 j)) (BMR.yFlat y)
  rw [gy_offset table _ _ y (bmrCoinsOf coins table) rfl] at step
  rw [gyOf_unfold_hint, step]
  rfl

/-- The `y` pad sums through the names. -/
theorem gyOf_padSum (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc)
    (i : Fin Entry.table.count) :
    (EntryCorrect.gyOf (H8.tagHash table) coins).padSum i (BMR.yFlat y) =
      (∑ ρ : ZMod (Entry.table.modulus i), (bmrCoinsOf coins table).pads i ρ (.inr y)).val := by
  rw [gyOf_unfold_padSum]
  exact gy_padSum table _ _ y (bmrCoinsOf coins table) rfl i

/-- **The published `y` records are P45's** (hint and joins). -/
theorem recY_eq (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (y : BMR.YEnc) :
    ((EntryCorrect.pubOf (H8.tagHash table) scalar coins).recY.get (BMR.yFlat y)).val =
      (if BMR.hint (bmrCoinsOf coins table) (.inr y) then Entry.table.product else 0) +
        ∑ i : Fin Entry.table.count,
          (BMR.nJoin (bmrContextOf scalar coins) (bmrCoinsOf coins table) (.inr y) i).val * Entry.table.radix i := by
  rw [EntryCorrect.pubOf_recY, records_formula, gyOf_hint]
  refine congrArg (HAdd.hAdd _) (Finset.sum_congr rfl fun i _ => ?_)
  rw [gyOf_padSum, slYOf_eq, BMR.nJoin, join_val]

end

end Kriterion.CRT.Privacy.BmrEntry
