/-
**The P45 targets of the swapped table** (for `TableKernel` and `KernelOff`).

The targets a tag table holds are its P45 pads and its row masks (`bmrTargetsOf`, BmrEntry's `bmrPadsOf` and
`bmrMasksOf`). Under `swappedTableLaw crtLayout`, in the product form of `Swap/Product.lean`:

* a table's targets are those of its site draws (`targetsOf_overwrite`), and they equal `τ` exactly when every site's
  draw matches `τ` (`targetsOfDraws_iff`): a pad site its digits (`PadLaw.matchSite`), a mask site its masks
  (`maskMatch`), through the one-to-one reading of the 728 row masks from the 273 collector sites, the 227 pair sites
  and the single site (`maskFun_maskInv`, `maskInv_maskFun`);
* a site matches any targets with the same mass (`siteMass_const`: every site's law is a fibre law);
* so the mass of "the table shows `w` at the positions `pos` and holds the targets `τ`" is a product over sites, and
  it is the same for `τ'` whenever `τ` and `τ'` agree at every site that holds one of the positions
  (`swapped_event_eq`). With no positions this makes the targets uniform (`swapped_targets_uniform`).

The swapped law conditioned on its targets (`TargetLaw.condLaw`) is then a kernel for them (`bind_condLaw`,
`condLaw_support`, `map_condLaw`).
-/

import Proof.Privacy.CRT.Swap.PadLaw
import Proof.Privacy.CRT.Core.BmrEntry

namespace Kriterion.CRT.Privacy

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3 (fibreLaw fibreLaw_map)
open scoped ENNReal

noncomputable section

/-- The P45 targets a tag table holds: its pads and its row masks. -/
def bmrTargetsOf (table : TagTable) : BMR.Pads Entry.table × (BMR.RowEnc → BaseField) :=
  (BmrEntry.bmrPadsOf table, BmrEntry.bmrMasksOf table)

namespace TargetLaw

/-! ### 1. Conditioning a law on a uniform reading -/

section Cond

variable {X Y : Type} [Fintype Y] [Nonempty Y] (μ : PMF X) (read : X → Y)
  (unif : μ.map read = PMF.uniformOfFintype Y)

include unif in
theorem cond_mass (y : Y) : μ.toOuterMeasure (read ⁻¹' {y}) = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  rw [← PMF.toOuterMeasure_map_apply, unif, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]

include unif in
theorem cond_nonempty (y : Y) : ∃ x ∈ read ⁻¹' {y}, x ∈ μ.support := by
  have pos : (μ.map read) y ≠ 0 := by
    rw [unif, PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  obtain ⟨x, hx, eq⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr pos)
  exact ⟨x, eq, hx⟩

/-- **The law conditioned on the reading `y`.** -/
def condLaw (y : Y) : PMF X := μ.filter (read ⁻¹' {y}) (cond_nonempty μ read unif y)

theorem card_ne_zero : (Fintype.card Y : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem condLaw_apply (y : Y) (x : X) :
    condLaw μ read unif y x = (read ⁻¹' {y}).indicator μ x * Fintype.card Y := by
  rw [condLaw, PMF.filter_apply, ← PMF.toOuterMeasure_apply, cond_mass μ read unif, inv_inv]

/-- The law is uniform readings followed by the conditioned laws. -/
theorem bind_condLaw : (PMF.uniformOfFintype Y).bind (condLaw μ read unif) = μ := by
  ext x
  rw [PMF.bind_apply, tsum_eq_single (read x)]
  · rw [condLaw_apply, PMF.uniformOfFintype_apply, Set.indicator_of_mem (show x ∈ read ⁻¹' {read x} from rfl),
      mul_comm (μ x), ← mul_assoc, ENNReal.inv_mul_cancel card_ne_zero (ENNReal.natCast_ne_top _), one_mul]
  · intro y other
    rw [condLaw_apply, Set.indicator_of_notMem (show x ∉ read ⁻¹' {y} from fun inside =>
      other (Set.mem_singleton_iff.mp inside).symm), zero_mul, mul_zero]

theorem condLaw_support (y : Y) : ∀ x ∈ (condLaw μ read unif y).support, read x = y := by
  intro x inside
  exact ((PMF.mem_support_filter_iff _).mp inside).1

theorem toOuterMeasure_condLaw (y : Y) (S : Set X) :
    (condLaw μ read unif y).toOuterMeasure S = μ.toOuterMeasure (S ∩ read ⁻¹' {y}) * Fintype.card Y := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases inS : x ∈ S
  · rw [Set.indicator_of_mem inS, condLaw_apply]
    by_cases inR : x ∈ read ⁻¹' {y}
    · rw [Set.indicator_of_mem inR, Set.indicator_of_mem (show x ∈ S ∩ read ⁻¹' {y} from ⟨inS, inR⟩)]
    · rw [Set.indicator_of_notMem inR, Set.indicator_of_notMem fun both => inR both.2]
  · rw [Set.indicator_of_notMem inS, Set.indicator_of_notMem fun both => inS both.1, zero_mul]

/-- Two conditioned laws have the same image under `f` when the joint masses agree. -/
theorem map_condLaw {Z : Type} (f : X → Z) (y y' : Y)
    (same : ∀ z, μ.toOuterMeasure {x | f x = z ∧ read x = y} = μ.toOuterMeasure {x | f x = z ∧ read x = y'}) :
    (condLaw μ read unif y).map f = (condLaw μ read unif y').map f := by
  ext z
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply, toOuterMeasure_condLaw, toOuterMeasure_condLaw]
  exact congrArg (· * _) (same z)

end Cond

/-! ### 2. The mask sites -/

/-- A two-answer site's reading of a list. -/
def readSingleL (a : List (Block × Block)) : BaseField := readSingle fun j => a.getD j.val (0, 0)

/-- A three-answer site's reading of a list. -/
def readPairL (a : List (Block × Block)) : BaseField × BaseField := readPair fun j => a.getD j.val (0, 0)

/-- The masks read from drawn mask-site answers. -/
def mvOfDraws (A : SiteId → List (Block × Block)) : MaskValues digitCount where
  collector c := readSingleL (A (.mask 0 c.val))
  pair k := readPairL (A (.mask 1 k.val))
  single := readSingleL (A (.mask 1 227))

/-- P45's row masks from mask values (`bmrMasksOf`'s body). -/
def maskFun (v : MaskValues digitCount) : BMR.RowEnc → BaseField
  | (d, .inl x) => maskOf v 0 (xElementIndex d x).val
  | (d, .inr y) => maskOf v 1 (yElementIndex d y).val

theorem bmrMasksOf_eq (table : TagTable) :
    BmrEntry.bmrMasksOf table = maskFun (maskValues (H8.tagHash table) 0 digitCount) := by
  funext r
  rcases r with ⟨d, x | y⟩ <;> rfl

theorem answers_mask0 (c : ℕ) : crtLayout.answers (.mask 0 c) = 2 := rfl

theorem answers_mask1 (k : ℕ) : crtLayout.answers (.mask 1 k) = if k = 227 then 2 else 3 := rfl

theorem getD_siteAnswersOf_mask (table : TagTable) (st k j : ℕ) (hj : j < crtLayout.answers (.mask st k)) :
    (Laws.siteAnswersOf crtLayout table (.mask st k)).getD j (0, 0) = table (tagPos (maskTag st k j)) := by
  unfold Laws.siteAnswersOf
  simp only [siteTags]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.map_some, Option.getD_some]
  rfl

theorem siteAnswers_tagHash (table : TagTable) (st k n : ℕ) :
    siteAnswers (H8.tagHash table) 0 st k n = fun part : Fin n => table (tagPos (maskTag st k part.val)) := by
  funext part
  unfold siteAnswers
  rw [BmrEntry.tagHash_hashInput]
  rfl

/-- **The masks of a tag table are read from its mask sites.** -/
theorem maskValues_eq (table : TagTable) :
    maskValues (H8.tagHash table) 0 digitCount = mvOfDraws (Laws.siteAnswersOf crtLayout table) := by
  have single : singleSites digitCount = 1 := by decide
  have pairs : pairSites digitCount = 227 := by decide
  have hc : ∀ c : Fin (collectorSites digitCount), readSingle (siteAnswers (H8.tagHash table) 0 0 c.val 2) =
      readSingleL (Laws.siteAnswersOf crtLayout table (.mask 0 c.val)) := by
    intro c
    show readSingle _ = readSingle _
    refine congrArg readSingle (funext fun j => ?_)
    rw [getD_siteAnswersOf_mask table 0 c.val j.val (by rw [answers_mask0]; exact j.isLt), siteAnswers_tagHash]
  have hp : ∀ k : Fin (pairSites digitCount), readPair (siteAnswers (H8.tagHash table) 0 1 k.val 3) =
      readPairL (Laws.siteAnswersOf crtLayout table (.mask 1 k.val)) := by
    intro k
    have hk : k.val < 227 := by have := k.isLt; omega
    show readPair _ = readPair _
    refine congrArg readPair (funext fun j => ?_)
    rw [getD_siteAnswersOf_mask table 1 k.val j.val (by rw [answers_mask1, if_neg (by omega)]; exact j.isLt),
      siteAnswers_tagHash]
  have hs : readSingle (siteAnswers (H8.tagHash table) 0 1 227 2) =
      readSingleL (Laws.siteAnswersOf crtLayout table (.mask 1 227)) := by
    show readSingle _ = readSingle _
    refine congrArg readSingle (funext fun j => ?_)
    rw [getD_siteAnswersOf_mask table 1 227 j.val (by rw [answers_mask1, if_pos rfl]; exact j.isLt),
      siteAnswers_tagHash]
  unfold maskValues mvOfDraws
  simp only [single, if_true, hc, hp, pairs, hs]

/-! ### 3. The row masks are the mask values, one to one -/

/-- The `x` element of a slot. -/
def xElemOfSlot : ℕ → XElement
  | 0 => .rowX_x7
  | 1 => .rowX_x9
  | 2 => .rowY_x7
  | 3 => .rowY_x9
  | _ => .rowZ_x9

/-- The `y` element of a slot. -/
def yElemOfSlot : ℕ → YElement
  | 0 => .rowX_y10
  | 1 => .rowY_y8
  | _ => .rowY_y10

theorem xslot_of {s : ℕ} (hs : s < 5) : (xElemOfSlot s).slot.val = s := by
  interval_cases s <;> rfl

theorem yslot_of {s : ℕ} (hs : s < 3) : (yElemOfSlot s).slot.val = s := by
  interval_cases s <;> rfl

theorem xElemOfSlot_slot (x : XElement) : xElemOfSlot x.slot.val = x := by
  cases x <;> rfl

theorem yElemOfSlot_slot (y : YElement) : yElemOfSlot y.slot.val = y := by
  cases y <;> rfl

/-- A digit from a natural (reduced mod 91). -/
def digitOf (n : ℕ) : Fin 91 := ⟨n % 91, by omega⟩

theorem digitOf_val (d : Fin 91) : digitOf d.val = d := Fin.ext (Nat.mod_eq_of_lt d.isLt)

/-- The row encoding of collector `c`: digit `c / 3`, `x` slot `collectorSlot (c % 3)`. -/
def collRow (c : ℕ) : BMR.RowEnc := (digitOf (c / 3), .inl (xElemOfSlot (collectorSlot (c % 3))))

/-- The row encoding of non-collector entry `n`. -/
def ncRow (n : ℕ) : BMR.RowEnc :=
  if n < 182 then (digitOf (n / 2), .inl (xElemOfSlot (2 * (n % 2))))
  else (digitOf ((n - 182) / 3), .inr (yElemOfSlot ((n - 182) % 3)))

/-- The mask values that give the row masks `τ`. -/
def maskInv (τ : BMR.RowEnc → BaseField) : MaskValues digitCount where
  collector c := τ (collRow c.val)
  pair k := (τ (ncRow (2 * k.val)), τ (ncRow (2 * k.val + 1)))
  single := τ (ncRow 454)

theorem collectorSites_eq : collectorSites digitCount = 273 := by decide

theorem pairSites_eq : pairSites digitCount = 227 := by decide

theorem coll_lt (c : Fin (collectorSites digitCount)) : c.val < 273 := by
  have := c.isLt
  have := collectorSites_eq
  omega

theorem pair_lt (k : Fin (pairSites digitCount)) : k.val < 227 := by
  have := k.isLt
  have := pairSites_eq
  omega

theorem lt_coll {c : ℕ} (hc : c < 273) : c < collectorSites digitCount := by rw [collectorSites_eq]; exact hc

theorem lt_pair {k : ℕ} (hk : k < 227) : k < pairSites digitCount := by rw [pairSites_eq]; exact hk

theorem atNat_collector (v : MaskValues digitCount) {c : ℕ} (hc : c < 273) (default : BaseField) :
    atNat v.collector default c = v.collector ⟨c, lt_coll hc⟩ := by
  unfold atNat
  rw [dif_pos (lt_coll hc)]

theorem nonCollector_pair (v : MaskValues digitCount) {n : ℕ} (hn : n < 454) :
    nonCollectorMask v n =
      if n % 2 = 0 then (v.pair ⟨n / 2, lt_pair (by omega)⟩).1 else (v.pair ⟨n / 2, lt_pair (by omega)⟩).2 := by
  unfold nonCollectorMask
  rw [dif_pos (lt_pair (by omega))]

theorem nonCollector_single (v : MaskValues digitCount) : nonCollectorMask v 454 = v.single := by
  unfold nonCollectorMask
  rw [dif_neg (by rw [pairSites_eq]; omega)]

/-- The mask of an `x` encoding index `e < 455`. -/
theorem maskOf_x (v : MaskValues digitCount) {e : ℕ} (he : e < 455) :
    maskOf v 0 e =
      if e % 5 = 1 then atNat v.collector 0 (3 * (e / 5))
      else if e % 5 = 3 then atNat v.collector 0 (3 * (e / 5) + 1)
      else if e % 5 = 4 then atNat v.collector 0 (3 * (e / 5) + 2)
      else nonCollectorMask v (2 * (e / 5) + (if e % 5 = 2 then 1 else 0)) := by
  unfold maskOf
  rw [if_pos rfl, if_pos (by show e < 5 * 91; omega)]

/-- The mask of a `y` encoding index `e < 273`. -/
theorem maskOf_y (v : MaskValues digitCount) {e : ℕ} (he : e < 273) :
    maskOf v 1 e = nonCollectorMask v (2 * 91 + e) := by
  unfold maskOf
  rw [if_neg one_ne_zero, if_pos (by show e < 3 * 91; omega)]
  rfl

theorem xIndex_val (d : Fin 91) (x : XElement) : (xElementIndex d x).val = 5 * d.val + x.slot.val := rfl

theorem yIndex_val (d : Fin 91) (y : YElement) : (yElementIndex d y).val = 3 * d.val + y.slot.val := rfl

theorem digit_lt (d : Fin 91) : d.val < 91 := d.isLt

/-- **The row masks of `maskInv τ` are `τ`.** -/
theorem maskFun_maskInv (τ : BMR.RowEnc → BaseField) : maskFun (maskInv τ) = τ := by
  funext r
  rcases r with ⟨d, x | y⟩
  · have hd := digit_lt d
    show maskOf (maskInv τ) 0 (xElementIndex d x).val = τ (d, .inl x)
    have hs : x.slot.val < 5 := x.slot.isLt
    rw [xIndex_val, maskOf_x _ (by omega)]
    generalize hsv : x.slot.val = s at hs ⊢
    have hx : x = xElemOfSlot s := by rw [← hsv, xElemOfSlot_slot]
    subst hx
    interval_cases s
    · -- slot 0: non-collector `2d`
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (show ¬ (5 * d.val + 0) % 5 = 2 by omega),
        show 2 * ((5 * d.val + 0) / 5) + 0 = 2 * d.val by omega, nonCollector_pair _ (by omega), if_pos (by omega)]
      show τ (ncRow (2 * (2 * d.val / 2))) = _
      rw [show 2 * (2 * d.val / 2) = 2 * d.val by omega]
      unfold ncRow
      rw [if_pos (by omega), show 2 * d.val / 2 = d.val by omega, show 2 * d.val % 2 = 0 by omega, digitOf_val]
    · -- slot 1: collector `3d`
      rw [if_pos (by omega), show (5 * d.val + 1) / 5 = d.val by omega, atNat_collector _ (by omega)]
      show τ (collRow (3 * d.val)) = _
      unfold collRow
      rw [show 3 * d.val / 3 = d.val by omega, show 3 * d.val % 3 = 0 by omega, digitOf_val]
      rfl
    · -- slot 2: non-collector `2d + 1`
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (show (5 * d.val + 2) % 5 = 2 by omega),
        show 2 * ((5 * d.val + 2) / 5) + 1 = 2 * d.val + 1 by omega, nonCollector_pair _ (by omega),
        if_neg (by omega)]
      show τ (ncRow (2 * ((2 * d.val + 1) / 2) + 1)) = _
      rw [show 2 * ((2 * d.val + 1) / 2) + 1 = 2 * d.val + 1 by omega]
      unfold ncRow
      rw [if_pos (by omega), show (2 * d.val + 1) / 2 = d.val by omega, show (2 * d.val + 1) % 2 = 1 by omega,
        digitOf_val]
    · -- slot 3: collector `3d + 1`
      rw [if_neg (by omega), if_pos (by omega), show (5 * d.val + 3) / 5 = d.val by omega,
        atNat_collector _ (by omega)]
      show τ (collRow (3 * d.val + 1)) = _
      unfold collRow
      rw [show (3 * d.val + 1) / 3 = d.val by omega, show (3 * d.val + 1) % 3 = 1 by omega, digitOf_val]
      rfl
    · -- slot 4: collector `3d + 2`
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (5 * d.val + 4) / 5 = d.val by omega,
        atNat_collector _ (by omega)]
      show τ (collRow (3 * d.val + 2)) = _
      unfold collRow
      rw [show (3 * d.val + 2) / 3 = d.val by omega, show (3 * d.val + 2) % 3 = 2 by omega, digitOf_val]
      rfl
  · have hd := digit_lt d
    show maskOf (maskInv τ) 1 (yElementIndex d y).val = τ (d, .inr y)
    have hs : y.slot.val < 3 := y.slot.isLt
    rw [yIndex_val, maskOf_y _ (by omega)]
    by_cases last : 2 * 91 + (3 * d.val + y.slot.val) = 454
    · rw [last, nonCollector_single]
      show τ (ncRow 454) = _
      unfold ncRow
      rw [if_neg (by norm_num)]
      have ed : digitOf ((454 - 182) / 3) = d := Fin.ext (by show (454 - 182) / 3 % 91 = d.val; omega)
      rw [ed, show (454 - 182) % 3 = y.slot.val by omega, yElemOfSlot_slot]
    · rw [nonCollector_pair _ (by omega)]
      split_ifs with even
      · show τ (ncRow (2 * ((2 * 91 + (3 * d.val + y.slot.val)) / 2))) = _
        rw [show 2 * ((2 * 91 + (3 * d.val + y.slot.val)) / 2) = 182 + (3 * d.val + y.slot.val) by omega]
        unfold ncRow
        rw [if_neg (by omega), show 182 + (3 * d.val + y.slot.val) - 182 = 3 * d.val + y.slot.val by omega,
          show (3 * d.val + y.slot.val) / 3 = d.val by omega, show (3 * d.val + y.slot.val) % 3 = y.slot.val by omega,
          digitOf_val, yElemOfSlot_slot]
      · show τ (ncRow (2 * ((2 * 91 + (3 * d.val + y.slot.val)) / 2) + 1)) = _
        rw [show 2 * ((2 * 91 + (3 * d.val + y.slot.val)) / 2) + 1 = 182 + (3 * d.val + y.slot.val) by omega]
        unfold ncRow
        rw [if_neg (by omega), show 182 + (3 * d.val + y.slot.val) - 182 = 3 * d.val + y.slot.val by omega,
          show (3 * d.val + y.slot.val) / 3 = d.val by omega, show (3 * d.val + y.slot.val) % 3 = y.slot.val by omega,
          digitOf_val, yElemOfSlot_slot]

/-- The mask of the row of non-collector entry `n < 455` is `nonCollectorMask v n`. -/
theorem maskFun_ncRow (v : MaskValues digitCount) {n : ℕ} (hn : n < 455) :
    maskFun v (ncRow n) = nonCollectorMask v n := by
  by_cases low : n < 182
  · have ev : ncRow n = (digitOf (n / 2), .inl (xElemOfSlot (2 * (n % 2)))) := if_pos low
    rw [ev]
    show maskOf v 0 (xElementIndex _ _).val = _
    have hs : 2 * (n % 2) < 5 := by omega
    rw [xIndex_val, xslot_of hs, maskOf_x _ (by show 5 * (n / 2 % 91) + 2 * (n % 2) < 455; omega)]
    have dig : (digitOf (n / 2)).val = n / 2 := by show n / 2 % 91 = n / 2; omega
    rw [dig]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show 2 * ((5 * (n / 2) + 2 * 0) / 5) + 0 = n by omega]
    · rw [h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        show 2 * ((5 * (n / 2) + 2 * 1) / 5) + 1 = n by omega]
  · have ev : ncRow n = (digitOf ((n - 182) / 3), .inr (yElemOfSlot ((n - 182) % 3))) := if_neg low
    rw [ev]
    show maskOf v 1 (yElementIndex _ _).val = _
    have hs : (n - 182) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have dig : (digitOf ((n - 182) / 3)).val = (n - 182) / 3 := by show (n - 182) / 3 % 91 = (n - 182) / 3; omega
    rw [yIndex_val, yslot_of hs, dig, maskOf_y _ (by omega),
      show 2 * 91 + (3 * ((n - 182) / 3) + (n - 182) % 3) = n by omega]

/-- **The mask values of row masks `maskFun v` are `v`.** -/
theorem maskInv_maskFun (v : MaskValues digitCount) : maskInv (maskFun v) = v := by
  rcases v with ⟨collector, pair, single⟩
  unfold maskInv
  congr 1
  · funext c
    have hc : c.val < 273 := coll_lt c
    have hs : collectorSlot (c.val % 3) < 5 := by unfold collectorSlot; split_ifs <;> omega
    show maskOf _ 0 (xElementIndex _ _).val = _
    have dig : (digitOf (c.val / 3)).val = c.val / 3 := by show c.val / 3 % 91 = c.val / 3; omega
    rw [xIndex_val, xslot_of hs, dig, maskOf_x _ (by omega)]
    rcases (by omega : c.val % 3 = 0 ∨ c.val % 3 = 1 ∨ c.val % 3 = 2) with h | h | h
    · rw [h, show collectorSlot 0 = 1 from rfl, if_pos (by omega), show 3 * ((5 * (c.val / 3) + 1) / 5) = c.val by omega,
        atNat_collector _ hc]
    · rw [h, show collectorSlot 1 = 3 from rfl, if_neg (by omega), if_pos (by omega),
        show 3 * ((5 * (c.val / 3) + 3) / 5) + 1 = c.val by omega, atNat_collector _ hc]
    · rw [h, show collectorSlot 2 = 4 from rfl, if_neg (by omega), if_neg (by omega), if_pos (by omega),
        show 3 * ((5 * (c.val / 3) + 4) / 5) + 2 = c.val by omega, atNat_collector _ hc]
  · funext k
    have hk : k.val < 227 := pair_lt k
    show (maskFun _ (ncRow (2 * k.val)), maskFun _ (ncRow (2 * k.val + 1))) = _
    rw [maskFun_ncRow _ (by omega), maskFun_ncRow _ (by omega), nonCollector_pair _ (by omega),
      nonCollector_pair _ (by omega), if_pos (by omega), if_neg (by omega)]
    have e1 : (⟨2 * k.val / 2, lt_pair (by omega)⟩ : Fin (pairSites digitCount)) = k := Fin.ext (by simp)
    have e2 : (⟨(2 * k.val + 1) / 2, lt_pair (by omega)⟩ : Fin (pairSites digitCount)) = k :=
      Fin.ext (by show (2 * k.val + 1) / 2 = k.val; omega)
    rw [e1, e2]

/-- The masks drawn at the mask sites, by row encoding. -/
def masksOfDraws (A : SiteId → List (Block × Block)) : BMR.RowEnc → BaseField := maskFun (mvOfDraws A)

theorem masksOfDraws_eq_iff (A : SiteId → List (Block × Block)) (τ : BMR.RowEnc → BaseField) :
    masksOfDraws A = τ ↔ mvOfDraws A = maskInv τ := by
  constructor
  · intro same
    rw [← same]
    exact (maskInv_maskFun _).symm
  · intro same
    unfold masksOfDraws
    rw [same, maskFun_maskInv]

theorem mask0_mem {c : ℕ} (hc : c < 273) : SiteId.mask 0 c ∈ Layout.maskSites :=
  List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

theorem mask1_mem {k : ℕ} (hk : k < 228) : SiteId.mask 1 k ∈ Layout.maskSites :=
  List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

theorem mvOfDraws_congr {A A' : SiteId → List (Block × Block)} (same : ∀ s ∈ Layout.maskSites, A s = A' s) :
    mvOfDraws A = mvOfDraws A' := by
  unfold mvOfDraws
  congr 1
  · funext c
    rw [same _ (mask0_mem (coll_lt c))]
  · funext k
    rw [same _ (mask1_mem (by have := pair_lt k; omega))]
  · rw [same _ (mask1_mem (by norm_num))]

/-- The event on one mask site that its reading matches the mask values `v`. -/
def maskMatch (v : MaskValues digitCount) : SiteId → Set (List (Block × Block))
  | .mask 0 c => {a | readSingleL a = atNat v.collector 0 c}
  | .mask 1 k => if k < 227 then {a | readPairL a = atNat v.pair (0, 0) k} else {a | readSingleL a = v.single}
  | _ => Set.univ

theorem mvOfDraws_eq_iff (A : SiteId → List (Block × Block)) (v : MaskValues digitCount) :
    mvOfDraws A = v ↔ ∀ s ∈ Layout.maskSites, A s ∈ maskMatch v s := by
  constructor
  · rintro rfl s member
    rcases Layout.mem_maskSites member with ⟨c, rfl, hc⟩ | ⟨k, rfl, hk⟩
    · show readSingleL (A (.mask 0 c)) = atNat (mvOfDraws A).collector 0 c
      rw [atNat_collector _ hc]
      rfl
    · by_cases pair : k < 227
      · show A (.mask 1 k) ∈ (if k < 227 then _ else _)
        rw [if_pos pair]
        show readPairL (A (.mask 1 k)) = atNat (mvOfDraws A).pair (0, 0) k
        unfold atNat
        rw [dif_pos (lt_pair pair)]
        rfl
      · have : k = 227 := by omega
        subst this
        exact rfl
  · intro hit
    rcases v with ⟨collector, pair, single⟩
    unfold mvOfDraws
    congr 1
    · funext c
      have hc : c.val < 273 := coll_lt c
      have := hit _ (mask0_mem hc)
      change readSingleL (A (.mask 0 c.val)) = atNat collector 0 c.val at this
      rw [this]
      unfold atNat
      rw [dif_pos c.isLt]
    · funext k
      have hk : k.val < 227 := pair_lt k
      have := hit _ (mask1_mem (by omega : k.val < 228))
      change A (.mask 1 k.val) ∈ (if k.val < 227 then _ else _) at this
      rw [if_pos hk] at this
      change readPairL (A (.mask 1 k.val)) = atNat pair (0, 0) k.val at this
      rw [this]
      unfold atNat
      rw [dif_pos k.isLt]
    · exact hit _ (mask1_mem (by norm_num : 227 < 228))

/-! ### 4. Every site's reading is uniform -/

/-- A fibre law read through a list reading: its uniform target. -/
theorem fibreSiteLaw_read {n : ℕ} {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (read : (Fin n → Block × Block) → X) (onto : Function.Surjective read) (E : Set X) :
    (Layout.fibreSiteLaw read onto).toOuterMeasure {a | read (fun j => a.getD j.val (0, 0)) ∈ E} =
      (PMF.uniformOfFintype X).toOuterMeasure E := by
  unfold Layout.fibreSiteLaw
  rw [PMF.toOuterMeasure_map_apply]
  have pre : List.ofFn ⁻¹' {a : List (Block × Block) | read (fun j => a.getD j.val (0, 0)) ∈ E} = read ⁻¹' E := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have same : (fun j : Fin n => (List.ofFn f).getD j.val (0, 0)) = f := by
      funext j
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.isLt, Option.getD_some]
    rw [same]
  rw [pre, ← PMF.toOuterMeasure_map_apply, PMF.map_bind]
  simp only [fibreLaw_map]
  rw [PMF.bind_pure]

theorem singleSite_mass (x : BaseField) :
    Layout.singleSiteLaw.toOuterMeasure {a | readSingleL a = x} = (Fintype.card BaseField : ℝ≥0∞)⁻¹ := by
  have := fibreSiteLaw_read readSingle Layout.readSingle_surjective {x}
  unfold Layout.singleSiteLaw
  rw [show {a : List (Block × Block) | readSingleL a = x} =
    {a | readSingle (fun j => a.getD j.val (0, 0)) ∈ ({x} : Set BaseField)} from rfl, this]
  exact PadLaw.uniform_single _ x fun w => Set.mem_singleton_iff

theorem pairSite_mass (x : BaseField × BaseField) :
    Layout.pairSiteLaw.toOuterMeasure {a | readPairL a = x} = (Fintype.card (BaseField × BaseField) : ℝ≥0∞)⁻¹ := by
  have := fibreSiteLaw_read readPair Layout.readPair_surjective {x}
  unfold Layout.pairSiteLaw
  rw [show {a : List (Block × Block) | readPairL a = x} =
    {a | readPair (fun j => a.getD j.val (0, 0)) ∈ ({x} : Set (BaseField × BaseField))} from rfl, this]
  exact PadLaw.uniform_single _ x fun w => Set.mem_singleton_iff

/-- **A mask site matches any mask values with the same mass.** -/
theorem maskMatch_mass (v v' : MaskValues digitCount) {s : SiteId} (member : s ∈ Layout.maskSites) :
    (crtLayout.law s).toOuterMeasure (maskMatch v s) = (crtLayout.law s).toOuterMeasure (maskMatch v' s) := by
  rcases Layout.mem_maskSites member with ⟨c, rfl, hc⟩ | ⟨k, rfl, hk⟩
  · show Layout.singleSiteLaw.toOuterMeasure {a | readSingleL a = _} =
      Layout.singleSiteLaw.toOuterMeasure {a | readSingleL a = _}
    rw [singleSite_mass, singleSite_mass]
  · by_cases pair : k < 227
    · have law : crtLayout.law (.mask 1 k) = Layout.pairSiteLaw := by
        show (if k = 227 then Layout.singleSiteLaw else Layout.pairSiteLaw) = _
        rw [if_neg (by omega)]
      show (crtLayout.law (.mask 1 k)).toOuterMeasure (if k < 227 then _ else _) =
        (crtLayout.law (.mask 1 k)).toOuterMeasure (if k < 227 then _ else _)
      rw [if_pos pair, if_pos pair, law, pairSite_mass, pairSite_mass]
    · have law : crtLayout.law (.mask 1 k) = Layout.singleSiteLaw := by
        show (if k = 227 then Layout.singleSiteLaw else Layout.pairSiteLaw) = _
        rw [if_pos (by omega)]
      show (crtLayout.law (.mask 1 k)).toOuterMeasure (if k < 227 then _ else _) =
        (crtLayout.law (.mask 1 k)).toOuterMeasure (if k < 227 then _ else _)
      rw [if_neg pair, if_neg pair, law, singleSite_mass, singleSite_mass]

/-! ### 5. The targets of the drawn sites -/

/-- The targets of the P45 pads and masks. -/
abbrev Targets := BMR.Pads Entry.table × (BMR.RowEnc → BaseField)

/-- The targets drawn at the sites. -/
def targetsOfDraws (A : SiteId → List (Block × Block)) : Targets := (PadLaw.padsOfDraws A, masksOfDraws A)

/-- The event on one site that it matches the targets `τ`. -/
def matchT (τ : Targets) (s : SiteId) : Set (List (Block × Block)) :=
  PadLaw.matchSite τ.1 s ∩ maskMatch (maskInv τ.2) s

theorem targetsOfDraws_iff (A : SiteId → List (Block × Block)) (τ : Targets) :
    targetsOfDraws A = τ ↔ ∀ s ∈ crtLayout.sites, A s ∈ matchT τ s := by
  have pads : PadLaw.padsOfDraws A = τ.1 ↔ ∀ s ∈ Layout.padSites, A s ∈ PadLaw.matchSite τ.1 s := by
    have := congrArg (A ∈ ·) (PadLaw.preimage_padsOfDraws τ.1)
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, eq_iff_iff] using this
  have masks := (masksOfDraws_eq_iff A τ.2).trans (mvOfDraws_eq_iff A (maskInv τ.2))
  rw [targetsOfDraws, Prod.ext_iff, pads, masks]
  show _ ↔ ∀ s ∈ Layout.padSites ++ Layout.maskSites, _
  constructor
  · rintro ⟨hp, hm⟩ s member
    rcases List.mem_append.mp member with pad | mask
    · refine ⟨hp s pad, ?_⟩
      obtain ⟨κ, i, ρ, rfl, -⟩ := Layout.mem_padSites pad
      exact Set.mem_univ _
    · refine ⟨?_, hm s mask⟩
      rcases Layout.mem_maskSites mask with ⟨c, rfl, -⟩ | ⟨k, rfl, -⟩ <;> exact Set.mem_univ _
  · intro hit
    exact ⟨fun s pad => (hit s (List.mem_append_left _ pad)).1,
      fun s mask => (hit s (List.mem_append_right _ mask)).2⟩

/-- **A site matches any targets with the same mass.** -/
theorem siteMass_const (τ τ' : Targets) {s : SiteId} (member : s ∈ crtLayout.sites) :
    (crtLayout.law s).toOuterMeasure (matchT τ s) = (crtLayout.law s).toOuterMeasure (matchT τ' s) := by
  rcases List.mem_append.mp member with pad | mask
  · obtain ⟨κ, i, ρ, rfl, -⟩ := Layout.mem_padSites pad
    have e : ∀ σ : Targets, matchT σ (.pad κ i ρ) = PadLaw.matchSite σ.1 (.pad κ i ρ) := fun σ => Set.inter_univ _
    rw [e, e, PadLaw.matchSite_mass τ.1 pad, PadLaw.matchSite_mass τ'.1 pad]
  · have e : ∀ σ : Targets, matchT σ s = maskMatch (maskInv σ.2) s := by
      intro σ
      rcases Layout.mem_maskSites mask with ⟨c, rfl, -⟩ | ⟨k, rfl, -⟩ <;> exact Set.univ_inter _
    rw [e, e]
    exact maskMatch_mass _ _ mask

theorem bmrPadsOf_eq_padsOf (table : TagTable) : BmrEntry.bmrPadsOf table = padsOf table := rfl

theorem lengths_of_support {A : SiteId → List (Block × Block)}
    (drawn : A ∈ (siteDraws crtLayout crtLayout.sites).support) :
    ∀ s ∈ crtLayout.sites, (A s).length = crtLayout.answers s := fun s member =>
  Laws.crtLayout_refill.lengths s member _ (siteDraws_support crtLayout _ A drawn s member)

/-- **The targets of the written table are the drawn targets.** -/
theorem targetsOf_overwrite (A : SiteId → List (Block × Block))
    (lengths : ∀ s ∈ crtLayout.sites, (A s).length = crtLayout.answers s) (T0 : TagTable) :
    bmrTargetsOf (overwriteSites crtLayout crtLayout.sites A T0) = targetsOfDraws A := by
  unfold bmrTargetsOf targetsOfDraws
  rw [bmrPadsOf_eq_padsOf, PadLaw.padsOf_overwriteSites A lengths T0, bmrMasksOf_eq, maskValues_eq]
  unfold masksOfDraws
  rw [mvOfDraws_congr fun s mask => siteAnswersOf_overwriteSites crtLayout Laws.crtLayout_refill A lengths T0 s
    (List.mem_append_right _ mask)]

/-! ### 6. The joint event is a product over sites -/

/-- The event on one site that it shows `w` at those of the positions `pos` it holds. -/
def visMatch {ι : Type} (pos : ι → Fin (2 ^ 40)) (w : ι → Block × Block) (s : SiteId) :
    Set (List (Block × Block)) :=
  {a | ∀ i, ∀ j (hj : j < (siteTags crtLayout s).length), tagPos ((siteTags crtLayout s)[j]) = pos i →
    a.getD j (0, 0) = w i}

/-- The base table shows `w` at the positions of no site. -/
def BaseMatch {ι : Type} (pos : ι → Fin (2 ^ 40)) (w : ι → Block × Block) (T0 : TagTable) : Prop :=
  ∀ i, (∀ s ∈ crtLayout.sites, pos i ∉ Laws.sitePos crtLayout s) → T0 (pos i) = w i

theorem getD_siteAnswersOf (table : TagTable) (s : SiteId) {j : ℕ} (hj : j < (siteTags crtLayout s).length) :
    (Laws.siteAnswersOf crtLayout table s).getD j (0, 0) = table (tagPos ((siteTags crtLayout s)[j])) := by
  unfold Laws.siteAnswersOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

theorem overwrite_shows_iff {ι : Type} (pos : ι → Fin (2 ^ 40)) (w : ι → Block × Block)
    (A : SiteId → List (Block × Block)) (lengths : ∀ s ∈ crtLayout.sites, (A s).length = crtLayout.answers s)
    (T0 : TagTable) (base : BaseMatch pos w T0) :
    (∀ i, overwriteSites crtLayout crtLayout.sites A T0 (pos i) = w i) ↔
      ∀ s ∈ crtLayout.sites, A s ∈ visMatch pos w s := by
  have back : ∀ s ∈ crtLayout.sites, Laws.siteAnswersOf crtLayout (overwriteSites crtLayout crtLayout.sites A T0) s
      = A s := fun s member =>
    siteAnswersOf_overwriteSites crtLayout Laws.crtLayout_refill A lengths T0 s member
  constructor
  · intro shows s member i j hj at_pos
    rw [← back s member, getD_siteAnswersOf _ s hj, at_pos]
    exact shows i
  · intro hit i
    by_cases inSite : ∃ s ∈ crtLayout.sites, pos i ∈ Laws.sitePos crtLayout s
    · obtain ⟨s, member, inside⟩ := inSite
      obtain ⟨tag, tagIn, at_pos⟩ := List.mem_map.mp inside
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem tagIn
      rw [← at_pos, ← getD_siteAnswersOf (overwriteSites crtLayout crtLayout.sites A T0) s hj, back s member]
      exact hit s member i j hj at_pos
    · simp only [not_exists, not_and] at inSite
      rw [overwriteSites_outside crtLayout A T0 (pos i) inSite]
      exact base i inSite

theorem overwrite_shows_base {ι : Type} (pos : ι → Fin (2 ^ 40)) (w : ι → Block × Block)
    (A : SiteId → List (Block × Block)) (T0 : TagTable)
    (shows : ∀ i, overwriteSites crtLayout crtLayout.sites A T0 (pos i) = w i) : BaseMatch pos w T0 := by
  intro i away
  rw [← overwriteSites_outside crtLayout A T0 (pos i) away]
  exact shows i

theorem toOuterMeasure_congr_support {α : Type} (p : PMF α) {S S' : Set α}
    (same : ∀ x ∈ p.support, x ∈ S ↔ x ∈ S') : p.toOuterMeasure S = p.toOuterMeasure S' := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases zero : p x = 0
  · rw [Set.indicator_apply_eq_zero.mpr (fun _ => zero), Set.indicator_apply_eq_zero.mpr (fun _ => zero)]
  · have iff := same x ((PMF.mem_support_iff _ _).mpr zero)
    by_cases inS : x ∈ S
    · rw [Set.indicator_of_mem inS, Set.indicator_of_mem (iff.mp inS)]
    · rw [Set.indicator_of_notMem inS, Set.indicator_of_notMem (fun h => inS (iff.mpr h))]

theorem sites_nodup : crtLayout.sites.Nodup := Laws.crtLayout_refill.sitesNodup

open Classical in
/-- The joint mass given the base table: a product over the sites. -/
theorem inner_mass {ι : Type} (pos : ι → Fin (2 ^ 40)) (w : ι → Block × Block) (τ : Targets) (T0 : TagTable) :
    (siteDraws crtLayout crtLayout.sites).toOuterMeasure
        ((fun A => overwriteSites crtLayout crtLayout.sites A T0) ⁻¹'
          {t | (∀ i, t (pos i) = w i) ∧ bmrTargetsOf t = τ}) =
      if BaseMatch pos w T0 then
        (crtLayout.sites.map fun s => (crtLayout.law s).toOuterMeasure (visMatch pos w s ∩ matchT τ s)).prod
      else 0 := by
  split_ifs with base
  · rw [← siteDraws_pi crtLayout _ sites_nodup]
    refine toOuterMeasure_congr_support _ fun A drawn => ?_
    have lengths := lengths_of_support drawn
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [overwrite_shows_iff pos w A lengths T0 base, targetsOf_overwrite A lengths T0, targetsOfDraws_iff]
    constructor
    · rintro ⟨h1, h2⟩ s member
      exact ⟨h1 s member, h2 s member⟩
    · intro h
      exact ⟨fun s member => (h s member).1, fun s member => (h s member).2⟩
  · have empty : (fun A => overwriteSites crtLayout crtLayout.sites A T0) ⁻¹'
        {t | (∀ i, t (pos i) = w i) ∧ bmrTargetsOf t = τ} = ∅ := by
      ext A
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro shows
      exact absurd (overwrite_shows_base pos w A T0 shows) base
    rw [empty]
    simp

end TargetLaw

open TargetLaw in
/-- **The joint event of the shown answers and the targets.** The mass of "the swapped table shows `w` at the
positions `pos` and holds the targets `τ`" is the same for `τ'`, when `τ` and `τ'` agree (as site events) at every
site that holds one of the positions. -/
theorem swapped_event_eq {ι : Type} (pos : ι → Fin (2 ^ 40)) (w : ι → Block × Block) (τ τ' : TargetLaw.Targets)
    (agree : ∀ s ∈ crtLayout.sites, (∃ i, pos i ∈ Laws.sitePos crtLayout s) → matchT τ s = matchT τ' s) :
    (swappedTableLaw crtLayout).toOuterMeasure {t | (∀ i, t (pos i) = w i) ∧ bmrTargetsOf t = τ} =
      (swappedTableLaw crtLayout).toOuterMeasure {t | (∀ i, t (pos i) = w i) ∧ bmrTargetsOf t = τ'} := by
  rw [swappedTableLaw_product crtLayout sites_nodup, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun T0 => congrArg _ ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply, inner_mass, inner_mass]
  split_ifs with base
  · refine congrArg List.prod (List.map_congr_left fun s member => ?_)
    by_cases holds : ∃ i, pos i ∈ Laws.sitePos crtLayout s
    · rw [agree s member holds]
    · have univ : visMatch pos w s = Set.univ := by
        ext a
        simp only [visMatch, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        intro i j hj at_pos
        exact absurd ⟨i, List.mem_map.mpr ⟨_, List.getElem_mem hj, at_pos⟩⟩ holds
      rw [univ, Set.univ_inter, Set.univ_inter]
      exact siteMass_const τ τ' member
  · rfl

/-- **The targets of the swapped table are uniform.** -/
theorem swapped_targets_uniform :
    (swappedTableLaw crtLayout).map bmrTargetsOf = PMF.uniformOfFintype TargetLaw.Targets := by
  refine PadLaw.eq_uniform_of_const _ fun τ τ' => ?_
  have event : ∀ σ : TargetLaw.Targets, ((swappedTableLaw crtLayout).map bmrTargetsOf) σ =
      (swappedTableLaw crtLayout).toOuterMeasure
        {t | (∀ i : Empty, t (Empty.elim i) = Empty.elim i) ∧ bmrTargetsOf t = σ} := by
    intro σ
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, IsEmpty.forall_iff, true_and]
  rw [event, event]
  exact swapped_event_eq _ _ τ τ' fun s _ holds => absurd holds (by simp)

end

end Kriterion.CRT.Privacy
