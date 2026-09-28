/-
**H7's `Δ` residual** (shared by `convHot`, `Hidden/CaseConv.lean`, and `digestOther`,
`Hidden/CaseDigest.lean`).

A stage-2 guess at a hidden conversion/body tag fixes `clip Δ_κ`; a hidden digest guess fixes the full `Δ_κ`.
This file preserves a full raw residual, uniform and independent of a view finer than the stage-2 view.
The downstream bounds are `2^-104` for the projected conversion guess and `2^-128` for the full digest guess:

* the **fine view** `fine` of a tape: coordinate `κ`'s published conversion material, the coins with `κ`'s zero
  labels replaced by `u`'s labels `E_κ = Z_κ ⊕ u·Δ_κ` and `Δ_κ` by `0` (`eCoins`), and the table outside the hot
  conversion tags of `κ` at `u` (`maskTable`);
* **independence** (`fine_split`): the law of `(fine, Δ_κ)` is the law of `fine` times the uniform law on blocks.
  The conversion material is uniform and independent of everything off its hot tags, the coins included (`crtConvSplit`), and the coin `Δ_κ` has a setter that keeps `u`'s labels (`setDelta`), so under the uniform coin law
  it is uniform and independent of `eCoins` (`split_sum`).
-/

import Proof.Privacy.CRT.Hidden.StageTwo
import Proof.Privacy.CRT.Core.ConvSplit
import Proof.Privacy.CRT.Laws.LabelsSplit

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Kriterion.CRT.Privacy.DeltaView

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.Laws (coinLaw swappedTableTape_eq tape_map_apply map_apply_inj map_apply_notMem)
open Kriterion.CRT.Privacy.Laws.LabelsSplitProof (LabelKeys coinKeys withKeys coinKeys_withKeys withKeys_coinKeys
  withKeys_withKeys split_sum coinLaw_eq)
open Kriterion.CRT.Privacy.Align (asked)
open Kriterion.ArgoMAC.PlanB (digitCount)
open scoped ENNReal

noncomputable section

attribute [local instance] Laws.LabelsSplitProof.coinsFintype Laws.LabelsSplitProof.coinsNonempty

/-! ### 1. The label keys of coordinate `κ` seen through `u`'s labels -/

/-- The bit of `u` at position `p` of coordinate `κ`, as the labels select it (`labelsFrom`). -/
def uBit (u : AffineInput) (κ : Fin 2) (p : ℕ) : Bool :=
  if κ.val = 0 then u.x.val.testBit p else u.y.val.testBit p

/-- `u`'s label at position `p` of coordinate `κ`, from label keys: `Z ⊕ Δ` at a set bit, `Z` otherwise. -/
def eLabel (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (p : Fin coordinateBitCount) : Block :=
  if uBit u κ p.val then keys.1 κ p ^^^ keys.2 κ else keys.1 κ p

/-- The label keys with coordinate `κ`'s zero labels replaced by `u`'s labels and its `Δ` by `0`. -/
def eKeys (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) : LabelKeys :=
  (Function.update keys.1 κ (eLabel u κ keys), Function.update keys.2 κ 0)

/-- The label keys with coordinate `κ`'s `Δ` set to `d` and `u`'s labels kept. -/
def shiftKeys (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (d : Block) : LabelKeys :=
  (Function.update keys.1 κ (fun p => if uBit u κ p.val then eLabel u κ keys p ^^^ d else eLabel u κ keys p),
    Function.update keys.2 κ d)

theorem xor_xor_cancel (a d : Block) : a ^^^ d ^^^ d = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem shiftKeys_delta (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (d : Block) :
    (shiftKeys u κ keys d).2 κ = d := by
  show Function.update keys.2 κ d κ = d
  exact Function.update_self κ d keys.2

theorem shiftKeys_zero (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (d : Block) :
    (shiftKeys u κ keys d).1 κ =
      fun p => if uBit u κ p.val then eLabel u κ keys p ^^^ d else eLabel u κ keys p := by
  show Function.update keys.1 κ _ κ = _
  exact Function.update_self κ _ keys.1

theorem eLabel_shiftKeys (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (d : Block) :
    eLabel u κ (shiftKeys u κ keys d) = eLabel u κ keys := by
  funext p
  show (if uBit u κ p.val then (shiftKeys u κ keys d).1 κ p ^^^ (shiftKeys u κ keys d).2 κ
    else (shiftKeys u κ keys d).1 κ p) = eLabel u κ keys p
  rw [shiftKeys_zero, shiftKeys_delta]
  by_cases bit : uBit u κ p.val = true
  · simp only [if_pos bit]
    exact xor_xor_cancel _ _
  · simp only [if_neg bit]

theorem shiftKeys_self (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) :
    shiftKeys u κ keys (keys.2 κ) = keys := by
  obtain ⟨zeros, deltas⟩ := keys
  refine Prod.ext ?_ ?_
  · funext κ' p
    by_cases same : κ' = κ
    · subst same
      rw [shiftKeys_zero]
      show (if uBit u κ' p.val then eLabel u κ' (zeros, deltas) p ^^^ deltas κ'
        else eLabel u κ' (zeros, deltas) p) = zeros κ' p
      unfold eLabel
      by_cases bit : uBit u κ' p.val = true
      · simp only [if_pos bit]
        exact xor_xor_cancel _ _
      · simp only [if_neg bit]
    · simp only [shiftKeys, Function.update_of_ne same]
  · funext κ'
    by_cases same : κ' = κ
    · subst same
      simp only [shiftKeys, Function.update_self]
    · simp only [shiftKeys, Function.update_of_ne same]

theorem shiftKeys_shiftKeys (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (d d' : Block) :
    shiftKeys u κ (shiftKeys u κ keys d) d' = shiftKeys u κ keys d' := by
  have first : (shiftKeys u κ (shiftKeys u κ keys d) d').1 = (shiftKeys u κ keys d').1 := by
    show Function.update (Function.update keys.1 κ _) κ _ = Function.update keys.1 κ _
    rw [Function.update_idem, eLabel_shiftKeys]
  have second : (shiftKeys u κ (shiftKeys u κ keys d) d').2 = (shiftKeys u κ keys d').2 := by
    show Function.update (Function.update keys.2 κ d) κ d' = Function.update keys.2 κ d'
    rw [Function.update_idem]
  exact Prod.ext first second

theorem eKeys_shiftKeys (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (d : Block) :
    eKeys u κ (shiftKeys u κ keys d) = eKeys u κ keys := by
  have first : (eKeys u κ (shiftKeys u κ keys d)).1 = (eKeys u κ keys).1 := by
    show Function.update (Function.update keys.1 κ _) κ (eLabel u κ (shiftKeys u κ keys d)) =
      Function.update keys.1 κ (eLabel u κ keys)
    rw [Function.update_idem, eLabel_shiftKeys]
  have second : (eKeys u κ (shiftKeys u κ keys d)).2 = (eKeys u κ keys).2 := by
    show Function.update (Function.update keys.2 κ d) κ 0 = Function.update keys.2 κ 0
    rw [Function.update_idem]
  exact Prod.ext first second

/-! ### 2. The coins -/

/-- The coins with coordinate `κ`'s zero labels replaced by `u`'s labels and its `Δ` by `0`. -/
def eCoins (u : AffineInput) (κ : Fin 2) (coins : Entry.Coins) : Entry.Coins :=
  withKeys coins (eKeys u κ (coinKeys coins))

/-- Coordinate `κ`'s `Δ` of the coins. -/
def deltaAt (κ : Fin 2) (coins : Entry.Coins) : Block := (coinKeys coins).2 κ

/-- The coins with coordinate `κ`'s `Δ` set to `d` and `u`'s labels kept. -/
def setDelta (u : AffineInput) (κ : Fin 2) (coins : Entry.Coins) (d : Block) : Entry.Coins :=
  withKeys coins (shiftKeys u κ (coinKeys coins) d)

theorem deltaAt_setDelta (u : AffineInput) (κ : Fin 2) (coins : Entry.Coins) (d : Block) :
    deltaAt κ (setDelta u κ coins d) = d := by
  unfold deltaAt setDelta
  rw [coinKeys_withKeys, shiftKeys_delta]

theorem setDelta_deltaAt (u : AffineInput) (κ : Fin 2) (coins : Entry.Coins) :
    setDelta u κ coins (deltaAt κ coins) = coins := by
  unfold deltaAt setDelta
  rw [shiftKeys_self, withKeys_coinKeys]

theorem setDelta_setDelta (u : AffineInput) (κ : Fin 2) (coins : Entry.Coins) (d d' : Block) :
    setDelta u κ (setDelta u κ coins d) d' = setDelta u κ coins d' := by
  unfold setDelta
  rw [coinKeys_withKeys, withKeys_withKeys, shiftKeys_shiftKeys]

theorem eCoins_setDelta (u : AffineInput) (κ : Fin 2) (coins : Entry.Coins) (d : Block) :
    eCoins u κ (setDelta u κ coins d) = eCoins u κ coins := by
  unfold eCoins setDelta
  rw [coinKeys_withKeys, withKeys_withKeys, eKeys_shiftKeys]

/-! ### 3. The fine view -/

open Classical in
/-- The table with the hot conversion tags of `κ` at `u` blanked. -/
def maskTable (u : AffineInput) (κ : Fin 2) (table : TagTable) : TagTable := fun tag =>
  if H8.hotConvTag Entry.table u κ.val tag then (0, 0) else table tag

theorem maskTable_eq (u : AffineInput) (κ : Fin 2) (table : TagTable) (tag : Fin (2 ^ 40))
    (cold : ¬ H8.hotConvTag Entry.table u κ.val tag) : maskTable u κ table tag = table tag := by
  unfold maskTable
  rw [if_neg cold]

/-- The type of the fine view. -/
abbrev WType := Vector Label Entry.convCount × Entry.Coins × TagTable

section Fine

variable [FieldCertificate] [GroupCertificate]

/-- Coordinate `κ`'s published conversion material (the part of `crtConvSplit`). -/
def crtPart (parameter : ℕ) (scalar : NonZeroScalar) (κ : Fin 2) (tape : TableTape crtEntry) :
    Vector Label Entry.convCount :=
  if κ = 0 then (H8.realGarbled crtEntry parameter scalar tape).1.crtX
  else (H8.realGarbled crtEntry parameter scalar tape).1.crtY

/-- The rest of the fine view: the coins through `u`'s labels, the table off the hot conversion tags. -/
def restOf (u : AffineInput) (κ : Fin 2) (tape : TableTape crtEntry) : Entry.Coins × TagTable :=
  (eCoins u κ tape.1, maskTable u κ tape.2)

/-- **The fine view** of a tape at `u` for coordinate `κ`. -/
def fine (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (κ : Fin 2) (tape : TableTape crtEntry) :
    WType :=
  (crtPart parameter scalar κ tape, restOf u κ tape)

/-- **The residual**: coordinate `κ`'s `Δ`. -/
def res (κ : Fin 2) (tape : TableTape crtEntry) : Block := deltaAt κ tape.1

/-! ### 4. Independence -/

theorem map_some_apply {X Y : Type} (μ : PMF X) (h : X → Y) (y : Y) :
    (μ.map fun x => (some (h x) : Option Y)) (some y) = (μ.map h) y := by
  have comp : (μ.map fun x => (some (h x) : Option Y)) = (μ.map h).map some := by
    rw [PMF.map_comp]
    rfl
  rw [comp]
  exact map_apply_inj _ (Option.some_injective Y) y

open Classical in
/-- the split with the flag `False`, without the option wrapper. -/
theorem conv_split (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (κ : Fin 2) {α : Type}
    (g : TableTape crtEntry → α) (reads : H8.ReadsOff Eq (H8.hotConvTag Entry.table u κ.val) g)
    (b : Vector Label Entry.convCount) (a : α) :
    ((swappedTableTape crtEntry).map fun tape => (crtPart parameter scalar κ tape, g tape)) (b, a) =
      ((@PMF.uniformOfFintype _ (Instance.view).sourceFintype (Instance.view).sourceNonempty).map fun source =>
          if κ = 0 then ((Instance.view).publish source).crtX else ((Instance.view).publish source).crtY) b *
        ((swappedTableTape crtEntry).map g) a := by
  have split := ConvSplit.crtConvSplit κ parameter scalar u g reads b a
  simp only [if_false] at split
  rw [map_some_apply, map_some_apply] at split
  exact split

theorem restOf_reads (u : AffineInput) (κ : Fin 2) :
    H8.ReadsOff Eq (H8.hotConvTag Entry.table u κ.val) (restOf u κ) := by
  intro tape tape' sameCoins agree
  unfold restOf
  rw [sameCoins]
  congr 1
  funext tag
  unfold maskTable
  split_ifs with hot
  · rfl
  · exact agree tag hot

theorem restRes_reads (u : AffineInput) (κ : Fin 2) :
    H8.ReadsOff Eq (H8.hotConvTag Entry.table u κ.val) (fun tape => (restOf u κ tape, res κ tape)) := by
  intro tape tape' sameCoins agree
  show (restOf u κ tape, res κ tape) = (restOf u κ tape', res κ tape')
  rw [restOf_reads u κ tape tape' sameCoins agree]
  unfold res
  rw [sameCoins]

open Classical in
/-- The table part of a tape's image, pulled out of the coins. -/
theorem table_map_apply (x : Entry.Coins) (y : Block) (c : Entry.Coins × TagTable) (r : Block)
    (u : AffineInput) (κ : Fin 2) :
    ((swappedTableLaw crtLayout).map fun table => ((x, maskTable u κ table), y)) (c, r) =
      if x = c.1 ∧ y = r then ((swappedTableLaw crtLayout).map (maskTable u κ)) c.2 else 0 := by
  by_cases same : x = c.1 ∧ y = r
  · rw [if_pos same]
    obtain ⟨hx, hy⟩ := same
    have point : (c, r) = ((x, c.2), y) := Prod.ext (Prod.ext hx.symm rfl) hy.symm
    have comp : ((swappedTableLaw crtLayout).map fun table => ((x, maskTable u κ table), y)) =
        ((swappedTableLaw crtLayout).map (maskTable u κ)).map fun t => ((x, t), y) := by
      rw [PMF.map_comp]
      rfl
    rw [point, comp]
    exact map_apply_inj _ (φ := fun t => ((x, t), y)) (fun a b h => by simpa using h) c.2
  · rw [if_neg same]
    refine map_apply_notMem _ _ _ fun table h => same ?_
    have first := congrArg (fun p => p.1.1) h
    have second := congrArg (fun p => p.2) h
    exact ⟨first, second⟩

open Classical in
theorem table_map_apply' (x : Entry.Coins) (c : Entry.Coins × TagTable) (u : AffineInput) (κ : Fin 2) :
    ((swappedTableLaw crtLayout).map fun table => (x, maskTable u κ table)) c =
      if x = c.1 then ((swappedTableLaw crtLayout).map (maskTable u κ)) c.2 else 0 := by
  by_cases same : x = c.1
  · rw [if_pos same]
    have point : c = (x, c.2) := Prod.ext same.symm rfl
    have comp : ((swappedTableLaw crtLayout).map fun table => (x, maskTable u κ table)) =
        ((swappedTableLaw crtLayout).map (maskTable u κ)).map fun t => (x, t) := by
      rw [PMF.map_comp]
      rfl
    rw [point, comp]
    exact map_apply_inj _ (φ := fun t => (x, t)) (fun a b h => by simpa using h) c.2
  · rw [if_neg same]
    exact map_apply_notMem _ _ _ fun table h => same (congrArg Prod.fst h)

open Classical in
/-- **The coin split**: `Δ_κ` is uniform and independent of the rest of the fine view. -/
theorem rest_split (u : AffineInput) (κ : Fin 2) (c : Entry.Coins × TagTable) (r : Block) :
    ((swappedTableTape crtEntry).map fun tape => (restOf u κ tape, res κ tape)) (c, r) =
      ((swappedTableTape crtEntry).map (restOf u κ)) c * PMF.uniformOfFintype Block r := by
  rw [tape_map_apply, tape_map_apply, coinLaw_eq, tsum_fintype, tsum_fintype]
  set q := ((swappedTableLaw crtLayout).map (maskTable u κ)) c.2 with hq
  have each : ∀ x : crtEntry.Coins,
      ((swappedTableLaw crtLayout).map fun table => (restOf u κ (x, table), res κ (x, table))) (c, r) =
        (if eCoins u κ x = c.1 then q else 0) * (if deltaAt κ x = r then 1 else 0) := by
    intro x
    have := table_map_apply (eCoins u κ x) (deltaAt κ x) c r u κ
    refine this.trans ?_
    by_cases h1 : eCoins u κ x = c.1
    · by_cases h2 : deltaAt κ x = r
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, mul_one]
      · rw [if_neg fun h => h2 h.2, if_neg h2, mul_zero]
    · rw [if_neg fun h => h1 h.1, if_neg h1, zero_mul]
  have each' : ∀ x : crtEntry.Coins,
      ((swappedTableLaw crtLayout).map fun table => restOf u κ (x, table)) c =
        if eCoins u κ x = c.1 then q else 0 :=
    fun x => table_map_apply' (eCoins u κ x) c u κ
  rw [Finset.sum_congr rfl fun x _ => congrArg _ (each x), Finset.sum_congr rfl fun x _ => congrArg _ (each' x)]
  have split := split_sum (X := crtEntry.Coins) (deltaAt κ) (setDelta u κ) (deltaAt_setDelta u κ)
    (setDelta_deltaAt u κ) (setDelta_setDelta u κ) (fun x => if eCoins u κ x = c.1 then q else 0)
    (fun x d => congrArg (fun e => if e = c.1 then q else 0) (eCoins_setDelta u κ x d))
    (fun d => if d = r then 1 else 0)
  refine split.trans ?_
  rw [Finset.sum_eq_single (ι := Block) r (fun d _ ne => by rw [if_neg ne, mul_zero])
    (fun h => absurd (Finset.mem_univ r) h), if_pos rfl, mul_one]

/-- **Independence**: the law of `(fine, Δ_κ)` is the law of the fine view times the uniform law on blocks. -/
theorem fine_split (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (κ : Fin 2) :
    (swappedTableTape crtEntry).map (fun tape => (fine parameter scalar u κ tape, res κ tape)) =
      ((swappedTableTape crtEntry).map (fine parameter scalar u κ)).bind fun w =>
        (PMF.uniformOfFintype Block).map fun r => (w, r) := by
  ext ⟨⟨b, c⟩, r⟩
  -- the left side, reassociated
  have assoc : (swappedTableTape crtEntry).map (fun tape => (fine parameter scalar u κ tape, res κ tape)) =
      ((swappedTableTape crtEntry).map fun tape =>
        (crtPart parameter scalar κ tape, (restOf u κ tape, res κ tape))).map fun p => ((p.1, p.2.1), p.2.2) := by
    rw [PMF.map_comp]
    rfl
  have assocInj : Function.Injective fun p : Vector Label Entry.convCount × (Entry.Coins × TagTable) × Block =>
      ((p.1, p.2.1), p.2.2) := by
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [h1, h2, h3]
  have lhs : ((swappedTableTape crtEntry).map (fun tape => (fine parameter scalar u κ tape, res κ tape)))
      ((b, c), r) = ((swappedTableTape crtEntry).map fun tape =>
        (crtPart parameter scalar κ tape, (restOf u κ tape, res κ tape))) (b, (c, r)) := by
    rw [assoc]
    exact map_apply_inj _ assocInj (b, (c, r))
  rw [lhs, conv_split parameter scalar u κ _ (restRes_reads u κ) b (c, r), rest_split u κ c r]
  -- the right side
  rw [PMF.bind_apply, tsum_eq_single (b, c)]
  · rw [map_apply_inj (PMF.uniformOfFintype Block) (φ := fun r' => ((b, c), r'))
      (fun a a' h => by simpa using h) r]
    have fineEq : ((swappedTableTape crtEntry).map (fine parameter scalar u κ)) (b, c) =
        ((swappedTableTape crtEntry).map fun tape => (crtPart parameter scalar κ tape, restOf u κ tape)) (b, c) :=
      rfl
    rw [fineEq, conv_split parameter scalar u κ _ (restOf_reads u κ) b c, mul_assoc]
  · intro w ne
    rw [map_apply_notMem (PMF.uniformOfFintype Block) (fun r' => (w, r')) ((b, c), r)
      (fun r' h => ne (congrArg Prod.fst h)), mul_zero]

end Fine

/-! ### 5. Reading the fine view: coins, labels, tables -/

theorem zeroOf_eq_coinKeys (coins : Entry.Coins) (κ : Fin 2) : Entry.zeroOf coins κ = (coinKeys coins).1 κ := by
  fin_cases κ <;> rfl

theorem deltaOf_eq_coinKeys (coins : Entry.Coins) (κ : Fin 2) : Entry.deltaOf coins κ = (coinKeys coins).2 κ := by
  fin_cases κ <;> rfl

theorem deltaAt_eq_deltaOf (coins : Entry.Coins) (κ : Fin 2) : deltaAt κ coins = Entry.deltaOf coins κ :=
  (deltaOf_eq_coinKeys coins κ).symm

section Same

variable {u : AffineInput} {κ : Fin 2} {c c' : Entry.Coins} (same : eCoins u κ c = eCoins u κ c')

include same

theorem eKeys_eq : eKeys u κ (coinKeys c) = eKeys u κ (coinKeys c') := by
  have keys := congrArg coinKeys same
  unfold eCoins at keys
  rwa [coinKeys_withKeys, coinKeys_withKeys] at keys

/-- **`u`'s labels of coordinate `κ` agree.** -/
theorem eLabel_eq : eLabel u κ (coinKeys c) = eLabel u κ (coinKeys c') := by
  have first := congrArg (fun keys : LabelKeys => keys.1 κ) (eKeys_eq same)
  simpa only [eKeys, Function.update_self] using first

/-- **The other coordinate's keys agree.** -/
theorem keys_other (i : Fin 2) (hi : i ≠ κ) :
    (coinKeys c).1 i = (coinKeys c').1 i ∧ (coinKeys c).2 i = (coinKeys c').2 i := by
  have first := congrArg (fun keys : LabelKeys => keys.1 i) (eKeys_eq same)
  have second := congrArg (fun keys : LabelKeys => keys.2 i) (eKeys_eq same)
  simp only [eKeys, Function.update_of_ne hi] at first second
  exact ⟨first, second⟩

theorem offsets_eq : c.offsets = c'.offsets := by
  have h := congrArg Scheme.Coins.offsets same
  exact h

theorem pointRandomness_eq : c.pointRandomness = c'.pointRandomness := by
  have h := congrArg Scheme.Coins.pointRandomness same
  exact h

theorem exceptionPad_eq : c.exceptionPad = c'.exceptionPad := by
  have h := congrArg Scheme.Coins.exceptionPad same
  exact h

theorem bridgeKey_eq : c.bridgeKey = c'.bridgeKey := by
  have h := congrArg Scheme.Coins.bridgeKey same
  exact h

theorem curveMask_eq : c.curveMask = c'.curveMask := by
  have h := congrArg Scheme.Coins.curveMask same
  exact h

theorem curveR1_eq : c.curveR1 = c'.curveR1 := by
  have h := congrArg Scheme.Coins.curveR1 same
  exact h

theorem curveR2_eq : c.curveR2 = c'.curveR2 := by
  have h := congrArg Scheme.Coins.curveR2 same
  exact h

theorem exceptional_eq (scalar : NonZeroScalar) : Entry.exceptional scalar c = Entry.exceptional scalar c' := by
  funext o
  unfold Entry.exceptional Entry.outputKeysOf
  rw [offsets_eq same]

end Same

/-- The hash of a tag table. -/
abbrev hashOf (table : TagTable) : HashN := schemeHash (tableOracle (FI := Empty) (EI := Empty) table)

theorem hashInput_small (label : Block) {τ : ℕ} (small : τ < 2 ^ 40) : hashInput label τ < baseFieldModulus := by
  have labelLt := label.isLt
  unfold hashInput
  calc label.toNat + 2 ^ 128 * τ < 2 ^ 128 + 2 ^ 128 * τ := by omega
    _ = 2 ^ 128 * (τ + 1) := by ring
    _ ≤ 2 ^ 128 * 2 ^ 40 := Nat.mul_le_mul_left _ (by omega)
    _ < baseFieldModulus := by unfold baseFieldModulus; norm_num

/-- **A labelled input is answered by the table at its tag**, whatever its label. -/
theorem hashOf_hashInput (table : TagTable) (label : Block) (τ : ℕ) (small : τ < 2 ^ 40) :
    hashOf table (hashInput label τ) = table ⟨τ, small⟩ := by
  show table (tagOfInput ((hashInput label τ : ℕ) : BaseField)) = table ⟨τ, small⟩
  congr 1
  apply Fin.ext
  show ((hashInput label τ : ℕ) : BaseField).val / 2 ^ 128 % 2 ^ 40 = τ
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hashInput_small label small), hashInput_tag, Nat.mod_eq_of_lt small]

/-- Two tables with equal masks agree off the hot conversion tags. -/
theorem table_agree {u : AffineInput} {κ : Fin 2} {t t' : TagTable} (same : maskTable u κ t = maskTable u κ t')
    (tag : Fin (2 ^ 40)) (cold : ¬ H8.hotConvTag Entry.table u κ.val tag) : t tag = t' tag := by
  rw [← maskTable_eq u κ t tag cold, ← maskTable_eq u κ t' tag cold, same]

/-- **Their hashes agree at every labelled input off the hot conversion tags**, whatever the two labels. -/
theorem hash_agree {u : AffineInput} {κ : Fin 2} {t t' : TagTable} (same : maskTable u κ t = maskTable u κ t')
    (label label' : Block) (τ : ℕ) (small : τ < 2 ^ 40) (cold : ¬ H8.hotConvTag Entry.table u κ.val ⟨τ, small⟩) :
    hashOf t (hashInput label τ) = hashOf t' (hashInput label' τ) := by
  rw [hashOf_hashInput t label τ small, hashOf_hashInput t' label' τ small]
  exact table_agree same _ cold

/-! ### 6. Related asked lists -/

/-- A constant raw-word shift, used by the narrow coordinate relation after embedding. -/
def RelAskedConst (hot : ℕ → Prop) (δ : Block) (A₁ A₂ : List ℕ) : Prop :=
  List.Forall₂ (fun n₁ n₂ => n₁ / 2 ^ 128 = n₂ / 2 ^ 128 ∧ (¬ hot (n₁ / 2 ^ 128) → n₁ = n₂) ∧
    (hot (n₁ / 2 ^ 128) → BitVec.ofNat 128 n₁ = BitVec.ofNat 128 n₂ ^^^ δ)) A₁ A₂

/-- Conversion controls carry the projected shift; digest controls retain the full shift. -/
def queryShift (δ : Block) (τ : ℕ) : Block :=
  if tagFamily τ ≤ 6 then embed (clip δ) else δ

/-- Equal tags and cold inputs, with the raw or projected shift selected by the tag family. -/
def RelAsked (hot : ℕ → Prop) (δ : Block) (A₁ A₂ : List ℕ) : Prop :=
  List.Forall₂ (fun n₁ n₂ => n₁ / 2 ^ 128 = n₂ / 2 ^ 128 ∧ (¬ hot (n₁ / 2 ^ 128) → n₁ = n₂) ∧
    (hot (n₁ / 2 ^ 128) → BitVec.ofNat 128 n₁ = BitVec.ofNat 128 n₂ ^^^ queryShift δ (n₁ / 2 ^ 128))) A₁ A₂

/-- **The tags whose garbler label is `u`'s label plus `Δ_κ`**: the hot conversion and body tags of `κ` (families 0
to 6), and the digest labels of `κ` at the bit `u` does not hold (family 8). -/
def Shifted (u : AffineInput) (κ : Fin 2) (τ : ℕ) : Prop :=
  tagCoord τ = κ.val ∧ ((tagFamily τ ≤ 6 ∧ hotTag Entry.table u τ = true) ∨
    (tagFamily τ = 8 ∧ tagPart τ ≠ inputBit u κ.val (tagSlot τ)))

theorem RelAsked.append {hot : ℕ → Prop} {δ : Block} {A B C D : List ℕ} (first : RelAsked hot δ A B)
    (second : RelAsked hot δ C D) : RelAsked hot δ (A ++ C) (B ++ D) :=
  List.rel_append first second

theorem RelAsked.refl {hot : ℕ → Prop} {δ : Block} {A : List ℕ} (none : ∀ n ∈ A, ¬ hot (n / 2 ^ 128)) :
    RelAsked hot δ A A := by
  induction A with
  | nil => exact List.Forall₂.nil
  | cons n rest ih =>
    refine List.Forall₂.cons ⟨rfl, fun _ => rfl, fun h => absurd h (none n (List.mem_cons_self))⟩
      (ih fun m inside => none m (List.mem_cons_of_mem _ inside))

theorem RelAsked.of_eq {hot : ℕ → Prop} {δ : Block} {A B : List ℕ} (eq : A = B)
    (none : ∀ n ∈ A, ¬ hot (n / 2 ^ 128)) : RelAsked hot δ A B := eq ▸ RelAsked.refl none

theorem RelAsked.congr {hot hot' : ℕ → Prop} {δ : Block} {A B : List ℕ}
    (iff : ∀ n ∈ A, hot (n / 2 ^ 128) ↔ hot' (n / 2 ^ 128)) (rel : RelAsked hot δ A B) : RelAsked hot' δ A B := by
  induction rel with
  | nil => exact List.Forall₂.nil
  | @cons a b rest rest' head tail ih =>
    refine List.Forall₂.cons ⟨head.1, fun h => head.2.1 fun h' => h ((iff a List.mem_cons_self).mp h'),
      fun h => head.2.2 ((iff a List.mem_cons_self).mpr h)⟩
      (ih fun m inside => iff m (List.mem_cons_of_mem _ inside))

/-- Lift a constant shift on a restricted list to its tag-dependent shift. -/
theorem RelAsked.of_constant {hot : ℕ → Prop} {δ raw : Block} {A B : List ℕ}
    (rel : RelAskedConst hot raw A B)
    (same : ∀ n ∈ A, queryShift δ (n / 2 ^ 128) = raw) : RelAsked hot δ A B := by
  induction rel with
  | nil => exact List.Forall₂.nil
  | @cons a b rest rest' head tail ih =>
    refine List.Forall₂.cons ⟨head.1, head.2.1, ?_⟩
      (ih fun n hn => same n (List.mem_cons_of_mem _ hn))
    intro h
    rw [same a List.mem_cons_self]
    exact head.2.2 h

/-- **The garbler's tail after the two coordinates**: the key, the masks, the digest. -/
def tailM (scalar : NonZeroScalar) (coins : Entry.Coins) :
    CM (MaskValues digitCount × (Fin digitCount → Exception.Entry)) :=
  keyM coins.bridgeKey >>= fun K =>
    maskAnswersM K digitCount >>= fun masks =>
      digestGarbleM coordinateBitCount digitCount (Entry.zeroOf coins) (Entry.deltaOf coins)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).digit)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).offset.coordinates)
          (fun o => coins.exceptionPad.get o) >>= fun entries =>
        pure (masks, entries)

/-- **The tail's relation** (`Hidden/DeltaTail.lean`): two coins with the same fine
coins and two tables with the same masks give related tail question lists and the same tail values. -/
def TailRel : Prop :=
  ∀ (scalar : NonZeroScalar) (u : AffineInput) (κ : Fin 2) (c c' : Entry.Coins) (t t' : TagTable),
    eCoins u κ c = eCoins u κ c' → maskTable u κ t = maskTable u κ t' →
      RelAsked (Shifted u κ) (deltaAt κ c ^^^ deltaAt κ c') (asked (hashOf t) (tailM scalar c))
          (asked (hashOf t') (tailM scalar c')) ∧
        (tailM scalar c).eval (hashOf t) = (tailM scalar c').eval (hashOf t')


end

end Kriterion.CRT.Privacy.DeltaView
