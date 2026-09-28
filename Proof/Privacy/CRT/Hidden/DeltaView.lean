/-
**H7's `Δ` residual** (shared by `convHot`, `Hidden/CaseConv.lean`, and `digestOther`,
`Hidden/CaseDigest.lean`).

A stage-2 guess at a hidden conversion/body tag fixes `clip Δ_κ`; a hidden digest guess fixes the full `Δ_κ`.
This file preserves a full raw residual, uniform and independent of a view finer than the stage-2 view.
The downstream bounds are `2^-104` for the projected conversion guess and `2^-128` for the full digest guess:

* the **fine view** `fine` of a tape: coordinate `κ`'s published conversion material, the coins with `κ`'s zero
  labels replaced by `u`'s labels `E_κ = Z_κ ⊕ u·Δ_κ` and `Δ_κ` by `0` (`eCoins`), the table outside the hot
  conversion tags of `κ` at `u` (`maskTable`), and (no chunk joins) the **actual selected labels** of `u`
  (`labelsAt`: the coins' zero labels with the chunk-tree level sums installed, `Laws.LabelsSplitProof.tapeLabels_eq`).
  With `E_κ` they fix `κ`'s chunk joins (`NoJoins.clip_selZ_actual`), which the flat vector omits;
* **independence** (`fine_split`): the law of `(fine, Δ_κ)` is the law of `fine` times the uniform law on blocks.
  The conversion material is uniform and independent of everything off its hot payload tags (families `1` to `5`),
  the coins, the chunk-tree answers and the labels included (`crtConvSplit`). The coin `Δ_κ` has a setter that keeps
  `u`'s coin labels (`setDelta`); refilling `κ`'s hot chunk-tree answers (uniform under the swapped table law,
  `HiddenGuess.swappedTableLaw_fill`) and shifting them by `u_j · clip (Δ_κ ⊕ Δ'_κ)` keeps the actual labels
  (`labelsAt_setDelta`), so the fill-averaged label mass does not read `Δ_κ` (`fillMass_setDelta`) and under the
  uniform coin law `Δ_κ` is uniform and independent of the rest (`split_sum`). The high part of `Δ_κ` is never
  conditioned on: the full 128-bit residual stays uniform.
-/

import Proof.Privacy.CRT.Hidden.StageTwo
import Proof.Privacy.CRT.Core.ConvSplit
import Proof.Privacy.CRT.Laws.LabelsSplit
import Proof.Privacy.CRT.NoJoins.View

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Kriterion.CRT.Privacy.DeltaView

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.Instance (crtEntry)
open Kriterion.CRT.Privacy.Laws (coinLaw swappedTableTape_eq tape_map_apply map_apply_inj map_apply_notMem)
open Kriterion.CRT.Privacy.Laws.LabelsSplitProof (LabelKeys coinKeys withKeys coinKeys_withKeys withKeys_coinKeys
  withKeys_withKeys split_sum coinLaw_eq zeroOfC deltaOfC zeroOfC_eq_coinKeys)
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

/-- **The labels of `u`** of a tape (no chunk joins): the actual selected labels, the source-form labels of the
coins' zero labels with the table's chunk-tree level sums installed (`Laws.LabelsSplitProof.tapeLabels_eq`). -/
def labelsAt (u : AffineInput) (tape : TableTape crtEntry) : LamportSignature :=
  NoJoins.sourceLabels (NoJoins.actualZeros (NoJoins.tableAnswers tape.2) (zeroOfC tape.1)) (deltaOfC tape.1) u

/-- The type of the rest of the fine view: the coins through `u`'s labels, the masked table, the labels. -/
abbrev RType := Entry.Coins × TagTable × LamportSignature

/-- The type of the fine view. -/
abbrev WType := Vector Label Entry.convCount × RType

/-! ### The labels through the hot chunk-tree answers of `κ` -/

/-- The labels read the table at the chunk-tree tags only (family `0`). -/
theorem labelsAt_congr (u : AffineInput) {c : crtEntry.Coins} {t t' : TagTable}
    (agree0 : ∀ p : Fin (2 ^ 40), tagFamily p.val = 0 → t p = t' p) : labelsAt u (c, t) = labelsAt u (c, t') := by
  unfold labelsAt
  dsimp only
  rw [NoJoins.actualZeros_family0 agree0]

/-- An indicator with the classical decision. -/
def indP (P : Prop) : ℝ≥0∞ := @ite _ P (Classical.propDecidable P) 1 0

theorem indP_pos {P : Prop} (h : P) : indP P = 1 := by
  unfold indP
  rw [if_pos h]

theorem indP_neg {P : Prop} (h : ¬ P) : indP P = 0 := by
  unfold indP
  rw [if_neg h]

theorem indP_and (P Q : Prop) : indP (P ∧ Q) = indP P * indP Q := by
  by_cases p : P
  · by_cases q : Q
    · rw [indP_pos ⟨p, q⟩, indP_pos p, indP_pos q, mul_one]
    · rw [indP_neg fun h => q h.2, indP_neg q, mul_zero]
  · rw [indP_neg fun h => p h.1, indP_neg p, zero_mul]

theorem map_apply_indP {X Y : Type} (μ : PMF X) (F : X → Y) (y : Y) :
    (μ.map F) y = ∑' x, μ x * indP (F x = y) := by
  rw [PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases h : F x = y
  · rw [if_pos h.symm, indP_pos h, mul_one]
  · rw [if_neg fun e => h e.symm, indP_neg h, mul_zero]

/-- Coordinate `κ`'s hot chunk-tree positions at `u`, filled with `f`. -/
abbrev fillOne (u : AffineInput) (κ : Fin 2) (f : NoJoins.Bits → Block × Block) (t : TagTable) : TagTable :=
  HiddenGuess.fillAt (NoJoins.hotPosOf u κ) f t

/-- **The hot chunk-tree answers of `κ` refill uniformly** under the swapped table law. -/
theorem table_fill (u : AffineInput) (κ : Fin 2) (W : TagTable → ℝ≥0∞) :
    ∑' t, swappedTableLaw crtLayout t * W t =
      ∑' t, swappedTableLaw crtLayout t * ∑' f, PMF.uniformOfFintype (NoJoins.Bits → Block × Block) f *
        W (fillOne u κ f t) := by
  have fill := HiddenGuess.swappedTableLaw_fill crtLayout (NoJoins.hotPosOf u κ) (NoJoins.hotPosOf_injective u κ)
    (NoJoins.hotPosOf_away u κ)
  conv_lhs => rw [← fill]
  rw [NoJoins.tsum_bind_mul]
  exact tsum_congr fun t => congrArg _ (NoJoins.tsum_map_mul _ _ W)

/-- The mask does not read the hot chunk-tree answers of `κ` (they are hot conversion tags of `κ`). -/
theorem maskTable_fillOne (u : AffineInput) (κ : Fin 2) (f : NoJoins.Bits → Block × Block) (t : TagTable) :
    maskTable u κ (fillOne u κ f t) = maskTable u κ t := by
  funext tag
  unfold maskTable
  split_ifs with hot
  · rfl
  · refine HiddenGuess.fillAt_apply_of_not_mem _ _ _ _ ?_
    rintro ⟨j, rfl⟩
    refine hot ⟨?_, NoJoins.hotPos_coord u (κ, j), NoJoins.hotPos_hot u (κ, j)⟩
    show tagFamily (NoJoins.hotPos u (κ, j)).val ≤ 5
    rw [NoJoins.hotPos_family]
    omega

theorem bitOf_eq_uBit (u : AffineInput) (κ : Fin 2) (j : NoJoins.Bits) : NoJoins.bitOf u κ j = uBit u κ j.val := by
  fin_cases κ <;> simp [NoJoins.bitOf, uBit]

/-- The per-bit selected labels of label keys are `u`'s labels. -/
theorem selZ_eq_eLabel (u : AffineInput) (κ : Fin 2) (keys : LabelKeys) (j : Fin coordinateBitCount) :
    NoJoins.selZ keys.1 keys.2 u κ j = eLabel u κ keys j := by
  rw [NoJoins.selZ_apply, bitOf_eq_uBit]
  rfl

theorem deltaOfC_eq_coinKeys (x : crtEntry.Coins) : deltaOfC x = (coinKeys x).2 := by
  funext κ
  fin_cases κ <;> rfl

theorem coinKeys_setDelta (u : AffineInput) (κ : Fin 2) (x : Entry.Coins) (d : Block) :
    coinKeys (setDelta u κ x d) = shiftKeys u κ (coinKeys x) d := by
  unfold setDelta
  rw [coinKeys_withKeys]

theorem zeroOfC_setDelta (u : AffineInput) (κ : Fin 2) (x : crtEntry.Coins) (d : Block) :
    zeroOfC (setDelta u κ x d) = (shiftKeys u κ (coinKeys x) d).1 := by
  have keys := coinKeys_setDelta u κ x d
  have e : zeroOfC (setDelta u κ x d) = (coinKeys (setDelta u κ x d)).1 := by
    funext κ'
    fin_cases κ' <;> rfl
  exact e.trans (congrArg Prod.fst keys)

theorem deltaOfC_setDelta (u : AffineInput) (κ : Fin 2) (x : crtEntry.Coins) (d : Block) :
    deltaOfC (setDelta u κ x d) = (shiftKeys u κ (coinKeys x) d).2 := by
  have keys := coinKeys_setDelta u κ x d
  have e : deltaOfC (setDelta u κ x d) = (coinKeys (setDelta u κ x d)).2 := by
    funext κ'
    fin_cases κ' <;> rfl
  exact e.trans (congrArg Prod.snd keys)

/-- **Resetting `Δ_κ` is shifting `κ`'s hot chunk-tree answers**: the labels of the tape with `Δ_κ` set to `d` and
`κ`'s hot positions filled with `f` are those of the tape with the hot answers shifted by `u_j · clip (Δ_κ ⊕ d)`. -/
theorem labelsAt_setDelta (u : AffineInput) (κ : Fin 2) (x : crtEntry.Coins) (d : Block)
    (f : NoJoins.Bits → Block × Block) (t : TagTable) :
    labelsAt u (setDelta u κ x d, fillOne u κ f t) =
      labelsAt u (x, fillOne u κ (NoJoins.shiftAns u κ (clip (deltaAt κ x ^^^ d)) f) t) := by
  unfold labelsAt
  apply NoJoins.labels_of_selZ
  dsimp only
  rw [zeroOfC_setDelta, deltaOfC_setDelta, zeroOfC_eq_coinKeys, deltaOfC_eq_coinKeys]
  have δ : deltaAt κ x ^^^ d = (coinKeys x).2 κ ^^^ (shiftKeys u κ (coinKeys x) d).2 κ := by
    rw [shiftKeys_delta]
    rfl
  rw [δ]
  refine NoJoins.selZ_fillOne_shift u κ t _ _ _ _ (fun j => ?_) (fun κ' ne => ?_) (fun κ' ne => ?_) f
  · rw [selZ_eq_eLabel, selZ_eq_eLabel, eLabel_shiftKeys]
  · simp only [shiftKeys, Function.update_of_ne ne]
  · simp only [shiftKeys, Function.update_of_ne ne]

/-- The mass of the labels `l` at coins `x`, averaged over `κ`'s hot chunk-tree answers. -/
def fillMass (u : AffineInput) (κ : Fin 2) (x : crtEntry.Coins) (t : TagTable) (l : LamportSignature) : ℝ≥0∞ :=
  ∑' f, PMF.uniformOfFintype (NoJoins.Bits → Block × Block) f * indP (labelsAt u (x, fillOne u κ f t) = l)

/-- **The fill-averaged label mass does not read `Δ_κ`.** -/
theorem fillMass_setDelta (u : AffineInput) (κ : Fin 2) (x : crtEntry.Coins) (d : Block) (t : TagTable)
    (l : LamportSignature) : fillMass u κ (setDelta u κ x d) t l = fillMass u κ x t l := by
  unfold fillMass
  simp only [labelsAt_setDelta, PMF.uniformOfFintype_apply]
  exact (NoJoins.shiftEquiv u κ (clip (deltaAt κ x ^^^ d))).tsum_eq
    (fun f => (↑(Fintype.card (NoJoins.Bits → Block × Block)) : ℝ≥0∞)⁻¹ *
      indP (labelsAt u (x, fillOne u κ f t) = l))

section Fine

variable [FieldCertificate] [GroupCertificate]

/-- Coordinate `κ`'s published conversion material (the part of `crtConvSplit`). -/
def crtPart (parameter : ℕ) (scalar : NonZeroScalar) (κ : Fin 2) (tape : TableTape crtEntry) :
    Vector Label Entry.convCount :=
  if κ = 0 then (H8.realGarbled crtEntry parameter scalar tape).1.crtX
  else (H8.realGarbled crtEntry parameter scalar tape).1.crtY

/-- The rest of the fine view: the coins through `u`'s labels, the table off the hot conversion tags, and the
actual selected labels of `u`. -/
def restOf (u : AffineInput) (κ : Fin 2) (tape : TableTape crtEntry) : RType :=
  (eCoins u κ tape.1, maskTable u κ tape.2, labelsAt u tape)

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
    (g : TableTape crtEntry → α) (reads : H8.ReadsOff Eq (H8.hotPayloadTag Entry.table u κ.val) g)
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
    H8.ReadsOff Eq (H8.hotPayloadTag Entry.table u κ.val) (restOf u κ) := by
  rintro ⟨c, t⟩ ⟨c', t'⟩ sameCoins agree
  dsimp only at sameCoins agree
  subst sameCoins
  have mask : maskTable u κ t = maskTable u κ t' := by
    funext tag
    unfold maskTable
    split_ifs with hot
    · rfl
    · exact agree tag fun payload => hot (H8.hotPayloadTag_hotConvTag payload)
  have labels : labelsAt u (c, t) = labelsAt u (c, t') :=
    labelsAt_congr u fun p zero => agree p fun payload => by
      have one := payload.1
      omega
  show (eCoins u κ c, maskTable u κ t, labelsAt u (c, t)) = (eCoins u κ c, maskTable u κ t', labelsAt u (c, t'))
  rw [mask, labels]

theorem restRes_reads (u : AffineInput) (κ : Fin 2) :
    H8.ReadsOff Eq (H8.hotPayloadTag Entry.table u κ.val) (fun tape => (restOf u κ tape, res κ tape)) := by
  intro tape tape' sameCoins agree
  show (restOf u κ tape, res κ tape) = (restOf u κ tape', res κ tape')
  rw [restOf_reads u κ tape tape' sameCoins agree]
  unfold res
  rw [sameCoins]

/-- **The coin split**: `Δ_κ` is uniform and independent of the rest of the fine view. -/
theorem rest_split (u : AffineInput) (κ : Fin 2) (c : RType) (r : Block) :
    ((swappedTableTape crtEntry).map fun tape => (restOf u κ tape, res κ tape)) (c, r) =
      ((swappedTableTape crtEntry).map (restOf u κ)) c * PMF.uniformOfFintype Block r := by
  let Q : crtEntry.Coins → ℝ≥0∞ := fun x => indP (eCoins u κ x = c.1) *
    ∑' t, swappedTableLaw crtLayout t * (indP (maskTable u κ t = c.2.1) * fillMass u κ x t c.2.2)
  have pointRest : ∀ (x : crtEntry.Coins) t f, indP (restOf u κ (x, fillOne u κ f t) = c) =
      indP (eCoins u κ x = c.1) *
        (indP (maskTable u κ t = c.2.1) * indP (labelsAt u (x, fillOne u κ f t) = c.2.2)) := by
    intro x t f
    rw [← indP_and, ← indP_and]
    congr 1
    obtain ⟨c1, c2, c3⟩ := c
    show ((eCoins u κ x, maskTable u κ (fillOne u κ f t), labelsAt u (x, fillOne u κ f t)) = (c1, c2, c3)) = _
    rw [maskTable_fillOne]
    simp only [Prod.mk.injEq]
  have inner : ∀ x : crtEntry.Coins,
      ∑' t, swappedTableLaw crtLayout t * indP (restOf u κ (x, t) = c) = Q x := by
    intro x
    rw [table_fill u κ]
    simp only [pointRest, Q, fillMass]
    simp_rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun t => tsum_congr fun f => by ring
  have lhs : ((swappedTableTape crtEntry).map fun tape => (restOf u κ tape, res κ tape)) (c, r) =
      ∑' x, coinLaw x * (Q x * indP (deltaAt κ x = r)) := by
    rw [map_apply_indP, Laws.tsum_tape]
    refine tsum_congr fun x => congrArg _ ?_
    have split : ∀ t, indP ((restOf u κ (x, t), res κ (x, t)) = (c, r)) =
        indP (restOf u κ (x, t) = c) * indP (deltaAt κ x = r) := by
      intro t
      rw [← indP_and]
      congr 1
      exact Prod.mk.injEq _ _ _ _
    simp only [split]
    rw [← inner x, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun t => by ring
  have rhs : ((swappedTableTape crtEntry).map (restOf u κ)) c = ∑' x, coinLaw x * Q x := by
    rw [map_apply_indP, Laws.tsum_tape]
    exact tsum_congr fun x => congrArg _ (inner x)
  have hQ : ∀ (x : crtEntry.Coins) d, Q (setDelta u κ x d) = Q x := by
    intro x d
    have e : eCoins u κ (setDelta u κ x d) = eCoins u κ x := eCoins_setDelta u κ x d
    simp only [Q, e, fillMass_setDelta]
  rw [lhs, rhs, coinLaw_eq, tsum_fintype, tsum_fintype]
  have split := split_sum (X := crtEntry.Coins) (deltaAt κ) (setDelta u κ) (deltaAt_setDelta u κ)
    (setDelta_deltaAt u κ) (setDelta_setDelta u κ) Q hQ (fun d => indP (d = r))
  refine split.trans ?_
  rw [Finset.sum_eq_single (ι := Block) r (fun d _ ne => by rw [indP_neg ne, mul_zero])
    (fun h => absurd (Finset.mem_univ r) h), indP_pos rfl, mul_one]

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
  have assocInj : Function.Injective fun p : Vector Label Entry.convCount × RType × Block =>
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

/-- **The garbler's tail after the two coordinates**: the key, the masks, the digest. No chunk joins: the digest
reads the actual zero labels `zero` (the coins' zero labels with the coordinates' chunk joins absorbed,
`Entry.keyZeroOf`), which the garbler computes from the two coordinate garblings. -/
def tailM (scalar : NonZeroScalar) (coins : Entry.Coins) (zero : Fin 2 → Fin coordinateBitCount → Block) :
    CM (MaskValues digitCount × (Fin digitCount → Exception.Entry)) :=
  keyM coins.bridgeKey >>= fun K =>
    maskAnswersM K digitCount >>= fun masks =>
      digestGarbleM coordinateBitCount digitCount zero (Entry.deltaOf coins)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).digit)
          (fun o => ((Entry.outputKeysOf scalar coins).get o).offset.coordinates)
          (fun o => coins.exceptionPad.get o) >>= fun entries =>
        pure (masks, entries)

/-- **The tail's relation** (`Hidden/DeltaTail.lean`): two coins with the same fine coins, two tables with the same
masks and two actual zero labels with the same selected labels of `u` give related tail question lists and the same
tail values. -/
def TailRel : Prop :=
  ∀ (scalar : NonZeroScalar) (u : AffineInput) (κ : Fin 2) (c c' : Entry.Coins)
    (z z' : Fin 2 → Fin coordinateBitCount → Block) (t t' : TagTable),
    eCoins u κ c = eCoins u κ c' → maskTable u κ t = maskTable u κ t' →
    NoJoins.sourceLabels z (Entry.deltaOf c) u = NoJoins.sourceLabels z' (Entry.deltaOf c') u →
      RelAsked (Shifted u κ) (deltaAt κ c ^^^ deltaAt κ c') (asked (hashOf t) (tailM scalar c z))
          (asked (hashOf t') (tailM scalar c' z')) ∧
        (tailM scalar c z).eval (hashOf t) = (tailM scalar c' z').eval (hashOf t')


end

end Kriterion.CRT.Privacy.DeltaView
