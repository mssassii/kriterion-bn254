/-
**`LabelsSplit`** (the named input of `Laws/Rest.lean`'s `crtRestSplit_of`).

The labels of `u` read only the coins' input label keys (`inputZero`, `inputDelta`). The key of a real garbling is
`coins.inputMacKey` on every hash (`EntryCorrect.garbleCM_eval`), so the table never enters, and the selected labels are
`Entry.labels` read on the coins' zeros and deltas (`EntryDelivery.labelX_honest`, `labelY_honest`).

The coin law of the swapped tape is uniform. The label keys are a coordinate of the coins with a setter, and neither
`SameOffLabels` nor the exceptional inputs (which read the offsets only) see it. Under a uniform law such a coordinate
is uniform and independent of every weight that ignores it (`split_sum`, through the equivalence of the space with a
fibre times the coordinate). The source's labels read the same coordinate of a uniform source, so they have the same
law (`map_comp_get`).
-/

import Proof.Privacy.CRT.Laws.Rest
import Proof.Correctness.CRT.EntryCorrect

namespace Kriterion.CRT.Privacy.Laws.LabelsSplitProof

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance Kriterion.CRT.Privacy.Laws
open scoped ENNReal

noncomputable section

/-! ### 1. A uniform law splits along a coordinate with a setter -/

theorem sum_equiv {X F Z : Type} [Fintype X] [Nonempty X] [Fintype F] [Nonempty F] [Fintype Z] [Nonempty Z]
    (e : X ≃ F × Z) (Φ : X → ℝ≥0∞) :
    ∑ x, PMF.uniformOfFintype X x * Φ x =
      ∑ y, ∑ z, PMF.uniformOfFintype F y * PMF.uniformOfFintype Z z * Φ (e.symm (y, z)) := by
  have card : (Fintype.card X : ℝ≥0∞)⁻¹ = (Fintype.card F : ℝ≥0∞)⁻¹ * (Fintype.card Z : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [PMF.uniformOfFintype_apply, card]
  exact (e.symm.sum_comp fun x => (Fintype.card F : ℝ≥0∞)⁻¹ * (Fintype.card Z : ℝ≥0∞)⁻¹ * Φ x).symm.trans
    (Fintype.sum_prod_type _)

theorem sum_uniform_one {Z : Type} [Fintype Z] [Nonempty Z] : ∑ z, PMF.uniformOfFintype Z z = 1 := by
  have total := PMF.tsum_coe (PMF.uniformOfFintype Z)
  rwa [tsum_fintype] at total

/-- **The split**: under a uniform law, a coordinate `get` with a setter is uniform and independent of every weight
that the setter does not change. -/
theorem split_sum {X Z : Type} [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (get : X → Z) (set : X → Z → X) (get_set : ∀ x z, get (set x z) = z) (set_get : ∀ x, set x (get x) = x)
    (set_set : ∀ x z z', set (set x z) z' = set x z')
    (f : X → ℝ≥0∞) (hf : ∀ x z, f (set x z) = f x) (g : Z → ℝ≥0∞) :
    ∑ x, PMF.uniformOfFintype X x * (f x * g (get x)) =
      (∑ x, PMF.uniformOfFintype X x * f x) * ∑ z, PMF.uniformOfFintype Z z * g z := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have : Nonempty {x : X // get x = get x₀} := ⟨⟨x₀, rfl⟩⟩
  let e : X ≃ {x : X // get x = get x₀} × Z :=
    { toFun := fun x => (⟨set x (get x₀), get_set x _⟩, get x)
      invFun := fun p => set p.1.1 p.2
      left_inv := fun x => by
        show set (set x (get x₀)) (get x) = x
        rw [set_set, set_get]
      right_inv := fun ⟨⟨y, hy⟩, z⟩ => by
        refine Prod.ext (Subtype.ext ?_) (get_set y z)
        show set (set y z) (get x₀) = y
        rw [set_set, ← hy, set_get] }
  have inner : ∀ y : {x : X // get x = get x₀},
      ∑ z, PMF.uniformOfFintype _ y * PMF.uniformOfFintype Z z * f (e.symm (y, z)) =
        PMF.uniformOfFintype _ y * f y.1 := fun y => by
    show ∑ z, _ * _ * f (set y.1 z) = _
    simp only [hf]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_uniform_one, mul_one]
  rw [sum_equiv e, sum_equiv e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [inner y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  show _ * _ * (f (set y.1 z) * g (get (set y.1 z))) = _
  rw [hf, get_set]
  ring

/-- The law of a function of the coordinate is the law of that function of a uniform coordinate. -/
theorem map_comp_get {X Z Y : Type} [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (get : X → Z) (set : X → Z → X) (get_set : ∀ x z, get (set x z) = z) (set_get : ∀ x, set x (get x) = x)
    (set_set : ∀ x z z', set (set x z) z' = set x z') (L : Z → Y) :
    (PMF.uniformOfFintype X).map (fun x => L (get x)) = (PMF.uniformOfFintype Z).map L := by
  classical
  ext y
  have split := split_sum get set get_set set_get set_set (fun _ => 1) (fun _ _ => rfl)
    (fun z => if y = L z then 1 else 0)
  simp only [mul_one, one_mul, sum_uniform_one] at split
  rw [PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype]
  refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) (split.trans (Finset.sum_congr rfl fun z _ => ?_))
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem sum_uniform_ite {Z Y : Type} [Fintype Z] [Nonempty Z] [DecidableEq Y] (L : Z → Y) (y : Y) :
    ∑ z, PMF.uniformOfFintype Z z * (if L z = y then 1 else 0) = ((PMF.uniformOfFintype Z).map L) y := by
  rw [PMF.map_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases same : L z = y
  · rw [if_pos same, if_pos same.symm, mul_one]
  · rw [if_neg same, if_neg fun h => same h.symm, mul_zero]

/-! ### 2. The label keys of the coins and of the source -/

/-- The label keys: the zero labels and the deltas of the two coordinates (`0` is `x`). -/
abbrev LabelKeys := (Fin 2 → Fin coordinateBitCount → Block) × (Fin 2 → Block)

/-- `Entry.labels`, read on the label keys alone. -/
def labelsFrom (keys : LabelKeys) (input : AffineInput) : LamportSignature :=
  Vector.ofFn fun index =>
    if inRange : index.val < coordinateBitCount then
      let position : Fin coordinateBitCount := ⟨index.val, inRange⟩
      if input.x.val.testBit index.val then keys.1 0 position ^^^ keys.2 0
      else keys.1 0 position
    else
      let position : Fin coordinateBitCount := ⟨index.val - coordinateBitCount, by
        have := index.isLt; simp only [coordinateBitCount] at *; omega⟩
      if input.y.val.testBit position.val then keys.1 1 position ^^^ keys.2 1
      else keys.1 1 position

/-- The label keys of a source. -/
def sourceKeys (source : Entry.Source) : LabelKeys := (source.zeros, source.deltas)

/-- A source with other label keys. -/
def withSourceKeys (source : Entry.Source) (keys : LabelKeys) : Entry.Source :=
  { source with zeros := keys.1, deltas := keys.2 }

theorem labels_eq (source : Entry.Source) (input : AffineInput) :
    Entry.labels source input = labelsFrom (sourceKeys source) input := rfl

/-- The coins' coordinate of a label-key index. -/
def coordOf (κ : Fin 2) : PlanB.Coord := if κ.val = 0 then .x else .y

/-- The label-key index of a coordinate. -/
def indexOf : PlanB.Coord → Fin 2
  | .x => 0
  | .y => 1

theorem indexOf_coordOf (κ : Fin 2) : indexOf (coordOf κ) = κ := by
  fin_cases κ <;> rfl

theorem coordOf_indexOf (q : PlanB.Coord) : coordOf (indexOf q) = q := by
  cases q <;> rfl

/-- The label keys of the coins. -/
def coinKeys (coins : Entry.Coins) : LabelKeys :=
  (fun κ => coins.inputZero (coordOf κ), fun κ => coins.inputDelta (coordOf κ))

/-- Coins with other label keys. -/
def withKeys (coins : Entry.Coins) (keys : LabelKeys) : Entry.Coins :=
  { coins with inputZero := fun q => keys.1 (indexOf q), inputDelta := fun q => keys.2 (indexOf q) }

theorem coinKeys_withKeys (coins : Entry.Coins) (keys : LabelKeys) : coinKeys (withKeys coins keys) = keys := by
  obtain ⟨zeros, deltas⟩ := keys
  simp only [coinKeys, withKeys, indexOf_coordOf]

theorem withKeys_coinKeys (coins : Entry.Coins) : withKeys coins (coinKeys coins) = coins := by
  cases coins
  simp only [withKeys, coinKeys, coordOf_indexOf]

theorem withKeys_withKeys (coins : Entry.Coins) (keys keys' : LabelKeys) :
    withKeys (withKeys coins keys) keys' = withKeys coins keys' := rfl

/-! ### 3. The labels read the coins' label keys only -/

theorem getElem_eq_getD (labels : LamportSignature) (i : ℕ) (hi : i < 508) :
    labels[i] = labels.toArray.getD i 0 := by
  simp [Array.getD, hi]

theorem selectedLabels_eq (coins : Entry.Coins) (u : AffineInput) :
    Lamport.selectedLabels (coins.inputMacKey.encode (BitInput.ofAffine u)) = labelsFrom (coinKeys coins) u := by
  apply Vector.ext
  intro i hi
  rw [getElem_eq_getD _ i hi]
  simp only [labelsFrom, Vector.getElem_ofFn]
  by_cases low : i < coordinateBitCount
  · rw [dif_pos low]
    have hx := EntryDelivery.labelX_honest coins.inputMacKey (coins.inputZero .x) (coins.inputDelta .x)
      (EntryDelivery.coins_key_x coins) u i low
    unfold Entry.labelX at hx
    rw [hx]
    simp only [atNat, dif_pos low, coinKeys]
    split <;> simp [coordOf]
  · rw [dif_neg low]
    have bound : i - coordinateBitCount < 254 := by
      change i < 508 at hi
      simp only [coordinateBitCount] at low ⊢
      omega
    have hy := EntryDelivery.labelY_honest coins.inputMacKey (coins.inputZero .y) (coins.inputDelta .y)
      (EntryDelivery.coins_key_y coins) u (i - coordinateBitCount) bound
    unfold Entry.labelY at hy
    rw [show coordinateBitCount + (i - coordinateBitCount) = i by simp only [coordinateBitCount] at low ⊢; omega]
      at hy
    rw [hy]
    simp only [atNat, dif_pos bound, coinKeys]
    split <;> simp [coordOf]

theorem tapeLabels_eq [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (coins : crtEntry.Coins) (table : TagTable) :
    tapeLabels parameter scalar u (coins, table) = labelsFrom (coinKeys coins) u := by
  unfold tapeLabels realGarbled
  dsimp only [crtEntry]
  unfold Entry.scheme
  dsimp only
  erw [EntryCorrect.garbleCM_eval]
  exact selectedLabels_eq coins u

theorem withKeys_offsets (coins : Entry.Coins) (keys : LabelKeys) : (withKeys coins keys).offsets = coins.offsets :=
  rfl

theorem exceptional_withKeys (scalar : NonZeroScalar) (coins : Entry.Coins) (keys : LabelKeys) (o : ℕ) :
    Entry.exceptional scalar (withKeys coins keys) o = Entry.exceptional scalar coins o := by
  unfold Entry.exceptional Entry.outputKeysOf
  rw [withKeys_offsets]

theorem sameOffLabels_withKeys (coins : crtEntry.Coins) (keys : LabelKeys) : SameOffLabels (withKeys coins keys) coins :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem view_labels_eq [FieldCertificate] [GroupCertificate] (source : Entry.Source) (u : AffineInput) :
    (view).labels source u = labelsFrom (sourceKeys source) u :=
  labels_eq source u

/-! ### 4. The coin law is uniform -/

local instance coinsFintype : Fintype crtEntry.Coins := @Fintype.ofFinite _ crtEntry.coinsFinite

local instance coinsNonempty : Nonempty crtEntry.Coins := ⟨crtEntry.coinWitness⟩

theorem coinLaw_eq : coinLaw = PMF.uniformOfFintype crtEntry.Coins := by
  have hconst : ∀ c : crtEntry.Coins,
      ((swappedTableLaw crtEntry.layout).map fun table => (c, table)).map Prod.fst = PMF.pure c := fun c => by
    rw [PMF.map_comp]
    exact PMF.map_const _ c
  unfold coinLaw swappedTableTape
  rw [PMF.map_bind]
  simp only [hconst, PMF.bind_pure]

end

end Kriterion.CRT.Privacy.Laws.LabelsSplitProof

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open Kriterion.CRT.Privacy.Laws.LabelsSplitProof
open scoped ENNReal

noncomputable section

local instance : Fintype crtEntry.Coins := coinsFintype

local instance : Nonempty crtEntry.Coins := coinsNonempty

open Classical in
/-- **`LabelsSplit`**: the labels of `u` read only the coins' label keys, which under the coin law are uniform,
distributed as the source's label keys, and independent of every weight that `SameOffLabels` and the exceptional
inputs cannot tell apart from the label keys. -/
theorem labelsSplit : LabelsSplit := by
  intro _ _ parameter scalar u
  refine ⟨fun c table => (tapeLabels_eq parameter scalar u c table).trans
    (tapeLabels_eq parameter scalar u c zeroTable).symm, ?_⟩
  intro H hH ℓ
  let f : crtEntry.Coins → ℝ≥0∞ := fun c => if ∃ o, crtEntry.exceptional scalar c o = some u then 0 else H c
  let g : LabelKeys → ℝ≥0∞ := fun keys => if labelsFrom keys u = ℓ then 1 else 0
  have hf : ∀ (c : crtEntry.Coins) keys, f (withKeys c keys) = f c := fun c keys => by
    have exc : ∀ o, crtEntry.exceptional scalar (withKeys c keys) o = crtEntry.exceptional scalar c o :=
      exceptional_withKeys scalar c keys
    simp only [f, exc, hH _ _ (sameOffLabels_withKeys c keys)]
  have labelsFun : (fun source => (view).labels source u) = fun source => labelsFrom (sourceKeys source) u :=
    funext fun source => view_labels_eq source u
  have sourceLaw := @map_comp_get (view).Source _ _ (view).sourceFintype (view).sourceNonempty _ _ sourceKeys withSourceKeys
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) fun keys => labelsFrom keys u
  rw [labelsFun]
  erw [sourceLaw]
  rw [← sum_uniform_ite (fun keys => labelsFrom keys u) ℓ]
  rw [coinLaw_eq, tsum_fintype, tsum_fintype]
  refine (Finset.sum_congr rfl fun c _ => ?_).trans
    ((split_sum (X := crtEntry.Coins) coinKeys withKeys coinKeys_withKeys withKeys_coinKeys withKeys_withKeys f hf
      g).trans (mul_comm _ _))
  rw [tapeLabels_eq]
  simp only [f, g]
  split_ifs <;> simp_all
end

end Kriterion.CRT.Privacy.Laws
