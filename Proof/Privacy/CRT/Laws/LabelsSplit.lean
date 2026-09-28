/-
**`LabelsSplit`** (the named input of `Laws/Rest.lean`'s `crtRestSplit_of`), no chunk joins.

The garbler's returned key absorbs the chunk joins: on a tag table the selected labels of `u` are the source-form
labels of the *actual* zero labels (the coins' zero labels with the chunk-tree level sums installed in their low
parts, `NoJoins.Key`) and the coins' offsets (`tapeLabels_eq`). The actual zero labels are the first component of a
bijection of (coins' zero labels, hot chunk-tree answers) that reads the cold table only (`NoJoins.actualZeros_fillAt`).

The swapped tape resamples both: the coins are uniform with a zero-label setter (`NoJoins.uniform_resample`), and the
hot chunk-tree positions are non-site positions, refilled uniformly (`HiddenGuess.swappedTableLaw_fill`). A weight
that reads the coins up to `SameOffLabels` and the table off the hot chunk-tree tags does not see the resampling, and
for every offset and cold table the labels of the resampled tape have the source's law (`NoJoins.keysLabels_law`,
`NoJoins.source_labels_law`): **`labelsSplit`**.
-/

import Proof.Privacy.CRT.Laws.Rest
import Proof.Correctness.CRT.EntryCorrect
import Proof.Privacy.CRT.NoJoins.Fill

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

/-! ### 3. The labels read the coins' label keys and the table's chunk-tree answers -/

theorem getElem_eq_getD (labels : LamportSignature) (i : ℕ) (hi : i < 508) :
    labels[i] = labels.toArray.getD i 0 := by
  simp [Array.getD, hi]

/-- The zero labels of coins of the chain's coin type (`Entry.zeroOf`). -/
def zeroOfC (coins : crtEntry.Coins) : NoJoins.KeyZeros := Entry.zeroOf coins

/-- The offsets of coins of the chain's coin type (`Entry.deltaOf`). -/
def deltaOfC (coins : crtEntry.Coins) : Fin 2 → Block := Entry.deltaOf coins

/-- **The labels of `u` of a tape**: the source-form labels of the actual zero labels (the coins' zero labels with the
table's chunk-tree level sums installed) and the coins' offsets. -/
theorem tapeLabels_eq [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (coins : crtEntry.Coins) (table : TagTable) :
    tapeLabels parameter scalar u (coins, table) =
      NoJoins.sourceLabels (NoJoins.actualZeros (NoJoins.tableAnswers table) (zeroOfC coins)) (deltaOfC coins) u := by
  unfold tapeLabels
  rw [ConvSplit.realGarbled_eq]
  exact NoJoins.encode_table scalar coins u table

/-- The labels of `u` of a tape whose hot chunk-tree positions are filled. -/
theorem tapeLabels_fillAt [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (coins : crtEntry.Coins) (f : Fin 2 × NoJoins.Bits → Block × Block) (table : TagTable) :
    tapeLabels parameter scalar u (coins, HiddenGuess.fillAt (NoJoins.hotPos u) f table) =
      NoJoins.sourceLabels (NoJoins.keysEquiv NoJoins.firstFlag (NoJoins.coldSum table u)
        (zeroOfC coins, fun κ j => f (κ, j))).1 (deltaOfC coins) u := by
  unfold tapeLabels
  rw [ConvSplit.realGarbled_eq]
  exact NoJoins.encode_fillAt scalar coins u f table

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

theorem crtEntry_exceptional : crtEntry.exceptional = Entry.exceptional := rfl

/-- The coins with other zero labels. -/
def setZeros (coins : crtEntry.Coins) (Z : NoJoins.KeyZeros) : crtEntry.Coins :=
  withKeys coins (Z, (coinKeys coins).2)

theorem zeroOfC_setZeros (coins : crtEntry.Coins) (Z : NoJoins.KeyZeros) : zeroOfC (setZeros coins Z) = Z := by
  funext κ j
  unfold zeroOfC Entry.zeroOf setZeros withKeys
  by_cases hκ : κ = 0
  · subst hκ
    rfl
  · have one : κ = 1 := by omega
    subst one
    rfl

theorem deltaOfC_setZeros (coins : crtEntry.Coins) (Z : NoJoins.KeyZeros) :
    deltaOfC (setZeros coins Z) = deltaOfC coins := by
  funext κ
  unfold deltaOfC Entry.deltaOf setZeros withKeys coinKeys
  by_cases hκ : κ = 0
  · subst hκ
    rfl
  · have one : κ = 1 := by omega
    subst one
    rfl

theorem zeroOfC_eq_coinKeys (coins : crtEntry.Coins) : zeroOfC coins = (coinKeys coins).1 := by
  funext κ j
  unfold zeroOfC Entry.zeroOf coinKeys
  by_cases hκ : κ = 0
  · subst hκ
    rfl
  · have one : κ = 1 := by omega
    subst one
    rfl

theorem setZeros_zeroOfC (coins : crtEntry.Coins) : setZeros coins (zeroOfC coins) = coins :=
  (congrArg (fun x => withKeys coins (x, (coinKeys coins).2)) (zeroOfC_eq_coinKeys coins)).trans
    (withKeys_coinKeys coins)

theorem setZeros_setZeros (coins : crtEntry.Coins) (Z Z' : NoJoins.KeyZeros) :
    setZeros (setZeros coins Z) Z' = setZeros coins Z' := by
  have h := congrArg Prod.snd (coinKeys_withKeys coins (Z, (coinKeys coins).2))
  exact (withKeys_withKeys coins _ _).trans (congrArg (fun d => withKeys coins (Z', d)) h)

theorem doubling_setZeros (scalar : NonZeroScalar) (u : AffineInput) (coins : crtEntry.Coins)
    (Z : NoJoins.KeyZeros) (t : TagTable) :
    Doubling crtEntry scalar (setZeros coins Z, t) u ↔ Doubling crtEntry scalar (coins, t) u := by
  show (∃ o, crtEntry.exceptional scalar (setZeros coins Z) o = some u) ↔
    ∃ o, crtEntry.exceptional scalar coins o = some u
  rw [crtEntry_exceptional]
  exact exists_congr fun o => by
    rw [show Entry.exceptional scalar (setZeros coins Z) o = Entry.exceptional scalar coins o from
      exceptional_withKeys scalar coins _ o]

/-- Doubling reads the coins only. -/
theorem doubling_coins (scalar : NonZeroScalar) (u : AffineInput) (coins : crtEntry.Coins) (t t' : TagTable) :
    Doubling crtEntry scalar (coins, t) u ↔ Doubling crtEntry scalar (coins, t') u := Iff.rfl

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
/-- **`LabelsSplit`**: the labels of `u` read the coins' label keys and the table's chunk-tree answers; under the
swapped tape, off doubling, they are distributed as the source's labels and are independent of every weight on the
tape that reads the coins up to `SameOffLabels` and the table off the hot chunk-tree tags. -/
theorem labelsSplit : LabelsSplit := by
  intro _ _ parameter scalar u H hH ℓ
  let _ : Fintype (view).Source := (view).sourceFintype
  have _ : Nonempty (view).Source := (view).sourceNonempty
  let F : TableTape crtEntry → ℝ≥0∞ := fun tape =>
    if Doubling crtEntry scalar tape u ∨ tapeLabels parameter scalar u tape ≠ ℓ then 0 else H tape
  let K := NoJoins.KeyZeros × (Fin 2 × NoJoins.Bits → Block × Block)
  -- the table averages over the hot chunk-tree answers
  have fill := HiddenGuess.swappedTableLaw_fill crtLayout (NoJoins.hotPos u) (NoJoins.hotPos_injective u)
    (NoJoins.hotPos_away u)
  have tableAvg : ∀ W : TagTable → ℝ≥0∞, ∑' t, swappedTableLaw crtLayout t * W t =
      ∑' t, swappedTableLaw crtLayout t * ∑' f, PMF.uniformOfFintype (Fin 2 × NoJoins.Bits → Block × Block) f *
        W (HiddenGuess.fillAt (NoJoins.hotPos u) f t) := by
    intro W
    conv_lhs => rw [← fill]
    rw [NoJoins.tsum_bind_mul]
    exact tsum_congr fun t => congrArg _ (NoJoins.tsum_map_mul _ _ W)
  -- the coins average over the zero labels
  have coinAvg : ∀ V : crtEntry.Coins → ℝ≥0∞, ∑' c, coinLaw c * V c =
      ∑' c, coinLaw c * ∑' Z, PMF.uniformOfFintype NoJoins.KeyZeros Z * V (setZeros c Z) := by
    intro V
    rw [coinLaw_eq]
    conv_lhs => rw [← NoJoins.uniform_resample (X := crtEntry.Coins) zeroOfC setZeros zeroOfC_setZeros
      setZeros_zeroOfC setZeros_setZeros]
    rw [NoJoins.tsum_bind_mul]
    exact tsum_congr fun c => congrArg _ (NoJoins.tsum_map_mul _ _ V)
  -- the resampled tape: doubling and the weight are unchanged, the labels are the relabelled keys
  have hD : ∀ c Z t, Doubling crtEntry scalar (setZeros c Z, t) u ↔ Doubling crtEntry scalar (c, t) u := by
    intro c Z t
    exact doubling_setZeros scalar u c Z t
  have hHfill : ∀ c Z f t, H (setZeros c Z, HiddenGuess.fillAt (NoJoins.hotPos u) f t) = H (c, t) := by
    intro c Z f t
    refine hH _ _ (sameOffLabels_withKeys c _) fun tag notHot => ?_
    refine HiddenGuess.fillAt_apply_of_not_mem _ _ _ _ ?_
    rintro ⟨p, rfl⟩
    exact notHot ⟨NoJoins.hotPos_family u p, NoJoins.hotPos_hot u p⟩
  -- ★: for fixed coins and cold table, the average over (zero labels, hot answers)
  have star : ∀ c t, ∑' Z, PMF.uniformOfFintype NoJoins.KeyZeros Z *
      ∑' f, PMF.uniformOfFintype (Fin 2 × NoJoins.Bits → Block × Block) f *
        F (setZeros c Z, HiddenGuess.fillAt (NoJoins.hotPos u) f t) =
      (if Doubling crtEntry scalar (c, t) u then 0 else H (c, t)) * NoJoins.labelLaw u ℓ := by
    intro c t
    let L : K → LamportSignature := fun p => NoJoins.sourceLabels (NoJoins.keysEquiv NoJoins.firstFlag
      (NoJoins.coldSum t u) (p.1, fun κ j => p.2 (κ, j))).1 (deltaOfC c) u
    have point : ∀ Z f, F (setZeros c Z, HiddenGuess.fillAt (NoJoins.hotPos u) f t) =
        (if Doubling crtEntry scalar (c, t) u then 0 else H (c, t)) *
          @ite _ (L (Z, f) = ℓ) (Classical.propDecidable _) 1 0 := by
      intro Z f
      simp only [F]
      rw [tapeLabels_fillAt, zeroOfC_setZeros, deltaOfC_setZeros, hHfill]
      by_cases D : Doubling crtEntry scalar (c, t) u
      · rw [if_pos (Or.inl ((hD c Z _).mpr ((doubling_coins scalar u c t
          (HiddenGuess.fillAt (NoJoins.hotPos u) f t)).mp D))), if_pos D, zero_mul]
      · rw [if_neg D]
        by_cases hL : L (Z, f) = ℓ
        · rw [if_neg (show ¬(Doubling crtEntry scalar (setZeros c Z, HiddenGuess.fillAt (NoJoins.hotPos u) f t) u ∨
              NoJoins.sourceLabels (NoJoins.keysEquiv NoJoins.firstFlag (NoJoins.coldSum t u)
                (Z, fun κ j => f (κ, j))).1 (deltaOfC c) u ≠ ℓ) by
              rintro (h | h)
              · exact D ((doubling_coins scalar u c t (HiddenGuess.fillAt (NoJoins.hotPos u) f t)).mpr
                  ((hD c Z _).mp h))
              · exact h hL), if_pos hL, mul_one]
        · rw [if_pos (Or.inr hL), if_neg hL, mul_zero]
    have mass : ((PMF.uniformOfFintype K).map L) ℓ = ∑' Z, PMF.uniformOfFintype NoJoins.KeyZeros Z *
        ∑' f, PMF.uniformOfFintype (Fin 2 × NoJoins.Bits → Block × Block) f *
          @ite _ (L (Z, f) = ℓ) (Classical.propDecidable _) 1 0 := by
      rw [map_apply_sum]
      exact NoJoins.tsum_uniform_pair (fun Z f => @ite _ (L (Z, f) = ℓ) (Classical.propDecidable _) 1 0)
    have law : (PMF.uniformOfFintype K).map L = NoJoins.labelLaw u :=
      NoJoins.keysLabels_law NoJoins.firstFlag (NoJoins.coldSum t u) (deltaOfC c) u
    simp only [point]
    rw [← law, mass]
    simp_rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun Z => tsum_congr fun f => ?_
    ring
  -- the assembly
  have viewLaw : ((PMF.uniformOfFintype (view).Source).map fun source => (view).labels source u) =
      NoJoins.labelLaw u := @NoJoins.source_labels_law (view).sourceFintype u
  rw [viewLaw]
  calc ∑' tape, swappedTableTape crtEntry tape * F tape
      = ∑' c, coinLaw c * ∑' t, swappedTableLaw crtLayout t * F (c, t) := tsum_tape F
    _ = ∑' c, coinLaw c * ∑' t, swappedTableLaw crtLayout t *
          ∑' f, PMF.uniformOfFintype (Fin 2 × NoJoins.Bits → Block × Block) f *
            F (c, HiddenGuess.fillAt (NoJoins.hotPos u) f t) :=
        tsum_congr fun c => congrArg _ (tableAvg fun t => F (c, t))
    _ = ∑' c, coinLaw c * ∑' Z, PMF.uniformOfFintype NoJoins.KeyZeros Z * ∑' t, swappedTableLaw crtLayout t *
          ∑' f, PMF.uniformOfFintype (Fin 2 × NoJoins.Bits → Block × Block) f *
            F (setZeros c Z, HiddenGuess.fillAt (NoJoins.hotPos u) f t) :=
        coinAvg fun c => ∑' t, swappedTableLaw crtLayout t *
          ∑' f, PMF.uniformOfFintype (Fin 2 × NoJoins.Bits → Block × Block) f *
            F (c, HiddenGuess.fillAt (NoJoins.hotPos u) f t)
    _ = ∑' c, coinLaw c * ∑' t, swappedTableLaw crtLayout t * ∑' Z, PMF.uniformOfFintype NoJoins.KeyZeros Z *
          ∑' f, PMF.uniformOfFintype (Fin 2 × NoJoins.Bits → Block × Block) f *
            F (setZeros c Z, HiddenGuess.fillAt (NoJoins.hotPos u) f t) := by
        refine tsum_congr fun c => congrArg _ ?_
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun t => tsum_congr fun Z => tsum_congr fun f => ?_
        ring
    _ = ∑' c, coinLaw c * ∑' t, swappedTableLaw crtLayout t *
          ((if Doubling crtEntry scalar (c, t) u then 0 else H (c, t)) * NoJoins.labelLaw u ℓ) :=
        tsum_congr fun c => congrArg _ (tsum_congr fun t => congrArg _ (star c t))
    _ = NoJoins.labelLaw u ℓ *
          ∑' tape, swappedTableTape crtEntry tape * (if Doubling crtEntry scalar tape u then 0 else H tape) := by
        rw [tsum_tape, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun c => ?_
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        ring

end

end Kriterion.CRT.Privacy.Laws
