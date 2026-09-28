/-
**No chunk joins, privacy groundwork (4/4): the laws.**

Imports `Hot.lean` (and through it `Key.lean`, `Algebra.lean`, `Sites.lean`, `Hybrids.lean`); nothing of
the H8 chain, so everything here builds while the chain is being ported.

Randomness per input `u`: the coins' zero labels `Z` (uniform), the hot chunk-tree answers `y` at `u`
(uniform, `withHotTree t u y`), the deltas `Δ`, and the rest of the table `t` (the **cold table**: the
level's other slots, which the evaluator reads and the view shows). The real selected labels at `u` are
`sourceLabels Z' Δ u` with `Z' = actualZeros (withHotTree t u y) Z` (`Hot.labelsFor_withHotTree`).

1. `actualZeros_law`: for every cold table `t` and input `u`, `Z'` is uniform (`(Z, y) ↦ Z'` is the first
   component of the bijection `keysEquiv`). It does not read `Δ`.
2. **`actualLabels_law`** (the joint law of the selected labels given the cold table): for every `t`, `u`
   and `Δ`, the real selected labels have the law `labelLaw u` of the source's labels (`sourceLabels_law`:
   the source-form labels of uniform zero labels have the same law for every `Δ`), and
   `source_labels_law`: that is the law of `Entry.labels source u` under a uniform `Entry.Source`.
3. **`labels_payload_joint`**: with a payload `P w` pushing uniform `w` to `π` (the reduced conversion
   payload, P3's bijection for fixed coins and cold table), the pair (selected labels, payload) has the
   product law `labelLaw u ⊗ π`, for every `Δ` and cold table.
4. **`residual_product` / `labels_residual`** (full-`Δ` residual independence): with any context law `μ`
   (the cold table and everything else the fine view shows) the joint law of `(Δ, (labels, payload, c))` is
   `uniform Δ ⊗ view law`: `Δ` — all 256 bits of both coordinates' offsets — is uniform and independent of
   the fine view. `residual_guess`: any guess of any projection of `Δ` with uniform image (the full offset,
   one coordinate's, or its `clip`) from the view succeeds with probability `1 / |image|` exactly (`2^-128`,
   resp. `2^-104`).
-/

import Proof.Privacy.CRT.NoJoins.Hot
import Proof.Privacy.CRT.Core.LabelUniform

namespace Kriterion.CRT.Privacy.NoJoins

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Entry
open Kriterion.CRT.Privacy
open scoped ENNReal

noncomputable section

/-! ### 1. Uniform laws under equivalences, projections and splits -/

theorem sum_uniform_one {Z : Type} [Fintype Z] [Nonempty Z] : ∑ z, PMF.uniformOfFintype Z z = 1 := by
  have total := PMF.tsum_coe (PMF.uniformOfFintype Z)
  rwa [tsum_fintype] at total

/-- The pushforward of a uniform law by an equivalence is uniform. -/
theorem map_uniform_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · rw [if_pos (e.apply_symm_apply b).symm, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
      Fintype.card_congr e]
  · intro a ne
    rw [if_neg]
    intro same
    exact ne (by rw [same, e.symm_apply_apply])

/-- The mass of a pair in a bind of maps along an injective pairing. -/
theorem bind_map_apply_inj {α β γ : Type} (ν : PMF β) (μ : PMF α) (f : β → α → γ)
    (inj : ∀ b a b' a', f b a = f b' a' → b = b' ∧ a = a') (b : β) (a : α) :
    (ν.bind fun b => μ.map (f b)) (f b a) = ν b * μ a := by
  rw [PMF.bind_apply, tsum_eq_single b]
  · rw [PMF.map_apply, tsum_eq_single a]
    · rw [if_pos rfl]
    · intro a' ne
      rw [if_neg]
      intro h
      exact ne (inj _ _ _ _ h).2.symm
  · intro b' ne
    refine mul_eq_zero_of_right _ ?_
    rw [PMF.map_apply]
    exact ENNReal.tsum_eq_zero.mpr fun a' => if_neg fun h => ne (inj _ _ _ _ h).1.symm

/-- The mass of `(d, v)` in the product law. -/
theorem product_apply {D V : Type} (μ : PMF D) (view : PMF V) (d : D) (v : V) :
    (μ.bind fun d => view.map fun v => (d, v)) (d, v) = μ d * view v :=
  bind_map_apply_inj μ view (fun d v => (d, v)) (fun _ _ _ _ h => Prod.mk.inj h) d v

/-- A uniform law on a product is the product of the uniform laws. -/
theorem uniform_prod_eq {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    PMF.uniformOfFintype (A × B) = (PMF.uniformOfFintype B).bind fun b =>
      (PMF.uniformOfFintype A).map fun a => (a, b) := by
  ext ⟨a, b⟩
  rw [bind_map_apply_inj (PMF.uniformOfFintype B) (PMF.uniformOfFintype A) (fun b a => (a, b))
    (fun _ _ _ _ h => ⟨(Prod.mk.inj h).2, (Prod.mk.inj h).1⟩) b a]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]

/-- The first marginal of a uniform law on a product is uniform. -/
theorem map_uniform_fst {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  rw [uniform_prod_eq, PMF.map_bind]
  have inner : ∀ b : β, ((PMF.uniformOfFintype α).map fun a => (a, b)).map Prod.fst = PMF.uniformOfFintype α := by
    intro b
    rw [PMF.map_comp]
    exact PMF.map_id _
  simp only [inner, PMF.bind_const]

/-- A uniform law splits along a coordinate with a setter (the chain's `LabelsSplitProof.split_sum`,
restated here so that this module does not import the chain). -/
theorem map_comp_get {X Z Y : Type} [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (get : X → Z) (set : X → Z → X) (get_set : ∀ x z, get (set x z) = z) (set_get : ∀ x, set x (get x) = x)
    (set_set : ∀ x z z', set (set x z) z' = set x z') (L : Z → Y) :
    (PMF.uniformOfFintype X).map (fun x => L (get x)) = (PMF.uniformOfFintype Z).map L := by
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
  have factor : (fun x => L (get x)) = (L ∘ Prod.snd) ∘ e := funext fun x => rfl
  rw [factor, ← PMF.map_comp, map_uniform_equiv e, ← PMF.map_comp]
  congr 1
  -- the second marginal of a uniform product is uniform
  have sndEq : (Prod.snd : {x : X // get x = get x₀} × Z → Z) =
      Prod.fst ∘ (Equiv.prodComm {x : X // get x = get x₀} Z) := funext fun _ => rfl
  rw [sndEq, ← PMF.map_comp, map_uniform_equiv, map_uniform_fst]

/-- If the law of `f a b` under uniform `a` is `lam` for every `b`, the law of `f` under a uniform pair is `lam`. -/
theorem map_uniform_prod_const {A B Y : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (f : A → B → Y)
    (lam : PMF Y) (h : ∀ b, (PMF.uniformOfFintype A).map (fun a => f a b) = lam) :
    (PMF.uniformOfFintype (A × B)).map (fun k => f k.1 k.2) = lam := by
  rw [uniform_prod_eq, PMF.map_bind]
  have inner : ∀ b, ((PMF.uniformOfFintype A).map fun a => (a, b)).map (fun k => f k.1 k.2) = lam := by
    intro b
    rw [PMF.map_comp]
    exact h b
  simp only [inner, PMF.bind_const]

/-! ### 2. The laws of the actual zero labels and of the selected labels, given the cold table -/

/-- **The actual zero labels are uniform given the cold table**: for every cold table `t` and input `u`, the
pushforward of uniform (coins' zero labels, hot answers) is uniform. It reads no offset. -/
theorem actualZeros_law (t : TagTable) (u : AffineInput) :
    (PMF.uniformOfFintype (KeyZeros × HotAnswers)).map
        (fun p => actualZeros (tableAnswers (withHotTree t u p.2)) p.1) =
      PMF.uniformOfFintype KeyZeros := by
  have factor : (fun p : KeyZeros × HotAnswers => actualZeros (tableAnswers (withHotTree t u p.2)) p.1) =
      Prod.fst ∘ keysEquiv firstFlag (coldSum t u) := funext fun p => actualZeros_withHotTree t u p.1 p.2
  rw [factor, ← PMF.map_comp, map_uniform_equiv, map_uniform_fst]

/-- The input bit of coordinate `κ`, position `j`. -/
def bitOf (u : AffineInput) (κ : Fin 2) (j : Bits) : Bool :=
  if κ = 0 then u.x.val.testBit j.val else u.y.val.testBit j.val

/-- The offsets at the set bits of `u`. -/
def deltaMask (Δ : Fin 2 → Block) (u : AffineInput) : KeyZeros :=
  fun κ j => if bitOf u κ j then Δ κ else 0

/-- XOR by a fixed family, an involution. -/
def xorEquiv (M : KeyZeros) : KeyZeros ≃ KeyZeros where
  toFun Z κ j := Z κ j ^^^ M κ j
  invFun Z κ j := Z κ j ^^^ M κ j
  left_inv Z := by
    funext κ j
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv Z := by
    funext κ j
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The source-form labels with offsets `Δ` are the source-form labels with zero offsets of the shifted zero
labels. -/
theorem sourceLabels_shift (Z : KeyZeros) (Δ : Fin 2 → Block) (u : AffineInput) :
    sourceLabels Z Δ u = sourceLabels (xorEquiv (deltaMask Δ u) Z) 0 u := by
  apply Vector.ext
  intro i hi
  simp only [sourceLabels, Vector.getElem_ofFn, xorEquiv, Equiv.coe_fn_mk, deltaMask, bitOf]
  split
  · simp only [Fin.isValue, ↓reduceIte, Pi.zero_apply]
    split <;> simp
  · simp only [Fin.isValue, one_ne_zero, ↓reduceIte, Pi.zero_apply]
    split <;> simp

/-- The label law at `u`: the source-form labels of uniform zero labels (with any offsets, `sourceLabels_law`). -/
def labelLaw (u : AffineInput) : PMF GarbledCircuit.LamportSignature :=
  (PMF.uniformOfFintype KeyZeros).map fun Z => sourceLabels Z 0 u

/-- **The source-form labels of uniform zero labels have the same law for every offset.** -/
theorem sourceLabels_law (Δ : Fin 2 → Block) (u : AffineInput) :
    (PMF.uniformOfFintype KeyZeros).map (fun Z => sourceLabels Z Δ u) = labelLaw u := by
  have factor : (fun Z => sourceLabels Z Δ u) = (fun Z => sourceLabels Z 0 u) ∘ xorEquiv (deltaMask Δ u) :=
    funext fun Z => sourceLabels_shift Z Δ u
  rw [factor, ← PMF.map_comp, map_uniform_equiv]
  rfl

/-- **The joint law of the real selected labels given the cold table**: for every cold table `t`, input `u` and
offsets `Δ`, the real selected labels (on uniform coins' zero labels and uniform hot answers) have the
source's label law. -/
theorem actualLabels_law (t : TagTable) (u : AffineInput) (Δ : Fin 2 → Block) :
    (PMF.uniformOfFintype (KeyZeros × HotAnswers)).map
        (fun p => sourceLabels (actualZeros (tableAnswers (withHotTree t u p.2)) p.1) Δ u) = labelLaw u := by
  have factor : (fun p : KeyZeros × HotAnswers =>
      sourceLabels (actualZeros (tableAnswers (withHotTree t u p.2)) p.1) Δ u) =
      (fun Z => sourceLabels Z Δ u) ∘ fun p => actualZeros (tableAnswers (withHotTree t u p.2)) p.1 := rfl
  rw [factor, ← PMF.map_comp, actualZeros_law, sourceLabels_law]

/-- The same, for the real garbling's selected labels (`EntryCorrect.labelsFor` on the tag table): coins with
their zero labels set. -/
theorem labelsFor_law (t : TagTable) (u : AffineInput) (coins : Coins) :
    (PMF.uniformOfFintype (KeyZeros × HotAnswers)).map
        (fun p => EntryCorrect.labelsFor (tableHash (withHotTree t u p.2))
          { coins with inputZero := fun q => p.1 (if q = .x then 0 else 1) } u) = labelLaw u := by
  have same : (fun p : KeyZeros × HotAnswers => EntryCorrect.labelsFor (tableHash (withHotTree t u p.2))
      { coins with inputZero := fun q => p.1 (if q = .x then 0 else 1) } u) =
      fun p => sourceLabels (actualZeros (tableAnswers (withHotTree t u p.2)) p.1) (deltaOf coins) u := by
    funext p
    rw [labelsFor_tagOnly (tagOnly_tableHash _)]
    have zeros : zeroOf { coins with inputZero := fun q => p.1 (if q = .x then 0 else 1) } = p.1 := by
      funext κ j
      unfold zeroOf
      by_cases hκ : κ = 0
      · subst hκ
        rfl
      · have one : κ = 1 := by omega
        subst one
        rfl
    rw [zeros]
    rfl
  rw [same, actualLabels_law]

/-! ### 3. The source's labels -/

/-- The zero labels of a source, with a setter. -/
def setZeros (source : Source) (Z : KeyZeros) : Source := { source with zeros := Z }

/-- **The law of the source's labels is `labelLaw`**: under a uniform source the labels of `u` are distributed
as the real selected labels (item 2), for every cold table and every offset. -/
theorem source_labels_law [Fintype Source] (u : AffineInput) :
    (PMF.uniformOfFintype Source).map (fun source => Entry.labels source u) = labelLaw u := by
  -- first split off the deltas: the labels read the zeros and the deltas
  have split := map_comp_get (X := Source) (Z := KeyZeros × (Fin 2 → Block))
    (fun source => (source.zeros, source.deltas)) (fun source k => { source with zeros := k.1, deltas := k.2 })
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun k => sourceLabels k.1 k.2 u)
  have labelsEq : (fun source => Entry.labels source u) =
      fun source => (fun k : KeyZeros × (Fin 2 → Block) => sourceLabels k.1 k.2 u) (source.zeros, source.deltas) :=
    funext fun source => labels_source source u
  rw [labelsEq, split]
  exact map_uniform_prod_const (fun Z Δ => sourceLabels Z Δ u) (labelLaw u) fun Δ => sourceLabels_law Δ u

/-! ### 4. The joint law with the payload, and full-`Δ` residual independence -/

/-- **The joint law of (selected labels, reduced payload) given the cold table**: if the payload `P` pushes
uniform payload material to `π` (P3's bijection, for the fixed offsets and cold table), then the real
selected labels and the payload are independent, with laws `labelLaw u` and `π`. -/
theorem labels_payload_joint {W Q : Type} [Fintype W] [Nonempty W] (t : TagTable) (u : AffineInput)
    (Δ : Fin 2 → Block) (P : W → Q) (π : PMF Q) (hP : (PMF.uniformOfFintype W).map P = π) :
    ((PMF.uniformOfFintype (KeyZeros × HotAnswers)).bind fun k => (PMF.uniformOfFintype W).map fun w =>
        (sourceLabels (actualZeros (tableAnswers (withHotTree t u k.2)) k.1) Δ u, P w)) =
      (labelLaw u).bind fun ℓ => π.map fun q => (ℓ, q) := by
  rw [← actualLabels_law t u Δ, PMF.bind_map, ← hP]
  congr 1
  funext k
  simp only [Function.comp_apply, PMF.map_comp]
  rfl

/-- **Full residual independence** (abstract). Randomness: offsets `d : D` uniform, key material `k : K`
uniform, payload material `w : W` uniform, and a context `c : C` of any law `μ`, independent; the view is
`(L d c k, P d c w, c)`. If for every `d` and `c` the labels push uniform `K` to `λ` and the payload pushes
uniform `W` to `π`, then the joint law of `(d, view)` is uniform `d` times the view law
`μ ⊗ λ ⊗ π`: the offsets are uniform and independent of the view. -/
theorem residual_product {D K W C Lb Q : Type} [Fintype D] [Nonempty D] [Fintype K] [Nonempty K] [Fintype W]
    [Nonempty W] (μ : PMF C) (L : D → C → K → Lb) (P : D → C → W → Q) (lam : PMF Lb) (π : PMF Q)
    (hL : ∀ d c, (PMF.uniformOfFintype K).map (L d c) = lam)
    (hP : ∀ d c, (PMF.uniformOfFintype W).map (P d c) = π) :
    ((PMF.uniformOfFintype D).bind fun d => μ.bind fun c => (PMF.uniformOfFintype K).bind fun k =>
        (PMF.uniformOfFintype W).map fun w => (d, (L d c k, P d c w, c))) =
      (PMF.uniformOfFintype D).bind fun d =>
        (μ.bind fun c => lam.bind fun l => π.map fun q => (l, q, c)).map fun v => (d, v) := by
  congr 1
  funext d
  rw [PMF.map_bind]
  congr 1
  funext c
  rw [← hL d c, PMF.bind_map, PMF.map_bind]
  congr 1
  funext k
  rw [← hP d c]
  simp only [Function.comp_apply, PMF.map_comp]
  rfl

/-- **A guess of the offsets from the view** succeeds with probability `1 / |E|` exactly, for any projection
`proj` of the offsets with uniform image (the full offsets, one coordinate's, or its `clip`), under the
product law of `residual_product`. -/
theorem residual_guess {D E V : Type} [Fintype D] [Nonempty D] [Fintype E] [Nonempty E] [DecidableEq E]
    (view : PMF V) (proj : D → E) (hproj : (PMF.uniformOfFintype D).map proj = PMF.uniformOfFintype E)
    (guess : V → E) :
    ∑' x : D × V, ((PMF.uniformOfFintype D).bind fun d => view.map fun v => (d, v)) x *
        (if proj x.1 = guess x.2 then 1 else 0) = (Fintype.card E : ℝ≥0∞)⁻¹ := by
  classical
  have point : ∀ x : D × V, ((PMF.uniformOfFintype D).bind fun d => view.map fun v => (d, v)) x =
      PMF.uniformOfFintype D x.1 * view x.2 := by
    rintro ⟨d, v⟩
    exact product_apply _ _ d v
  simp only [point]
  rw [ENNReal.tsum_prod (f := fun d v => PMF.uniformOfFintype D d * view v * (if proj d = guess v then 1 else 0)),
    ENNReal.tsum_comm]
  have inner : ∀ v, ∑' d, PMF.uniformOfFintype D d * view v * (if proj d = guess v then 1 else 0) =
      view v * (Fintype.card E : ℝ≥0∞)⁻¹ := by
    intro v
    have mass := congrArg (fun q : PMF E => q (guess v)) hproj
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply] at mass
    rw [← mass, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun d => ?_
    by_cases same : proj d = guess v
    · rw [if_pos same, if_pos same.symm, mul_one, mul_comm, PMF.uniformOfFintype_apply]
    · rw [if_neg same, if_neg fun h => same h.symm, mul_zero, mul_zero]
  simp only [inner]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]


/-- **Full-`Δ` residual independence for the real selected labels**: for any context law `μ` whose component
`tableOf c` is the cold table (everything else the fine view shows may be in `c`), and any payload whose law
`π` does not depend on the offsets or the context (P3's bijection), the offsets of both coordinates are
uniform and independent of (real selected labels, payload, context), whose law is `labelLaw u ⊗ π ⊗ μ`. -/
theorem labels_residual {C W Q : Type} [Fintype W] [Nonempty W] (u : AffineInput) (μ : PMF C)
    (tableOf : C → TagTable) (P : (Fin 2 → Block) → C → W → Q) (π : PMF Q)
    (hP : ∀ Δ c, (PMF.uniformOfFintype W).map (P Δ c) = π) :
    ((PMF.uniformOfFintype (Fin 2 → Block)).bind fun Δ => μ.bind fun c =>
        (PMF.uniformOfFintype (KeyZeros × HotAnswers)).bind fun k => (PMF.uniformOfFintype W).map fun w =>
          (Δ, (sourceLabels (actualZeros (tableAnswers (withHotTree (tableOf c) u k.2)) k.1) Δ u, P Δ c w, c))) =
      (PMF.uniformOfFintype (Fin 2 → Block)).bind fun Δ =>
        (μ.bind fun c => (labelLaw u).bind fun l => π.map fun q => (l, q, c)).map fun v => (Δ, v) := by
  apply residual_product
  · intro Δ c
    exact actualLabels_law (tableOf c) u Δ
  · exact hP

/-! ### 5. The projections of the offsets -/

/-- A raw block is its low part and its high part (`setLow x 0`, a block with zero low part). -/
def lowHighEquiv : Block ≃ Label × {x : Block // clip x = 0} where
  toFun x := (clip x, ⟨setLow x 0, clip_setLow x 0⟩)
  invFun p := setLow p.2.1 p.1
  left_inv x := by
    show setLow (setLow x 0) (clip x) = x
    rw [setLow_setLow, setLow_clip]
  right_inv p := by
    obtain ⟨l, h, low⟩ := p
    refine Prod.ext (clip_setLow h l) (Subtype.ext ?_)
    show setLow (setLow h l) 0 = h
    rw [setLow_setLow, ← low, setLow_clip]

instance highNonempty : Nonempty {x : Block // clip x = 0} := ⟨⟨0, Narrow.clip_zero⟩⟩

/-- The low 104 bits of a uniform raw block are uniform. -/
theorem uniform_clip_block : (PMF.uniformOfFintype Block).map clip = PMF.uniformOfFintype Label := by
  classical
  have factor : (clip : Block → Label) = Prod.fst ∘ lowHighEquiv := funext fun _ => rfl
  rw [factor, ← PMF.map_comp, map_uniform_equiv, map_uniform_fst]

/-- One coordinate's offset of uniform offsets is uniform. -/
theorem uniform_eval (κ : Fin 2) :
    (PMF.uniformOfFintype (Fin 2 → Block)).map (fun Δ => Δ κ) = PMF.uniformOfFintype Block := by
  classical
  have split := map_comp_get (X := Fin 2 → Block) (Z := Block) (fun Δ => Δ κ) (fun Δ b => Function.update Δ κ b)
    (fun _ _ => Function.update_self _ _ _) (fun _ => Function.update_eq_self _ _)
    (fun _ _ _ => Function.update_idem _ _ _) id
  rw [PMF.map_id] at split
  exact split

/-- **Guessing one coordinate's projected offset from the fine view** (`clip Δ_κ`, the conversion's
residual) succeeds with probability exactly `2^-104`. -/
theorem clip_delta_guess {V : Type} (view : PMF V) (κ : Fin 2) (guess : V → Label) :
    ∑' x : (Fin 2 → Block) × V, ((PMF.uniformOfFintype (Fin 2 → Block)).bind fun d => view.map fun v => (d, v)) x *
        (if clip (x.1 κ) = guess x.2 then 1 else 0) = ((2 : ℝ≥0∞) ^ 104)⁻¹ := by
  have proj : (PMF.uniformOfFintype (Fin 2 → Block)).map (fun Δ => clip (Δ κ)) = PMF.uniformOfFintype Label := by
    have factor : (fun Δ : Fin 2 → Block => clip (Δ κ)) = clip ∘ fun Δ => Δ κ := rfl
    rw [factor, ← PMF.map_comp, uniform_eval]
    exact uniform_clip_block
  have main := residual_guess (D := Fin 2 → Block) (E := Label) view (fun Δ => clip (Δ κ)) proj guess
  rw [main, Narrow.card_label]
  norm_num

/-- **Guessing one coordinate's full offset from the fine view** (the digest's residual) succeeds with
probability exactly `2^-128`. -/
theorem delta_guess {V : Type} (view : PMF V) (κ : Fin 2) (guess : V → Block) :
    ∑' x : (Fin 2 → Block) × V, ((PMF.uniformOfFintype (Fin 2 → Block)).bind fun d => view.map fun v => (d, v)) x *
        (if x.1 κ = guess x.2 then 1 else 0) = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  have main := residual_guess (D := Fin 2 → Block) (E := Block) view (fun Δ => Δ κ) (uniform_eval κ) guess
  have card : Fintype.card Block = 2 ^ 128 := by
    rw [Fintype.card_congr (BitVec.equivFin : Block ≃+* Fin (2 ^ 128)).toEquiv, Fintype.card_fin]
  rw [main, card]
  norm_num

/-! ### 6. Resampling a coordinate of a uniform law -/

/-- The product of two uniform laws, first component first. -/
theorem uniform_prod_eq' {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    PMF.uniformOfFintype (A × B) = (PMF.uniformOfFintype A).bind fun a =>
      (PMF.uniformOfFintype B).map fun b => (a, b) := by
  ext ⟨a, b⟩
  rw [bind_map_apply_inj (PMF.uniformOfFintype A) (PMF.uniformOfFintype B) (fun a b => (a, b))
    (fun _ _ _ _ h => Prod.mk.inj h) a b]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

theorem map_apply_of_injective {α β : Type} (p : PMF α) {f : α → β} (inj : Function.Injective f) (a : α) :
    (p.map f) (f a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · rw [if_pos rfl]
  · intro a' ne
    rw [if_neg fun same => ne (inj same).symm]

/-- A pushforward along an injective map determines the law. -/
theorem map_eq_of_injective {α β : Type} {p q : PMF α} {f : α → β} (inj : Function.Injective f)
    (h : p.map f = q.map f) : p = q := by
  ext a
  have e : (p.map f) (f a) = (q.map f) (f a) := by rw [h]
  rwa [map_apply_of_injective p inj a, map_apply_of_injective q inj a] at e

/-- **Resampling a coordinate of a uniform law**: for a coordinate `get` with a setter `set` (the lens laws),
setting the coordinate of a uniform point to an independent uniform value leaves the law uniform. -/
theorem uniform_resample {X Z : Type} [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (get : X → Z) (set : X → Z → X) (get_set : ∀ x z, get (set x z) = z) (set_get : ∀ x, set x (get x) = x)
    (set_set : ∀ x z z', set (set x z) z' = set x z') :
    ((PMF.uniformOfFintype X).bind fun x => (PMF.uniformOfFintype Z).map (set x)) = PMF.uniformOfFintype X := by
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
  have eset : ∀ x z, e (set x z) = ((e x).1, z) := fun x z =>
    Prod.ext (Subtype.ext (show set (set x z) (get x₀) = set x (get x₀) by rw [set_set])) (get_set x z)
  apply map_eq_of_injective e.injective
  rw [map_uniform_equiv e, PMF.map_bind]
  have inner : ∀ x, ((PMF.uniformOfFintype Z).map (set x)).map e =
      (PMF.uniformOfFintype Z).map fun z => ((e x).1, z) := by
    intro x
    rw [PMF.map_comp]
    exact congrArg (fun f => PMF.map f _) (funext fun z => eset x z)
  simp only [inner]
  have fstLaw : (PMF.uniformOfFintype X).map (fun x => (e x).1) = PMF.uniformOfFintype {x : X // get x = get x₀} := by
    have factor : (fun x => (e x).1) = Prod.fst ∘ e := rfl
    rw [factor, ← PMF.map_comp, map_uniform_equiv, map_uniform_fst]
  rw [show ((PMF.uniformOfFintype X).bind fun x => (PMF.uniformOfFintype Z).map fun z => ((e x).1, z)) =
      ((PMF.uniformOfFintype X).map fun x => (e x).1).bind fun f => (PMF.uniformOfFintype Z).map fun z => (f, z) from
    (PMF.bind_map (PMF.uniformOfFintype X) (fun x => (e x).1)
      (fun f => (PMF.uniformOfFintype Z).map fun z => (f, z))).symm, fstLaw, ← uniform_prod_eq']

/-! ### 7. Sums against binds and maps; the label law on a pair indexing -/

theorem tsum_bind_mul {X Y : Type} (μ : PMF X) (G : X → PMF Y) (W : Y → ℝ≥0∞) :
    ∑' y, (μ.bind G) y * W y = ∑' x, μ x * ∑' y, G x y * W y := by
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => tsum_congr fun y => ?_
  ring

theorem tsum_map_mul {X Y : Type} (ν : PMF X) (R : X → Y) (W : Y → ℝ≥0∞) :
    ∑' y, (ν.map R) y * W y = ∑' x, ν x * W (R x) := by
  classical
  simp only [PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (R x)]
  · rw [if_pos rfl]
  · intro y ne
    rw [if_neg ne, zero_mul]

/-- **The real selected labels on uniform (zero labels, hot answers indexed by pairs)** have the source's label
law, for every first-bit flags, cold XORs and offsets. -/
theorem keysLabels_law (first : Fin 2 → Bits → Bool) (cold : Fin 2 → Bits → Label) (Δ : Fin 2 → Block)
    (u : AffineInput) :
    (PMF.uniformOfFintype (KeyZeros × (Fin 2 × Bits → Answer))).map
        (fun p => sourceLabels (keysEquiv first cold (p.1, fun κ j => p.2 (κ, j))).1 Δ u) = labelLaw u := by
  let e : KeyZeros × (Fin 2 × Bits → Answer) ≃ KeyZeros × HotAnswers :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.curry (Fin 2) Bits Answer)
  have factor : (fun p : KeyZeros × (Fin 2 × Bits → Answer) =>
      sourceLabels (keysEquiv first cold (p.1, fun κ j => p.2 (κ, j))).1 Δ u) =
      (fun Z => sourceLabels Z Δ u) ∘ Prod.fst ∘ (e.trans (keysEquiv first cold)) := rfl
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, map_uniform_equiv, map_uniform_fst, sourceLabels_law]

theorem uniform_pair_apply {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (a : A) (b : B) :
    PMF.uniformOfFintype (A × B) (a, b) = PMF.uniformOfFintype A a * PMF.uniformOfFintype B b := by
  rw [uniform_prod_eq']
  exact product_apply _ _ a b

theorem tsum_uniform_pair {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (W : A → B → ℝ≥0∞) :
    ∑' p : A × B, PMF.uniformOfFintype (A × B) p * W p.1 p.2 =
      ∑' a, PMF.uniformOfFintype A a * ∑' b, PMF.uniformOfFintype B b * W a b := by
  rw [ENNReal.tsum_prod (f := fun a b => PMF.uniformOfFintype (A × B) (a, b) * W a b)]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [uniform_pair_apply, mul_assoc]

end

end Kriterion.CRT.Privacy.NoJoins
