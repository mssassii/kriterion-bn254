/-
Parity-constrained extraction stages. The hidden cast stores only its upper bits;
its low plane is the label of the hot leaf. The public pin stores only its upper
bits, since the XOR of all leaf labels is the global offset.
-/

import Proof.Privacy.CRT.Core.ExtractStageSpec
import Construction.CRT.Parity

namespace Kriterion.CRT.Privacy.ExtractStage

variable {L w l : ℕ}

/-- Split a prefix XOR into two adjacent ranges. -/
theorem xorUpTo_add (f : ℕ → BitVec L) (m : ℕ) :
    ∀ n, xorUpTo f (m + n) = xorUpTo f m ^^^ xorUpTo (fun i => f (m + i)) n
  | 0 => by simp [xorUpTo]
  | n + 1 => by
      rw [← Nat.add_assoc, xorUpTo, xorUpTo_add f m n, xorUpTo]
      simp only [BitVec.xor_assoc]

/-- The XOR of every complete tree level equals the root offset. No condition
on the (possibly label-dependent) tree materials is needed. -/
theorem level_xor (F : Frame L w l) (s : ℕ) (y : Fin (w - 1) → BitVec L) :
    ∀ k, xorUpTo (level F s y k) (2 ^ (k + 1)) = F.delta
  | 0 => by
      simp only [Nat.zero_add, pow_one, xorUpTo, level, ↓reduceIte,
        BitVec.zero_xor]
      calc
        (bit0 F ^^^ F.delta) ^^^ bit0 F = (bit0 F ^^^ bit0 F) ^^^ F.delta := by ac_rfl
        _ = F.delta := by simp
  | k + 1 => by
      have split : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by
        rw [pow_succ]
        omega
      rw [split, xorUpTo_add]
      have left : xorUpTo (level F s y (k + 1)) (2 ^ (k + 1)) =
          xorUpTo (fun i => level F s y k i ^^^ material F s y k (level F s y k) i)
            (2 ^ (k + 1)) :=
        xorUpTo_congr _ _ _ (fun i hi => by simp only [level, if_pos hi])
      have right : xorUpTo (fun i => level F s y (k + 1) (2 ^ (k + 1) + i)) (2 ^ (k + 1)) =
          xorUpTo (material F s y k (level F s y k)) (2 ^ (k + 1)) :=
        xorUpTo_congr _ _ _ (fun i _ => by
          have h : ¬ 2 ^ (k + 1) + i < 2 ^ (k + 1) := by omega
          simp only [level, if_neg h, Nat.add_sub_cancel_left])
      rw [left, right, xorUpTo_xor]
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      exact level_xor F s y k


/-! The arithmetic labels below have the construction's lane count. -/

open Cryptography

/-- Independent hidden data: tree materials and the upper planes of the hot cast. -/
abbrev ParityHidden (w r : ℕ) := (Fin (w - 1) → Label) × Kriterion.CRT.Lanes r

/-- Actual public data: joins and a half-pin, without a redundant zero plane. -/
abbrev ParityPublished (w r : ℕ) := (Fin (w - 1) → Label) × Kriterion.CRT.Lanes r

/-- Expand the hidden upper cast using the label of the hot leaf. -/
def embedParityHidden {w r : ℕ} (F : Frame labelBits w (r + 1)) (s : ℕ)
    (h : ParityHidden w r) : Hidden labelBits w (r + 1) :=
  (h.1, Parity.parityLift h.2 (level F s h.1 (w - 1) s))

/-- The hidden expansion loses no data, including when the hot leaf label
changes with the hidden tree materials. -/
theorem embedParityHidden_injective {w r : ℕ} (F : Frame labelBits w (r + 1)) (s : ℕ) :
    Function.Injective (embedParityHidden F s) := by
  intro h h' same
  have trees := congrArg Prod.fst same
  change h.1 = h'.1 at trees
  have casts := congrArg Prod.snd same
  change Parity.parityLift h.2 (level F s h.1 (w - 1) s) =
    Parity.parityLift h'.2 (level F s h'.1 (w - 1) s) at casts
  rw [trees] at casts
  exact Prod.ext trees (Parity.parityLift_injective _ casts)

/-- Publish the stage's joins and the upper planes of its pin. -/
def parityPublish {w r : ℕ} (F : Frame labelBits w (r + 1)) (s : ℕ)
    (h : ParityHidden w r) : ParityPublished w r :=
  ((publish F s (embedParityHidden F s h)).1,
    Parity.halfLanes (pin F s (embedParityHidden F s h)))

/-- The low plane commutes with a finite sum, turning addition into XOR. -/
theorem laneBit_sum_range_zero {r : ℕ} (f : ℕ → Kriterion.CRT.Lanes (r + 1)) :
    ∀ n, Kriterion.CRT.laneBit (∑ i ∈ Finset.range n, f i) 0 =
      xorUpTo (fun i => Kriterion.CRT.laneBit (f i) 0) n
  | 0 => by simp [xorUpTo, Parity.laneBit_zero]
  | n + 1 => by
      rw [Finset.sum_range_succ, Parity.laneBit_add_zero, xorUpTo,
        laneBit_sum_range_zero f n]

/-- Every cast, including the expanded hidden cast, has its leaf's label as
its low plane. Cold answers may otherwise depend arbitrarily on that label. -/
theorem castAt_embedParityHidden_laneBit_zero {w r : ℕ} (F : Frame labelBits w (r + 1))
    (cold : ∀ α G, Kriterion.CRT.laneBit (F.cast α G) 0 = G)
    (s : ℕ) (h : ParityHidden w r) (α : ℕ) :
    Kriterion.CRT.laneBit (castAt F s (embedParityHidden F s h) α) 0 =
      level F s h.1 (w - 1) α := by
  by_cases hot : α = s
  · subst α
    simp only [castAt, ↓reduceIte, embedParityHidden, Parity.laneBit_parityLift_zero]
  · simp only [castAt, if_neg hot, embedParityHidden, cold]

/-- The parity law on casts makes the actual stage pin even in every lane. -/
theorem pin_embedParityHidden_even {w r : ℕ} (F : Frame labelBits w (r + 1))
    (hw : 1 ≤ w) (cold : ∀ α G, Kriterion.CRT.laneBit (F.cast α G) 0 = G)
    (s : ℕ) (h : ParityHidden w r) :
    Parity.EvenLanes (pin F s (embedParityHidden F s h)) := by
  apply (Parity.evenLanes_iff_laneBit_zero _).2
  have sumBit : Kriterion.CRT.laneBit (castSum F s (embedParityHidden F s h)) 0 = F.delta := by
    rw [castSum, laneBit_sum_range_zero]
    calc
      xorUpTo (fun i => Kriterion.CRT.laneBit (castAt F s (embedParityHidden F s h) i) 0)
          (2 ^ w) = xorUpTo (level F s h.1 (w - 1)) (2 ^ w) :=
        xorUpTo_congr _ _ _ (fun i _ => castAt_embedParityHidden_laneBit_zero F cold s h i)
      _ = F.delta := by
        simpa only [Nat.sub_add_cancel hw] using level_xor F s h.1 (w - 1)
  change Kriterion.CRT.laneBit
    (castSum F s (embedParityHidden F s h) + Kriterion.CRT.deltaLanes (r + 1) F.delta) 0 = 0
  rw [Parity.laneBit_add_zero, sumBit, Parity.laneBit_deltaLanes_zero, BitVec.xor_self]
  rfl

/-- If the actual full pins are even, publication of half-pins is injective.
The proof reuses the full stage's injectivity, never full-width uniformity. -/
theorem parityPublish_injective_of_even {w r : ℕ} (F : Frame labelBits w (r + 1))
    (s : ℕ) (hs : s < 2 ^ w)
    (even : ∀ h, Parity.EvenLanes (pin F s (embedParityHidden F s h))) :
    Function.Injective (parityPublish F s) := by
  intro h h' same
  have joins := congrArg Prod.fst same
  have halves := congrArg Prod.snd same
  apply embedParityHidden_injective F s
  apply publish_injective F s hs
  exact Prod.ext joins (Parity.halfLanes_injective_on_even (even h) (even h') halves)

/-- Equal finite hidden/public spaces turn the restricted injection into a
bijection onto every tuple of joins and half-pins. -/
theorem parityPublish_bijective_of_even {w r : ℕ} (F : Frame labelBits w (r + 1))
    (s : ℕ) (hs : s < 2 ^ w)
    (even : ∀ h, Parity.EvenLanes (pin F s (embedParityHidden F s h))) :
    Function.Bijective (parityPublish F s) :=
  bijective_of_injective_card (parityPublish_injective_of_even F s hs even) rfl

/-- Uniform independent upper cast planes and hot tree materials publish
uniform joins and half-pins, independently of the frame. -/
theorem parity_stage_published_uniform_of_even {w r : ℕ} {Rest : Type*} (rest : PMF Rest)
    (frame : Rest → Frame labelBits w (r + 1)) (s : ℕ) (hs : s < 2 ^ w)
    (even : ∀ x h, Parity.EvenLanes (pin (frame x) s (embedParityHidden (frame x) s h))) :
    (rest.bind fun x => (PMF.uniformOfFintype (ParityHidden w r)).map fun h =>
      (x, parityPublish (frame x) s h)) =
    rest.bind fun x => (PMF.uniformOfFintype (ParityPublished w r)).map fun b => (x, b) :=
  bind_map_uniform_of_injective rest (fun x => parityPublish (frame x) s)
    (fun x => parityPublish_injective_of_even (frame x) s hs (even x)) rfl

/-- Restricted stage publication is a bijection for every parity-correct
frame and every actual stage value. -/
theorem parityPublish_bijective {w r : ℕ} (F : Frame labelBits w (r + 1))
    (hw : 1 ≤ w) (cold : ∀ α G, Kriterion.CRT.laneBit (F.cast α G) 0 = G)
    (s : ℕ) (hs : s < 2 ^ w) : Function.Bijective (parityPublish F s) :=
  parityPublish_bijective_of_even F s hs (pin_embedParityHidden_even F hw cold s)

/-- The new cast law yields the new public law: uniform joins and half-pins.
The independent hot draw contains only upper cast planes. -/
theorem parity_stage_published_uniform {w r : ℕ} {Rest : Type*} (rest : PMF Rest)
    (frame : Rest → Frame labelBits w (r + 1)) (hw : 1 ≤ w)
    (cold : ∀ x α G, Kriterion.CRT.laneBit ((frame x).cast α G) 0 = G)
    (s : ℕ) (hs : s < 2 ^ w) :
    (rest.bind fun x => (PMF.uniformOfFintype (ParityHidden w r)).map fun h =>
      (x, parityPublish (frame x) s h)) =
    rest.bind fun x => (PMF.uniformOfFintype (ParityPublished w r)).map fun b => (x, b) :=
  parity_stage_published_uniform_of_even rest frame s hs
    (fun x => pin_embedParityHidden_even (frame x) hw (cold x) s)


/-! Construction-stage instance. The hot answer keeps the queried label in
its low plane instead of overriding the complete cast by a constant. -/

open Kriterion.CRT.ExtractSpec (StageParams stepMat gNode gBit0 gLeaf gCast gRes gBit gLevelSum gJoin gPin)

/-- Override only the independent hot answers. The hot cast remains a
function of its label, with the hidden data supplying its upper planes. -/
def parityOverrideHot {r : ℕ} (sp : StageParams (r + 1)) (s : ℕ)
    (h : ParityHidden sp.w r) : StageParams (r + 1) where
  w := sp.w
  hw := sp.hw
  mat n x lab := if x = s % 2 ^ n then hot (w := sp.w) h.1 (n - 1) else sp.mat n x lab
  castF α lab := if α = s then Parity.parityLift h.2 lab else sp.castF α lab

/-- Changing the cast rule does not change the garbler's tree. -/
theorem gNode_parityOverrideHot {r : ℕ} (sp : StageParams (r + 1))
    (R : Kriterion.CRT.Lanes (r + 1)) (Δ : Label) (s : ℕ) (h : ParityHidden sp.w r) :
    ∀ n x, gNode (parityOverrideHot sp s h) (gBit0 (parityOverrideHot sp s h) R) Δ n x =
      gNode (overrideHot sp s (embedParityHidden (specFrame sp R Δ) s h))
        (gBit0 (overrideHot sp s (embedParityHidden (specFrame sp R Δ) s h)) R) Δ n x
  | 0, _ => rfl
  | n + 1, x => by
      simp only [gNode, gNode_parityOverrideHot sp R Δ s h n]
      cases n <;> rfl

/-- The construction's parity override casts the same actual leaf values as
the abstract stage with its restricted hidden tuple expanded. -/
theorem gCast_parityOverrideHot {r : ℕ} (sp : StageParams (r + 1)) (hw : 1 ≤ sp.w)
    (R : Kriterion.CRT.Lanes (r + 1)) (Δ : Label) (s : ℕ) (h : ParityHidden sp.w r)
    (α : ℕ) (hα : α < 2 ^ sp.w) :
    gCast (parityOverrideHot sp s h) R Δ α =
      castAt (specFrame sp R Δ) s (embedParityHidden (specFrame sp R Δ) s h) α := by
  have node := gNode_override sp R Δ s (embedParityHidden (specFrame sp R Δ) s h)
    (sp.w - 1) α (by simpa only [Nat.sub_add_cancel hw] using hα)
  rw [Nat.sub_add_cancel hw] at node
  unfold gCast gLeaf
  rw [gNode_parityOverrideHot]
  rw [show (parityOverrideHot sp s h).w = sp.w from rfl, node]
  by_cases atHot : α = s
  · subst α
    simp only [parityOverrideHot, castAt, ↓reduceIte, embedParityHidden]
  · simp only [parityOverrideHot, castAt, if_neg atHot, specFrame]

/-- Public joins and the half-pin of the construction's overridden stage. -/
def paritySpecPublish {r : ℕ} (sp : StageParams (r + 1)) (R : Kriterion.CRT.Lanes (r + 1))
    (Δ : Label) (s : ℕ) (h : ParityHidden sp.w r) : ParityPublished sp.w r :=
  ((fun k => gJoin (parityOverrideHot sp s h) R Δ (k.val + 1)),
    Parity.halfLanes (gPin (parityOverrideHot sp s h) R Δ))

/-- Bridge from the construction's label-aware hot override to the abstract
restricted publication map. -/
theorem parity_spec_publish_eq {r : ℕ} (sp : StageParams (r + 1)) (hw : 1 ≤ sp.w)
    (R : Kriterion.CRT.Lanes (r + 1)) (Δ : Label) (s : ℕ) (h : ParityHidden sp.w r) :
    paritySpecPublish sp R Δ s h = parityPublish (specFrame sp R Δ) s h := by
  have casts : ∀ α ∈ Finset.range (2 ^ sp.w),
      gCast (parityOverrideHot sp s h) R Δ α =
        gCast (overrideHot sp s (embedParityHidden (specFrame sp R Δ) s h)) R Δ α := by
    intro α hα
    rw [gCast_parityOverrideHot sp hw R Δ s h α (Finset.mem_range.mp hα),
      gCast_override sp R Δ s _ hw α (Finset.mem_range.mp hα)]
  have res : ∀ n, gRes (parityOverrideHot sp s h) R Δ n =
      gRes (overrideHot sp s (embedParityHidden (specFrame sp R Δ) s h)) R Δ n := by
    intro n
    exact Finset.sum_congr rfl (fun α hα => by rw [casts α hα])
  have bits : ∀ n, gBit (parityOverrideHot sp s h) R Δ n =
      gBit (overrideHot sp s (embedParityHidden (specFrame sp R Δ) s h)) R Δ n := by
    intro n
    unfold gBit
    rw [res]
    rfl
  have sums : ∀ n, gLevelSum (parityOverrideHot sp s h) R Δ n =
      gLevelSum (overrideHot sp s (embedParityHidden (specFrame sp R Δ) s h)) R Δ n := by
    intro n
    unfold gLevelSum
    simp only [gNode_parityOverrideHot]
    rfl
  have pins : gPin (parityOverrideHot sp s h) R Δ =
      gPin (overrideHot sp s (embedParityHidden (specFrame sp R Δ) s h)) R Δ := by
    unfold gPin
    exact congrArg (fun A : Kriterion.CRT.Lanes (r + 1) => A + Kriterion.CRT.deltaLanes (r + 1) Δ)
      (Finset.sum_congr rfl casts)
  have full := spec_publish_eq sp R Δ s (embedParityHidden (specFrame sp R Δ) s h) hw
  have mapped := congrArg (fun p : Published labelBits sp.w (r + 1) => (p.1, Parity.halfLanes p.2)) full
  change _ = parityPublish (specFrame sp R Δ) s h at mapped
  rw [← mapped]
  apply Prod.ext
  · funext k
    exact congrArg₂ (· ^^^ ·) (sums (k.val + 1)) (bits (k.val + 1))
  · exact congrArg Parity.halfLanes pins

/-- The construction's stage is injective in independent hot tree materials
and hot cast upper planes. -/
theorem parity_spec_publish_injective {r : ℕ} (sp : StageParams (r + 1)) (hw : 1 ≤ sp.w)
    (cold : ∀ α G, Kriterion.CRT.laneBit (sp.castF α G) 0 = G)
    (R : Kriterion.CRT.Lanes (r + 1)) (Δ : Label) (s : ℕ) (hs : s < 2 ^ sp.w) :
    Function.Injective (paritySpecPublish sp R Δ s) := by
  have same : paritySpecPublish sp R Δ s = parityPublish (specFrame sp R Δ) s :=
    funext (parity_spec_publish_eq sp hw R Δ s)
  rw [same]
  exact (parityPublish_bijective (specFrame sp R Δ) hw cold s hs).1

/-- The exact uniform primitive for chaining parity stages through arbitrary
rest-of-view data. Stage casts may depend on labels through their required
low plane and through arbitrary cold upper planes. -/
theorem parity_spec_stage_uniform {r w : ℕ} {Rest : Type*} (rest : PMF Rest)
    (hw : w ≤ r + 1) (hw1 : 1 ≤ w)
    (matOf : Rest → ℕ → ℕ → Label → Label)
    (castOf : Rest → ℕ → Label → Kriterion.CRT.Lanes (r + 1))
    (cold : ∀ x α G, Kriterion.CRT.laneBit (castOf x α G) 0 = G)
    (remOf : Rest → Kriterion.CRT.Lanes (r + 1)) (deltaOf : Rest → Label)
    (s : ℕ) (hs : s < 2 ^ w) :
    (rest.bind fun x => (PMF.uniformOfFintype (ParityHidden w r)).map fun h =>
      (x, paritySpecPublish (stageOf w hw (matOf x) (castOf x)) (remOf x) (deltaOf x) s h)) =
    rest.bind fun x => (PMF.uniformOfFintype (ParityPublished w r)).map fun b => (x, b) :=
  bind_map_uniform_of_injective rest _
    (fun x => parity_spec_publish_injective (stageOf w hw (matOf x) (castOf x)) hw1
      (cold x) (remOf x) (deltaOf x) s hs) rfl

/-! Total-width adapters for the empty-row convention of the conversion core.
These keep the actual lane width `rb` in the stage and store only `rb - 1` bits.
The zero-width type is a singleton, and every nonempty stage reduces to the
successor-width restricted theorem above. -/

abbrev UpperHidden (w rb : ℕ) := Hidden labelBits w (rb - 1)

/-- Replace the hot cast's upper planes while deriving its low plane from
its actual leaf label. This also has a total zero-width convention. -/
def upperOverrideHot {rb : ℕ} (sp : StageParams rb) (s : ℕ)
    (h : UpperHidden sp.w rb) : StageParams rb where
  w := sp.w
  hw := sp.hw
  mat n x lab := if x = s % 2 ^ n then hot (w := sp.w) h.1 (n - 1) else sp.mat n x lab
  castF α lab := if α = s then Parity.liftUpper rb h.2 lab else sp.castF α lab

/-- The public tuple at the reduced lane width. -/
def upperSpecPublish {rb : ℕ} (sp : StageParams rb) (R : Kriterion.CRT.Lanes rb)
    (Δ : Label) (s : ℕ) (h : UpperHidden sp.w rb) : UpperHidden sp.w rb :=
  ((fun k => gJoin (upperOverrideHot sp s h) R Δ (k.val + 1)),
    Parity.pinHalf rb (gPin (upperOverrideHot sp s h) R Δ))

@[simp] theorem upperOverrideHot_succ {r : ℕ} (sp : StageParams (r + 1))
    (s : ℕ) (h : UpperHidden sp.w (r + 1)) :
    upperOverrideHot sp s h = parityOverrideHot sp s h := rfl

@[simp] theorem upperSpecPublish_succ {r : ℕ} (sp : StageParams (r + 1))
    (R : Kriterion.CRT.Lanes (r + 1)) (Δ : Label) (s : ℕ)
    (h : UpperHidden sp.w (r + 1)) :
    upperSpecPublish sp R Δ s h = paritySpecPublish sp R Δ s h := rfl

/-- The total-width interface to restricted publication injectivity. -/
theorem upper_spec_publish_injective {rb : ℕ} (sp : StageParams rb) (hw : 1 ≤ sp.w)
    (cold : ∀ α G, Kriterion.CRT.laneBit (sp.castF α G) 0 = G)
    (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s : ℕ) (hs : s < 2 ^ sp.w) :
    Function.Injective (upperSpecPublish sp R Δ s) := by
  cases rb with
  | zero => have bound := sp.hw; omega
  | succ r => exact parity_spec_publish_injective sp hw cold R Δ s hs

/-- Reconstruct a full cast from its upper planes and its proved low plane. -/
theorem liftUpper_pinHalf_of_low {rb : ℕ} (A : Kriterion.CRT.Lanes rb) (G : Label)
    (low : Kriterion.CRT.laneBit A 0 = G) :
    Parity.liftUpper rb (Parity.pinHalf rb A) G = A := by
  cases rb with
  | zero => rfl
  | succ rb =>
      show Parity.parityLift (Parity.halfLanes A) G = A
      rw [← low]
      exact Parity.parityLift_halfLanes_laneBit A

/-- Only the tree-material component influences tree nodes. -/
theorem gNode_upperOverrideHot {rb : ℕ} (sp : StageParams rb) (b0 Δ : Label) (s : ℕ)
    (h : UpperHidden sp.w rb) (full : Kriterion.CRT.Lanes rb) :
    ∀ n x, gNode (upperOverrideHot sp s h) b0 Δ n x =
      gNode (overrideHot sp s (h.1, full)) b0 Δ n x
  | 0, _ => rfl
  | n + 1, x => by
      simp only [gNode, gNode_upperOverrideHot sp b0 Δ s h full n]
      cases n <;> rfl

/-- The independent upper data of the stage's own hot answers. -/
def upperHiddenOfSpec {rb : ℕ} (sp : StageParams rb) (R : Kriterion.CRT.Lanes rb)
    (Δ : Label) (s : ℕ) : UpperHidden sp.w rb :=
  ((hiddenOfSpec sp R Δ s).1, Parity.pinHalf rb (gCast sp R Δ s))

/-- At its own hot upper data, every cast is restored exactly. -/
theorem gCast_upper_override_self {rb : ℕ} (sp : StageParams rb)
    (cold : ∀ α G, Kriterion.CRT.laneBit (sp.castF α G) 0 = G)
    (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s α : ℕ) :
    gCast (upperOverrideHot sp s (upperHiddenOfSpec sp R Δ s)) R Δ α = gCast sp R Δ α := by
  unfold gCast gLeaf
  show (if α = s then _ else sp.castF α _) = _
  rw [show (upperOverrideHot sp s (upperHiddenOfSpec sp R Δ s)).w = sp.w from rfl,
    show gBit0 (upperOverrideHot sp s (upperHiddenOfSpec sp R Δ s)) R = gBit0 sp R from rfl,
    gNode_upperOverrideHot sp (gBit0 sp R) Δ s _ (gCast sp R Δ s)]
  change (if α = s then _ else sp.castF α
    (gNode (overrideHot sp s (hiddenOfSpec sp R Δ s)) (gBit0 sp R) Δ sp.w α)) = _
  rw [gNode_override_self sp R Δ s sp.w le_rfl α]
  split_ifs with hα
  · subst α
    have hnode : gNode (overrideHot sp s ((upperHiddenOfSpec sp R Δ s).1, gCast sp R Δ s)) (gBit0 sp R) Δ sp.w s =
        gLeaf sp R Δ s :=
      gNode_override_self sp R Δ s sp.w le_rfl s
    rw [hnode]
    exact liftUpper_pinHalf_of_low (gCast sp R Δ s) (gLeaf sp R Δ s) (cold s (gLeaf sp R Δ s))
  · rfl

/-- The stage's class sums are unchanged at its own hot upper data. -/
theorem gRes_upper_override_self {rb : ℕ} (sp : StageParams rb)
    (cold : ∀ α G, Kriterion.CRT.laneBit (sp.castF α G) 0 = G)
    (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s n : ℕ) :
    gRes (upperOverrideHot sp s (upperHiddenOfSpec sp R Δ s)) R Δ n = gRes sp R Δ n :=
  Finset.sum_congr rfl fun α _ => by rw [gCast_upper_override_self sp cold R Δ s α]

theorem gNext_upper_override_self {rb : ℕ} (sp : StageParams rb)
    (cold : ∀ α G, Kriterion.CRT.laneBit (sp.castF α G) 0 = G)
    (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s : ℕ) :
    (Kriterion.CRT.ExtractSpec.gNext (upperOverrideHot sp s (upperHiddenOfSpec sp R Δ s)) R Δ :
      Kriterion.CRT.Lanes (rb - sp.w)) = Kriterion.CRT.ExtractSpec.gNext sp R Δ := by
  show Kriterion.CRT.peelDiv R
    (gRes (upperOverrideHot sp s (upperHiddenOfSpec sp R Δ s)) R Δ sp.w) sp.w = _
  rw [gRes_upper_override_self sp cold R Δ s sp.w]
  rfl

theorem gBit_upper_override_self {rb : ℕ} (sp : StageParams rb)
    (cold : ∀ α G, Kriterion.CRT.laneBit (sp.castF α G) 0 = G)
    (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s n : ℕ) :
    gBit (upperOverrideHot sp s (upperHiddenOfSpec sp R Δ s)) R Δ n = gBit sp R Δ n := by
  unfold gBit
  rw [gRes_upper_override_self sp cold R Δ s n]
  rfl

/-- At its own upper readings the stage publishes its actual joins and half-pin. -/
theorem upperSpecPublish_self {rb : ℕ} (sp : StageParams rb) (hw : 1 ≤ sp.w)
    (cold : ∀ α G, Kriterion.CRT.laneBit (sp.castF α G) 0 = G)
    (R : Kriterion.CRT.Lanes rb) (Δ : Label) (s : ℕ) (hs : s < 2 ^ sp.w) :
    upperSpecPublish sp R Δ s (upperHiddenOfSpec sp R Δ s) =
      ((fun k => gJoin sp R Δ (k.val + 1)), Parity.pinHalf rb (gPin sp R Δ)) := by
  cases rb with
  | zero => have bound := sp.hw; omega
  | succ rb =>
      rw [upperSpecPublish_succ, parity_spec_publish_eq sp hw R Δ s]
      have leaf : level (specFrame sp R Δ) s (hiddenOfSpec sp R Δ s).1 (sp.w - 1) s =
          gLeaf sp R Δ s := by
        have nodes := gNode_override sp R Δ s (hiddenOfSpec sp R Δ s) (sp.w - 1) s
          (by simpa only [Nat.sub_add_cancel hw] using hs)
        rw [Nat.sub_add_cancel hw,
          show gBit0 (overrideHot sp s (hiddenOfSpec sp R Δ s)) R = gBit0 sp R from rfl,
          gNode_override_self sp R Δ s sp.w le_rfl s] at nodes
        exact nodes.symm
      have hidden : embedParityHidden (specFrame sp R Δ) s (upperHiddenOfSpec sp R Δ s) =
          hiddenOfSpec sp R Δ s := by
        refine Prod.ext rfl ?_
        change Parity.parityLift (Parity.halfLanes (gCast sp R Δ s))
          (level (specFrame sp R Δ) s (hiddenOfSpec sp R Δ s).1 (sp.w - 1) s) = gCast sp R Δ s
        rw [leaf]
        exact liftUpper_pinHalf_of_low (gCast sp R Δ s) _ (cold s _)
      show ((publish (specFrame sp R Δ) s
          (embedParityHidden (specFrame sp R Δ) s (upperHiddenOfSpec sp R Δ s))).1,
        Parity.halfLanes (pin (specFrame sp R Δ) s
          (embedParityHidden (specFrame sp R Δ) s (upperHiddenOfSpec sp R Δ s)))) = _
      rw [hidden]
      have full := spec_garbler_eq_publish sp R Δ s hw
      refine Prod.ext ?_ ?_
      · exact (congrArg Prod.fst full).symm
      · exact congrArg Parity.halfLanes (congrArg Prod.snd full.symm)

end Kriterion.CRT.Privacy.ExtractStage
