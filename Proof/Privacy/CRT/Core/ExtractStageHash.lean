/-
**The extraction-stage instance on the frozen oracle reading**.

Every CRT definition takes the oracle as `H : HashN := Nat → Block × Block`; the answer-table reading is the instance
`tableHash T = fun n => T (n / 2 ^ 128)`, which answers a labelled query by its tag alone. This file connects
`Proof.Privacy.CRT.Core.ExtractStage` (the stage with its hidden tuple as parameters) to that reading:

* `garbleStage H tags sub Δ`: one fused stage of the garbler run on `H`, every slot hashed, input-free: tree materials
  `h128 H G (treeTag n σ)`, casts `castLanes l (hlong H G (castTag α) (castAnswers l))` (D11), joins
  `Y_n ⊕ laneBit (sub − reduce res_n) n`, pin `Σ_α A_α + Δ⃗`;
* `garbleStage_eq_publish`: for **every** `H` and every stage value `s`, the garbler's published tuple is `publish`
  of the frame read from `H` at the hidden tuple read from `H` at the hot positions of `s` (the point reading, where
  the cold answers depend on the labels);
* `garbleStage_tableHash`: on a table, the frame is `tableFrame T` (cold answers by tag, labels ignored) and the
  hidden tuple is `readHot T s`, read from the hot tags only;
* `publish_congr_cold`: `publish` reads the frame's answers at cold positions only, so on a table the published tuple
  is a function of the cold tags of `T` and of the hidden tuple;
* `table_stage_uniform`: the instance of the inversion lemma on tables.

The stage tags are a parameter (`StageTags`); `frozenTags κ idx st` are the frozen ones (families 2 and 3 of the
tag layout). Nothing here depends on the garbler's program form.
-/

import Construction.CRT.Interface
import Proof.Privacy.CRT.Core.ExtractStage

namespace Kriterion.CRT.Privacy.ExtractStage

open Cryptography

variable {w l : ℕ}

/-! ### Tags, the cast read, and the frame of a hash -/

/-- The tags one stage asks: `treeTag n σ` for the tree answer at level `n`, slot `σ`; `castTag α j` for answer `j`
of the cast of leaf `α`. -/
structure StageTags where
  treeTag : ℕ → ℕ → ℕ
  castTag : ℕ → ℕ → ℕ

/-- The frozen tags of stage `st` of modulus index `idx` of coordinate `κ`. -/
def frozenTags (κ idx st : ℕ) : StageTags where
  treeTag n σ := Kriterion.CRT.tagCode Kriterion.CRT.Family.extTree κ idx st n σ 0
  castTag α j := Kriterion.CRT.tagCode Kriterion.CRT.Family.extCast κ idx st 0 α j

/-- A cast of width `l` read from `H` at label `G` (D11). -/
def castRead (H : Kriterion.CRT.HashN) (l : ℕ) (tagOf : ℕ → ℕ) (G : Block) : Lanes 128 l :=
  Kriterion.CRT.castLanes l (Kriterion.CRT.hlong H G tagOf (Kriterion.CRT.castAnswers l))

/-- The frame of one stage run on `H`: the cold answers are `H`'s at the points the garbler asks. -/
def hashFrame (H : Kriterion.CRT.HashN) (tags : StageTags) (sub : Lanes 128 w) (Δ : Block) :
    Frame 128 w l where
  sub := sub
  delta := Δ
  tree n σ G := Kriterion.CRT.h128 H G (tags.treeTag n σ)
  cast α G := castRead H l (tags.castTag α) G

/-! ### The garbler of one stage on a hash, every slot hashed -/

section Full

variable (H : Kriterion.CRT.HashN) (tags : StageTags) (sub : Lanes 128 w) (Δ : Block)

/-- The labels of tree level `k + 1`, every material hashed. -/
def fullLevel : ℕ → ℕ → Block
  | 0 => fun i => if i = 0 then laneBit sub 0 ^^^ Δ else laneBit sub 0
  | k + 1 => fun i =>
      if i < 2 ^ (k + 1) then
        fullLevel k i ^^^ Kriterion.CRT.h128 H (fullLevel k i) (tags.treeTag (k + 1) i)
      else
        Kriterion.CRT.h128 H (fullLevel k (i - 2 ^ (k + 1))) (tags.treeTag (k + 1) (i - 2 ^ (k + 1)))

/-- The material of slot `σ` of tree level `k + 1`. -/
def fullMaterial (k σ : ℕ) : Block :=
  Kriterion.CRT.h128 H (fullLevel H tags sub Δ k σ) (tags.treeTag (k + 1) σ)

/-- The cast of leaf `α`. -/
def fullCast (α : ℕ) : Lanes 128 l :=
  castRead H l (tags.castTag α) (fullLevel H tags sub Δ (w - 1) α)

/-- The class sum `res_n`. -/
def fullClassSum (n : ℕ) : Lanes 128 l :=
  ∑ α ∈ Finset.range (2 ^ w), (((α % 2 ^ n : ℕ) : ZMod (2 ^ l)) • fullCast (l := l) H tags sub Δ α)

/-- **The stage garbler on `H`** (input-free): the joins `J_{k+1}` for `k < w − 1` and the pin. -/
def garbleStage : Published 128 w l :=
  (fun k => xorUpTo (fullMaterial H tags sub Δ k.val) (2 ^ (k.val + 1))
      ^^^ laneBit (sub - reduceTo w (fullClassSum (l := l) H tags sub Δ (k.val + 1))) (k.val + 1),
    (∑ α ∈ Finset.range (2 ^ w), fullCast (l := l) H tags sub Δ α) + deltaLanes l Δ)

/-- The hidden tuple at stage value `s`: the hot materials of every level and the hot leaf's cast, as `H` answers
them at the garbler's points. -/
def hiddenOf (s : ℕ) : Hidden 128 w l :=
  (fun k => fullMaterial H tags sub Δ k.val (s % 2 ^ (k.val + 1)), fullCast H tags sub Δ s)

end Full

/-! ### The garbler is `publish` at the hidden tuple, for every hash -/

section Bridge

variable (H : Kriterion.CRT.HashN) (tags : StageTags) (sub : Lanes 128 w) (Δ : Block) (s : ℕ)

theorem level_hashFrame_eq :
    ∀ k, k ≤ w - 1 →
      level (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s).1 k
        = fullLevel H tags sub Δ k
  | 0, _ => rfl
  | k + 1, hk => by
      have prev := level_hashFrame_eq k (by omega)
      have mat : material (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s).1 k
          (level (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s).1 k)
          = fullMaterial H tags sub Δ k := by
        funext σ
        rw [prev]
        unfold material
        by_cases hσ : σ = s % 2 ^ (k + 1)
        · rw [if_pos hσ, hσ]
          simp only [hot, dif_pos (show k < w - 1 by omega), hiddenOf]
        · rw [if_neg hσ]
          rfl
      funext i
      show (if i < 2 ^ (k + 1) then _ else _) = (if i < 2 ^ (k + 1) then _ else _)
      rw [mat, prev]
      rfl

theorem castAt_hashFrame_eq (α : ℕ) :
    castAt (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s) α
      = fullCast H tags sub Δ α := by
  unfold castAt
  by_cases hα : α = s
  · rw [if_pos hα, hα]
    rfl
  · rw [if_neg hα, level_hashFrame_eq H tags sub Δ s (w - 1) le_rfl]
    rfl

/-- **The bridge, point reading.** For every hash `H` and every stage value `s`, the stage garbler's published
tuple is `publish` of the frame read from `H`, at the hidden tuple that `H` gives at the hot positions of `s`. -/
theorem garbleStage_eq_publish :
    garbleStage (l := l) H tags sub Δ
      = publish (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s) := by
  have casts : ∀ α, castAt (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s) α
      = fullCast H tags sub Δ α := castAt_hashFrame_eq H tags sub Δ s
  have classes : ∀ n, classSum (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s) n
      = fullClassSum (l := l) H tags sub Δ n := by
    intro n
    unfold classSum fullClassSum
    exact Finset.sum_congr rfl fun α _ => by rw [casts α]
  unfold garbleStage publish
  refine Prod.ext ?_ ?_
  · funext k
    show _ = levelSum _ _ _ _ ^^^ bitMask _ _ _ _
    unfold levelSum bitMask
    rw [classes]
    have lv := level_hashFrame_eq (l := l) H tags sub Δ s k.val (by omega)
    have mat : material (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s).1 k.val
        (level (hashFrame (l := l) H tags sub Δ) s (hiddenOf (l := l) H tags sub Δ s).1 k.val)
        = fullMaterial H tags sub Δ k.val := by
      funext σ
      rw [lv]
      unfold material
      by_cases hσ : σ = s % 2 ^ (k.val + 1)
      · rw [if_pos hσ, hσ]
        simp only [hot, dif_pos k.isLt, hiddenOf]
      · rw [if_neg hσ]
        rfl
    rw [mat]
    rfl
  · show _ = castSum _ _ _ + _
    unfold castSum
    rw [Finset.sum_congr rfl fun α _ => casts α]
    rfl

end Bridge

/-! ### The answer-table instance -/

/-! `Kriterion.CRT.tableHash T = fun n => T (n / 2 ^ 128)` (frozen interface) is the answer-table
reading of a tag-indexed table. -/

open Kriterion.CRT (tableHash)

theorem hashInput_div (G : Block) (tag : ℕ) : Kriterion.CRT.hashInput G tag / 2 ^ 128 = tag := by
  unfold Kriterion.CRT.hashInput
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.div_eq_of_lt G.isLt, Nat.zero_add]

@[simp] theorem h128_tableHash (T : ℕ → Block × Block) (G : Block) (tag : ℕ) :
    Kriterion.CRT.h128 (tableHash T) G tag = (T tag).1 := by
  simp only [Kriterion.CRT.h128, tableHash, hashInput_div]

@[simp] theorem hlong_tableHash (T : ℕ → Block × Block) (G : Block) (tagOf : ℕ → ℕ) (count : ℕ) :
    Kriterion.CRT.hlong (tableHash T) G tagOf count
      = Kriterion.CRT.packAnswers count fun j => T (tagOf j.val) := by
  simp only [Kriterion.CRT.hlong, tableHash, hashInput_div]

/-- The frame of a stage on a table: the cold answers by tag, the labels ignored. -/
def tableFrame (T : ℕ → Block × Block) (tags : StageTags) (sub : Lanes 128 w) (Δ : Block) :
    Frame 128 w l where
  sub := sub
  delta := Δ
  tree n σ _ := (T (tags.treeTag n σ)).1
  cast α _ := Kriterion.CRT.castLanes l
    (Kriterion.CRT.packAnswers (Kriterion.CRT.castAnswers l) fun j => T (tags.castTag α j.val))

/-- The hidden tuple read from the hot tags of a table at stage value `s`. -/
def readHot (T : ℕ → Block × Block) (tags : StageTags) (s : ℕ) : Hidden 128 w l :=
  (fun k => (T (tags.treeTag (k.val + 1) (s % 2 ^ (k.val + 1)))).1,
    Kriterion.CRT.castLanes l
      (Kriterion.CRT.packAnswers (Kriterion.CRT.castAnswers l) fun j => T (tags.castTag s j.val)))

theorem hashFrame_tableHash (T : ℕ → Block × Block) (tags : StageTags) (sub : Lanes 128 w) (Δ : Block) :
    hashFrame (l := l) (tableHash T) tags sub Δ = tableFrame T tags sub Δ := by
  unfold hashFrame tableFrame castRead
  simp only [h128_tableHash, hlong_tableHash]

theorem hiddenOf_tableHash (T : ℕ → Block × Block) (tags : StageTags) (sub : Lanes 128 w) (Δ : Block)
    (s : ℕ) : hiddenOf (l := l) (tableHash T) tags sub Δ s = readHot T tags s := by
  unfold hiddenOf readHot fullMaterial fullCast castRead
  simp only [h128_tableHash, hlong_tableHash]

/-- **The bridge, table reading.** On a table the stage garbler publishes `publish (tableFrame T) s (readHot T s)`. -/
theorem garbleStage_tableHash (T : ℕ → Block × Block) (tags : StageTags) (sub : Lanes 128 w) (Δ : Block)
    (s : ℕ) :
    garbleStage (l := l) (tableHash T) tags sub Δ = publish (tableFrame T tags sub Δ) s (readHot T tags s) := by
  rw [garbleStage_eq_publish (tableHash T) tags sub Δ s, hashFrame_tableHash, hiddenOf_tableHash]

/-! ### `publish` reads the frame at cold positions only -/

section Cold

variable {L : ℕ}

/-- Two frames that agree on `sub`, `Δ`, every cold tree answer and every cold cast give the same published tuple
for every hidden tuple. -/
theorem publish_congr_cold {F F' : Frame L w l} (s : ℕ) (subEq : F.sub = F'.sub)
    (deltaEq : F.delta = F'.delta)
    (treeEq : ∀ k σ G, σ ≠ s % 2 ^ (k + 1) → F.tree (k + 1) σ G = F'.tree (k + 1) σ G)
    (castEq : ∀ α G, α ≠ s → F.cast α G = F'.cast α G) (h : Hidden L w l) :
    publish F s h = publish F' s h := by
  have lv : ∀ k, level F s h.1 k = level F' s h.1 k := by
    intro k
    induction k with
    | zero =>
      funext i
      simp only [level, bit0, subEq, deltaEq]
    | succ k ih =>
      have mat : material F s h.1 k (level F s h.1 k) = material F' s h.1 k (level F' s h.1 k) := by
        funext σ
        unfold material
        by_cases hσ : σ = s % 2 ^ (k + 1)
        · rw [if_pos hσ, if_pos hσ]
        · rw [if_neg hσ, if_neg hσ, ih, treeEq k σ _ hσ]
      funext i
      show (if i < 2 ^ (k + 1) then _ else _) = (if i < 2 ^ (k + 1) then _ else _)
      rw [mat, ih]
  have casts : ∀ α, castAt F s h α = castAt F' s h α := by
    intro α
    unfold castAt
    by_cases hα : α = s
    · rw [if_pos hα, if_pos hα]
    · rw [if_neg hα, if_neg hα, lv, castEq α _ hα]
  have classes : ∀ n, classSum F s h n = classSum F' s h n := fun n =>
    Finset.sum_congr rfl fun α _ => by rw [casts α]
  unfold publish
  refine Prod.ext ?_ ?_
  · funext k
    show levelSum F s h k.val ^^^ bitMask F s h (k.val + 1)
      = levelSum F' s h k.val ^^^ bitMask F' s h (k.val + 1)
    have mat : material F s h.1 k.val (level F s h.1 k.val)
        = material F' s h.1 k.val (level F' s h.1 k.val) := by
      funext σ
      unfold material
      by_cases hσ : σ = s % 2 ^ (k.val + 1)
      · rw [if_pos hσ, if_pos hσ]
      · rw [if_neg hσ, if_neg hσ, lv, treeEq k.val σ _ hσ]
    unfold levelSum bitMask
    rw [mat, classes, subEq]
  · show castSum F s h + deltaLanes l F.delta = castSum F' s h + deltaLanes l F'.delta
    unfold castSum
    rw [Finset.sum_congr rfl fun α _ => casts α, deltaEq]

end Cold

/-- On tables, the published tuple depends on the table at cold tags only: two tables that agree at every cold tree
tag and every cold cast tag of `s` give the same published tuple for every hidden tuple. -/
theorem publish_tableFrame_congr {T T' : ℕ → Block × Block} (tags : StageTags) (sub : Lanes 128 w) (Δ : Block)
    (s : ℕ) (treeEq : ∀ k σ, σ ≠ s % 2 ^ (k + 1) → T (tags.treeTag (k + 1) σ) = T' (tags.treeTag (k + 1) σ))
    (castEq : ∀ α j, α ≠ s → T (tags.castTag α j) = T' (tags.castTag α j)) (h : Hidden 128 w l) :
    publish (tableFrame T tags sub Δ) s h = publish (tableFrame T' tags sub Δ) s h :=
  publish_congr_cold (F := tableFrame T tags sub Δ) (F' := tableFrame T' tags sub Δ) s rfl rfl
    (fun k σ _ hσ => by show (T _).1 = (T' _).1; rw [treeEq k σ hσ])
    (fun α _ hα => by
      show Kriterion.CRT.castLanes l (Kriterion.CRT.packAnswers _ _)
        = Kriterion.CRT.castLanes l (Kriterion.CRT.packAnswers _ _)
      congr 2
      funext j
      exact castEq α j.val hα) h

/-- **The instance on tables.** Draw the rest (a table, whose cold tags are what the frame reads, `sub` and `Δ`)
from any law and the hidden tuple uniformly: the published tuple of the stage is uniform and independent of the
rest. -/
theorem table_stage_uniform {Rest : Type*} (rest : PMF Rest) (table : Rest → ℕ → Block × Block)
    (tags : StageTags) (subOf : Rest → Lanes 128 w) (deltaOf : Rest → Block) (s : ℕ) (hs : s < 2 ^ w) :
    (rest.bind fun r => (PMF.uniformOfFintype (Hidden 128 w l)).map fun h =>
        (r, publish (tableFrame (table r) tags (subOf r) (deltaOf r)) s h))
      = rest.bind fun r => (PMF.uniformOfFintype (Published 128 w l)).map fun b => (r, b) :=
  stage_published_uniform rest (fun r => tableFrame (table r) tags (subOf r) (deltaOf r)) s hs

end Kriterion.CRT.Privacy.ExtractStage
