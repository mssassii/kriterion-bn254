/-
**`CrtReplayDelivered`**: on a full tag table read through `tagHash`,
the delivered values of the view's replay program are P45's ideal delivered values `BMR.deliveredIdeal u J cold` at
the joins the records carry and the cold pads the table holds, for every source.

**The route** (it replaces the bijection route first proposed). No property of the
conversion material is used, so `convPublish` bijection is not a dependency of this file:

* a labelled input `hashInput label tag` is answered by `tagHash` from its tag alone (`label < 2 ^ 128`,
  `tagHash_hashInput`), so the body's pad answers do not depend on the labels of the final one-hot, and the body's
  residues are read from the table at the body tags (`eval_bodyEvalM_tag`, with `padVectorM_eq_padVector`);
* the hot index of every modulus is a function of the coordinate value `v` alone: `v mod 256` for the power of two,
  and for an odd modulus the folds' index, which starts at `σ mod 2 ^ keep mod m` and moves by
  `bit_j(σ) · (2 ^ j mod m)` whatever the answers (`eval_conversionEvalM_hot`), ends at `σ mod 2 ^ ell mod m =
  σ mod m = v mod m` (`foldHot_eq`, L5: `wordValue_lt`, `wordValue_modEq`);
* the evaluator's two sums over `Fin m` with the hot slot skipped are P45's sums over the residues other than the
  hot one (`sum_skip_eq_subtype`); `crtWith` is `T.crt`; the records the source publishes are below `M`, so the hint
  is false and `wrapDecode` is the identity.

The hypothesis `validate u = true` of the statement is not used.
-/

import Proof.Privacy.CRT.Core.H8
import Proof.Privacy.CRT.Swap.PadBridge
import Proof.Correctness.CRT.FoldChain
import Proof.Correctness.CRT.Word
import Proof.Correctness.CRT.RealTable

namespace Kriterion.CRT.Privacy.ReplayDelivered

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT

noncomputable section

/-! ### Reading a tag table -/

/-- **A labelled input is answered by its tag** on a tag table. -/
theorem tagHash_hashInput (table : TagTable) (label : Block) (tag : ℕ) :
    H8.tagHash table (hashInput label tag) = table ⟨tag % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ := by
  unfold H8.tagHash hashInput
  congr 1
  apply Fin.ext
  show (label.toNat + 2 ^ 128 * tag) / 2 ^ 128 % 2 ^ 40 = tag % 2 ^ 40
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt label.isLt, Nat.zero_add]

/-- The pad values of body slot `ρ` of modulus index `i` of coordinate `coord` a tag table holds. -/
def padsAt (table : TagTable) (m S q coord i ρ : ℕ) : Fin S → ZMod m :=
  padVector m S q fun j => table ⟨bodyTag coord i ρ j.val % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

theorem eval_padVectorM_tag (table : TagTable) (m S q : ℕ) (label : Block) (coord i ρ : ℕ) (e : Fin S) :
    ((((padVectorM m S q label (bodyTag coord i ρ)).eval (H8.tagHash table)) e : ℕ) : ZMod m) =
      padsAt table m S q coord i ρ e := by
  have := congrFun (padVectorM_eq_padVector (H8.tagHash table) m S q label (bodyTag coord i ρ)) e
  rw [this]
  unfold padsAt
  congr 1
  funext j
  exact tagHash_hashInput table label _

/-! ### The body on a tag table -/

theorem eval_bodyEvalM_tag (table : TagTable) (m S q coord i : ℕ) (final : Fin m → Block) (hot : ℕ)
    (joins : Fin S → ℕ) (e : Fin S) :
    ((bodyEvalM m S q coord i final hot joins).eval (H8.tagHash table)) e =
      ((∑ ρ : Fin m, if ρ.val = hot then 0 else (ρ.val : ZMod m) * padsAt table m S q coord i ρ.val e) +
        (hot : ZMod m) * ((joins e : ZMod m) -
          ∑ ρ : Fin m, if ρ.val = hot then 0 else padsAt table m S q coord i ρ.val e)).val := by
  unfold bodyEvalM
  simp only [FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq]
  congr 2
  · refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases h : ρ.val = hot
    · simp only [if_pos h]
    · simp only [if_neg h]
      rw [eval_padVectorM_tag]
  · congr 2
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases h : ρ.val = hot
    · simp only [if_pos h]
    · simp only [if_neg h]
      rw [eval_padVectorM_tag]

/-! ### The hot index is the coordinate value's residue -/

theorem eval_foldsEvalM_hot (H : HashN) (m : ℕ) (tagOf : ℕ → ℕ → ℕ) (value : ℕ) (bitLabel join : ℕ → Block) :
    ∀ (count start hot : ℕ) (labels : Fin m → Block),
      ((foldsEvalM m tagOf value bitLabel join count start hot labels).eval H).2 =
        SliceC.foldHot m value count start hot
  | 0, _, _, _ => rfl
  | count + 1, start, hot, labels => by
      rw [foldsEvalM, FreeQuery.eval_bind]
      exact eval_foldsEvalM_hot H m tagOf value bitLabel join count (start + 1) _ _

theorem eval_conversionEvalM_hot (H : HashN) (coord i : ℕ) (row : OddRow) (m σ : ℕ) (word : Lanes row.ell)
    (pub : ConvPublic) :
    ((conversionEvalM coord i row m σ word pub).eval H).2 =
      SliceC.foldHot m σ (row.ell - row.keep) row.keep (σ % 2 ^ row.keep % m) := by
  unfold conversionEvalM
  simp only [FreeQuery.eval_bind]
  exact eval_foldsEvalM_hot H m _ σ _ _ _ _ _ _

theorem conversion_hot (T : CrtTable) (hT : SliceC.CorrectTable T) (i : Fin T.count) (row : OddRow)
    (hk : T.kind i = .odd row) (v : ℕ) (hv : v < 2 ^ T.inputBits) :
    SliceC.foldHot (T.modulus i) (T.wordValue (T.modulus i) v) (row.ell - row.keep) row.keep
        (T.wordValue (T.modulus i) v % 2 ^ row.keep % T.modulus i) = v % T.modulus i := by
  obtain ⟨_, _, _, _, hk1, _, hcount⟩ := hT.odd i row hk
  have hm := hT.modulus_pos i
  rw [SliceC.foldHot_eq _ _ hm _ _ _ rfl, Nat.add_sub_cancel' hk1,
    Nat.mod_eq_of_lt (SliceC.wordValue_lt T _ v _ hm hcount)]
  exact SliceC.wordValue_modEq T hT.chunkBits_pos _ v hv

/-- The residue formula of the body at the hot index `v mod m`. -/
def residueAt (table : TagTable) (T : CrtTable) (S coord : ℕ) (joins : Fin T.count → Fin S → ℕ) (v : ℕ)
    (i : Fin T.count) (e : Fin S) : ℕ :=
  ((∑ ρ : Fin (T.modulus i), if ρ.val = v % T.modulus i then 0 else
        (ρ.val : ZMod (T.modulus i)) * padsAt table (T.modulus i) S (T.padAnswers S i) coord i.val ρ.val e) +
    ((v % T.modulus i : ℕ) : ZMod (T.modulus i)) * ((joins i e : ZMod (T.modulus i)) -
      ∑ ρ : Fin (T.modulus i), if ρ.val = v % T.modulus i then 0 else
        padsAt table (T.modulus i) S (T.padAnswers S i) coord i.val ρ.val e)).val

theorem eval_modEvalM_tag (table : TagTable) (T : CrtTable) (hT : SliceC.CorrectTable T) (S coord : ℕ)
    (pub : ConvPublic) (joins : Fin T.count → Fin S → ℕ) (v : ℕ) (hv : v < 2 ^ T.inputBits)
    (chunks : ℕ → ChunkEval T.castWidth) (i : Fin T.count) (e : Fin S) :
    ((modEvalM T S coord pub joins v chunks i).eval (H8.tagHash table)) e = residueAt table T S coord joins v i e := by
  unfold modEvalM
  dsimp only
  split
  · exact eval_bodyEvalM_tag table _ _ _ _ _ _ _ _ e
  · rename_i row hk
    simp only [FreeQuery.eval_bind, eval_materializeM]
    rw [eval_bodyEvalM_tag, eval_conversionEvalM_hot, conversion_hot T hT i row hk v hv]
    rfl

/-! ### One coordinate -/

theorem coord_crtValue (table : TagTable) (T : CrtTable) (hT : SliceC.CorrectTable T) (S coord : ℕ)
    (pub : ConvPublic) (records : Fin S → ℕ) (v : ℕ) (hv : v < 2 ^ T.inputBits) (labels : ℕ → Block) (e : Fin S) :
    ((coordEvalM T S coord pub records v labels).eval (H8.tagHash table)).crtValue e =
      T.crt fun i => residueAt table T S coord
        (fun i e => recordJoin T T.product T.radix (records e) i) v i e := by
  unfold coordEvalM
  simp only [FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq]
  rw [crt_eq_crtWith]
  congr 1
  funext i
  exact eval_modEvalM_tag table T hT S coord pub _ v hv _ i e

theorem coord_decoded (table : TagTable) (T : CrtTable) (hT : SliceC.CorrectTable T) (S coord : ℕ)
    (pub : ConvPublic) (records : Fin S → ℕ) (recLt : ∀ e, records e < T.product) (v : ℕ)
    (hv : v < 2 ^ T.inputBits) (labels : ℕ → Block) (e : Fin S) :
    ((coordEvalM T S coord pub records v labels).eval (H8.tagHash table)).decoded e =
      T.crt fun i => residueAt table T S coord
        (fun i e => recordJoin T T.product T.radix (records e) i) v i e := by
  unfold coordEvalM
  simp only [FreeQuery.eval_bind, eval_tableM, FreeQuery.eval_pure, stored_eq]
  have hint : decide (T.product ≤ records e) = false := decide_eq_false (by have := recLt e; omega)
  rw [hint]
  unfold wrapDecode
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [crt_eq_crtWith]
  congr 1
  funext i
  exact eval_modEvalM_tag table T hT S coord pub _ v hv _ i e

/-! ### From the evaluator's sums to P45's -/

theorem sum_skip_eq_subtype (m hot : ℕ) [NeZero m] (hlt : hot < m) (f : ZMod m → ZMod m) :
    (∑ ρ : Fin m, if ρ.val = hot then 0 else f (ρ.val : ZMod m)) =
      ∑ ρ : {ρ : ZMod m // ρ ≠ (hot : ZMod m)}, f ρ.1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
  rw [← Finset.sum_subtype (Finset.univ.filter fun ρ : ZMod (n + 1) => ρ ≠ (hot : ZMod (n + 1)))
    (fun ρ => by simp) f, Finset.sum_filter]
  refine Fintype.sum_equiv (Equiv.refl (Fin (n + 1))) _ _ fun ρ => ?_
  change (if ρ.val = hot then (0 : ZMod (n + 1)) else f ((ρ.val : ℕ) : ZMod (n + 1))) =
    if (ρ : ZMod (n + 1)) ≠ (hot : ZMod (n + 1)) then f (ρ : ZMod (n + 1)) else 0
  have cast : ((ρ.val : ℕ) : ZMod (n + 1)) = (ρ : ZMod (n + 1)) :=
    ZMod.natCast_zmod_val (n := n + 1) (ρ : ZMod (n + 1))
  have iff : (ρ.val = hot) ↔ ((ρ : ZMod (n + 1)) = (hot : ZMod (n + 1))) := by
    constructor
    · intro h
      rw [← cast, h]
    · intro h
      have := congrArg (fun x : ZMod (n + 1) => x.val) h
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at this
      exact this
  by_cases h : ρ.val = hot
  · have h' : ¬ ((ρ : ZMod (n + 1)) ≠ (hot : ZMod (n + 1))) := not_not.mpr (iff.mp h)
    rw [if_pos h, if_neg h']
  · have h' : (ρ : ZMod (n + 1)) ≠ (hot : ZMod (n + 1)) := fun same => h (iff.mpr same)
    rw [if_neg h, if_pos h', cast]

theorem residueAt_eq (table : TagTable) (T : CrtTable) (S coord : ℕ) (joins : Fin T.count → Fin S → ℕ)
    (v : ℕ) (i : Fin T.count) [NeZero (T.modulus i)] (e : Fin S) :
    residueAt table T S coord joins v i e =
      ((∑ ρ : {ρ : ZMod (T.modulus i) // ρ ≠ (v : ZMod (T.modulus i))},
          ρ.1 * padsAt table (T.modulus i) S (T.padAnswers S i) coord i.val ρ.1.val e) +
        (v : ZMod (T.modulus i)) * ((joins i e : ZMod (T.modulus i)) -
          ∑ ρ : {ρ : ZMod (T.modulus i) // ρ ≠ (v : ZMod (T.modulus i))},
            padsAt table (T.modulus i) S (T.padAnswers S i) coord i.val ρ.1.val e)).val := by
  have hlt : v % T.modulus i < T.modulus i := Nat.mod_lt _ (NeZero.pos _)
  have valCast : ∀ ρ : Fin (T.modulus i), ((ρ.val : ZMod (T.modulus i))).val = ρ.val := fun ρ => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt ρ.isLt]
  unfold residueAt
  have w := sum_skip_eq_subtype (T.modulus i) (v % T.modulus i) hlt fun ρ =>
    ρ * padsAt table (T.modulus i) S (T.padAnswers S i) coord i.val ρ.val e
  have k := sum_skip_eq_subtype (T.modulus i) (v % T.modulus i) hlt fun ρ =>
    padsAt table (T.modulus i) S (T.padAnswers S i) coord i.val ρ.val e
  simp only [valCast] at w k
  rw [w, k, ZMod.natCast_mod]

/-! ### The entry -/

theorem val_lt_inputBits (x : BaseField) : x.val < 2 ^ Entry.table.inputBits :=
  lt_trans (ZMod.val_lt x) (by show baseFieldModulus < 2 ^ 254; unfold baseFieldModulus; norm_num)

theorem recX_lt (source : Entry.Source) (e : Fin Entry.xCount) :
    ((Entry.publish source).recX.get e).val < Entry.table.product := by
  simp only [Entry.publish, vector_get_ofFn, Entry.toRecord]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (source.recX e).isLt

theorem recY_lt (source : Entry.Source) (e : Fin Entry.yCount) :
    ((Entry.publish source).recY.get e).val < Entry.table.product := by
  simp only [Entry.publish, vector_get_ofFn, Entry.toRecord]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (source.recY e).isLt

theorem padVector_congr {m S q q' : ℕ} (hq : q = q') (f : Fin q → Block × Block) (f' : Fin q' → Block × Block)
    (hf : ∀ j : Fin q, f j = f' (Fin.cast hq j)) : padVector m S q f = padVector m S q' f' := by
  subst hq
  congr 1
  funext j
  exact hf j

theorem padCount_x (i : Fin Entry.table.count) : Layout.padCount 0 i.val = Entry.table.padAnswers 458 i := by
  unfold Layout.padCount
  exact dif_pos i.isLt

theorem padCount_y (i : Fin Entry.table.count) : Layout.padCount 1 i.val = Entry.table.padAnswers 275 i := by
  unfold Layout.padCount
  exact dif_pos i.isLt

theorem padValues_x (table : TagTable) (i : Fin Entry.table.count) (ρ : ℕ) (e : Fin 458) (h : e.val < Layout.padS 0) :
    H8.padValues table 0 i ρ ⟨e.val, h⟩ =
      padsAt table (Entry.table.modulus i) 458 (Entry.table.padAnswers 458 i) 0 i.val ρ e := by
  unfold H8.padValues padsAt
  exact congrFun (padVector_congr (padCount_x i) _ _ fun j =>
    congrArg table (Fin.ext (by simp only [bodyTag, Fin.coe_cast]))) e

theorem padValues_y (table : TagTable) (i : Fin Entry.table.count) (ρ : ℕ) (e : Fin 275) (h : e.val < Layout.padS 1) :
    H8.padValues table 1 i ρ ⟨e.val, h⟩ =
      padsAt table (Entry.table.modulus i) 275 (Entry.table.padAnswers 275 i) 1 i.val ρ e := by
  unfold H8.padValues padsAt
  exact congrFun (padVector_congr (padCount_y i) _ _ fun j =>
    congrArg table (Fin.ext (by simp only [bodyTag, Fin.coe_cast]))) e

end

end Kriterion.CRT.Privacy.ReplayDelivered

namespace Kriterion.CRT.Privacy.H8

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy.ReplayDelivered

section Values

open Kriterion.CRT.Privacy.Instance

variable [FieldCertificate] [GroupCertificate]

/-- The CRT integer of an `x` encoding, from the residue formula, is P45's `evalInt`. -/
theorem evalInt_x (source : (view).Source) (u : AffineInput) (table : TagTable) (x : BMR.XEnc) :
    Entry.table.crt (fun i => residueAt table Entry.table Entry.xCount 0
        (fun i e => recordJoin Entry.table Entry.table.product Entry.table.radix
          (((view).publish source).recX.get e).val i) u.x.val i (BMR.xFlat x)) =
      BMR.evalInt u (bmrJoinsOf ((view).publish source)) (bmrColdOf table u) (.inl x) := by
  unfold BMR.evalInt
  congr 1
  funext i
  rw [residueAt_eq]
  unfold BMR.evalResidue
  simp only [bmrColdOf, padValues_x]
  rfl

/-- The CRT integer of a `y` encoding, from the residue formula, is P45's `evalInt`. -/
theorem evalInt_y (source : (view).Source) (u : AffineInput) (table : TagTable) (y : BMR.YEnc) :
    Entry.table.crt (fun i => residueAt table Entry.table Entry.yCount 1
        (fun i e => recordJoin Entry.table Entry.table.product Entry.table.radix
          (((view).publish source).recY.get e).val i) u.y.val i (BMR.yFlat y)) =
      BMR.evalInt u (bmrJoinsOf ((view).publish source)) (bmrColdOf table u) (.inr y) := by
  unfold BMR.evalInt
  congr 1
  funext i
  rw [residueAt_eq]
  unfold BMR.evalResidue
  simp only [bmrColdOf, padValues_y]
  rfl

/-- **The replay's CRT integer of an `x` encoding** (before the hint and the field) is P45's `evalInt`, for every
source and tag table. -/
theorem crtValue_x (source : (view).Source) (u : AffineInput) (table : TagTable) (x : BMR.XEnc) :
    ((coordEvalM Entry.table Entry.xCount 0 (Entry.convOf ((view).publish source).crtX)
        (fun e => (((view).publish source).recX.get e).val) u.x.val
        (Entry.labelX ((view).labels source u))).eval (tagHash table)).crtValue (BMR.xFlat x) =
      BMR.evalInt u (bmrJoinsOf ((view).publish source)) (bmrColdOf table u) (.inl x) := by
  rw [coord_crtValue table Entry.table SliceC.bn254_correctTable Entry.xCount 0 _ _ u.x.val
    (val_lt_inputBits u.x) _ (BMR.xFlat x)]
  exact evalInt_x source u table x

/-- **The replay's CRT integer of a `y` encoding** is P45's `evalInt`. -/
theorem crtValue_y (source : (view).Source) (u : AffineInput) (table : TagTable) (y : BMR.YEnc) :
    ((coordEvalM Entry.table Entry.yCount 1 (Entry.convOf ((view).publish source).crtY)
        (fun e => (((view).publish source).recY.get e).val) u.y.val
        (Entry.labelY ((view).labels source u))).eval (tagHash table)).crtValue (BMR.yFlat y) =
      BMR.evalInt u (bmrJoinsOf ((view).publish source)) (bmrColdOf table u) (.inr y) := by
  rw [coord_crtValue table Entry.table SliceC.bn254_correctTable Entry.yCount 1 _ _ u.y.val
    (val_lt_inputBits u.y) _ (BMR.yFlat y)]
  exact evalInt_y source u table y

/-- **The reveal's CRT values** (`replayCrtValues`) are P45's `evalInt`, `x` encodings. -/
theorem replayCrtValues_x (source : (view).Source) (u : AffineInput) (table : TagTable) (x : BMR.XEnc) :
    (replayCrtValues source u table).1 (BMR.xFlat x) =
      BMR.evalInt u (bmrJoinsOf ((view).publish source)) (bmrColdOf table u) (.inl x) := by
  unfold replayCrtValues
  dsimp only
  exact crtValue_x source u table x

/-- **The reveal's CRT values** (`replayCrtValues`) are P45's `evalInt`, `y` encodings. -/
theorem replayCrtValues_y (source : (view).Source) (u : AffineInput) (table : TagTable) (y : BMR.YEnc) :
    (replayCrtValues source u table).2 (BMR.yFlat y) =
      BMR.evalInt u (bmrJoinsOf ((view).publish source)) (bmrColdOf table u) (.inr y) := by
  unfold replayCrtValues
  dsimp only
  exact crtValue_y source u table y

end Values

/-- **`CrtReplayDelivered`**: on a full tag table the replay delivers P45's ideal values, for every source (every
conversion material), at every input. -/
theorem crtReplayDelivered : CrtReplayDelivered := by
  intro _ _ source u table _
  rw [Instance.view_replayProgram_eval]
  simp only [Entry.replayRouteM, FreeQuery.eval_bind, FreeQuery.eval_pure, Entry.replayConv]
  funext e
  rcases e with x | y
  · show Entry.toField _ = ((BMR.evalInt u _ _ _ : ℕ) : BaseField)
    refine congrArg (fun n : ℕ => (n : BaseField)) ?_
    rw [coord_decoded table Entry.table SliceC.bn254_correctTable Entry.xCount 0
      (Entry.convOf ((Instance.view).publish source).crtX)
      (fun e => (((Instance.view).publish source).recX.get e).val) (recX_lt source) u.x.val
      (val_lt_inputBits u.x) _ (BMR.xFlat x)]
    exact evalInt_x source u table x
  · show Entry.toField _ = ((BMR.evalInt u _ _ _ : ℕ) : BaseField)
    refine congrArg (fun n : ℕ => (n : BaseField)) ?_
    rw [coord_decoded table Entry.table SliceC.bn254_correctTable Entry.yCount 1
      (Entry.convOf ((Instance.view).publish source).crtY)
      (fun e => (((Instance.view).publish source).recY.get e).val) (recY_lt source) u.y.val
      (val_lt_inputBits u.y) _ (BMR.yFlat y)]
    exact evalInt_y source u table y

end Kriterion.CRT.Privacy.H8
