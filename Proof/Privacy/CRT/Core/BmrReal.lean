/-
**The real reading** (`BmrSplit.RealReading`, row (R) of `CrtBmrSplit`).

* `bmrPart_realView` (pointwise, every tape and every `u`): the P45 part of the real view is `bmrOf` of P45's real
  output at `bmrContextOf scalar coins` and `bmrCoinsOf coins table`, with the table's answers at the visible tags.
  The garbling on the table oracle is `pubOf` on `tagHash table`, because the garbler asks only inputs below `p`
  (`garbler_input_lt`), where the two hashes agree; then `BmrEntry`'s `curve_eq`, `rows_eq`, `recX_eq`, `recY_eq`.
* `swappedTableTape_eq`: the swapped tape is uniform coins, uniform targets, then the kernel's table.
* `realReading K : RealReading K`: on the kernel's support the table reads the targets (`K.reads`), so P45's coins are
  `coinsOf τ (layerOf coins)`; the answers at the visible tags depend only on the visible targets (`K.visible`).
-/

import Proof.Privacy.CRT.Core.BmrSplit
import Proof.Privacy.CRT.Core.ConvSplit
import Proof.Privacy.CRT.Hidden.Reached

namespace Kriterion.CRT.Privacy.BmrReal

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.Instance Kriterion.CRT.Privacy.BmrSplit
open scoped ENNReal

noncomputable section

/- `BMR`'s definitions at the entry's table were elaborated with H8's instance; other imported instances for the
same moduli (the simulator's `modulusAtNeZero`) make the terms differ and their comparison expensive. -/
attribute [local instance 2000] H8.tableModulusNeZero

/-! ### 1. The garbling on the table oracle -/

/-- A program's value depends only on the hash at the inputs it asks. -/
theorem eval_congr_asked (H H' : HashN) {α : Type} :
    ∀ R : CM α, (∀ n ∈ Align.asked H R, H n = H' n) → R.eval H = R.eval H'
  | .pure _, _ => rfl
  | .query n next, agree => by
    have head : H n = H' n := agree n List.mem_cons_self
    show (next (H n)).eval H = (next (H' n)).eval H'
    rw [← head]
    exact eval_congr_asked H H' (next (H n)) fun m member => agree m (List.mem_cons_of_mem _ member)

/-- Below `p` the scheme's reading of the table oracle is `tagHash`. -/
theorem schemeHash_eq_tagHash (table : TagTable) (n : ℕ) (small : n < baseFieldModulus) :
    schemeHash (tableOracle (FI := Empty) (EI := Empty) table) n = H8.tagHash table n := by
  have hval : ((n : BaseField)).val = n := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt small]
  show table (tagOfInput (n : BaseField)) = table _
  refine congrArg table (Fin.ext ?_)
  show ((n : BaseField)).val / 2 ^ 128 % 2 ^ 40 = n / 2 ^ 128 % 2 ^ 40
  rw [hval]

/-- **The published value on the table oracle is `pubOf` on `tagHash`.** -/
theorem pubOf_table (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) :
    EntryCorrect.pubOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins =
      EntryCorrect.pubOf (H8.tagHash table) scalar coins := by
  have same := eval_congr_asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) (H8.tagHash table)
    (Kriterion.CRT.Entry.garbleCM scalar coins) fun n asked =>
      schemeHash_eq_tagHash table n (Align.garbler_input_lt _ scalar coins n asked)
  rw [EntryCorrect.garbleCM_eval, EntryCorrect.garbleCM_eval] at same
  exact (Prod.mk.inj same).1

variable [FieldCertificate] [GroupCertificate]

/-- The garbling on a pair tape, as a pair (rewrite with this before any projection is reduced: a projection of an
unevaluated garbling compared against anything else unfolds the garbler). -/
theorem realGarbled_pair (parameter : ℕ) (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins)
    (table : TagTable) :
    H8.realGarbled crtEntry parameter scalar (coins, table) =
      (EntryCorrect.pubOf (H8.tagHash table) scalar coins, coins.inputMacKey) := by
  rw [ConvSplit.realGarbled_eq]
  dsimp only
  rw [EntryCorrect.garbleCM_eval, pubOf_table]

theorem realGarbled_pub (parameter : ℕ) (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins)
    (table : TagTable) :
    (H8.realGarbled crtEntry parameter scalar (coins, table)).1 = EntryCorrect.pubOf (H8.tagHash table) scalar coins := by
  rw [realGarbled_pair]


/-! ### 2. The published part as P45's -/

theorem vector_eq_ofFn {α : Type} {n : ℕ} (v : Vector α n) (f : Fin n → α) (h : ∀ i : Fin n, v.get i = f i) :
    v = Vector.ofFn f := by
  ext i hi
  rw [Vector.getElem_ofFn, ← h ⟨i, hi⟩]
  rfl

theorem toRecord_val (r : Kriterion.CRT.Entry.Record) : Kriterion.CRT.Entry.toRecord r.val = r :=
  Fin.ext (Nat.mod_eq_of_lt r.isLt)

theorem realOut_join (ctx : BMR.NContext) (u : AffineInput) (c : BMR.Coins Tb) :
    (BMR.nRealOut ctx u c).1.1.1 = BMR.nJoin ctx c := by
  simp only [BMR.nRealOut]

theorem realOut_gamma (ctx : BMR.NContext) (u : AffineInput) (c : BMR.Coins Tb) :
    (BMR.nRealOut ctx u c).1.1.2.1 = BMR.nGamma ctx c := by
  simp only [BMR.nRealOut]

theorem realOut_curve (ctx : BMR.NContext) (u : AffineInput) (c : BMR.Coins Tb) :
    (BMR.nRealOut ctx u c).1.1.2.2 = BMR.curveTable c := by
  simp only [BMR.nRealOut]

theorem realOut_hint (ctx : BMR.NContext) (u : AffineInput) (c : BMR.Coins Tb) :
    (BMR.nRealOut ctx u c).1.2 = BMR.hint c := by
  simp only [BMR.nRealOut]

theorem recX_vec (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) :
    (EntryCorrect.pubOf (H8.tagHash table) scalar coins).recX = Vector.ofFn fun e =>
      Kriterion.CRT.Entry.toRecord (recordOf (BMR.nJoin (BmrEntry.bmrContextOf scalar coins)
        (BmrEntry.bmrCoinsOf coins table)) (BMR.hint (BmrEntry.bmrCoinsOf coins table)) (.inl (BMR.xEncEquiv.symm e))) := by
  refine vector_eq_ofFn _ _ fun e => ?_
  have value := BmrEntry.recX_eq scalar coins table (BMR.xEncEquiv.symm e)
  have flat : BMR.xFlat (BMR.xEncEquiv.symm e) = e := BMR.xEncEquiv.apply_symm_apply e
  rw [flat] at value
  rw [← toRecord_val ((EntryCorrect.pubOf (H8.tagHash table) scalar coins).recX.get e), value]
  rfl

theorem recY_vec (scalar : NonZeroScalar) (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) :
    (EntryCorrect.pubOf (H8.tagHash table) scalar coins).recY = Vector.ofFn fun e =>
      Kriterion.CRT.Entry.toRecord (recordOf (BMR.nJoin (BmrEntry.bmrContextOf scalar coins)
        (BmrEntry.bmrCoinsOf coins table)) (BMR.hint (BmrEntry.bmrCoinsOf coins table)) (.inr (BMR.yEncEquiv.symm e))) := by
  refine vector_eq_ofFn _ _ fun e => ?_
  have value := BmrEntry.recY_eq scalar coins table (BMR.yEncEquiv.symm e)
  have flat : BMR.yFlat (BMR.yEncEquiv.symm e) = e := BMR.yEncEquiv.apply_symm_apply e
  rw [flat] at value
  rw [← toRecord_val ((EntryCorrect.pubOf (H8.tagHash table) scalar coins).recY.get e), value]
  rfl

/-- **The P45 part of the real view at a pair, pointwise** (every `u`). -/
theorem bmrPart_realView_pair (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) :
    H8.bmrPart Tb u (H8.realView crtEntry Tb parameter scalar u (coins, table)) =
      bmrOf u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u (BmrEntry.bmrCoinsOf coins table))
        (restrictBmr u table) := by
  unfold H8.bmrPart H8.realView
  rw [realGarbled_pair]
  unfold bmrOf
  dsimp only
  rw [realOut_join, realOut_gamma, realOut_curve, realOut_hint, BmrEntry.curve_eq, recX_vec, recY_vec]
  have rows : (EntryCorrect.pubOf (H8.tagHash table) scalar coins).rows =
      Vector.ofFn fun d => BMR.nGamma (BmrEntry.bmrContextOf scalar coins) (BmrEntry.bmrCoinsOf coins table) d :=
    vector_eq_ofFn _ _ fun d => BmrEntry.rows_eq scalar coins table d
  rw [rows]
  rfl

/-- **The P45 part of the real view, pointwise** (every tape, every `u`). -/
theorem bmrPart_realView (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape crtEntry) :
    H8.bmrPart Tb u (H8.realView crtEntry Tb parameter scalar u tape) =
      bmrOf u (BMR.nRealOut (BmrEntry.bmrContextOf scalar tape.1) u (BmrEntry.bmrCoinsOf tape.1 tape.2))
        (restrictBmr u tape.2) := by
  obtain ⟨coins, table⟩ := tape
  exact bmrPart_realView_pair parameter scalar u coins table

/-! ### 3. The swapped tape through the kernel -/

/-- **The swapped tape is uniform coins, uniform targets, then the kernel's table.** -/
theorem swappedTableTape_eq (K : TableKernel) :
    swappedTableTape crtEntry = coinLaw.bind fun coins => (PMF.uniformOfFintype Targets).bind fun τ =>
      (K.given τ).map fun table => ((coins, table) : TableTape crtEntry) := by
  unfold swappedTableTape
  rw [show crtEntry.layout = crtLayout from rfl, K.law]
  simp only [PMF.map_bind]
  rfl

/-! ### 4. The reading -/

theorem map_congr_support {α β : Type*} (p : PMF α) (f f' : α → β) (h : ∀ a ∈ p.support, f a = f' a) :
    p.map f = p.map f' := by
  ext b
  simp only [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff p a).mpr ha, ite_self, ite_self]

theorem map_eq_pure {α β : Type*} (p : PMF α) (f : α → β) (b : β) (h : ∀ a, f a = b) : p.map f = PMF.pure b := by
  rw [show f = Function.const α b from funext h, PMF.map_const]

/-- On the kernel's support, P45's coins read from the table are the targets and the coins' layer. -/
theorem bmrCoinsOf_of_reads (coins : Kriterion.ArgoMAC.Scheme.Coins) (table : TagTable) (τ : Targets)
    (pads : BmrEntry.bmrPadsOf table = τ.1) (masks : BmrEntry.bmrMasksOf table = τ.2) :
    BmrEntry.bmrCoinsOf coins table = coinsOf τ (layerOf coins) := by
  unfold coinsOf layerOf
  unfold BmrEntry.bmrCoinsOf
  rw [pads, masks]

/-- **The P45 part of the real view on the kernel's support** (every `u`). -/
theorem bmrPart_realView_support (K : TableKernel) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (coins : Kriterion.ArgoMAC.Scheme.Coins) (τ : Targets) (table : TagTable) (member : table ∈ (K.given τ).support) :
    H8.bmrPart Tb u (H8.realView crtEntry Tb parameter scalar u (coins, table)) =
      bmrOf u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u (coinsOf τ (layerOf coins))) (restrictBmr u table) := by
  obtain ⟨pads, masks⟩ := K.reads τ table member
  rw [bmrPart_realView_pair, bmrCoinsOf_of_reads coins table τ pads masks]

theorem coldOfPads_padsOfCold (u : AffineInput) (cold : BMR.Cold Tb u) : coldOfPads u (padsOfCold u cold) = cold := by
  funext i e ρ
  unfold coldOfPads padsOfCold
  rw [dif_neg ρ.2]

/-- The visible targets of P45's real output at `coinsOf τ layer`. -/
theorem visTargets_realOut (ctx : BMR.NContext) (u : AffineInput) (τ : Targets) (layer : Layer) :
    coldOfPads u τ.1 = coldOfPads u (padsOfCold u (visTargets u (BMR.nRealOut ctx u (coinsOf τ layer))).1) ∧
      τ.2 = (visTargets u (BMR.nRealOut ctx u (coinsOf τ layer))).2 := by
  refine ⟨?_, ?_⟩
  · rw [coldOfPads_padsOfCold]
    rfl
  · funext r
    unfold visTargets
    dsimp only
    split <;> rfl

open Classical in
/-- **`G1U°`'s P45 part** (row (R)). -/
theorem realReading (K : TableKernel) : RealReading K := by
  intro parameter scalar u
  unfold H8.realCore
  rw [PMF.map_comp, swappedTableTape_eq K, PMF.map_bind]
  refine congrArg (PMF.bind coinLaw) (funext fun coins => ?_)
  rw [PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun τ => ?_)
  rw [PMF.map_comp]
  by_cases dbl : H8.Doubling crtEntry scalar (coins, fun _ => (0, 0)) u
  · rw [if_pos dbl]
    refine map_eq_pure _ _ _ fun table => ?_
    simp only [Function.comp_apply]
    rw [if_pos ((doubling_congr scalar u (fun _ => (0, 0)) table rfl).mp dbl)]
    rfl
  · rw [if_neg dbl]
    have vis := visTargets_realOut (BmrEntry.bmrContextOf scalar coins) u τ (layerOf coins)
    calc _ = (K.given τ).map fun table => some (bmrOf u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u
            (coinsOf τ (layerOf coins))) (restrictBmr u table)) := by
          refine map_congr_support _ _ _ fun table member => ?_
          simp only [Function.comp_apply]
          rw [if_neg fun d => dbl ((doubling_congr scalar u table (fun _ => (0, 0)) rfl).mp d), Option.map_some,
            bmrPart_realView_pair]
          obtain ⟨pads, masks⟩ := K.reads τ table member
          rw [bmrCoinsOf_of_reads coins table τ pads masks]
      _ = ((K.given τ).map (restrictBmr u)).map (some ∘ bmrOf u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u
            (coinsOf τ (layerOf coins)))) := by
          rw [PMF.map_comp]
          rfl
      _ = _ := by
          rw [K.visible u τ (padsOfCold u (visTargets u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u
            (coinsOf τ (layerOf coins)))).1, (visTargets u (BMR.nRealOut (BmrEntry.bmrContextOf scalar coins) u
            (coinsOf τ (layerOf coins)))).2) vis.1 vis.2]
          unfold bmrLaw bmrKernel
          rw [PMF.map_comp, PMF.map_comp, PMF.map_comp]

end

end Kriterion.CRT.Privacy.BmrReal
