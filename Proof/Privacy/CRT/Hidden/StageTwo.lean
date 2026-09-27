/-
**H7 for the CRT entry: the stage-2 guess, split by the family of the touched tag** (P2b).

A stage-2 query touches a hidden garbler entry only at the garbler's input at its tag (the garbler asks each tag once,
at a fixed input below `p`). The tag of the query is fixed, so its family is fixed, and the designed rule hides it in
exactly one way:

* families 0 to 6: the tag is hot at `u` (the garbler's label is the evaluator's plus `Δ`);
* family 7 or 10 off the curve: a mask (label `K`) or the key (label `t mod 2^128`);
* family 8 at the other bit (label the evaluator's plus `Δ`);
* family 9 at a digit whose exceptional input is not `u` (label the digit's key, an XOR of digest answers).

`crtEntry_stageTwoGuess` proves `CrtStageTwoGuess crtEntry table (ofReal crtHiddenCharge) (ofReal hiddenWindowError)`
from one bound per case (`GuessCase`), each at most the charge, and the mass of the bad event:
`curveNearEdge`, a curve encoding's CRT offset within `B` of the ends of the wrap window, where its hint could pin the
curve mask. The key's case is required off that event only (`notNearEdge`); `CurveWindowMass` is its mass row.
-/

import Proof.Privacy.CRT.Hidden.Reached
import Proof.Privacy.CRT.Glue.Budget
import Proof.Privacy.CRT.Paths.Transcript

namespace Kriterion.CRT.Privacy.StageTwo

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy.Align
open scoped ENNReal

noncomputable section

/-! ### The garbler's inputs on a tape -/

/-- The garbler's inputs on a table tape. -/
def gAsked (scalar : NonZeroScalar) (tape : TableTape Instance.crtEntry) : List ℕ :=
  asked (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) (Entry.garbleCM scalar tape.1)

/-- The garbler's entries are its inputs with the table's answers. -/
theorem garblerEntries_eq [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape Instance.crtEntry) :
    garblerEntries Instance.crtEntry parameter scalar tape =
      (gAsked scalar tape).map fun n : ℕ =>
        (⟨.hash (n : BaseField), (tableOracle (FI := Empty) (EI := Empty) tape.2).2.2 (n : BaseField)⟩ :
          Entry Empty Empty) := by
  obtain ⟨coins, table⟩ := tape
  have transcriptG := transcript_toProgram (publicAnswer (tableOracle (FI := Empty) (EI := Empty) table))
    (liftHash (Entry.garbleCM scalar coins)) Entry.garbleBudget (Entry.bounded_garbleM scalar coins)
  unfold garblerEntries tapeOracle
  dsimp only [Instance.crtEntry]
  unfold Entry.garbleProgram Entry.garbleM
  rw [transcriptG, ftranscript_liftHash]
  rfl

/-- **A touched hidden entry is the garbler's input at the query**, and its tag is not designed. -/
theorem touch_hidden [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput) (tape : TableTape Instance.crtEntry) (x : BaseField)
    (touch : Touches (hiddenEntries Instance.crtEntry Entry.table parameter scalar tape u) (.hash x)) :
    x.val ∈ gAsked scalar tape ∧
      designTag Entry.table (Entry.exceptional scalar tape.1) u (x.val / 2 ^ 128) = false := by
  obtain ⟨coins, table⟩ := tape
  unfold Touches hiddenEntries at touch
  obtain ⟨entry, inHidden, same⟩ := List.mem_map.mp touch
  rw [List.mem_filter] at inHidden
  obtain ⟨inGarbler, notDesigned⟩ := inHidden
  have inGarbler' := inGarbler
  rw [garblerEntries_eq] at inGarbler'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp inGarbler'
  simp only at same
  have hx : x = (n : BaseField) := (PublicQuery.hash.inj same).symm
  have small := garbler_input_lt (schemeHash (tableOracle (FI := Empty) (EI := Empty) table)) scalar coins n hn
  have hval : x.val = n := by rw [hx]; exact val_natCast_of_lt small
  refine ⟨by rw [hval]; exact hn, ?_⟩
  unfold designedEntries at notDesigned
  simp only [List.mem_filter, not_and, decide_eq_true_eq] at notDesigned
  have designed := notDesigned inGarbler
  unfold tapeOracle at designed
  dsimp only [Instance.crtEntry] at designed
  rw [crtDesigned_hash, val_natCast_of_lt small] at designed
  dsimp only at designed
  rw [hval]
  simpa using designed

/-! ### The cases -/

/-- **One case of the stage-2 guess**: at every tag satisfying `cond`, the garbler's input at it (with the coin
condition `extra`) has conditional mass at most `ε` given the stage-2 view. -/
def GuessCase (cond : AffineInput → ℕ → Prop)
    (extra : NonZeroScalar → AffineInput → ℕ → TableTape Instance.crtEntry → Prop) (ε : ℝ≥0∞) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (view : Instance.crtEntry.Public × LamportSignature × List (Entry Empty Empty)) (N : ℕ),
    cond u (N / 2 ^ 128) →
    (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
          N ∈ gAsked scalar tape ∧ extra scalar u N tape} ≤
      ε * (swappedTableTape Instance.crtEntry).toOuterMeasure
        {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view}

/-- Families 0 to 6, hot at `u`. -/
def convHot (u : AffineInput) (τ : ℕ) : Prop := tagFamily τ ≤ 6 ∧ hotTag Entry.table u τ = true

/-- Family 8, the bit `u` does not hold. -/
def digestOther (u : AffineInput) (τ : ℕ) : Prop :=
  tagFamily τ = 8 ∧ tagPart τ ≠ inputBit u (tagCoord τ) (tagSlot τ)

/-- Family 7 off the curve. -/
def maskOff (u : AffineInput) (τ : ℕ) : Prop := tagFamily τ = 7 ∧ validate u = false

/-- Family 10 off the curve. -/
def keyOff (u : AffineInput) (τ : ℕ) : Prop := tagFamily τ = 10 ∧ validate u = false

/-- Family 9. -/
def final (_ : AffineInput) (τ : ℕ) : Prop := tagFamily τ = 9

/-- No coin condition. -/
def noExtra (_ : NonZeroScalar) (_ : AffineInput) (_ : ℕ) (_ : TableTape Instance.crtEntry) : Prop := True

/-- The digit of the final is not exceptional at `u`. -/
def notExceptional (scalar : NonZeroScalar) (u : AffineInput) (N : ℕ) (tape : TableTape Instance.crtEntry) : Prop :=
  Entry.exceptional scalar tape.1 (tagSlot (N / 2 ^ 128)) ≠ some u

/-! ### The curve-window bad event -/

/-- A CRT offset within `B` of an end of the two-sided wrap window: `O < B` or `O > M − 2B`. If the evaluator's
integer `(O + a·v) mod M` of an encoding lies in the window `[0, B − 1) ∪ (M − B, M)` at some input (`a·v < B`), then
its offset is near an edge; the event does not depend on the input. -/
def nearEdge (offset : ℕ) : Prop := offset < Entry.table.wrapBound ∨ Entry.table.product < offset + 2 * Entry.table.wrapBound

/-- **The bad event**: a curve encoding's offset (`x` encodings `364 ..`, `y` encodings `273 ..`) is near an edge. -/
def curveNearEdge (tape : TableTape Instance.crtEntry) : Prop :=
  (∃ e : Fin Entry.xCount, Kriterion.ArgoMAC.PlanB.pointElementCountX ≤ e.val ∧
      nearEdge ((EntryCorrect.gxOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) tape.1).offset e)) ∨
    (∃ e : Fin Entry.yCount, Kriterion.ArgoMAC.PlanB.pointElementCountY ≤ e.val ∧
      nearEdge ((EntryCorrect.gyOf (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) tape.1).offset e))

/-- The key's case holds off the bad event. -/
def notNearEdge (_ : NonZeroScalar) (_ : AffineInput) (_ : ℕ) (tape : TableTape Instance.crtEntry) : Prop :=
  ¬ curveNearEdge tape

/-- **The mass row of the bad event**. -/
def CurveWindowMass : Prop :=
  (swappedTableTape Instance.crtEntry).toOuterMeasure {tape | curveNearEdge tape} ≤ ENNReal.ofReal hiddenWindowError

/-! ### The reduction -/

theorem designTag_false_cases (exc : ℕ → Option AffineInput) (u : AffineInput) (τ : ℕ)
    (hidden : designTag Entry.table exc u τ = false) :
    convHot u τ ∨ digestOther u τ ∨ maskOff u τ ∨ keyOff u τ ∨ (final u τ ∧ exc (tagSlot τ) ≠ some u) ∨
      10 < tagFamily τ := by
  unfold designTag at hidden
  unfold convHot digestOther maskOff keyOff final
  generalize hf : tagFamily τ = f at hidden
  rcases Nat.lt_or_ge 10 f with big | small
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr big))))
  · interval_cases f <;> simp_all

/-- **H7 from the five cases and the bad event's mass**. -/
theorem crtEntry_stageTwoGuess {εConv εDigest εMask εKey εFinal : ℝ≥0∞}
    (conv : GuessCase convHot noExtra εConv) (digest : GuessCase digestOther noExtra εDigest)
    (mask : GuessCase maskOff noExtra εMask) (key : GuessCase keyOff notNearEdge εKey)
    (fin : GuessCase final notExceptional εFinal)
    (le : εConv ≤ ENNReal.ofReal crtHiddenCharge ∧ εDigest ≤ ENNReal.ofReal crtHiddenCharge ∧
      εMask ≤ ENNReal.ofReal crtHiddenCharge ∧ εKey ≤ ENNReal.ofReal crtHiddenCharge ∧
      εFinal ≤ ENNReal.ofReal crtHiddenCharge)
    (window : CurveWindowMass) :
    CrtStageTwoGuess Instance.crtEntry Entry.table (ENNReal.ofReal crtHiddenCharge)
      (ENNReal.ofReal hiddenWindowError) := by
  intro field group parameter scalar
  refine ⟨curveNearEdge, window, fun u view query => ?_⟩
  cases query with
  | fixedForward index _ => exact index.elim
  | fixedInverse index _ => exact index.elim
  | encForward index _ => exact index.elim
  | encInverse index _ => exact index.elim
  | hash x =>
    set N := x.val with hN
    set μ := swappedTableTape Instance.crtEntry
    set V := μ.toOuterMeasure {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view}
    have sub : {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
        Touches (hiddenEntries Instance.crtEntry Entry.table parameter scalar tape u) (.hash x) ∧
          ¬ curveNearEdge tape} ⊆
        {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧ N ∈ gAsked scalar tape ∧
          designTag Entry.table (Entry.exceptional scalar tape.1) u (N / 2 ^ 128) = false ∧ ¬ curveNearEdge tape} := by
      intro tape ⟨hv, touch, far⟩
      exact ⟨hv, (touch_hidden parameter scalar u tape x touch).1, (touch_hidden parameter scalar u tape x touch).2, far⟩
    refine le_trans (MeasureTheory.measure_mono sub) ?_
    -- a case bound, weakened to the charge
    have weaken : ∀ {cond extra ε}, GuessCase cond extra ε → ε ≤ ENNReal.ofReal crtHiddenCharge →
        cond u (N / 2 ^ 128) → ∀ S : Set (TableTape Instance.crtEntry),
          S ⊆ {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
            N ∈ gAsked scalar tape ∧ extra scalar u N tape} →
          μ.toOuterMeasure S ≤ ENNReal.ofReal crtHiddenCharge * V := by
      intro cond extra ε case hε hc S hS
      exact le_trans (MeasureTheory.measure_mono hS)
        (le_trans (case parameter scalar u view N hc) (mul_le_mul' hε le_rfl))
    -- the family of the fixed tag
    by_cases small : tagFamily (N / 2 ^ 128) ≤ 10
    · by_cases hf6 : tagFamily (N / 2 ^ 128) ≤ 6
      · by_cases hot : hotTag Entry.table u (N / 2 ^ 128) = true
        · exact weaken conv le.1 ⟨hf6, hot⟩ _ fun tape h => ⟨h.1, h.2.1, trivial⟩
        · have empty : {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
              N ∈ gAsked scalar tape ∧
              designTag Entry.table (Entry.exceptional scalar tape.1) u (N / 2 ^ 128) = false ∧
              ¬ curveNearEdge tape} = ∅ := by
            ext tape
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
            intro _ _ hd _
            revert hd
            rw [designTag_conv _ _ _ hf6]
            simp_all
          rw [empty, MeasureTheory.measure_empty]
          exact zero_le
      · -- families 7 to 10
        by_cases h7 : tagFamily (N / 2 ^ 128) = 7
        · by_cases on : validate u = true
          · have empty : {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
                N ∈ gAsked scalar tape ∧
                designTag Entry.table (Entry.exceptional scalar tape.1) u (N / 2 ^ 128) = false ∧
                ¬ curveNearEdge tape} = ∅ := by
              ext tape
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
              intro _ _ hd _
              revert hd
              rw [designTag_of_family _ _ _ (Or.inl h7)]
              simp_all
            rw [empty, MeasureTheory.measure_empty]
            exact zero_le
          · exact weaken mask le.2.2.1 ⟨h7, by simpa using on⟩ _ fun tape h => ⟨h.1, h.2.1, trivial⟩
        · by_cases h10 : tagFamily (N / 2 ^ 128) = 10
          · by_cases on : validate u = true
            · have empty : {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
                  N ∈ gAsked scalar tape ∧
                  designTag Entry.table (Entry.exceptional scalar tape.1) u (N / 2 ^ 128) = false ∧
                  ¬ curveNearEdge tape} = ∅ := by
                ext tape
                simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
                intro _ _ hd _
                revert hd
                rw [designTag_of_family _ _ _ (Or.inr h10)]
                simp_all
              rw [empty, MeasureTheory.measure_empty]
              exact zero_le
            · exact weaken key le.2.2.2.1 ⟨h10, by simpa using on⟩ _ fun tape h => ⟨h.1, h.2.1, h.2.2.2⟩
          · by_cases h8 : tagFamily (N / 2 ^ 128) = 8
            · by_cases bit : tagPart (N / 2 ^ 128) = inputBit u (tagCoord (N / 2 ^ 128)) (tagSlot (N / 2 ^ 128))
              · have empty : {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
                    N ∈ gAsked scalar tape ∧
                    designTag Entry.table (Entry.exceptional scalar tape.1) u (N / 2 ^ 128) = false ∧
                    ¬ curveNearEdge tape} = ∅ := by
                  ext tape
                  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
                  intro _ _ hd _
                  revert hd
                  rw [designTag_label _ _ _ h8, bit]
                  simp
                rw [empty, MeasureTheory.measure_empty]
                exact zero_le
              · exact weaken digest le.2.1 ⟨h8, bit⟩ _ fun tape h => ⟨h.1, h.2.1, trivial⟩
            · have h9 : tagFamily (N / 2 ^ 128) = 9 := by omega
              refine weaken fin le.2.2.2.2 h9 _ fun tape h => ⟨h.1, h.2.1, ?_⟩
              have := h.2.2.1
              rw [designTag_final _ _ _ h9] at this
              simpa [notExceptional] using this
    · -- no garbler tag has a family above 10
      have empty : {tape | stageTwoView Instance.crtEntry Entry.table parameter scalar u tape = view ∧
          N ∈ gAsked scalar tape ∧
          designTag Entry.table (Entry.exceptional scalar tape.1) u (N / 2 ^ 128) = false ∧
          ¬ curveNearEdge tape} = ∅ := by
        ext tape
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ inside _ _
        unfold gAsked at inside
        obtain ⟨k, member, range, label, same⟩ := asked_of_tagged (Paths.garbleCM_tagged scalar tape.1)
          (schemeHash (tableOracle (FI := Empty) (EI := Empty) tape.2)) N inside
        have fam : tagFamily (N / 2 ^ 128) = k.fam := by rw [same, hashInput_div, tagFamily_key range]
        exact absurd (fam ▸ Paths.garblerKeys_fam k member) small
      rw [empty, MeasureTheory.measure_empty]
      exact zero_le

end

end Kriterion.CRT.Privacy.StageTwo
