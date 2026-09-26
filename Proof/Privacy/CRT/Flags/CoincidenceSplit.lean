/-
**P8, the coincidence guess split by tag family** (`CrtCoincidenceGuess` at `crtEntry` and its table).

A coincidence (`Coincide`: the reach's entries are not the designed ones) is, given the containment
`DesignedReached` (`crtEntry_designedReached`), a garbler entry that the reach asks and the designed
rule hides (`HiddenReached`, `coincide_hiddenReached`). Split by the entry's tag family (`entryFamily`):

* families 0 to 6 (conversion and body), `CrtConvCoincide`: only when an input `Δ` is zero; the mass
  of `Δ_x = 0 ∨ Δ_y = 0` against every weight on the published value is `CrtDeltaGuess` (at most `2/2^128`);
* families 7 and 10 (masks and key), `CrtKeyMaskHidden`: never (on the curve the rule shows them, off
  it the reach does not ask them);
* family 8 (digest labels), `CrtLabelCoincide`: never (the reach asks only the part equal to `u`'s bit);
* family 9 (digest finals), `CrtFinalCoincide`: at most `91/2^128` against every weight on the published
  value;
* families 11 and above: no garbler entry (`crtEntry_garbler_small`).

`crtCoincidenceGuess_of`: `CrtCoincidenceGuess crtEntry Entry.table coincidenceError` from these five inputs
(`93/2^128 ≤ 94/2^128`).
-/

import Proof.Privacy.CRT.Flags.Coincidence
import Proof.Privacy.CRT.Hidden.Reached
import Proof.Privacy.CRT.Paths.Transcript

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-! ### 1. Hidden entries the reach asks -/

/-- The tag family of an entry (`11` for a permutation entry, of which the CRT entry has none). -/
def entryFamily {FI EI : Type} : Entry FI EI → ℕ
  | ⟨.hash x, _⟩ => tagFamily (x.val / 2 ^ 128)
  | _ => 11

open Classical in
/-- The indicator of a proposition. -/
def ind (P : Prop) : ℝ≥0∞ := if P then 1 else 0

variable {FI EI : Type} (E : CrtEntry FI EI)

section Hidden

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **A garbler entry the reach asks and the designed rule hides**, at input `u`. -/
def HiddenReached (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput)
    (e : Entry FI EI) : Prop :=
  e ∈ garblerEntries E parameter scalar tape ∧ e.1 ∈ (reachedEntries E parameter scalar tape u).map Sigma.fst ∧
    crtDesigned T ⟨fun scalar tape => E.exceptional scalar tape.1⟩ scalar (tape.1, tapeOracle E tape) u e = false

/-- **A coincidence is a hidden garbler entry the reach asks**, given the containment. -/
theorem coincide_hiddenReached (T : CrtTable) (reached : DesignedReached E T) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape E) (u : AffineInput) (coincide : Coincide E T parameter scalar tape u) :
    ∃ e, HiddenReached E T parameter scalar tape u e := by
  by_contra none
  apply coincide
  unfold visibleRule designedRule designedEntries
  refine List.filter_congr fun e member => ?_
  have inGarbler : e ∈ garblerEntries E parameter scalar tape := member
  cases shown : crtDesigned T ⟨fun scalar tape => E.exceptional scalar tape.1⟩ scalar (tape.1, tapeOracle E tape) u e
  · by_cases asked : e.1 ∈ (reachedEntries E parameter scalar tape u).map Sigma.fst
    · exact absurd ⟨e, inGarbler, asked, shown⟩ none
    · exact decide_eq_false_iff_not.mpr asked
  · have inReach := reached parameter scalar tape u e (List.mem_filter.mpr ⟨inGarbler, shown⟩)
    have asked : e.1 ∈ (reachedEntries E parameter scalar tape u).map Sigma.fst := List.mem_map_of_mem inReach
    by_contra ne
    exact decide_eq_false_iff_not.mp (Bool.eq_false_iff.mpr ne) asked

end Hidden

/-! ### 2. The five inputs, at `crtEntry` -/

/-- **Families 0 to 6**: a hidden conversion or body entry that the reach asks forces an input `Δ` to
be zero. -/
def CrtConvCoincide : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape crtEntry) (u : AffineInput) (e : Entry Empty Empty),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    HiddenReached crtEntry Entry.table parameter scalar tape u e → entryFamily e ≤ 6 →
      tape.1.inputDelta .x = 0 ∨ tape.1.inputDelta .y = 0

/-- **A zero input `Δ`**: its mass under the swapped tape, against every weight on the published value, is at most
`2/2^128`. -/
def CrtDeltaGuess : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) (scalar : NonZeroScalar),
    letI := field
    letI := group
    ∀ weight : crtEntry.Public → ℝ≥0∞,
      ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) *
            ind (tape.1.inputDelta .x = 0 ∨ tape.1.inputDelta .y = 0))
        ≤ ENNReal.ofReal (2 / 2 ^ 128) *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape)

/-- **Families 7 and 10**: no hidden mask or key entry is asked by the reach. -/
def CrtKeyMaskHidden : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape crtEntry) (u : AffineInput) (e : Entry Empty Empty),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    HiddenReached crtEntry Entry.table parameter scalar tape u e → entryFamily e ≠ 7 ∧ entryFamily e ≠ 10

/-- **Family 8**: no hidden digest label is asked by the reach (it asks only the part equal to `u`'s
bit). -/
def CrtLabelCoincide : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : TableTape crtEntry) (u : AffineInput) (e : Entry Empty Empty),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    HiddenReached crtEntry Entry.table parameter scalar tape u e → entryFamily e ≠ 8

/-- **Family 9**: a hidden digest final asked by the reach (`key(u)_o = key_o` with `u ≠ exc_o`) has mass
at most `91/2^128` under the swapped tape, against every weight on the published value. -/
def CrtFinalCoincide : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ) (scalar : NonZeroScalar)
    (u : AffineInput),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    ∀ weight : crtEntry.Public → ℝ≥0∞,
      ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) *
            ind (∃ e, HiddenReached crtEntry Entry.table parameter scalar tape u e ∧ entryFamily e = 9))
        ≤ ENNReal.ofReal (91 / 2 ^ 128) *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape)

/-! ### 3. The assembly -/

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind
  split <;> simp

theorem ind_of {P : Prop} (holds : P) : ind P = 1 := by
  unfold ind
  rw [if_pos holds]

/-- **`CrtCoincidenceGuess` at `crtEntry` from the five inputs.** -/
theorem crtCoincidenceGuess_of (conv : CrtConvCoincide) (delta : CrtDeltaGuess) (keyMask : CrtKeyMaskHidden)
    (label : CrtLabelCoincide) (final : CrtFinalCoincide) :
    CrtCoincidenceGuess crtEntry Entry.table (ENNReal.ofReal coincidenceError) := by
  intro field group parameter scalar u
  letI := field
  letI := group
  letI := @Fintype.ofFinite Empty inferInstance
  letI := Classical.decEq Empty
  intro weight
  -- a coincidence is a zero `Δ` or a hidden final
  have split : ∀ tape, coincideWeight crtEntry Entry.table parameter scalar tape u ≤
      ind (tape.1.inputDelta .x = 0 ∨ tape.1.inputDelta .y = 0) +
        ind (∃ e, HiddenReached crtEntry Entry.table parameter scalar tape u e ∧ entryFamily e = 9) := by
    intro tape
    unfold coincideWeight
    split
    · rename_i coincide
      obtain ⟨e, hidden⟩ := coincide_hiddenReached crtEntry Entry.table Align.crtEntry_designedReached parameter scalar
        tape u coincide
      obtain ⟨x, hash, small⟩ := Paths.crtEntry_garbler_small parameter scalar tape e hidden.1
      have family : entryFamily e = tagFamily (x.val / 2 ^ 128) := by
        obtain ⟨query, answer⟩ := e
        simp only at hash
        subst hash
        rfl
      by_cases low : entryFamily e ≤ 6
      · have zero := conv field group parameter scalar tape u e hidden low
        rw [ind_of zero]
        exact le_self_add
      · have notKey := keyMask field group parameter scalar tape u e hidden
        have notLabel := label field group parameter scalar tape u e hidden
        have nine : entryFamily e = 9 := by omega
        rw [ind_of (P := ∃ e, HiddenReached crtEntry Entry.table parameter scalar tape u e ∧ entryFamily e = 9)
          ⟨e, hidden, nine⟩]
        exact le_add_self
    · exact zero_le
  calc ∑' tape, swappedTableTape crtEntry tape *
        (weight (stageOneView crtEntry parameter scalar tape) *
          coincideWeight crtEntry Entry.table parameter scalar tape u)
      ≤ ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) *
            (ind (tape.1.inputDelta .x = 0 ∨ tape.1.inputDelta .y = 0) +
              ind (∃ e, HiddenReached crtEntry Entry.table parameter scalar tape u e ∧ entryFamily e = 9))) :=
        ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl (mul_le_mul' le_rfl (split tape))
    _ = ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) *
            ind (tape.1.inputDelta .x = 0 ∨ tape.1.inputDelta .y = 0)) +
        ∑' tape, swappedTableTape crtEntry tape *
          (weight (stageOneView crtEntry parameter scalar tape) *
            ind (∃ e, HiddenReached crtEntry Entry.table parameter scalar tape u e ∧ entryFamily e = 9)) := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun tape => ?_
        ring
    _ ≤ ENNReal.ofReal (2 / 2 ^ 128) *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) +
        ENNReal.ofReal (91 / 2 ^ 128) *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) :=
        add_le_add (delta field group parameter scalar weight) (final field group parameter scalar u weight)
    _ = ENNReal.ofReal (93 / 2 ^ 128) *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
    _ ≤ ENNReal.ofReal coincidenceError *
          ∑' tape, swappedTableTape crtEntry tape * weight (stageOneView crtEntry parameter scalar tape) := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        unfold coincidenceError frac
        norm_num

end

end Kriterion.CRT.Privacy.Flags
