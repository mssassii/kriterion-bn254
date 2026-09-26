/-
**P8, the flag guess for `crtEntry` and its shadow** (`H8.crtShadow`, `Core/H8.lean`).

`crtShadow`'s reveals are `rowsDoubling targets ∨ replayWraps source u (stateTable state)` on the curve and
`replayWraps source u (stateTable state)` off it, so `crtFlagGuess_of` applies with `D := rowsDoubling` and
`W := replayWraps ∘ stateTable` (`stateTable` reads only the hash table, so a merge into the empty state keeps it).

`crtFlagGuess_crt`: `CrtFlagGuess crtEntry crtShadow (smudgeError + exceptionalError)` from
* no abort (`CrtNoAbort`: the rows, preimage and fourth-block kernels always return, and a private collector program
  never fails; the last is a query-structure fact of the replay);
* the doubling bound in the form (`realRows`' mass of `rowsDoubling`, at most `exceptionalError`);
* the wrap bound on `M'`'s private run in the weight form (`CrtWrapGuess`, at most `smudgeError`).
-/

import Proof.Privacy.CRT.Flags.FlagSplit
import Proof.Privacy.CRT.Core.H8

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open scoped ENNReal

noncomputable section

/-- `stateTable` reads only the hash table: a merge into the empty state keeps it. -/
theorem stateTable_merge_empty {FI EI : Type} [DecidableEq FI] [DecidableEq EI] (state : LazyOracle.State FI EI) :
    stateTable (mergeState LazyOracle.empty state) = stateTable state := by
  unfold stateTable mergeState
  simp only [LazyOracle.empty, List.append_nil]
  rfl

/-- The doubling event on the rows, without instance arguments (`H8.rowsDoubling` carries unused ones). -/
def rowsZero (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) : Prop := ∃ d, (targets d).z = 0

/-- The wrap event on a private state. -/
def crtWrapOn [FieldCertificate] [GroupCertificate] (source : (viewHere crtEntry).Source) (u : AffineInput)
    (state : LazyOracle.State Empty Empty) : Prop :=
  replayWraps source u (stateTable state)

/-- **No abort** (P8): `M'`'s stage 2 at the empty stage-1 state, with no reveal, never flags. -/
def CrtNoAbort : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar)
    (source : (viewHere crtEntry).Source) (u : AffineInput),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    flagAt crtEntry (withReveal crtShadow fun _ _ _ => False) (tableRun (swappedTableLaw crtEntry.layout)) scalar
      source u = 0

/-- **The wrap guess** (P8): at every input, against every weight on the published value, `M'`'s unflagged final
private state has the wrap event with mass at most `smudgeError`. -/
def CrtWrapGuess : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar) (u : AffineInput),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    letI := (viewHere crtEntry).sourceFintype
    haveI := (viewHere crtEntry).sourceNonempty
    ∀ weight : crtEntry.Public → ℝ≥0∞,
      ∑' source, PMF.uniformOfFintype (viewHere crtEntry).Source source *
          (weight ((viewHere crtEntry).publish source) *
            wrapAt crtEntry crtShadow (tableRun (swappedTableLaw crtEntry.layout)) scalar source u crtWrapOn)
        ≤ ENNReal.ofReal smudgeError * ∑' source, PMF.uniformOfFintype (viewHere crtEntry).Source source *
            weight ((viewHere crtEntry).publish source)

/-- The doubling mass from the bound on the rows kernel. -/
theorem doublingAt_le [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput)
    (rows : ∀ Q, (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
      ((viewHere crtEntry).realRows scalar u Q).toOuterMeasure
          {r | ∃ targets, r = some targets ∧ rowsDoubling targets} ≤ ENNReal.ofReal exceptionalError) :
    doublingAt crtEntry scalar u rowsZero ≤ ENNReal.ofReal exceptionalError := by
  classical
  unfold doublingAt
  cases valid : (crtEntry.scheme inferInstance inferInstance).function scalar u with
  | none => exact zero_le
  | some Q =>
    dsimp only
    refine le_trans (le_of_eq ?_) (rows Q valid)
    rw [toOuterMeasure_eq_tsum]
    refine tsum_congr fun r => congrArg _ ?_
    rcases r with _ | targets
    · simp [rowsWeight]
    · by_cases event : rowsZero targets
      · have event' : rowsDoubling targets := event
        simp [rowsWeight, event, event']
      · have event' : ¬ rowsDoubling targets := event
        simp [rowsWeight, event, event']

/-- **`CrtFlagGuess` for `crtEntry` and `crtShadow`.** -/
theorem crtFlagGuess_crt (noAbort : CrtNoAbort)
    (rows : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar)
      (u : AffineInput),
      letI := field
      letI := group
      ∀ Q : Point, (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
        ((viewHere crtEntry).realRows scalar u Q).toOuterMeasure
          {r | ∃ targets, r = some targets ∧ rowsDoubling targets} ≤ ENNReal.ofReal exceptionalError)
    (wrap : CrtWrapGuess) :
    CrtFlagGuess crtEntry crtShadow (ENNReal.ofReal (smudgeError + exceptionalError)) := by
  have split := crtFlagGuess_of crtEntry crtShadow rowsZero @crtWrapOn
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (fun source u state => by unfold crtWrapOn; rw [stateTable_merge_empty])
    (ENNReal.ofReal exceptionalError) (ENNReal.ofReal smudgeError)
    (fun field group scalar source u => noAbort field group scalar source u)
    (fun field group scalar u => by
      letI := field
      letI := group
      exact doublingAt_le scalar u fun Q valid => rows field group scalar u Q valid)
    (fun field group scalar u => wrap field group scalar u)
  have nonnegS : 0 ≤ smudgeError := by unfold smudgeError; exact frac_nonneg _ _
  have nonnegE : 0 ≤ exceptionalError := by unfold exceptionalError; exact frac_nonneg _ _
  rw [ENNReal.ofReal_add nonnegS nonnegE, add_comm]
  convert split using 1

end

end Kriterion.CRT.Privacy.Flags
