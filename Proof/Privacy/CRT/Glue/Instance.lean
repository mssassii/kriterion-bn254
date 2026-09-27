/-
**The chain closed on the CRT entry, up to the rows it takes as hypotheses**.

Every row of `crt_privacy_of_named` that is proved for a generic entry is discharged here for `crtEntry`, through the
names of `Named.lean` (a row restated at `FI = EI = Empty` would collapse the instance binders; see `Named.lean`):

* H1 `CrtRealLazy`: from `GarblerTableFacts` (`crt_real_lazy_of_facts`, via `Laws.lazy_eq_real` and the challenge's
  uniform coin tape), at the entry with `crtEntry_garblerTableFacts`;
* H2 `CrtTableHop`: `Laws.crt_table_hop` with `crtEntry_garblerTableFacts`;
* H3 `CrtSwapHop`: `crtEntry_swap` (EntryInstance);
* H8 `CrtPublicFirstHop`: `crt_publicFirst_of_layout` (generic), `PublicFirst.crt_publicFirst_of_parts` with
  `CrtMiddleBelow` discharged by `crtMiddleBelow_of_layout` and the coincidence bound by
  `Flags.crtCoincidenceBound_of_guess`;
* H9 `CrtOpeningHop`: `crt_opening_of_rows` (generic: `HW` and `H` differ only in the rows kernel, so data processing
  bounds them by the kernels' distance at the adversary's input and output), at `crtEntry` with release-r1's
  `rows_etvDist_le` and `kernel_le_outputKernelError`;
* H10 `CrtRefillHop`: `crt_refill_of_layout` with `crtLayout_facts` and `crtEntry_replaySingleLabel`;
* H8's third swap: `crtEntry_thirdSwap`, `crtThirdSwap_of_tagged`, closed at the shadow by
  `crtShadow_offCurve_tagged` (`crtEntry_thirdSwap_closed`); `crtEntry_privacy_of_shadow` is the field at
  that shadow.

`crtEntry_privacy_of_open` is the privacy field of `Solution` for `crtEntry` from the rows it takes as hypotheses;
`Final.lean` proves them.
-/

import Proof.Privacy.CRT.EntryInstance
import Proof.Privacy.CRT.Laws.Table
import Proof.Privacy.CRT.Refill.Hop
import Proof.Privacy.CRT.PublicFirst.Obligation
import Proof.Privacy.CRT.PublicFirst.Layout
import Proof.Privacy.CRT.Flags.Coincidence
import Proof.Privacy.Phase3.OpeningBound
import Proof.Privacy.Phase3.Glue.RandomnessSplit
import Proof.Privacy.CRT.Paths.TableFacts
import Proof.Privacy.CRT.Flags.ThirdSwap
import Proof.Privacy.CRT.Paths.SingleLabel
import Proof.Privacy.CRT.Paths.Reach
import Proof.Privacy.CRT.Hidden.Reached

namespace Kriterion.CRT.Privacy.Instance

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le_const advantage_eq_etvDist)
open scoped ENNReal

noncomputable section

/-! ### Generic rows -/

/-- **H1 from the garbler's table facts**: the library's lazy real game of the entry is `G0`. -/
theorem crt_real_lazy_of_facts {FI EI : Type} [Finite FI] [Finite EI] (E : CrtEntry FI EI)
    (facts : Laws.GarblerTableFacts E) : CrtRealLazy E := by
  intro field group adversary parameter scalar
  let _coinsFintype : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
  have _coinsNonempty : Nonempty E.Coins := ⟨E.coinWitness⟩
  have tape : @uniformRandomTape E.Coins (@Fintype.ofFinite E.Coins E.coinsFinite) E.coinWitness
      = fun _ => PMF.uniformOfFintype E.Coins := by
    funext parameter
    rw [uniformRandomTape, Kriterion.Cryptography.uniformTape_eq]
  rw [tape]
  exact @Laws.lazy_eq_real FI EI field group (Fintype.ofFinite FI) (Fintype.ofFinite EI) (Classical.decEq FI)
    (Classical.decEq EI) E facts adversary parameter scalar

/-- **H9 from the rows kernels** (generic): if at every input and output of the scheme the real and simulated rows
kernels are within `outputKernelError`, then so are `HW` and `H`. -/
theorem crt_opening_of_rows {FI EI : Type} [Finite FI] [Finite EI] (E : CrtEntry FI EI)
    (close : ∀ [field : FieldCertificate] [group : GroupCertificate] (scalar : NonZeroScalar) (u : AffineInput)
      (target : Point), (E.scheme field group).function scalar u = some target →
      (((E.view field group).realRows scalar u target).etvDist ((E.view field group).simRows scalar u target))
        ≤ ENNReal.ofReal outputKernelError) :
    CrtOpeningHop E := by
  intro field group adversary parameter scalar _
  simp only [atSolution, crtChain]
  rw [advantage_eq_etvDist]
  refine ENNReal.toReal_le_of_le_ofReal (frac_nonneg _ _) ?_
  let _field := field
  let _group := group
  let _fintypeFI := Fintype.ofFinite FI
  let _fintypeEI := Fintype.ofFinite EI
  let _decFI := Classical.decEq FI
  let _decEI := Classical.decEq EI
  unfold publicFirstHybrid openedHybrid
  rw [Refill.abstractIdealGame_eq_staged, Refill.abstractIdealGame_eq_staged]
  unfold Refill.stagedGame
  refine etvDist_bind_left_le_const _ _ _ _ fun first => ?_
  rcases first with _ | ⟨circuit, state, oracle⟩
  · simp
  refine etvDist_bind_left_le_const _ _ _ _ fun selected => ?_
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  cases output : (E.scheme field group).function scalar selected.1.1 with
  | none => simp [routeMSimulator]
  | some target =>
      simp only [routeMSimulator]
      refine etvDist_bind_left_le_const _ _ _ _ fun ran => ?_
      exact le_trans (PMF.etvDist_bind_right_le _ _ _) (close scalar _ target output)

/-! ### The rows at the entry -/

/-- release-r1's `outputKernelError` is the CRT budget's. -/
theorem outputKernelError_eq : Kriterion.ArgoMAC.Phase3.Glue.outputKernelError = outputKernelError := by
  unfold Kriterion.ArgoMAC.Phase3.Glue.outputKernelError outputKernelError frac
  have same : BudgetData.r = scalarFieldModulus := by
    unfold BudgetData.r scalarFieldModulus
    rfl
  have one : 1 ≤ scalarFieldModulus := by
    unfold scalarFieldModulus
    norm_num
  rw [same, Nat.cast_sub one, Nat.cast_one]
  norm_num

/-- **H9 for the entry.** -/
theorem crtEntry_opening : CrtOpeningHop crtEntry := by
  refine crt_opening_of_rows crtEntry fun scalar u target output => ?_
  change (decodePoint u).map (scalarMultiplication scalar.value) = some target at output
  obtain ⟨point, decoded, rfl⟩ := Option.map_eq_some_iff.mp output
  have rows := Security.Phase3.rows_etvDist_le scalar u point decoded
  have finite : (455 * (Fintype.card Point : ℝ≥0∞)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  refine le_trans rows ?_
  rw [ENNReal.le_ofReal_iff_toReal_le finite (show 0 ≤ outputKernelError from frac_nonneg _ _),
    ← outputKernelError_eq]
  exact Security.Phase3.kernel_le_outputKernelError

/-- **H8 from its parts on the real layout** (generic): `M` below `HW` is `crtMiddleBelow_of_layout`, the coincidence
bound comes from the per-input guess. The guess comes before the shadow so that an instantiation never elaborates
the shadow against an expected type with instance binders. -/
theorem crt_publicFirst_of_layout {FI EI : Type} [Finite FI] [Finite EI] (E : CrtEntry FI EI)
    (layout : E.layout = crtLayout) (T : CrtTable)
    (guess : Flags.CrtCoincidenceGuess E T (ENNReal.ofReal coincidenceError))
    (shadow : ∀ [FieldCertificate] [GroupCertificate], PublicFirst.CrtShadow (PublicFirst.viewHere E).Source FI EI)
    (core : PublicFirst.CrtLiftCore E T shadow) (flag : PublicFirst.CrtFlagMass E shadow)
    (swap : PublicFirst.CrtThirdSwap E shadow) : CrtPublicFirstHop E :=
  PublicFirst.crt_publicFirst_of_parts E T shadow (Flags.crtCoincidenceBound_of_guess E T guess) core
    (PublicFirst.crtMiddleBelow_of_layout E layout shadow) flag swap

/-! ### The rows at the entry

At `FI = EI = Empty` a hypothesis whose type unfolds to instance binders (`CrtLiftCore`, the shadow) must be passed
with `@`: otherwise the elaborator instantiates its binders by instance search, where the two `Fintype Empty` (and
`DecidableEq Empty`) slots collapse to one local instance, and the unifier times out comparing the result with the
generic statement. -/

/-- The entry's layout is the real one. -/
theorem crtEntry_layout : crtEntry.layout = crtLayout := rfl

/-- **H1 for the entry** (`crtEntry_garblerTableFacts`). -/
theorem crtEntry_real : CrtRealLazy crtEntry :=
  crt_real_lazy_of_facts crtEntry Paths.crtEntry_garblerTableFacts

/-- **H2 for the entry** (`crtEntry_garblerTableFacts`). -/
theorem crtEntry_table : CrtTableHop crtEntry :=
  Laws.crt_table_hop crtEntry Paths.crtEntry_garblerTableFacts

/-- **H10 for the entry**, from `ReplaySingleLabel` (its `answers_le` field is `crtLayout_answers_le`). -/
theorem crtEntry_refill (single : ReplaySingleLabel crtEntry) : CrtRefillHop crtEntry :=
  crt_refill_of_layout crtEntry crtLayout_facts single

/-- **H10 for the entry, closed** (`crtEntry_replaySingleLabel`). -/
theorem crtEntry_refill_closed : CrtRefillHop crtEntry :=
  crtEntry_refill Paths.crtEntry_replaySingleLabel

/-- **H8 for the entry**, from the coincidence guess, the core, the flag mass and the third swap. -/
theorem crtEntry_publicFirst (T : CrtTable)
    (guess : Flags.CrtCoincidenceGuess crtEntry T (ENNReal.ofReal coincidenceError))
    (shadow : ∀ [FieldCertificate] [GroupCertificate], PublicFirst.CrtShadow (PublicFirst.viewHere crtEntry).Source
      Empty Empty)
    (core : PublicFirst.CrtLiftCore crtEntry T shadow) (flag : PublicFirst.CrtFlagMass crtEntry shadow)
    (swap : PublicFirst.CrtThirdSwap crtEntry shadow) : CrtPublicFirstHop crtEntry :=
  crt_publicFirst_of_layout crtEntry crtEntry_layout T guess @shadow @core @flag @swap

/-- **The third swap for the entry** (`crtThirdSwap_of_tagged` with `crtLayout_facts`), from `Tagged` fact for the shadow's off-curve program. -/
theorem crtEntry_thirdSwap
    (shadow : ∀ [FieldCertificate] [GroupCertificate], PublicFirst.CrtShadow (PublicFirst.viewHere crtEntry).Source
      Empty Empty)
    (tagged : ∀ [FieldCertificate] [GroupCertificate] (source : (PublicFirst.viewHere crtEntry).Source)
      (u : AffineInput) (coin : shadow.Coin), ∃ S : Set Paths.TagKey, Paths.Tagged S (shadow.offCurve source u coin)) :
    PublicFirst.CrtThirdSwap crtEntry shadow :=
  Flags.crtThirdSwap_of_tagged crtEntry crtLayout_facts @shadow @tagged

/-- **The privacy field of `Solution` for the CRT entry from the rows it takes as hypotheses**: the hidden hop's rows (H5 to H7),
the public-first parts (H8: the coincidence guess, the shadow, the core, the flag mass, the third swap) and the machine
law (H11). H1, H2, H3, H9 and H10 are proved, and in H8 `M` below `HW`. -/
theorem crtEntry_privacy_of_open (T : CrtTable) (simulator : BoundedMachine.Simulator)
    (reached : DesignedReached crtEntry T)
    (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess crtEntry T (ENNReal.ofReal crtHiddenCharge) (ENNReal.ofReal hiddenWindowError))
    (guess : Flags.CrtCoincidenceGuess crtEntry T (ENNReal.ofReal coincidenceError))
    (shadow : ∀ [FieldCertificate] [GroupCertificate], PublicFirst.CrtShadow (PublicFirst.viewHere crtEntry).Source
      Empty Empty)
    (core : PublicFirst.CrtLiftCore crtEntry T shadow) (flag : PublicFirst.CrtFlagMass crtEntry shadow)
    (swap : PublicFirst.CrtThirdSwap crtEntry shadow)
    (machine : CrtMachineHop crtEntry simulator) : CrtPrivacy crtEntry :=
  crtEntry_privacy_of T simulator crtEntry_real crtEntry_table @reached @one @two
    (crtEntry_publicFirst T guess @shadow @core @flag @swap) crtEntry_opening crtEntry_refill_closed @machine

/-- **The third swap for the entry's shadow, closed** (`crtShadow_offCurve_tagged`). -/
theorem crtEntry_thirdSwap_closed : PublicFirst.CrtThirdSwap crtEntry @H8.crtShadow :=
  crtEntry_thirdSwap @H8.crtShadow @Paths.crtShadow_offCurve_tagged

/-- **The privacy field of `Solution` for the CRT entry at the shadow**: the hidden hop's rows (H5 to H7),
H8's coincidence guess, core and flag mass at `H8.crtShadow`, and the machine law (H11). H1, H2, H3, H9, H10 and H8's
third swap and `M` below `HW` are proved. -/
theorem crtEntry_privacy_of_shadow (T : CrtTable) (simulator : BoundedMachine.Simulator)
    (reached : DesignedReached crtEntry T)
    (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess crtEntry T (ENNReal.ofReal crtHiddenCharge) (ENNReal.ofReal hiddenWindowError))
    (guess : Flags.CrtCoincidenceGuess crtEntry T (ENNReal.ofReal coincidenceError))
    (core : PublicFirst.CrtLiftCore crtEntry T @H8.crtShadow) (flag : PublicFirst.CrtFlagMass crtEntry @H8.crtShadow)
    (machine : CrtMachineHop crtEntry simulator) : CrtPrivacy crtEntry :=
  crtEntry_privacy_of_open T simulator @reached @one @two guess @H8.crtShadow @core @flag crtEntry_thirdSwap_closed
    @machine

/-- **The privacy field of `Solution` for the CRT entry at the real table and the shadow**: H5 is `crtEntry_designedReached`. Taken as hypotheses (proved in `Final.lean`): the stage guesses (H6, H7), H8's coincidence guess, core and flag mass at
`H8.crtShadow`, and the machine law (H11). -/
theorem crtEntry_privacy_of_table (simulator : BoundedMachine.Simulator)
    (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess crtEntry Entry.table (ENNReal.ofReal crtHiddenCharge)
      (ENNReal.ofReal hiddenWindowError))
    (guess : Flags.CrtCoincidenceGuess crtEntry Entry.table (ENNReal.ofReal coincidenceError))
    (core : PublicFirst.CrtLiftCore crtEntry Entry.table @H8.crtShadow)
    (flag : PublicFirst.CrtFlagMass crtEntry @H8.crtShadow)
    (machine : CrtMachineHop crtEntry simulator) : CrtPrivacy crtEntry :=
  crtEntry_privacy_of_shadow Entry.table simulator @Align.crtEntry_designedReached @one @two guess @core @flag
    @machine

end

end Kriterion.CRT.Privacy.Instance
