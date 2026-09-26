/-
**P7, the public-first hop `G1U → HW`, part 1: `G1U` read with an installation rule, and the designed hop
`G1U → G1U°`** (port of xinshu's `PublicFirst/Lift.lean` section 2 and `PublicFirst/LiftHop.lean` sections 1 and 2 to
the CRT games of `Hybrids.lean`; hash-only, so nothing is planted before the input choice and `G1U`'s later form is
`G1U` itself).

* `InstallRule`: the garbler entries installed at the input choice, from the tape and the input.
* `stageOneLaw`, `stageTwoWith`, `hiddenDeletedWith`: `G1U` split at the input choice and read with a rule;
  `hiddenDeleted_eq_visible`: the reach's rule `visibleRule` gives `G1U` (`hiddenDeletedHybrid`).
* `designedRule T`: the designed-visible garbler entries of the hidden hop (`designedEntries`, rule `crtDesigned`);
  `hiddenDesignedHybrid T` (`G1U°`).
* `Coincide`, `coincidenceMass`: the reach's entries are not the designed ones, and its mass under `G1U`'s stage 1;
  `designed_hop_le`: `advantage(G1U, G1U°) ≤ coincidenceMass` (identical until the coincidence event).
-/

import Proof.Privacy.CRT.Statements
import Proof.Privacy.CRT.PublicFirst.Overlap

namespace Kriterion.CRT.Privacy.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open scoped ENNReal

noncomputable section

/-! ### 1. Two continuations that agree off an event (xinshu's `LiftHop.lean`, generic) -/

theorem bind_le_add_bad {A : Type} (μ : PMF A) (f g : A → PMF Bool) (bad : Set A)
    (agree : ∀ a, a ∉ bad → f a = g a) (b : Bool) :
    (μ.bind f) b ≤ (μ.bind g) b + μ.toOuterMeasure bad := by
  rw [PMF.bind_apply, PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases inside : a ∈ bad
  · rw [Set.indicator_of_mem inside]
    exact le_trans (mul_le_of_le_one_right' (PMF.coe_le_one _ _)) le_add_self
  · rw [Set.indicator_of_notMem inside, add_zero, agree a inside]

/-- **Identical until bad**: two continuations of one law that agree off an event are within its mass. -/
theorem advantage_le_of_agree {A : Type} (μ : PMF A) (f g : A → PMF Bool) (bad : Set A)
    (agree : ∀ a, a ∉ bad → f a = g a) :
    Assumptions.advantage (μ.bind f) (μ.bind g) ≤ (μ.toOuterMeasure bad).toReal := by
  have finite : μ.toOuterMeasure bad ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [PMF.toOuterMeasure_apply]
    exact le_trans (ENNReal.tsum_le_tsum fun a => Set.indicator_le_self bad (⇑μ) a)
      (le_of_eq μ.tsum_coe)
  have one := bind_le_add_bad μ f g bad agree true
  have two := bind_le_add_bad μ g f bad (fun a outside => (agree a outside).symm) true
  have r1 : ((μ.bind f) true).toReal ≤ ((μ.bind g) true).toReal + (μ.toOuterMeasure bad).toReal := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) finite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, finite⟩) one
  have r2 : ((μ.bind g) true).toReal ≤ ((μ.bind f) true).toReal + (μ.toOuterMeasure bad).toReal := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) finite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, finite⟩) two
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

/-! ### 2. `G1U` read with an installation rule -/

variable {FI EI : Type} (E : CrtEntry FI EI)

section Rules

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **An installation rule**: the garbler entries installed at the input choice, from the parameter, the scalar,
the tape and the input. -/
abbrev InstallRule := ℕ → NonZeroScalar → TableTape E → AffineInput → List (Entry FI EI)

open Classical in
/-- **The reach's rule** (`G1U`'s own): the garbler entries whose query the honest evaluator asks at the input. -/
def visibleRule : InstallRule E := fun parameter scalar tape u =>
  let oracle : PublicOracle FI EI := tableOracle tape.2
  let scheme := E.scheme inferInstance inferInstance
  let garbled := scheme.garble parameter scalar (tape.1, oracle)
  let entries := programTranscript (publicAnswer oracle)
    (E.garbleProgram inferInstance inferInstance parameter scalar tape.1)
  let labels := scheme.encode garbled.2 u
  let reach := programTranscript (publicAnswer oracle)
    (E.reachProgram inferInstance inferInstance garbled.1 u labels)
  entries.filter fun entry => decide (entry.1 ∈ reach.map Sigma.fst)

/-- **The designed rule**: the garbler entries `crtDesigned` keeps at the input (`designedEntries`). -/
def designedRule (T : CrtTable) : InstallRule E := fun parameter scalar tape u =>
  designedEntries E T parameter scalar tape u

/-- `G1U`'s stage 1: the tape and the adversary's stage-1 outcome on the empty oracle. -/
def stageOneLaw (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ) (scalar : NonZeroScalar) :
    PMF (TableTape E × ((AffineInput × adversary.State) × LazyOracle.State FI EI)) :=
  (swappedTableTape E).bind fun tape =>
    let oracle : PublicOracle FI EI := tableOracle tape.2
    let garbled := (E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, oracle)
    (LazyOracle.run (adversary.chooseInput parameter garbled.1 ()) LazyOracle.empty).map
      fun selected => (tape, selected)

/-- `G1U`'s stage 2 read with a rule. -/
def stageTwoWith (rule : InstallRule E) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar)
    (x : TableTape E × ((AffineInput × adversary.State) × LazyOracle.State FI EI)) : PMF Bool :=
  let oracle : PublicOracle FI EI := tableOracle x.1.2
  let scheme := E.scheme inferInstance inferInstance
  let garbled := scheme.garble parameter scalar (x.1.1, oracle)
  let labels := scheme.encode garbled.2 x.2.1.1
  (LazyOracle.run (adversary.decide parameter garbled.1 labels () x.2.1.2)
    (installEntries (rule parameter scalar x.1 x.2.1.1) x.2.2)).map Prod.fst

/-- **`G1U` read with an installation rule.** -/
def hiddenDeletedWith (rule : InstallRule E) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) : PMF Bool :=
  (stageOneLaw E adversary parameter scalar).bind (stageTwoWith E rule adversary parameter scalar)

/-- **The reach's rule is `G1U`.** -/
theorem hiddenDeleted_eq_visible (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    hiddenDeletedHybrid E adversary parameter scalar =
      hiddenDeletedWith E (visibleRule E) adversary parameter scalar := by
  unfold hiddenDeletedHybrid hiddenDeletedWith stageOneLaw
  rw [PMF.bind_bind]
  congr 1
  funext tape
  rw [PMF.bind_map]
  rfl

/-- **The coincidence event** at an input: the reach's entries are not the designed ones (the reach meets a
garbler point the designed rule hides). -/
def Coincide (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput) :
    Prop :=
  visibleRule E parameter scalar tape u ≠ designedRule E T parameter scalar tape u

/-- Its mass under `G1U`'s stage 1 (the input is the adversary's). -/
def coincidenceMass (T : CrtTable) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) : ℝ≥0∞ :=
  (stageOneLaw E adversary parameter scalar).toOuterMeasure
    {x | Coincide E T parameter scalar x.1 x.2.1.1}

/-- **The designed hop `G1U → G1U°`**: identical until a coincidence. -/
theorem designed_hop_le (T : CrtTable) (adversary : ChainAdversary FI EI E.Public) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    Assumptions.advantage (hiddenDeletedHybrid E adversary parameter scalar)
        (hiddenDeletedWith E (designedRule E T) adversary parameter scalar)
      ≤ (coincidenceMass E T adversary parameter scalar).toReal := by
  rw [hiddenDeleted_eq_visible]
  refine advantage_le_of_agree _ _ _ _ fun x outside => ?_
  have same : visibleRule E parameter scalar x.1 x.2.1.1 = designedRule E T parameter scalar x.1 x.2.1.1 := by
    by_contra different
    exact outside different
  unfold stageTwoWith
  rw [same]

end Rules

/-- **`G1U°`**: `G1U` with the designed entries installed at the input choice. -/
def hiddenDesignedHybrid (T : CrtTable) : ChainGame FI EI E.Public := fun adversary parameter scalar =>
  hiddenDeletedWith E (designedRule E T) adversary parameter scalar

end

end Kriterion.CRT.Privacy.PublicFirst
