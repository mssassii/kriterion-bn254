/-
**The decomposition of H8, the core of `G1U → HW`**. It is the target for
the parts P3, P5a, P6a2, P6b1, P6b2, P7 and P8.

`PublicFirst/Obligation.lean` reduces `CrtPublicFirstHop` to five rows, one of which is the per-input
core `PublicFirst.CrtLiftCore E T shadow`. This file splits that row into three factor rows and proves the split
(`crtLiftCore_of_factors`, no `sorry`):

* **the view.** At an input `u`, `G1U°`'s stage 2 depends on the tape only through
  `CoreView E T u = Public × LamportSignature × (VisTags T u → Block × Block)`: the published value, the labels of
  `u`, and the table at the tags the designed rule shows at `u` (`visTag`; `crtDesigned_eq_visTag` checks it). The
  stage 2 run from a view is `viewWeight`: install the reach's entries at the visible tags, read on the view's table,
  and run the adversary's stage 2.
* **`CrtUpperFactor` (P6a2).** `G1U°`'s stage-2 mass is at least the law of the view (`realCore`, flagged
  on doubling) integrated against `viewWeight`.
* **`CrtMiddleFactor` (P6b1, P6b2, P7).** `M'`'s stage-2 mass is at most the law of the
  ideal view (`idealAt`) integrated against `viewWeight`. The ideal view is route M's: a uniform source, a swapped table
  read through `tagHash`, the collector answers programmed from the solve, flagged by the reveal.
* **`CrtCoreBelow` (the product over families).** At every view, the ideal law is below the real one. It splits into
  four statements for the concrete entry (section 5); the composition `crtCoreBelow_of_parts` is in `Core/CoreBelow.lean`:

| part of the view | statement | owner |
|---|---|---|
| `crtX`, `crtY` | `CrtConvSplit κ`: uniform, independent of everything off the hot conversion tags of `κ` | P3 |
| `exception` | `CrtDigestSplit`: off doubling, uniform, independent of everything off the finals, the other digest bit and the exception pads | P5a |
| rows, curve, records, tags of families 6, 7, 10 | `CrtBmrSplit`: route M's law, off the reveal (P45: `BMR.bmr_core`) | P45 |
| labels, tags of families 0 to 5 and 8 | `CrtRestSplit`: uniform labels and table, independent | P2b, P6 |

**The shadow**: no coins; on the curve the reach's digest (labels and finals, which `HW`
does not replay, F6); off the curve the reach off the curve (conversion blocks and digest; changes 6 and 14). The reveal is a function of the ideal view
and the target rows: doubling (a target row with `Z = 0`) or wrap (a CRT value within `B − 1` of either end of
`[0, M)`: the two-sided window, because the ideal side cannot see `a_e v`).

The table tape is `coins × tag table`, and the key is the family-10 tag, visible iff on the
curve.
-/

import Proof.Privacy.CRT.EntryInstance
import Proof.Privacy.CRT.PublicFirst.Obligation
import Proof.Correctness.CRT.Record

namespace Kriterion.CRT.Privacy.H8

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT
open Kriterion.CRT.Privacy.PublicFirst
open scoped ENNReal

noncomputable section

/-! ### 1. The visible tags -/

/-- **The tags `crtDesigned` shows at `u` off the doubling event**: cold conversion and body positions, the masks and
the key on the curve, the digest labels of `u`'s bits; never a digest final. -/
def visTag (T : CrtTable) (u : AffineInput) (tag : ℕ) : Bool :=
  match tagFamily tag with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => !hotTag T u tag
  | 7 => validate u
  | 8 => tagPart tag == inputBit u (tagCoord tag) (tagSlot tag)
  | 10 => validate u
  | _ => false

/-- The visible tags at `u`. -/
abbrev VisTags (T : CrtTable) (u : AffineInput) := {tag : Fin (2 ^ 40) // visTag T u tag.val = true}

/-- **The designed rule is the tag reading** off the doubling event (every family a garbler tag can have). -/
theorem crtDesigned_eq_visTag {FI EI Coins Oracle : Type} (T : CrtTable) (view : TapeView Coins Oracle)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) (u : AffineInput) (x : BaseField) (answer : Block × Block)
    (small : tagFamily (x.val / 2 ^ 128) ≤ 10) (noDoubling : ∀ o, view.exceptional scalar tape o ≠ some u) :
    crtDesigned (FI := FI) (EI := EI) T view scalar tape u ⟨.hash x, answer⟩ = visTag T u (x.val / 2 ^ 128) := by
  unfold crtDesigned visTag
  dsimp only
  generalize hfam : tagFamily (x.val / 2 ^ 128) = fam at small
  interval_cases fam <;> simp [noDoubling]

/-- A tag table read as a hash of the layer (every labelled input answered by its tag). -/
def tagHash (table : TagTable) : HashN := fun n => table ⟨n / 2 ^ 128 % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- The tag of answer `j` of collector site `k` (`collectorPoint`'s tag). -/
def collectorTag (k j : ℕ) : Fin (2 ^ 40) :=
  ⟨tagCode Family.mask 0 0 0 0 k j % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- The table with the collector answers programmed (`programRequests`'s answers at their tags). -/
def programmedTable (table : TagTable) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    TagTable :=
  drawn.foldl (fun current entry =>
    let k := collectorIndex entry.1
    let limbs := entry.2.1
    Function.update (Function.update current (collectorTag k 0) (limbs.1, limbs.2.1)) (collectorTag k 1)
      (limbs.2.2, entry.2.2)) table

/-! ### 2. The two view laws, for a generic entry -/

variable {FI EI : Type} (E : CrtEntry FI EI)

/-- The per-input view: the published value, the labels of `u`, the answers at the visible tags. -/
abbrev CoreView (T : CrtTable) (u : AffineInput) := E.Public × LamportSignature × (VisTags T u → Block × Block)

/-- The doubling event: `u` is the exceptional input of a digit. -/
def Doubling (scalar : NonZeroScalar) (tape : TableTape E) (u : AffineInput) : Prop :=
  ∃ o, E.exceptional scalar tape.1 o = some u

section Laws

variable [FieldCertificate] [GroupCertificate]

/-- The real garbling on a table tape. -/
def realGarbled (parameter : ℕ) (scalar : NonZeroScalar) (tape : TableTape E) : E.Public × E.Key :=
  (E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, tableOracle tape.2)

/-- **The real view** of a tape at `u`. -/
def realView (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (tape : TableTape E) :
    CoreView E T u :=
  ((realGarbled E parameter scalar tape).1,
    (E.scheme inferInstance inferInstance).encode (realGarbled E parameter scalar tape).2 u, fun tag => tape.2 tag.1)

open Classical in
/-- **`G1U°`'s side**: the real view under the swapped tape, flagged on the doubling event. -/
def realCore (T : CrtTable) (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) :
    PMF (Option (CoreView E T u)) :=
  (swappedTableTape E).map fun tape =>
    if Doubling E scalar tape u then none else some (realView E T parameter scalar u tape)

/-- Route M's collector draws (preimages and fourth blocks; any abort aborts). -/
def collectorDrawsOf (masks : BMR.Collector → BaseField) :
    PMF (Option (List (BMR.Collector × ((Block × Block × Block) × Block)))) :=
  drawAll (fun c => ((viewHere E).preimage (masks c)).bind fun limbs => match limbs with
      | none => PMF.pure none
      | some limbs => (viewHere E).fourth.map (Option.map fun fourth => (limbs, fourth)))
    collectorList

open Classical in
/-- **`M'`'s side on the curve** (output `Q`): a uniform source, a swapped table read through `tagHash`, the target
rows, the collector answers programmed from the solve; flagged by the reveal (which reads the source, the target rows
and the programmed table) and by an abort. -/
def idealCore (T : CrtTable)
    (reveal : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (scalar : NonZeroScalar) (u : AffineInput) (Q : Point) : PMF (Option (CoreView E T u)) :=
  letI := (viewHere E).sourceFintype
  haveI := (viewHere E).sourceNonempty
  (PMF.uniformOfFintype (viewHere E).Source).bind fun source =>
    (swappedTableLaw E.layout).bind fun table =>
      let published := (viewHere E).publish source
      let labels := (viewHere E).labels source u
      let out := ((viewHere E).replayProgram published u labels).eval (tagHash table)
      ((viewHere E).realRows scalar u Q).bind fun drawnRows => match drawnRows with
        | none => PMF.pure none
        | some targets =>
          (collectorDrawsOf E (collectorMasks u out ((viewHere E).gammaOf published) targets)).map fun drawn =>
            match drawn with
            | none => none
            | some drawn =>
              if reveal source u targets (programmedTable table drawn) then none
              else some (published, labels, fun tag => programmedTable table drawn tag.1)

open Classical in
/-- **`M'`'s side off the curve**: a uniform source and a swapped table, flagged by the reveal. -/
def idealCoreOff (T : CrtTable) (reveal : (viewHere E).Source → AffineInput → TagTable → Prop) (u : AffineInput) :
    PMF (Option (CoreView E T u)) :=
  letI := (viewHere E).sourceFintype
  haveI := (viewHere E).sourceNonempty
  (PMF.uniformOfFintype (viewHere E).Source).bind fun source =>
    (swappedTableLaw E.layout).map fun table =>
      if reveal source u table then none
      else some ((viewHere E).publish source, (viewHere E).labels source u, fun tag => table tag.1)

/-- The ideal view law at `u`: `idealCore` on the curve, `idealCoreOff` off it. -/
def idealAt (T : CrtTable)
    (revealOn : (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop)
    (revealOff : (viewHere E).Source → AffineInput → TagTable → Prop) (scalar : NonZeroScalar) (u : AffineInput) :
    PMF (Option (CoreView E T u)) :=
  match (E.scheme inferInstance inferInstance).function scalar u with
  | some Q => idealCore E T revealOn scalar u Q
  | none => idealCoreOff E T revealOff u

end Laws

/-- A reveal on the curve, at every instance. -/
abbrev RevealOn (E : CrtEntry FI EI) : Type :=
  ∀ [FieldCertificate] [GroupCertificate],
    (viewHere E).Source → AffineInput → (Fin 91 → FieldMacToECMac.HomogeneousValue) → TagTable → Prop

/-- A reveal off the curve, at every instance. -/
abbrev RevealOff (E : CrtEntry FI EI) : Type :=
  ∀ [FieldCertificate] [GroupCertificate], (viewHere E).Source → AffineInput → TagTable → Prop

/-- **H8's core row**: at every input and view, the ideal flagged law is below the real one. -/
def CrtCoreBelow (T : CrtTable) (revealOn : RevealOn E) (revealOff : RevealOff E) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput)
    (v : CoreView E T u),
    idealAt E T revealOn revealOff scalar u (some v) ≤ realCore E T parameter scalar u (some v)

/-! ### 3. The stage 2 run from a view, and the two factor rows -/

section Weights

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- The view's table, with `(0, 0)` off the visible tags. -/
def viewTable (T : CrtTable) (u : AffineInput) (v : CoreView E T u) : TagTable :=
  fun tag => if visible : visTag T u tag.val = true then v.2.2 ⟨tag, visible⟩ else (0, 0)

/-- **The entries a view installs**: the reach's transcript at `u` on the view's table, at the visible tags. -/
def viewEntries (T : CrtTable) (u : AffineInput) (v : CoreView E T u) : List (Entry FI EI) :=
  (programTranscript (publicAnswer (tableOracle (FI := FI) (EI := EI) (viewTable E T u v)))
    (E.reachProgram inferInstance inferInstance v.1 u v.2.1)).filter fun entry =>
      match entry.1 with
      | .hash x => visTag T u (x.val / 2 ^ 128)
      | _ => false

/-- **The stage-2 weight of a view**: the adversary's stage 2 on the stage-1 state with the view's entries installed. -/
def viewWeight (T : CrtTable) (u : AffineInput) (v : CoreView E T u) (planted : LazyOracle.State FI EI)
    {budget : ℕ} (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (b : Bool) : ℝ≥0∞ :=
  ((LazyOracle.run (decide v.1 v.2.1) (installEntries (viewEntries E T u v) planted)).map Prod.fst) b

end Weights

/-- **P6a2**: `G1U°`'s stage-2 mass, averaged over the swapped tape, is at least the real view law
integrated against the view's stage-2 weight. -/
def CrtUpperFactor (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (planted : LazyOracle.State FI EI) (budget : ℕ)
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool),
    ∑' v, realCore E T parameter scalar u (some v) * (weight v.1 * viewWeight E T u v planted decide b)
      ≤ ∑' tape, swappedTableTape E tape *
        (weight ((E.scheme inferInstance inferInstance).garble parameter scalar (tape.1, tableOracle tape.2)).1 *
          upperWeight E T parameter scalar tape u planted decide b)

/-- **P6b1, P6b2 and P7**: `M'`'s flag-down stage-2 mass, averaged over the source, is at
most the ideal view law integrated against the view's stage-2 weight. -/
def CrtMiddleFactor (T : CrtTable) (shadow : ∀ [FieldCertificate] [GroupCertificate],
      CrtShadow (viewHere E).Source FI EI) (revealOn : RevealOn E) (revealOff : RevealOff E) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
    (scalar : NonZeroScalar) (u : AffineInput) (planted : LazyOracle.State FI EI) (budget : ℕ)
    (decide : E.Public → LamportSignature → OracleProgram (publicOracleSpec FI EI) Bool budget)
    (weight : E.Public → ℝ≥0∞) (b : Bool),
    (letI := (viewHere E).sourceFintype
     haveI := (viewHere E).sourceNonempty
     ∑' source, PMF.uniformOfFintype (viewHere E).Source source *
        (weight ((viewHere E).publish source) *
          middleWeight E shadow (tableRun (swappedTableLaw E.layout)) scalar source u planted decide b))
      ≤ ∑' v, idealAt E T revealOn revealOff scalar u (some v) * (weight v.1 * viewWeight E T u v planted decide b)

/-- **The split of the per-input core**: the middle factor, the core row and the upper factor give
`CrtLiftCore`. -/
theorem crtLiftCore_of_factors (T : CrtTable) (shadow : ∀ [FieldCertificate] [GroupCertificate],
      CrtShadow (viewHere E).Source FI EI) (revealOn : RevealOn E) (revealOff : RevealOff E)
    (middle : CrtMiddleFactor E T shadow revealOn revealOff) (core : CrtCoreBelow E T revealOn revealOff)
    (upper : CrtUpperFactor E T) : CrtLiftCore E T shadow := by
  intro _ _ _ _ _ _ parameter scalar u planted budget decide weight b
  refine le_trans (middle scalar u planted budget decide weight b) (le_trans ?_
    (upper parameter scalar u planted budget decide weight b))
  exact ENNReal.tsum_le_tsum fun v => by gcongr; exact core parameter scalar u v

/-! ### 4. The shadow of `crtEntry` -/

section Shadow

open Kriterion.CRT.Privacy.Instance

variable [FieldCertificate] [GroupCertificate]

/-- On the curve: the reach's digest (labels, then finals), which `HW` does not replay (F6). -/
def crtShadowOnCurve (source : (view).Source) (u : AffineInput) : CM Unit :=
  digestEvalM coordinateBitCount digitCount (Kriterion.CRT.Entry.labelsOf ((view).labels source u)) u
    (fun o => ((view).publish source).exception.get o) >>= fun _ => pure ()

/-- Off the curve: the reach off the curve, the conversion blocks and the digest (changes 6 and 14). -/
def crtShadowOffCurve (source : (view).Source) (u : AffineInput) : CM Unit :=
  Kriterion.CRT.EntryReading.reachOffCM ((view).publish source) u ((view).labels source u) >>= fun _ => pure ()

/-- The doubling reveal: a target row with `Z = 0` (at `u = exc_o` the incomplete addition's `Z` vanishes, and also
at the negated offset; its mass is `exceptionalError`). -/
def rowsDoubling (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) : Prop :=
  ∃ d, (targets d).z = 0 ∨ (targets d).y = 0

/-- The CRT values `w_e` of both coordinates, as the replay computes them on a table. -/
def replayCrtValues (source : (view).Source) (u : AffineInput) (table : TagTable) :
    (Fin Kriterion.CRT.Entry.xCount → ℕ) × (Fin Kriterion.CRT.Entry.yCount → ℕ) :=
  let published := (view).publish source
  let labels := (view).labels source u
  (((coordEvalM Kriterion.CRT.Entry.table Kriterion.CRT.Entry.xCount 0 (Kriterion.CRT.Entry.convOf published.crtX)
      (fun e => (published.recX.get e).val) u.x.val (fun i => clip (Kriterion.CRT.Entry.labelX labels i))).eval (tagHash table)).crtValue,
    ((coordEvalM Kriterion.CRT.Entry.table Kriterion.CRT.Entry.yCount 1 (Kriterion.CRT.Entry.convOf published.crtY)
      (fun e => (published.recY.get e).val) u.y.val (fun i => clip (Kriterion.CRT.Entry.labelY labels i))).eval (tagHash table)).crtValue)

/-- A CRT value in the two-sided wrap window `[0, B − 1) ∪ (M − B, M)`: the image, under the smudge bijection, of every
real offset with the hint set (`O > M − B` gives `w = O + a v ∈ (M − B, M)` or `w = O + a v − M < a v ≤ B − 1`). -/
def inWrapWindow (w : ℕ) : Prop :=
  w + 1 < Kriterion.CRT.Entry.table.wrapBound ∨
    Kriterion.CRT.Entry.table.product - Kriterion.CRT.Entry.table.wrapBound < w

/-- The wrap reveal: some encoding's CRT value in the two-sided window. -/
def replayWraps (source : (view).Source) (u : AffineInput) (table : TagTable) : Prop :=
  (∃ e, inWrapWindow ((replayCrtValues source u table).1 e)) ∨
    ∃ e, inWrapWindow ((replayCrtValues source u table).2 e)

end Shadow

/-- The reveal on the curve: doubling or wrap. -/
def crtRevealOn : RevealOn Kriterion.CRT.Privacy.Instance.crtEntry := fun source u targets table =>
  rowsDoubling targets ∨ replayWraps source u table

/-- The reveal off the curve: wrap. -/
def crtRevealOff : RevealOff Kriterion.CRT.Privacy.Instance.crtEntry := fun source u table =>
  replayWraps source u table

/-- The table a private state holds, read by tag (the first stored point with that tag; `(0, 0)` if none). -/
def stateTable {FI EI : Type} [DecidableEq FI] [DecidableEq EI] (state : LazyOracle.State FI EI) : TagTable :=
  fun tag => ((state.hash.find? fun pair => decide (tagOfInput pair.1 = tag)).bind fun pair =>
    LazyOracle.lookup (.hash pair.1) state).getD (0, 0)

/-- **The shadow of `crtEntry`**: no coins; the reach's digest on the curve, the reach off it; the reveals read the
private state's table. -/
def crtShadow : ∀ [FieldCertificate] [GroupCertificate],
    CrtShadow (viewHere Kriterion.CRT.Privacy.Instance.crtEntry).Source Empty Empty := fun {_ _} =>
  { Coin := Unit
    law := PMF.pure ()
    onCurve := fun source u _ => crtShadowOnCurve source u
    offCurve := fun source u _ => crtShadowOffCurve source u
    revealOn := fun source u targets _ state => crtRevealOn source u targets (stateTable state)
    revealOff := fun source u _ state => crtRevealOff source u (stateTable state) }

/-! ### 5. The product over families, for `crtEntry` -/

section Families

open Kriterion.CRT.Privacy.Instance

/-- `g` reads the tape only off the hidden tags, and reads the coins only up to `sameCoins`. -/
def ReadsOff {α : Type} (sameCoins : crtEntry.Coins → crtEntry.Coins → Prop) (hidden : Fin (2 ^ 40) → Prop)
    (g : TableTape crtEntry → α) : Prop :=
  ∀ tape tape', sameCoins tape.1 tape'.1 → (∀ tag, ¬ hidden tag → tape.2 tag = tape'.2 tag) → g tape = g tape'

open Classical in
/-- **A part of the real garbling splits off**: off `flag`, the part is distributed as `ideal` and is independent of
every `g` that reads the tape off `hidden` (and the coins up to `sameCoins`). -/
def PartSplit {β : Type} (sameCoins : crtEntry.Coins → crtEntry.Coins → Prop) (hidden : Fin (2 ^ 40) → Prop)
    (flag : TableTape crtEntry → Prop) (part : TableTape crtEntry → β) (ideal : PMF β) : Prop :=
  ∀ {α : Type} (g : TableTape crtEntry → α), ReadsOff sameCoins hidden g → ∀ (b : β) (a : α),
    ((swappedTableTape crtEntry).map fun tape => if flag tape then none else some (part tape, g tape)) (some (b, a)) =
      ideal b * ((swappedTableTape crtEntry).map fun tape => if flag tape then none else some (g tape)) (some a)

/-- The hot conversion tags of coordinate `κ` at `u` (families `0` to `5`). -/
def hotConvTag (T : CrtTable) (u : AffineInput) (κ : ℕ) (tag : Fin (2 ^ 40)) : Prop :=
  tagFamily tag.val ≤ 5 ∧ tagCoord tag.val = κ ∧ hotTag T u tag.val = true

/-- **P3**: the conversion material of coordinate `κ` is uniform (as the source publishes it) and
independent of everything off the hot conversion tags of `κ` at `u`, the coins included. -/
def CrtConvSplit (T : CrtTable) (κ : Fin 2) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    PartSplit Eq (hotConvTag T u κ.val) (fun _ => False)
      (fun tape => if κ = 0 then (realGarbled crtEntry parameter scalar tape).1.crtX
        else (realGarbled crtEntry parameter scalar tape).1.crtY)
      ((PMF.uniformOfFintype (view).Source).map fun source =>
        if κ = 0 then ((view).publish source).crtX else ((view).publish source).crtY)

/-- The coins up to the exception pads. -/
def SameOffExceptionPad (first second : crtEntry.Coins) : Prop :=
  first.offsets = second.offsets ∧ first.pointRandomness = second.pointRandomness ∧
    first.bridgeKey = second.bridgeKey ∧ first.curveMask = second.curveMask ∧ first.curveR1 = second.curveR1 ∧
    first.curveR2 = second.curveR2 ∧ first.inputZero = second.inputZero ∧ first.inputDelta = second.inputDelta

/-- The digest tags hidden at `u`: every final, and the digest label of the other bit. -/
def hiddenDigestTag (u : AffineInput) (tag : Fin (2 ^ 40)) : Prop :=
  tagFamily tag.val = 9 ∨ (tagFamily tag.val = 8 ∧ tagPart tag.val ≠ inputBit u (tagCoord tag.val) (tagSlot tag.val))

/-- **P5a**: off the doubling event the exception entries are uniform (as the source publishes them) and
independent of everything off the hidden digest tags and the exception pads. -/
def CrtDigestSplit : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    PartSplit SameOffExceptionPad (hiddenDigestTag u) (fun tape => Doubling crtEntry scalar tape u)
      (fun tape => (realGarbled crtEntry parameter scalar tape).1.exception)
      ((PMF.uniformOfFintype (view).Source).map fun source => ((view).publish source).exception)

/-- The visible tags of the body, mask and key families (`6`, `7`, `10`). -/
abbrev BmrTags (T : CrtTable) (u : AffineInput) :=
  {tag : VisTags T u // tagFamily tag.1.val = 6 ∨ tagFamily tag.1.val = 7 ∨ tagFamily tag.1.val = 10}

/-- The part of the view P45 governs: the curve and row constants, the records, the answers at the body, mask and
key tags (disjoint from `RestTags`, so the rest split applies to it). -/
def bmrPart (T : CrtTable) (u : AffineInput) (v : CoreView crtEntry T u) :
    (BaseField × BaseField × BaseField) × Vector RowGamma digitCount ×
      Vector Kriterion.CRT.Entry.Record Kriterion.CRT.Entry.xCount ×
      Vector Kriterion.CRT.Entry.Record Kriterion.CRT.Entry.yCount × (BmrTags T u → Block × Block) :=
  (v.1.curve, v.1.rows, v.1.recX, v.1.recY, fun tag => v.2.2 tag.1)

/-- **P45 at the entry**: the P45 part of the ideal view is below the real one, off the reveal: the
entry's reading of `BMR.bmr_core` (pads from the body sites, masks from the mask sites, row randomizers and curve
coins from the scheme's coins), with the reveal covering the wrap event's image and the doubling. -/
def CrtBmrSplit (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput) (Q : Point),
    (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q → ∀ w,
      (idealCore crtEntry T crtRevealOn scalar u Q).map (Option.map (bmrPart T u)) (some w) ≤
        (realCore crtEntry T parameter scalar u).map (Option.map (bmrPart T u)) (some w)

/-- **P45 at the entry off the curve**: the P45 part of the ideal off-curve view (records, curve and row
constants, the table at the visible body tags) is below the real one, off the wrap reveal: the entry's reading of
`BMR.bmr_core_off` (`BMR.bmrEquivOff`). -/
def CrtBmrSplitOff (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    (crtEntry.scheme inferInstance inferInstance).function scalar u = none → ∀ w,
      (idealCoreOff crtEntry T crtRevealOff u).map (Option.map (bmrPart T u)) (some w) ≤
        (realCore crtEntry T parameter scalar u).map (Option.map (bmrPart T u)) (some w)

/-- The coins up to the input labels (`inputZero`, `inputDelta`). -/
def SameOffLabels (first second : crtEntry.Coins) : Prop :=
  first.offsets = second.offsets ∧ first.pointRandomness = second.pointRandomness ∧
    first.exceptionPad = second.exceptionPad ∧ first.bridgeKey = second.bridgeKey ∧
    first.curveMask = second.curveMask ∧ first.curveR1 = second.curveR1 ∧ first.curveR2 = second.curveR2

/-- The visible tags of families `0` to `5` and `8`. -/
abbrev RestTags (T : CrtTable) (u : AffineInput) :=
  {tag : VisTags T u // tagFamily tag.1.val ≤ 5 ∨ tagFamily tag.1.val = 8}

/-- **P2b and P6**: under the swapped tape, off doubling, the labels of `u` and the table at
the visible tags of families `0` to `5` and `8` are uniform and independent of everything that reads the coins off
the input labels and the table off those tags (in the composition: the P45 part, after P3 and P5a have split the
conversion material and the exception entries off). -/
def CrtRestSplit (T : CrtTable) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar) (u : AffineInput),
    letI := (view).sourceFintype
    haveI := (view).sourceNonempty
    PartSplit SameOffLabels (fun tag => visTag T u tag.val = true ∧ (tagFamily tag.val ≤ 5 ∨ tagFamily tag.val = 8))
      (fun tape => Doubling crtEntry scalar tape u)
      (fun tape => ((crtEntry.scheme inferInstance inferInstance).encode (realGarbled crtEntry parameter scalar tape).2 u,
        fun tag : RestTags T u => tape.2 tag.1.1))
      ((PMF.uniformOfFintype (view).Source).bind fun source =>
        (swappedTableLaw crtLayout).map fun table => ((view).labels source u, fun tag : RestTags T u => table tag.1.1))

/-! #### The route-M replay delivers `deliveredIdeal` for every conversion material -/

instance tableModulusNeZero (i : Fin Kriterion.CRT.Entry.table.count) :
    NeZero (Kriterion.CRT.Entry.table.modulus i) :=
  ⟨(Kriterion.CRT.bn254Table_modulus_pos i).ne'⟩

/-- The residue joins the published records carry, as the evaluator reads them (`recordJoin`), in P45's index. -/
def bmrJoinsOf (pub : Kriterion.CRT.Entry.Public) : BMR.Joins Kriterion.CRT.Entry.table := fun e i =>
  ((recordJoin Kriterion.CRT.Entry.table Kriterion.CRT.Entry.table.product Kriterion.CRT.Entry.table.radix
    (match e with
      | .inl x => (pub.recX.get (BMR.xFlat x)).val
      | .inr y => (pub.recY.get (BMR.yFlat y)).val) i : ℕ) : ZMod (Kriterion.CRT.Entry.table.modulus i))

/-- The pad values a tag table holds at the body site `(κ, i, ρ)`: `padVector` of its answers at the site's tags. -/
def padValues (table : TagTable) (κ : ℕ) (i : Fin Kriterion.CRT.Entry.table.count) (ρ : ℕ) :
    Fin (Layout.padS κ) → ZMod (Kriterion.CRT.Entry.table.modulus i) :=
  padVector (Kriterion.CRT.Entry.table.modulus i) (Layout.padS κ) (Layout.padCount κ i) fun j =>
    table ⟨tagCode Family.body κ i 0 0 ρ j % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩

/-- The cold pad values a tag table holds at `u`, in P45's index (encoding `e` of coordinate `κ` is entry `flat e` of
the pad vector). -/
def bmrColdOf (table : TagTable) (u : AffineInput) : BMR.Cold Kriterion.CRT.Entry.table u := fun i e ρ =>
  match e with
  | .inl x => padValues table 0 i ρ.1.val ⟨(BMR.xFlat x).val, by simp [Layout.padS]⟩
  | .inr y => padValues table 1 i ρ.1.val ⟨(BMR.yFlat y).val, by simp [Layout.padS]⟩

/-- **The route-M replay delivers `deliveredIdeal` (`convPublish` bijection)**: for
every source (so every conversion material the source can publish) and every tag table, at a valid input, the
delivered values of the view's replay program are P45's ideal delivered values at the joins the records carry and the
cold pads the table holds. For fixed cold answers and labels every material is the honest garbling of some hot
answers, and the evaluator is correct there (derived). -/
def CrtReplayDelivered : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (source : (view).Source) (u : AffineInput) (table : TagTable),
    validate u = true →
      (((view).replayProgram ((view).publish source) u ((view).labels source u)).eval (tagHash table)).delivered =
        BMR.deliveredIdeal u (bmrJoinsOf ((view).publish source)) (bmrColdOf table u)

end Families

end

end Kriterion.CRT.Privacy.H8
