/-
**The CRT entry read by the privacy chain** (`crtEntry : CrtEntry Empty Empty`), on the frozen tier-1
definitions (`Construction/CRT/{Public, Layout, Entry}.lean`).

* the `Solution` fields: coins (release-r1's `Scheme.Coins`), the public value and codec, the scheme, the garbler and
  evaluator programs with their budgets;
* the bridge input `t` and the digest's exceptional inputs;
* the site layout: `crtLayout` (so H3 is `crt_swap crtEntry rfl`);
* the route-M view: the stage-1 source with `publish` and `labels`; route M's replay in the parts
  (`Entry.replayConv`, the key query at the labelled input `maskKeyInput` of the curve check's output,
  `nonCollectorMasksM`: `Entry.replayRouteM`),
  read in the tier-2 encoding index (P45.0's `xFlat`, `yFlat`, and release-r1's element indices for the masks); the
  published row constants; release-r1's rows kernels (`realRows`, `simulatedRows`) and preimage sampler
  (`idealPreimage`);
* the reach program: on the curve `Entry.reachM`, off it the conversion blocks and the digest only
  (`reachOffCM`), with the evaluator's decode appended.

Then `crtChain crtEntry` is the concrete chain, and the ledger's rows are the names of `Named.lean` at `crtEntry`
(state them through the names: re-elaborating a hop at `FI = EI = Empty` gives a different term, see `Named.lean`).
-/

import Proof.Privacy.CRT.Named
import Proof.Privacy.CRT.Swap.Layout
import Proof.Privacy.CRT.Core.EncIndex
import Construction.CRT.Entry
import Construction.CRT.Layout
import Proof.Privacy.Phase3.Opened
import Proof.Privacy.CRT.NormRows

/-! ### The entry's programs as the privacy chain reads them

`Construction/CRT/Entry.lean` provides the reach program
(`Entry.reachCM`, `Entry.reachM`) and route M's replay (`Entry.replayConv`, `Entry.curveOutput`,
`nonCollectorMasksM`, together `Entry.replayRouteM`). This section only adapts them to the tier-2 signatures:

* `reachProgram`: `Entry.reachM` followed by the evaluator's decode, so that it has `evaluateProgram`'s result type
  (`CrtEntry.reachProgram`); its queries are `Entry.reachM`'s;
* `nonCollectorValues`: the mask values the 546 non-collector answers determine (collector entries `0`, never read),
  read by `Entry.maskFunction`; `maskOf_eq_of_noncollector` shows they agree with `maskOf` of every mask at every
  non-collector slot. -/

namespace Kriterion.CRT.EntryReading

open Kriterion Kriterion.BN254 Kriterion.Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB
open FreeQuery (Bounded)

/-- **The reach off the curve**: the conversion blocks and the digest, without the key and the
masks. On the tag-only table the key is answered by its tag whatever `t'` is, so off the curve the masks would be the
garbler's; the masks' result slots are `0`. -/
def reachOffCM (pub : Entry.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    CM FieldMacToECMac.Result :=
  Entry.replayConv pub input labels >>= fun conv =>
    digestEvalM coordinateBitCount digitCount (Entry.labelsOf labels) input (fun o => pub.exception.get o)
      >>= fun digits => pure (Entry.resultOf pub input
        { deliveredX := conv.deliveredX, deliveredY := conv.deliveredY, masks := fun _ => 0, key := 0 } digits)

theorem bounded_reachOffCM (pub : Entry.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    (reachOffCM pub input labels).Bounded Entry.evaluateBudget :=
  ((Bounded.bind (Entry.bounded_replayConv pub input labels) fun _ =>
    Bounded.bind (bounded_digestEvalM _ _ _ _ _) fun _ => Bounded.pure' _ 0).mono
      (by
        simp only [Entry.replayConvBudget, Entry.replayConvBudgetOf, Entry.evaluateBudget, Entry.evaluateBudgetOf]
        omega))

/-- The reach (on the curve `Entry.reachM`, off it `reachOffCM`) with the evaluator's decode appended. -/
def reachDecodedM [FieldCertificate] [GroupCertificate] (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) : FreeQuery Entry.Spec (Option (Option Point)) :=
  (if validate input then Entry.reachM pub input labels else liftHash (reachOffCM pub input labels)) >>= fun result =>
    pure (some (Garbling.decodeResult result))

theorem bounded_reachDecodedM [FieldCertificate] [GroupCertificate] (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    (reachDecodedM pub input labels).Bounded Entry.evaluateBudget :=
  (Bounded.bind (Bounded.ite (fun _ => Entry.bounded_reachM pub input labels)
    (fun _ => bounded_liftHash (bounded_reachOffCM pub input labels))) fun _ => Bounded.pure' _ 0).of_eq
    (Nat.add_zero _)

/-- The reach program at the evaluator's budget, with the evaluator's result type. -/
def reachProgram [FieldCertificate] [GroupCertificate] (pub : Entry.Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    QueryProgram Entry.Spec (Option (Option Point)) Entry.evaluateBudget :=
  FreeQuery.toProgram (reachDecodedM pub input labels) Entry.evaluateBudget
    (bounded_reachDecodedM pub input labels)

/-- The mask values the non-collector sites determine (the collector entries are `0` and never read). -/
def nonCollectorValues (rest : (Fin (pairSites digitCount) → BaseField × BaseField) × BaseField) :
    MaskValues digitCount :=
  { collector := fun _ => 0, pair := rest.1, single := rest.2 }

/-- The non-collector mask sites at the key `K` (546 queries), read as masks by row encoding. -/
def nonCollectorReplay (key : Block) : CM (Entry.RowEncoding → BaseField) :=
  nonCollectorMasksM key digitCount >>= fun rest => pure (Entry.maskFunction (nonCollectorValues rest))

/-- `maskOf` reads the collector masks only at the `x` slots `1, 2, 3` of a digit. -/
theorem maskOf_eq_of_noncollector {first second : MaskValues digitCount} (pair : first.pair = second.pair)
    (single : first.single = second.single) (coord e : ℕ)
    (slot : ¬ (coord = 0 ∧ e < 4 * digitCount ∧ (e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3))) :
    maskOf first coord e = maskOf second coord e := by
  unfold maskOf nonCollectorMask
  split_ifs <;> simp_all

/-- The key's hash input is below `2 ^ 168`, so below `p`. -/
theorem maskKeyInput_lt (t : BaseField) : maskKeyInput t < baseFieldModulus := by
  have label : (BitVec.ofNat 128 t.val).toNat < 2 ^ 128 := BitVec.isLt _
  have tag : maskKeyTag = 687194767360 := by
    unfold maskKeyTag tagCode Family.key; norm_num
  have bound : (2 : ℕ) ^ 168 ≤ baseFieldModulus := by unfold baseFieldModulus; decide +kernel
  unfold maskKeyInput hashInput
  rw [tag]
  have : (2 : ℕ) ^ 168 = 2 ^ 128 * 2 ^ 40 := by norm_num
  omega

/-- **The key input as a field element** (the view's `keyInput`): its value is the natural `keyM` asks. -/
def keyField (t : BaseField) : BaseField := (maskKeyInput t : BaseField)

theorem keyField_val (t : BaseField) : (keyField t).val = maskKeyInput t := by
  unfold keyField
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (maskKeyInput_lt t)]

end Kriterion.CRT.EntryReading

namespace Kriterion.CRT.Privacy.Instance

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

/-- The delivered values in the tier-2 encoding index (P45.0). -/
def toDelivered (conv : Kriterion.CRT.Entry.ConvOut) : BMR.Enc → BaseField
  | .inl x => conv.deliveredX (BMR.xFlat x)
  | .inr y => conv.deliveredY (BMR.yFlat y)

/-- The masks in the tier-2 encoding index (release-r1's element indices). -/
def toMasks (masks : Kriterion.CRT.Entry.RowEncoding → BaseField) : BMR.NonCollector → BaseField
  | ⟨(d, .inl x), _⟩ => masks (.inl (xElementIndex d x))
  | ⟨(d, .inr y), _⟩ => masks (.inr (yElementIndex d y))

/-- **The route-M view of the CRT entry.** -/
def view [FieldCertificate] [GroupCertificate] : RouteMView Kriterion.CRT.Entry.Public where
  Source := Kriterion.CRT.Entry.Source
  sourceFintype := Fintype.ofFinite _
  sourceNonempty := inferInstance
  publish := Kriterion.CRT.Entry.publish
  labels := Kriterion.CRT.Entry.labels
  ConvOut := Kriterion.CRT.Entry.ConvOut
  replayConv := Kriterion.CRT.Entry.replayConv
  delivered := toDelivered
  keyInput pub u conv := Kriterion.CRT.EntryReading.keyField (Kriterion.CRT.Entry.curveOutput pub u conv)
  nonCollectorReplay key := Kriterion.CRT.EntryReading.nonCollectorReplay key >>= fun masks => pure (toMasks masks)
  gammaOf := Kriterion.CRT.Entry.gammaOf
  realRows scalar := NormRows.normRealRows scalar
  simRows _ := Security.Phase3.simulatedRows
  preimage value := (Phase3.Glue.idealPreimage value).map some
  fourth := (PMF.uniformOfFintype Block).map some

/-- **The view's replay program is `Entry.replayRouteM`**, read in the tier-2 index, on every hash. -/
theorem view_replayProgram_eval [FieldCertificate] [GroupCertificate] (H : HashN) (pub : Kriterion.CRT.Entry.Public)
    (u : AffineInput) (labels : LamportSignature) :
    ((view).replayProgram pub u labels).eval H =
      let out := (Kriterion.CRT.Entry.replayRouteM pub u labels).eval H
      { delivered := toDelivered out.conv
        masks := toMasks (Kriterion.CRT.Entry.maskFunction
          (Kriterion.CRT.EntryReading.nonCollectorValues (out.pairs, out.single)))
        key := out.key } := by
  simp [RouteMView.replayProgram, view, Kriterion.CRT.Entry.replayRouteM, keyM,
    Kriterion.CRT.EntryReading.nonCollectorReplay, Kriterion.CRT.EntryReading.keyField_val]

/-- **The CRT entry, as the privacy chain reads it.** -/
def crtEntry : CrtEntry Empty Empty where
  Coins := Kriterion.CRT.Entry.Coins
  coinsFinite := inferInstance
  coinWitness := Kriterion.CRT.Entry.witness
  Public := Kriterion.CRT.Entry.Public
  Key := Kriterion.CRT.Entry.Key
  encoding := Kriterion.CRT.Entry.Wire.encoding
  bytes := Kriterion.CRT.Entry.ciphertextBytes
  garbleBudget := Kriterion.CRT.Entry.garbleBudget
  scheme field group := @Kriterion.CRT.Entry.scheme field group
  garbleProgram _ _ _ scalar coins := Kriterion.CRT.Entry.garbleProgram scalar coins
  evaluateBudget := Kriterion.CRT.Entry.evaluateBudget
  evaluateProgram field group := @Kriterion.CRT.Entry.evaluateProgram field group
  reachProgram field group := @Kriterion.CRT.EntryReading.reachProgram field group
  bridgeInput := Kriterion.CRT.Entry.bridgeInput
  exceptional := Kriterion.CRT.Entry.exceptional
  layout := crtLayout
  view field group := @view field group

/-- **H3 for the entry** (`crt_swap`). -/
theorem crtEntry_swap : CrtSwapHop crtEntry := crt_swap crtEntry rfl

/-- **The privacy field for the CRT entry from the remaining named rows** (`crt_privacy_of_named` at `crtEntry`,
with H3 discharged). -/
theorem crtEntry_privacy_of (T : CrtTable) (simulator : BoundedMachine.Simulator) (real : CrtRealLazy crtEntry)
    (table : CrtTableHop crtEntry) (reached : DesignedReached crtEntry T)
    (one : CrtStageOneGuess crtEntry (ENNReal.ofReal crtHiddenCharge))
    (two : CrtStageTwoGuess crtEntry T (ENNReal.ofReal crtHiddenCharge) (ENNReal.ofReal hiddenWindowError))
    (publicFirst : CrtPublicFirstHop crtEntry) (opening : CrtOpeningHop crtEntry) (refill : CrtRefillHop crtEntry)
    (machine : CrtMachineHop crtEntry simulator) : CrtPrivacy crtEntry :=
  crt_privacy_of_named crtEntry T simulator real table crtEntry_swap reached one two publicFirst opening
    refill machine

end

end Kriterion.CRT.Privacy.Instance
