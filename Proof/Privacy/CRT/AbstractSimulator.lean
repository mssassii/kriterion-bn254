/-
**The route-M abstract simulator of the CRT entry**.

`HW`, `H` and `I` are one simulator with two knobs, the rows kernel and the site reader; all three abort on a failed
program (F5), and none replays the digest (F6):

* **stage 1**: draw the source uniformly and publish it; no oracle call;
* **stage 2, output `none`** (an invalid or off-curve input): return the selected labels; no oracle call;
* **stage 2, output `some Q`**: run route M's replay on the shared lazy oracle (`routeMReplay`):
  the conversion and body blocks through `reader`, the key query at `t'` asked of the lazy oracle directly (never
  through a tag-decoding reader: `t'` is uniform on `F_p` and may decode as a site tag), then the 683 non-collector
  mask answers through `reader` (the 546 collector-mask positions are never read); as one program of the layer this
  is `RouteMView.replayProgram`, `replayRouteM`; draw the target rows `W_d`;
  set each collector's mask `π_c = v_c − τ_c` with `τ_c` the route-M solve (`BMR.collectorSolve`); draw a `sampleFp`
  preimage and a fourth block per collector; program the 546 points `K + 2^128 · tag(mask, 0, c, j)`, aborting on a
  failed program; return the labels.

The entry enters through `RouteMView`, so this file elaborates before they
are frozen. `LazyAbstractSimulator` and `abstractIdealGame` are xinshu's (`Glue/LazyIdeal.lean:37-67`), generic.
-/

import Proof.Privacy.CRT.Glue.Shapes
import Proof.Privacy.CRT.Core.BodyMaskRow

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT

noncomputable section

/-! ### Abstract simulators on the shared lazy oracle (xinshu's `LazyIdeal.lean`, generic) -/

/-- A PMF-level simulator on the shared lazy oracle; `none` is an abort, and the game then returns `false`. -/
structure LazyAbstractSimulator [FieldCertificate] (FI EI Public : Type) where
  State : Type
  stage1 : ℕ → LazyOracle.State FI EI → PMF (Option (Public × State × LazyOracle.State FI EI))
  stage2 : State → AffineInput → Option Point → LazyOracle.State FI EI →
    PMF (Option (LamportSignature × LazyOracle.State FI EI))

/-- The abstract ideal game: `LazySimulatorProtocol.idealGame` with two kernels in place of the machine runs. -/
def abstractIdealGame [FieldCertificate] {FI EI Randomness Public Key Oracle Aux : Type}
    [DecidableEq FI] [DecidableEq EI]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FI EI Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FI EI) AffineInput Public LamportSignature Aux)
    (parameter : ℕ) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  let experiment : OptionT PMF Bool := do
    let (circuit, state, oracle) ← OptionT.mk (simulator.stage1 parameter LazyOracle.empty)
    let (selected, chosen) ←
      liftM (LazyOracle.run (adversary.chooseInput parameter circuit auxiliary) oracle)
    let (labels, updated) ← OptionT.mk
      (simulator.stage2 state selected.1 (scheme.function scalar selected.1) chosen)
    let (decision, _) ← liftM (LazyOracle.run
      (adversary.decide parameter circuit labels auxiliary selected.2) updated)
    pure decision
  experiment.run.map (fun result => result.getD false)

/-! ### What the simulator reads from the entry -/

/-- The result of route M's replay: the delivered value of every encoding (wrap-hint decoding with the published
hints), the non-collector masks as read, and the key `K = (hash t').1`. -/
structure ReplayOut where
  delivered : BMR.Enc → BaseField
  masks : BMR.NonCollector → BaseField
  key : Block

/-- **The entry as route M's simulator reads it**. -/
structure RouteMView [FieldCertificate] (Public : Type) where
  /-- The stage-1 source: every published cell in source form, and the Lamport key. -/
  Source : Type
  sourceFintype : Fintype Source
  sourceNonempty : Nonempty Source
  publish : Source → Public
  labels : Source → AffineInput → LamportSignature
  /-- What the evaluator's conversion and body blocks produce. -/
  ConvOut : Type
  /-- The evaluator's conversion and body blocks (`chunkTree` to the body) as a program of the layer;
  every query is labelled, so its tag decodes exactly. -/
  replayConv : Public → AffineInput → LamportSignature → CM ConvOut
  /-- The delivered value of every encoding. -/
  delivered : ConvOut → BMR.Enc → BaseField
  /-- The key input `t'`, from the published curve constants, the input and the delivered curve values. -/
  keyInput : Public → AffineInput → ConvOut → BaseField
  /-- The evaluator's non-collector mask sites at the key `K` (inputs `K + 2^128 · maskTag`, labelled; 683
  queries): the non-collector masks. -/
  nonCollectorReplay : Block → CM (BMR.NonCollector → BaseField)
  /-- The published row constants. -/
  gammaOf : Public → Fin 91 → RowGamma
  /-- The rows kernels: the construction's true rows under its coin law (`HW`), and the tail, head clamp and lift
  sampler (`H`, `I`); `none` is a sampler abort. -/
  realRows : NonZeroScalar → AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))
  simRows : NonZeroScalar → AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))
  /-- A `sampleFp` preimage of a field element (xinshu's `idealPreimage` in the exact samplers). -/
  preimage : BaseField → PMF (Option (Block × Block × Block))
  /-- The unused fourth block of a collector site. -/
  fourth : PMF (Option Block)

/-! ### The opening of route M -/

/-- The 273 collectors, digit by digit, in the order `rowX_x9`, `rowY_x9`, `rowZ_x9`. -/
def collectorList : List BMR.Collector :=
  (List.finRange 91).flatMap fun d =>
    [⟨(d, .inl .rowX_x9), Or.inl rfl⟩, ⟨(d, .inl .rowY_x9), Or.inr (Or.inl rfl)⟩,
      ⟨(d, .inl .rowZ_x9), Or.inr (Or.inr rfl)⟩]

/-- The collector number `c = 3 d + k`. -/
def collectorIndex (c : BMR.Collector) : ℕ :=
  3 * c.1.1.val + match c.1.2 with
    | .inl .rowX_x9 => 0
    | .inl .rowY_x9 => 1
    | _ => 2

/-- The point of answer `j` of collector site `k`, read at the key `K`. -/
def collectorPoint (key : Block) (k j : ℕ) : BaseField :=
  (hashInput key (tagCode Family.mask 0 0 0 0 k j) : BaseField)

/-- The row-level values of a digit's non-collector elements, from the replay: `v_e − π_e`. -/
def replayRowValues (out : ReplayOut) (d : Fin 91) : Biquadratic.Values := fun element =>
  if collector : BMR.IsCollector element then 0
  else out.delivered (BMR.rowEnc (d, element)) - out.masks ⟨(d, element), collector⟩

/-- **Route M's collector masks** `π_c = v_c − τ_c`, `τ_c` the solve at the target rows. -/
def collectorMasks (u : AffineInput) (out : ReplayOut) (gamma : Fin 91 → RowGamma)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) (c : BMR.Collector) : BaseField :=
  out.delivered (BMR.rowEnc c.1) -
    BMR.collectorSolve (targets c.1.1) (gamma c.1.1) u (replayRowValues out c.1.1) c.1.2

/-- Independent draws over a list; any abort aborts. -/
def drawAll {α β : Type} (sample : α → PMF (Option β)) : List α → PMF (Option (List (α × β)))
  | [] => PMF.pure (some [])
  | a :: rest => (sample a).bind fun drawn => match drawn with
    | none => PMF.pure none
    | some b => (drawAll sample rest).map (Option.map fun tail => (a, b) :: tail)

/-- The two program requests of each collector: `(point, answer)` for answers 0 and 1. -/
def programRequests (key : Block) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    List (BaseField × (Block × Block)) :=
  drawn.flatMap fun entry =>
    let k := collectorIndex entry.1
    let limbs := entry.2.1
    [(collectorPoint key k 0, (limbs.1, limbs.2.1)), (collectorPoint key k 1, (limbs.2.2, entry.2.2))]

/-- **Program every request; a failed program aborts (F5).** -/
def programHashAll {FI EI : Type} [DecidableEq FI] [DecidableEq EI] :
    List (BaseField × (Block × Block)) → LazyOracle.State FI EI → Option (LazyOracle.State FI EI)
  | [], oracle => some oracle
  | (point, answer) :: rest, oracle =>
    (LazyOracle.program (.hash point) answer oracle).bind (programHashAll rest)

/-! ### The simulator -/

variable {FI EI Public : Type}

/-- **Route M's replay as one program of the layer** (`replayRouteM`; the machine's M5b target): the
conversion and body blocks, the key query at `t'`, the non-collector mask sites. -/
def RouteMView.replayProgram [FieldCertificate] (view : RouteMView Public) (published : Public) (u : AffineInput)
    (labels : LamportSignature) : CM ReplayOut :=
  view.replayConv published u labels >>= fun conv =>
    askN (view.keyInput published u conv).val >>= fun answer =>
      view.nonCollectorReplay answer.1 >>= fun masks =>
        pure { delivered := view.delivered conv, masks, key := answer.1 }

/-- **Route M's replay on the lazy oracle**: the conversion and body blocks and the non-collector mask
sites through `reader`; the key query at `t'` asked of the lazy oracle directly (`K` is its first block). -/
def routeMReplay [FieldCertificate] [DecidableEq FI] [DecidableEq EI] (view : RouteMView Public)
    (reader : Reader FI EI) (published : Public) (u : AffineInput) (labels : LamportSignature)
    (oracle : LazyOracle.State FI EI) : PMF (ReplayOut × LazyOracle.State FI EI) :=
  (runReader reader (view.replayConv published u labels) oracle).bind fun conv =>
    (LazyOracle.query (.hash (view.keyInput published u conv.1)) conv.2).bind fun keyed =>
      let key : Block := (keyed.1 : Block × Block).1
      (runReader reader (view.nonCollectorReplay key) keyed.2).map fun masked =>
        ({ delivered := view.delivered conv.1, masks := masked.1, key }, masked.2)

/-- **The route-M simulator** with a rows kernel and a site reader. -/
def routeMSimulator [FieldCertificate] [DecidableEq FI] [DecidableEq EI] (view : RouteMView Public)
    (rows : AffineInput → Point → PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
    (reader : Reader FI EI) : LazyAbstractSimulator FI EI Public where
  State := view.Source
  stage1 _ oracle :=
    letI := view.sourceFintype
    letI := view.sourceNonempty
    (PMF.uniformOfFintype view.Source).map fun source => some (view.publish source, source, oracle)
  stage2 source u output oracle :=
    let labels := view.labels source u
    let published := view.publish source
    match output with
    | none => PMF.pure (some (labels, oracle))
    | some target =>
      (routeMReplay view reader published u labels oracle).bind fun ran =>
        (rows u target).bind fun drawnRows => match drawnRows with
          | none => PMF.pure none
          | some targets =>
            let masks := collectorMasks u ran.1 (view.gammaOf published) targets
            (drawAll (fun c => (view.preimage (masks c)).bind fun limbs => match limbs with
                | none => PMF.pure none
                | some limbs => view.fourth.map (Option.map fun fourth => (limbs, fourth)))
              collectorList).map fun drawn => match drawn with
              | none => none
              | some drawn => (programHashAll (programRequests ran.1.key drawn) ran.2).map fun updated =>
                  (labels, updated)

end

end Kriterion.CRT.Privacy
