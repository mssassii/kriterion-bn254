/-
**Route M's replay program on the lazy oracle** (the request (B)): running
`liftHash (Entry.replayRouteM pub u labels)` on the shared lazy oracle and reading the output in the
tier-2 index (`routeView`) is the abstract simulator's `routeMReplay` of the entry's view with the
lazy reader. With `Machine.agree_replay` and `agree_run`, the machine's valid arm runs as the
abstract route-M stage 2.
-/

import Proof.Simulator.CRT.ReplayEntry
import Proof.Privacy.CRT.EntryInstance

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB BN254

namespace Lazy

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- **A lifted program runs on the lazy oracle as the lazy reader runs it.** -/
theorem runT_liftHash {α : Type} :
    ∀ (program : CM α) (oracle : LazyOracle.State FI EI),
      runT (FixedIndex := FI) (EncIndex := EI) (liftHash program) oracle =
        runReader lazyReader program oracle
  | .pure _, _ => rfl
  | .query input next, oracle => by
      show (LazyOracle.query (.hash (input : BaseField)) oracle).bind
          (fun answer => runT (liftHash (next answer.1)) answer.2) =
        (LazyOracle.query (.hash (input : BaseField)) oracle).bind
          (fun answered => runReader lazyReader (next answered.1) answered.2)
      congr 1
      funext answer
      exact runT_liftHash (next answer.1) answer.2

theorem runReader_bind (reader : Reader FI EI) {α β : Type} :
    ∀ (program : CM α) (next : α → CM β) (state : LazyOracle.State FI EI),
      runReader reader (FreeQuery.bind program next) state =
        (runReader reader program state).bind fun result => runReader reader (next result.1) result.2
  | .pure _, _, _ => by
      show _ = (PMF.pure _).bind _
      rw [PMF.pure_bind]
      rfl
  | .query input rest, next, state => by
      show (reader input state).bind (fun answered => runReader reader (FreeQuery.bind (rest answered.1) next) answered.2) =
        ((reader input state).bind fun answered => runReader reader (rest answered.1) answered.2).bind _
      rw [PMF.bind_bind]
      congr 1
      funext answered
      exact runReader_bind reader (rest answered.1) next answered.2

theorem runReader_askN (reader : Reader FI EI) (input : Nat) (state : LazyOracle.State FI EI) :
    runReader reader (askN input) state = (reader input state).bind fun answered => PMF.pure answered := by
  show (reader input state).bind (fun answered => PMF.pure (answered.1, answered.2)) = _
  rfl

theorem runReader_pure (reader : Reader FI EI) {α : Type} (value : α) (state : LazyOracle.State FI EI) :
    runReader reader (FreeQuery.pure value : CM α) state = PMF.pure (value, state) := rfl

variable [FieldCertificate] [GroupCertificate]

/-- The replay's result adapters are the privacy instance's (the simulator keeps its own copies so that it
does not import the privacy glue). -/
theorem replayView_toDelivered_eq (conv : Entry.ConvOut) :
    ReplayView.toDelivered conv = Instance.toDelivered conv := by
  funext e
  cases e <;> rfl

theorem replayView_toMasks_eq (masks : Entry.RowEncoding → BaseField) :
    ReplayView.toMasks masks = Instance.toMasks masks := by
  funext n
  obtain ⟨⟨d, x | y⟩, h⟩ := n <;> rfl

/-- **The lazy-oracle link**: the lifted route-M replay, read in the tier-2 index, is `routeMReplay` of
the entry's view with the lazy reader. -/
theorem runT_replayRouteM (pub : Entry.Public) (u : AffineInput) (labels : GarbledCircuit.LamportSignature)
    (oracle : LazyOracle.State FI EI) :
    (runT (FixedIndex := FI) (EncIndex := EI) (liftHash (Entry.replayRouteM pub u labels)) oracle).map
        (fun result => (routeView result.1, result.2)) =
      routeMReplay Instance.view lazyReader pub u labels oracle := by
  rw [runT_liftHash]
  unfold Entry.replayRouteM routeMReplay
  simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, runReader_bind, PMF.map_bind]
  congr 1
  funext conv
  unfold keyM
  simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, runReader_bind, runReader_askN, runReader_pure,
    PMF.bind_bind, PMF.pure_bind]
  rw [show Instance.view.keyInput pub u conv.1 =
      ((maskKeyInput (Entry.curveOutput pub u conv.1) : Nat) : BaseField) from rfl]
  simp only [lazyReader]
  refine congrArg (PMF.bind _) (funext fun keyed => ?_)
  simp only [Instance.view, EntryReading.nonCollectorReplay, TreeLaws.monad_bind, TreeLaws.monad_pure,
    runReader_bind, runReader_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.pure_map]
  refine congrArg (PMF.bind _) (funext fun masked => ?_)
  simp only [routeView, ReplayView.nonCollectorValues, EntryReading.nonCollectorValues,
    replayView_toDelivered_eq, replayView_toMasks_eq]

end Lazy

end Kriterion.CRT.SimMachine
