/-
**P6b1: route M's replay reads a swapped table**.

`HW`'s stage 2 on a valid input runs `routeMReplay view (refillReader layout)`: the conversion and body blocks through
the refill reader, the key query on the lazy oracle, then the non-collector mask sites through the refill reader
(changes 8 and 9). This file composes the general law of `ReplayOn.lean` over it:

* `replayProgram view published u labels`: the replay as one program of the layer (the key asked as its query);
* `routeMReplay_eq_run`: when the key query is outside every site, the replay
  is `runReader (refillReader layout)` of that one program (`runReader_bind`, `refill_nonSite_query`);
* **`routeMReplay_table`**: along refill paths from the state (`RefillPath`), the replay is the table run of `replayProgram` on a table drawn from `swappedTableLaw layout`.
-/

import Proof.Privacy.CRT.Laws.RefillFacts

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT

noncomputable section

variable {FI EI Public : Type}

/-- **Route M's replay as one program of the layer**: the conversion and body blocks, the key query at `t'`, the
non-collector mask sites at the key. -/
def replayProgram [FieldCertificate] (view : RouteMView Public) (published : Public) (u : AffineInput)
    (labels : LamportSignature) : CM ReplayOut :=
  view.replayConv published u labels >>= fun conv =>
    askN (view.keyInput published u conv).val >>= fun keyed =>
      view.nonCollectorReplay keyed.1 >>= fun masks =>
        pure { delivered := view.delivered conv, masks := masks, key := keyed.1 }

theorem runReader_pure {α : Type} (rd : Reader FI EI) (value : α) (σ : LazyOracle.State FI EI) :
    runReader rd (pure value : CM α) σ = PMF.pure (value, σ) := rfl

/-- **The replay is one reader run** when the key query is outside every site. -/
theorem routeMReplay_eq_run [FieldCertificate] [DecidableEq FI] [DecidableEq EI] (view : RouteMView Public)
    (layout : SiteLayout) (published : Public) (u : AffineInput) (labels : LamportSignature)
    (keyNonSite : ∀ conv, siteOf ((view.keyInput published u conv).val / 2 ^ 128) = none)
    (σ : LazyOracle.State FI EI) :
    routeMReplay view (refillReader layout) published u labels σ =
      runReader (refillReader layout) (replayProgram view published u labels) σ := by
  unfold routeMReplay replayProgram
  rw [runReader_bind]
  refine congrArg _ (funext fun conv => ?_)
  rw [runReader_bind, refill_nonSite_query layout (refillReader_like layout) _ (keyNonSite conv.1),
    ZMod.natCast_zmod_val]
  refine congrArg _ (funext fun keyed => ?_)
  rw [runReader_bind]
  show _ = (runReader (refillReader layout) (view.nonCollectorReplay keyed.1.1) keyed.2).bind fun masked =>
    PMF.pure (_, masked.2)
  exact (PMF.bind_pure_comp _ _).symm

/-- **P6b1: route M's replay reads a swapped table.** Along refill paths from the state, the replay is the table
run of `replayProgram` on a table drawn from the swapped table law. -/
theorem routeMReplay_table [FieldCertificate] [DecidableEq FI] [DecidableEq EI] (view : RouteMView Public)
    (layout : SiteLayout) (facts : RefillLayoutFacts layout) (published : Public) (u : AffineInput)
    (labels : LamportSignature)
    (keyNonSite : ∀ conv, siteOf ((view.keyInput published u conv).val / 2 ^ 128) = none)
    (σ : LazyOracle.State FI EI) (path : RefillPath layout ∅ σ (replayProgram view published u labels)) :
    routeMReplay view (refillReader layout) published u labels σ =
      (swappedTableLaw layout).bind fun T =>
        runReader (tableReader layout T) (replayProgram view published u labels) σ := by
  rw [routeMReplay_eq_run view layout published u labels keyNonSite σ]
  exact runReader_refill_table layout facts (refillReader_like layout) path

end

end Kriterion.CRT.Privacy.Laws
