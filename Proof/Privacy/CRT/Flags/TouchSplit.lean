/-
**P8, the stage-1 touch guess by route (B)** (`CrtTouchGuess` at `crtEntry` and `crtShadow`).

The unflagged final state of `M'`'s stage 2 at the empty stage-1 state stores:
* on the curve: the private state after the collector programs, whose lookups are the view's entries off `u`'s digest
  labels (`OnDecomp`'s containment), then the digest's lazy reads: `u`'s digest labels (family 8) and the 91 finals at
  the key `key(u)` (family 9);
* off the curve: the view's entries and the finals at `key(t)` (`crtOffDecomp`, `xs = xsOf`).

A family-9 tag is never visible, so the view's entries have no family-9 input. The touch of a point `x` therefore
splits by `x`'s family:
* not 9: `x` is an input of the view's entries (the digest labels by `CrtDigestLabelsViewed`); through
  `CrtCoreBelow` the ideal view law is below the real one, whose entries are the designed garbler entries
  (`crtEntry_viewEntriesPerm`), so `CrtStageOneGuess` at `crtHiddenCharge` bounds it;
* 9: a final at a key that is an XOR of fresh reads (`CrtOnFinalFresh`) or of the uniform table off the
  sites (`CrtOffFinalFresh`), at most `1/2^128` against the unflagged mass, which `CrtCoreBelow` moves to
  the swapped tape.

The three named inputs are stated here at `crtEntry`.
-/

import Proof.Privacy.CRT.Flags.FlagMass
import Proof.Privacy.CRT.Flags.CoincidenceSplit
import Proof.Privacy.CRT.Flags.CrtRows
import Proof.Privacy.CRT.Laws.MiddleCrt
import Proof.Privacy.CRT.Core.OffDecomp
import Proof.Privacy.CRT.Paths.Upper

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.Instance Kriterion.CRT.Privacy.H8
open scoped ENNReal

noncomputable section

/-! ### 1. The three named inputs, at `crtEntry` -/

/-- **The digest labels are view entries**: at every view, each of `u`'s digest-label inputs (the
family-8 queries of `digestKeyM` on the view's labels) is an input of the view's entries. The reach runs the digest
after the replay (`reachCM`, `reachOffCM`), `digestKeyM`'s queries do not depend on the answers
(`asked_digestKeyM`), and at part `coordBit u c p` the tag is visible. -/
def CrtDigestLabelsViewed : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (u : AffineInput)
    (v : CoreView crtEntry Entry.table u) (c : Fin 2) (p : Fin coordinateBitCount),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    ((hashInput (Entry.labelsOf v.2.1 c p) (digestLabelTag c.val p.val (coordBit u c p.val)) : ℕ) : BaseField) ∈
      (viewEntries crtEntry Entry.table u v).map Laws.entryInput

/-- **The finals are fresh on the curve**: after the collector programs (as in `OnDecomp`'s containment),
the digest's lazy run stores a given family-9 point with mass at most `1/2^128`. Its key is the XOR of the answers at
`u`'s digest labels, which the private state does not store (they are `OnDecomp`'s `ds`), so the lazy reader draws
them fresh. -/
def CrtOnFinalFresh : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar) (u : AffineInput),
    letI := field
    letI := group
    letI := @Fintype.ofFinite Empty inferInstance
    letI := Classical.decEq Empty
    ∀ Q : Point, (crtEntry.scheme inferInstance inferInstance).function scalar u = some Q →
    ∀ (source : (viewHere crtEntry).Source) (table : TagTable)
      (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State Empty Empty),
      drawn.map Prod.fst = collectorList →
      programHashAll (programRequests (Laws.outOf crtEntry table source u).key drawn)
          (Laws.finOf crtEntry table source u) = some installed →
      ∀ x : BaseField, tagFamily (x.val / 2 ^ 128) = 9 →
        (runReader lazyReader (crtShadowOnCurve source u) installed).toOuterMeasure {p | x ∈ storedPoints p.2}
          ≤ ENNReal.ofReal (1 / 2 ^ 128)

/-- **The finals are fresh off the curve**: under the swapped table, a given family-9 point is one of
the finals `xsOf source u t` (at the key `keyOf source u t`, the XOR of the table at `u`'s digest-label positions,
outside every site) with mass at most `1/2^128` times the mass of no reveal (`crtRevealOff` reads only the conversion
blocks). -/
def CrtOffFinalFresh : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (source : (viewHere crtEntry).Source)
    (u : AffineInput),
    letI := field
    letI := group
    validate u = false → ∀ x : BaseField, tagFamily (x.val / 2 ^ 128) = 9 →
      ∑' t, swappedTableLaw crtEntry.layout t *
          (ind (¬ crtRevealOff source u t) * ind (x ∈ OffDecomp.xsOf source u t))
        ≤ ENNReal.ofReal (1 / 2 ^ 128) *
          ∑' t, swappedTableLaw crtEntry.layout t * ind (¬ crtRevealOff source u t)

end

end Kriterion.CRT.Privacy.Flags
