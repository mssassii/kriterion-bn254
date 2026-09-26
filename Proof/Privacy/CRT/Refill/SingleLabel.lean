/-
**P10's obligation on the entry: the replay reads each site at one label** (`ReplaySingleLabel`, row H10).

The refill hop `H → I` pays, for each site the refill reader draws from the swapped law, that site's bias
(`SwapLayoutFacts.close`), and the biases sum to `padSwapError` only if no site is drawn twice. A site is drawn when a
query decodes to it while its points at the query's label are untouched; after one draw its points at that label
are all set, so a second draw needs the same site read at a second label. `ReplaySingleLabel` excludes that: along
every path of the programs route M runs through the reader (`routeMReplay`: the conversion and body blocks, then
the non-collector mask sites at the key; the key query itself goes to the lazy oracle directly), every query whose tag decodes to a site names a site of the layout, is not a
collector-mask position (route M programs those after the replay), and uses the label at which the path first read
that site. With the bound `answers ≤ 64` on the layout's sites (so a site's tags are `tagCode` of in-range fields),
the refilled points are then never route M's collector points.

* `recordSite`: the site labels fixed after one query;
* `SiteQueryOK`: one query is well formed at the labels fixed so far;
* `SingleLabelFrom`: every query of every path is well formed, every leaf satisfies a leaf predicate at its labels;
* `ReplaySingleLabel`: the obligation.
-/

import Proof.Privacy.CRT.Hybrids

namespace Kriterion.CRT.Privacy

open BN254 Cryptography GarbledCircuit Kriterion.CRT
open Kriterion.ArgoMAC (FreeQuery)

/-- The site labels fixed after a query: a query whose tag decodes to a site fixes that site's label to the query's
low 128 bits. -/
def recordSite (seen : SiteId → Option ℕ) (input : ℕ) : SiteId → Option ℕ :=
  match siteOf (input / 2 ^ 128) with
  | none => seen
  | some site => Function.update seen site (some (input % 2 ^ 128))

/-- **One query is well formed for the refill**: if its tag decodes to a site, the site is one of the layout's, the
query is not at a collector-mask position, and its label is the one the site was first read at, if it was read. -/
def SiteQueryOK (layout : SiteLayout) (seen : SiteId → Option ℕ) (input : ℕ) : Prop :=
  match siteOf (input / 2 ^ 128) with
  | none => True
  | some site => site ∈ layout.sites ∧ isCollectorMaskTag (input / 2 ^ 128) = false ∧
      (seen site = none ∨ seen site = some (input % 2 ^ 128))

/-- **Every path reads each site at one label**: from the labels `seen` fixed so far, every query of every path is
well formed (`SiteQueryOK`), and every leaf satisfies `leaf` at the labels fixed along its path. -/
def SingleLabelFrom (layout : SiteLayout) {α : Type} (leaf : (SiteId → Option ℕ) → α → Prop) :
    (SiteId → Option ℕ) → CM α → Prop
  | seen, .pure value => leaf seen value
  | seen, .query input next => SiteQueryOK layout seen input ∧
      ∀ answer, SingleLabelFrom layout leaf (recordSite seen input) (next answer)

/-- **The obligation of `crt_refill_of_layout`** (P10): the layout's sites read at most 64 answers, and along every
path of the two programs route M runs through the reader (`routeMReplay`: the conversion and body blocks
`replayConv`, then the non-collector mask sites `nonCollectorReplay K` at every key `K`), from no fixed labels, every
query is well formed. The key query between them is asked of the lazy oracle directly and carries no condition. -/
structure ReplaySingleLabel {FI EI : Type} (E : CrtEntry FI EI) : Prop where
  /-- Every site of the layout reads at most 64 answers (its tags are `tagCode` of in-range fields). -/
  answers_le : ∀ site ∈ E.layout.sites, E.layout.answers site ≤ 64
  /-- Every path of the reader's programs reads each site at one label. -/
  replay : ∀ [field : FieldCertificate] (group : @GroupCertificate field) (published : E.Public) (u : AffineInput)
    (labels : LamportSignature),
    SingleLabelFrom E.layout
      (fun seen _ => ∀ key : Block,
        SingleLabelFrom E.layout (fun _ _ => True) seen ((E.view field group).nonCollectorReplay key))
      (fun _ => none) ((E.view field group).replayConv published u labels)

/-- `SingleLabelFrom` of a bind: the first program's paths, with the second's condition at each leaf. -/
theorem singleLabelFrom_bind (layout : SiteLayout) {α β : Type} (leaf : (SiteId → Option ℕ) → β → Prop)
    (first : CM α) (second : α → CM β) (seen : SiteId → Option ℕ) :
    SingleLabelFrom layout leaf seen (first >>= second) ↔
      SingleLabelFrom layout (fun seen' value => SingleLabelFrom layout leaf seen' (second value)) seen first := by
  induction first generalizing seen with
  | pure value => exact Iff.rfl
  | query input next ih =>
      show (SiteQueryOK layout seen input ∧ ∀ answer, SingleLabelFrom layout leaf (recordSite seen input)
          (next answer >>= second)) ↔ _
      simp only [ih]
      rfl

end Kriterion.CRT.Privacy
