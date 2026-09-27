/-
**Tags, hot positions, sites and readers of the CRT privacy chain**.

* Tag fields (`tagFamily`, `tagCoord`, ..., `tagPart`) and their decoding of `tagCode` in range (`tagFamily_tagCode`,
  ...), by `omega`.
* `hotTag T u tag`: whether the position `tag` is hot at input `u` (a function of `u` alone): the hot
  slot of every chunk tree and cast, extraction tree and cast, growth level, fold and body pad of either coordinate.
* Sites (F4): a pad site `(κ, i, ρ)` (family 6) or a mask site `(stage, site)` (family 7), with its tags.
* Readers of the replay's hash queries on the shared lazy oracle: `lazyReader` (`I`) and `refillReader` (`HW`, `H`:
  an untouched site is refilled from the swapped law as a unit; a partially touched one is answered lazily). Route M
  never reads a collector-mask position (its replay asks only the non-collector mask sites), so
  there is no virtual reader.
* `runReader`: a `FreeQuery CrtSpec` program run on the lazy oracle through a reader.

Everything here is a definition or a decoding lemma; nothing is `sorry`.
-/

import Construction.CRT.Params
import Construction.CRT.Query
import Cryptography.LazyOracle
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Kriterion.CRT.Privacy

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.CRT

/-! ### Tag fields (`((((((fam·2 + coord)·128 + idx)·4 + stage)·16 + level)·2^16 + slot)·64 + part)`) -/

def tagPart (tag : ℕ) : ℕ := tag % 64
def tagSlot (tag : ℕ) : ℕ := tag / 64 % 65536
def tagLevel (tag : ℕ) : ℕ := tag / 4194304 % 16
def tagStage (tag : ℕ) : ℕ := tag / 67108864 % 4
def tagIdx (tag : ℕ) : ℕ := tag / 268435456 % 128
def tagCoord (tag : ℕ) : ℕ := tag / 34359738368 % 2
def tagFamily (tag : ℕ) : ℕ := tag / 68719476736

section Decode

variable {fam coord idx stage level slot part : ℕ}

/-- The fields of a tag in range. -/
structure TagInRange (coord idx stage level slot part : ℕ) : Prop where
  coord : coord < 2
  idx : idx < 128
  stage : stage < 4
  level : level < 16
  slot : slot < 65536
  part : part < 64

theorem tagPart_tagCode (h : TagInRange coord idx stage level slot part) :
    tagPart (tagCode fam coord idx stage level slot part) = part := by
  have := h.part; unfold tagPart tagCode; omega

theorem tagSlot_tagCode (h : TagInRange coord idx stage level slot part) :
    tagSlot (tagCode fam coord idx stage level slot part) = slot := by
  have := h.part; have := h.slot; unfold tagSlot tagCode; omega

theorem tagLevel_tagCode (h : TagInRange coord idx stage level slot part) :
    tagLevel (tagCode fam coord idx stage level slot part) = level := by
  have := h.part; have := h.slot; have := h.level; unfold tagLevel tagCode; omega

theorem tagStage_tagCode (h : TagInRange coord idx stage level slot part) :
    tagStage (tagCode fam coord idx stage level slot part) = stage := by
  have := h.part; have := h.slot; have := h.level; have := h.stage; unfold tagStage tagCode; omega

theorem tagIdx_tagCode (h : TagInRange coord idx stage level slot part) :
    tagIdx (tagCode fam coord idx stage level slot part) = idx := by
  have := h.part; have := h.slot; have := h.level; have := h.stage; have := h.idx
  unfold tagIdx tagCode; omega

theorem tagCoord_tagCode (h : TagInRange coord idx stage level slot part) :
    tagCoord (tagCode fam coord idx stage level slot part) = coord := by
  have := h.part; have := h.slot; have := h.level; have := h.stage; have := h.idx; have := h.coord
  unfold tagCoord tagCode; omega

theorem tagFamily_tagCode (h : TagInRange coord idx stage level slot part) :
    tagFamily (tagCode fam coord idx stage level slot part) = fam := by
  have := h.part; have := h.slot; have := h.level; have := h.stage; have := h.idx; have := h.coord
  unfold tagFamily tagCode; omega

/-- Distinct in-range fields give distinct tags (each position has its own tag). -/
theorem tagCode_injective {fam' coord' idx' stage' level' slot' part' : ℕ}
    (h : TagInRange coord idx stage level slot part) (h' : TagInRange coord' idx' stage' level' slot' part')
    (same : tagCode fam coord idx stage level slot part = tagCode fam' coord' idx' stage' level' slot' part') :
    fam = fam' ∧ coord = coord' ∧ idx = idx' ∧ stage = stage' ∧ level = level' ∧ slot = slot' ∧ part = part' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← tagFamily_tagCode (fam := fam) h, same, tagFamily_tagCode h']
  · rw [← tagCoord_tagCode (fam := fam) h, same, tagCoord_tagCode h']
  · rw [← tagIdx_tagCode (fam := fam) h, same, tagIdx_tagCode h']
  · rw [← tagStage_tagCode (fam := fam) h, same, tagStage_tagCode h']
  · rw [← tagLevel_tagCode (fam := fam) h, same, tagLevel_tagCode h']
  · rw [← tagSlot_tagCode (fam := fam) h, same, tagSlot_tagCode h']
  · rw [← tagPart_tagCode (fam := fam) h, same, tagPart_tagCode h']

end Decode

/-- A labelled hash input `label + 2^128 · tag` decodes to its tag (labels are below `2^128`). -/
theorem hashInput_tag (label : Block) (tag : ℕ) : hashInput label tag / 2 ^ 128 = tag := by
  unfold hashInput
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.div_eq_of_lt label.isLt, Nat.zero_add]

/-! ### Hot positions at an input (a function of the input alone) -/

/-- The value of coordinate `κ` of an input (`x` for `κ = 0`). -/
def coordValue (u : AffineInput) (κ : ℕ) : ℕ := if κ = 0 then u.x.val else u.y.val

/-- The stage value of extraction stage `stage` of an odd row at word value `σ`: `σ mod 2^w0` for stage 0,
`⌊σ / 2^w0⌋ mod 2^w1` for stage 1. -/
def stageValue (row : OddRow) (σ stage : ℕ) : ℕ :=
  if stage = 0 then σ % 2 ^ row.width0 else σ / 2 ^ row.width0 % 2 ^ row.width1

/-- **The hot positions of the conversion and body layers at input `u`** (families 0 to 6). A tree level `n` is hot at the slot `s mod 2^n` of its stage value `s`; a cast at the leaf `s`;
growth at bit position `n` at `σ mod 2^n`; fold `j` at `(σ mod 2^j) mod m`; the body at `v mod m`. -/
def hotTag (T : CrtTable) (u : AffineInput) (tag : ℕ) : Bool :=
  let κ := tagCoord tag
  let idx := tagIdx tag
  let level := tagLevel tag
  let slot := tagSlot tag
  let v := coordValue u κ
  match tagFamily tag with
  | 0 => slot == T.chunkValue v idx % 2 ^ level
  | 1 => slot == T.chunkValue v idx
  | 6 =>
    if h : idx < T.count then slot == v % T.modulus ⟨idx, h⟩ else false
  | fam =>
    if h : idx < T.count then
      match T.kind ⟨idx, h⟩ with
      | .chunkZero => false
      | .odd row =>
        let m := T.modulus ⟨idx, h⟩
        let σ := T.wordValue m v
        match fam with
        | 2 => slot == stageValue row σ (tagStage tag) % 2 ^ level
        | 3 => slot == stageValue row σ (tagStage tag)
        | 4 => slot == σ % 2 ^ level
        | 5 => slot == σ % 2 ^ level % m
        | _ => false
    else false

/-! ### Sites (F4) -/

/-- A site: the pad vector of one `(coordinate, modulus index, residue)` (family 6), or one mask site
`(stage, site)` (family 7: stage 0 the 273 collector sites, stage 1 the 182 paired sites). -/
inductive SiteId where
  | pad (coord idx residue : ℕ)
  | mask (stage site : ℕ)
deriving DecidableEq

/-- The site of a tag (families 6 and 7), if any. -/
def siteOf (tag : ℕ) : Option SiteId :=
  match tagFamily tag with
  | 6 => some (.pad (tagCoord tag) (tagIdx tag) (tagSlot tag))
  | 7 => some (.mask (tagStage tag) (tagSlot tag))
  | _ => none

/-- The site layout of the swap and the refill: how many answers each site reads, and the swapped tape's law of
the answers of an untouched site (a uniform target, then answers uniform on its fibre under the site's reading:
D6's fraction reading for pads, `sampleFp` for masks). -/
structure SiteLayout where
  /-- Every site of the layer (the pad sites of both coordinates and all moduli, the 501 mask sites). -/
  sites : List SiteId
  answers : SiteId → ℕ
  law : SiteId → PMF (List (Block × Block))

/-- The tags of a site. -/
def siteTags (layout : SiteLayout) : SiteId → List ℕ
  | .pad κ i ρ => (List.range (layout.answers (.pad κ i ρ))).map fun j => tagCode Family.body κ i 0 0 ρ j
  | .mask st k => (List.range (layout.answers (.mask st k))).map fun j => tagCode Family.mask 0 0 st 0 k j

/-- The points of a site read at a label: `label + 2^128 · tag` for each of its tags. -/
def sitePoints (layout : SiteLayout) (site : SiteId) (label : ℕ) : List BaseField :=
  (siteTags layout site).map fun tag => ((label + 2 ^ 128 * tag : ℕ) : BaseField)

/-- The collector-mask positions (family 7, stage 0): route M programs them; the replay never asks them. -/
def isCollectorMaskTag (tag : ℕ) : Bool := tagFamily tag == 7 && tagStage tag == 0

/-! ### Readers on the shared lazy oracle -/

variable {FI EI : Type}

/-- A reader answers one hash query of the CRT layer (a natural input) on the lazy oracle. -/
abbrev Reader (FI EI : Type) :=
  ℕ → LazyOracle.State FI EI → PMF ((Block × Block) × LazyOracle.State FI EI)

/-- `I`'s reader: the shared lazy oracle, position by position. -/
noncomputable def lazyReader [DecidableEq FI] [DecidableEq EI] : Reader FI EI := fun input state =>
  LazyOracle.query (.hash (input : BaseField)) state

/-- A site is untouched when none of its points is in the table. -/
noncomputable def untouched (points : List BaseField) (state : LazyOracle.State FI EI) : Bool :=
  points.all fun point => (LazyOracle.lookup (.hash point) state).isNone

/-- Install answers at fresh points (a failed program is skipped; on an untouched site none fails). -/
noncomputable def installPoints [DecidableEq FI] [DecidableEq EI] (pairs : List (BaseField × (Block × Block)))
    (state : LazyOracle.State FI EI) : LazyOracle.State FI EI :=
  pairs.foldl (fun current pair => (LazyOracle.program (.hash pair.1) pair.2 current).getD current) state

/-- **`HW`'s and `H`'s reader (F4).** The first query at a pad or mask site whose points are all untouched draws the
whole site from the swapped law and installs it, then answers the query lazily on the installed state; a query at a
partially or fully touched site, or outside every site, is answered lazily. On a well-formed query the input is one
of the site's points, so the lazy answer is the installed one; on an input whose tag decodes to a site but whose
point is not among its points, the answer is a recorded fresh draw, never a phantom. -/
noncomputable def refillReader [DecidableEq FI] [DecidableEq EI] (layout : SiteLayout) : Reader FI EI :=
  fun input state =>
    match siteOf (input / 2 ^ 128) with
    | none => lazyReader input state
    | some site =>
      let points := sitePoints layout site (input % 2 ^ 128)
      if untouched points state then
        (layout.law site).bind fun answers => lazyReader input (installPoints (points.zip answers) state)
      else lazyReader input state

/-- A `FreeQuery CrtSpec` program run on the lazy oracle through a reader. -/
noncomputable def runReader (reader : Reader FI EI) {α : Type} :
    FreeQuery CrtSpec α → LazyOracle.State FI EI → PMF (α × LazyOracle.State FI EI)
  | .pure value, state => PMF.pure (value, state)
  | .query input next, state =>
    (reader input state).bind fun answered => runReader reader (next answered.1) answered.2

end Kriterion.CRT.Privacy
