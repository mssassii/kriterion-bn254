/-
**Tag paths of CRT programs**: along every path of a program, every query is a labelled input
`hashInput label tag` whose tag is `tagCode` of a key in a given set, the keys are in range (`TagKey.InRange`, so the
tag is below `2 ^ 40` and the input below `2 ^ 168 < p`), the keys along one path are pairwise distinct, and every
site (a pad vector, family 6, or a mask site, family 7; `Sites.siteOf`) is asked at one label only along a path.

* `TagKey`, `TagKey.code`, `TagKey.InRange`, `TagKey.code_injective`, `TagKey.code_lt`, `TagKey.site`;
* `KeyRun S Q seen program` (keys in `S`, fresh against the keys of `seen` and against each other, site labels
  consistent with `seen`, every final (value, history) in `Q`), its sequencing rule `KeyRun.bind` and history
  extension `KeyRun.extend`;
* `Tagged S program` (from the empty history, keys of the final history in `S`), with the combinators
  `Tagged.pure`, `Tagged.mono`, `Tagged.bind` (disjoint key sets with disjoint sites), `Tagged.vector`,
  `Tagged.tableM`, and the single queries `Tagged.askN`, `Tagged.h128M`, `Tagged.hlongM` (one label, one site
  allowed).

The garbler's and the replay's programs are built from these combinators block by block (`Paths/Blocks.lean`).
-/

import Construction.CRT.Coord
import Proof.Privacy.CRT.Sites

namespace Kriterion.CRT.Paths

open Cryptography Kriterion.ArgoMAC

/-! ### Keys -/

/-- The seven fields of a tag (`tagCode fam coord idx stage level slot part`). -/
structure TagKey where
  fam : Nat
  coord : Nat
  idx : Nat
  stage : Nat
  level : Nat
  slot : Nat
  part : Nat
deriving DecidableEq

namespace TagKey

/-- The tag of a key. -/
def code (k : TagKey) : Nat := tagCode k.fam k.coord k.idx k.stage k.level k.slot k.part

/-- The field bounds of `tagCode`. -/
def InRange (k : TagKey) : Prop :=
  k.fam < 16 ∧ k.coord < 2 ∧ k.idx < 128 ∧ k.stage < 4 ∧ k.level < 16 ∧ k.slot < 65536 ∧ k.part < 64

theorem code_lt {k : TagKey} (range : k.InRange) : k.code < 2 ^ 40 := by
  obtain ⟨fam, coord, idx, stage, level, slot, part⟩ := range
  unfold code tagCode
  omega

/-- **`tagCode` is injective on keys in range.** -/
theorem code_injective {k k' : TagKey} (range : k.InRange) (range' : k'.InRange)
    (same : k.code = k'.code) : k = k' := by
  obtain ⟨fam, coord, idx, stage, level, slot, part⟩ := k
  obtain ⟨fam', coord', idx', stage', level', slot', part'⟩ := k'
  obtain ⟨hf, hc, hi, hs, hl, hsl, hp⟩ := range
  obtain ⟨hf', hc', hi', hs', hl', hsl', hp'⟩ := range'
  simp only [code, tagCode] at same hf hc hi hs hl hsl hp hf' hc' hi' hs' hl' hsl' hp'
  have partSame : part = part' := by omega
  have slotSame : slot = slot' := by omega
  have levelSame : level = level' := by omega
  have stageSame : stage = stage' := by omega
  have idxSame : idx = idx' := by omega
  have coordSame : coord = coord' := by omega
  have famSame : fam = fam' := by omega
  subst partSame slotSame levelSame stageSame idxSame coordSame famSame
  rfl

/-- The site of a key (`Sites.siteOf` of its code, `pad` for family 6 and `mask` for family 7). -/
def site (k : TagKey) : Option Privacy.SiteId :=
  match k.fam with
  | 6 => some (.pad k.coord k.idx k.slot)
  | 7 => some (.mask k.stage k.slot)
  | _ => none

end TagKey

/-! ### Paths -/

/-- The keys of a list of (key, label) pairs. -/
abbrev keysOf (seen : List (TagKey × Block)) : List TagKey := seen.map Prod.fst

/-- A key is compatible with the keys already asked at their labels: a key of the same site was asked at the same
label. -/
def SiteLabel (seen : List (TagKey × Block)) (key : TagKey) (label : Block) : Prop :=
  ∀ p ∈ seen, p.1.site = key.site → key.site ≠ none → p.2 = label

/-- **A tag run**: along every path of the program, every query is `hashInput label tag` with `tag` the code of a
key in `S`, in range, not among the keys of `seen`, and asked at the label of every earlier key of its site; every
leaf's value and final history satisfy `Q`. -/
inductive KeyRun {α : Type} (S : Set TagKey) (Q : α → List (TagKey × Block) → Prop) :
    List (TagKey × Block) → CM α → Prop
  | pure (seen : List (TagKey × Block)) (value : α) (post : Q value seen) :
      KeyRun S Q seen (FreeQuery.pure value)
  | query (seen : List (TagKey × Block)) (label : Block) (tag : Nat) (key : TagKey)
      (next : Block × Block → CM α) (coded : key.code = tag) (member : key ∈ S)
      (range : key.InRange) (fresh : key ∉ keysOf seen) (sameLabel : SiteLabel seen key label)
      (rest : ∀ answer, KeyRun S Q ((key, label) :: seen) (next answer)) :
      KeyRun S Q seen (FreeQuery.query (hashInput label tag) next)

/-- **Tagged**: every query is labelled by a key of `S`, in range, pairwise distinct and site-consistent along every
path (from the empty history). -/
def Tagged {α : Type} (S : Set TagKey) (program : CM α) : Prop :=
  KeyRun S (fun _ seen => ∀ p ∈ seen, p.1 ∈ S) [] program

/-- Two key sets share no site. -/
def SiteDisjoint (S S' : Set TagKey) : Prop :=
  ∀ k ∈ S, ∀ k' ∈ S', k.site = k'.site → k.site = none

/-- Key sets without sites are site-disjoint from every set. -/
theorem siteDisjoint_of_none {S S' : Set TagKey} (none : ∀ k ∈ S, k.site = Option.none) :
    SiteDisjoint S S' := fun k inS _ _ _ => none k inS

namespace KeyRun

variable {α β : Type}

theorem mono {S S' : Set TagKey} {Q Q' : α → List (TagKey × Block) → Prop} {seen : List (TagKey × Block)}
    {program : CM α} (run : KeyRun S Q seen program) (sub : S ⊆ S') (weaker : ∀ v s, Q v s → Q' v s) :
    KeyRun S' Q' seen program := by
  induction run with
  | pure seen value post => exact .pure _ value (weaker _ _ post)
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
      exact .query _ label tag key next coded (sub member) range fresh sameLabel ih

/-- **Sequencing.** -/
theorem bind {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop} {R : β → List (TagKey × Block) → Prop}
    {seen : List (TagKey × Block)} {program : CM α} {next : α → CM β} (run : KeyRun S Q seen program)
    (rest : ∀ value seen', Q value seen' → KeyRun S R seen' (next value)) :
    KeyRun S R seen (program >>= next) := by
  induction run with
  | pure seen value post => exact rest value seen post
  | query seen label tag key step coded member range fresh sameLabel restRun ih =>
      exact .query _ label tag key _ coded member range fresh sameLabel fun answer => ih answer

/-- The keys of the final history are the start's and keys of `S`. -/
theorem keys_final {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop} {seen : List (TagKey × Block)}
    {program : CM α} (run : KeyRun S Q seen program) :
    KeyRun S (fun v s => Q v s ∧ ∃ added, s = added ++ seen ∧ ∀ p ∈ added, p.1 ∈ S) seen program := by
  induction run with
  | pure seen value post => exact .pure _ value ⟨post, [], rfl, fun _ inside => absurd inside List.not_mem_nil⟩
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
      refine .query _ label tag key next coded member range fresh sameLabel fun answer =>
        (ih answer).mono le_rfl fun v s holds => ⟨holds.1, ?_⟩
      obtain ⟨added, same, inS⟩ := holds.2
      refine ⟨added ++ [(key, label)], by rw [same, List.append_assoc]; rfl, fun p inside => ?_⟩
      rcases List.mem_append.mp inside with old | new
      · exact inS p old
      · rw [List.mem_singleton.mp new]
        exact member

/-- More history that the program's keys never meet (neither the keys nor their sites). -/
theorem extend {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop} {seen : List (TagKey × Block)}
    {program : CM α} (run : KeyRun S Q seen program) (extra : List (TagKey × Block))
    (away : ∀ k ∈ S, k ∉ keysOf extra ∧ ∀ p ∈ extra, p.1.site = k.site → k.site = none) :
    KeyRun S (fun v s => ∃ s0, s = s0 ++ extra ∧ Q v s0) (seen ++ extra) program := by
  induction run with
  | pure seen value post => exact .pure _ value ⟨seen, rfl, post⟩
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
      refine .query _ label tag key next coded member range ?_ ?_ fun answer => ih answer
      · simp only [keysOf, List.map_append, List.mem_append, not_or]
        exact ⟨fresh, (away key member).1⟩
      · intro p inside sameSite notNone
        rcases List.mem_append.mp inside with old | new
        · exact sameLabel p old sameSite notNone
        · exact absurd ((away key member).2 p new sameSite) notNone

end KeyRun

namespace Tagged

variable {α β : Type}

theorem pure (S : Set TagKey) (value : α) : Tagged S (Pure.pure value : CM α) :=
  KeyRun.pure _ value fun _ inside => absurd inside List.not_mem_nil

theorem mono {S S' : Set TagKey} {program : CM α} (tagged : Tagged S program) (sub : S ⊆ S') :
    Tagged S' program :=
  KeyRun.mono tagged sub fun _ _ keys p inside => sub (keys p inside)

/-- **Sequencing**: keys of the two parts in disjoint sets, no shared site. -/
theorem bind {S S' : Set TagKey} {program : CM α} {next : α → CM β} (first : Tagged S program)
    (rest : ∀ value, Tagged S' (next value)) (disjoint : Disjoint S S') (sites : SiteDisjoint S S') :
    Tagged (S ∪ S') (program >>= next) := by
  refine KeyRun.bind (KeyRun.mono first Set.subset_union_left fun _ _ holds => holds)
    fun value seen' keys => ?_
  have extended := (rest value).extend seen' fun k inS' =>
    ⟨fun inside => by
      obtain ⟨p, inSeen, same⟩ := List.mem_map.mp inside
      have inS := keys p inSeen
      rw [same] at inS
      exact Set.disjoint_left.mp disjoint inS inS',
    fun p inside sameSite => by
      rw [← sameSite]
      exact sites p.1 (keys p inside) k inS' sameSite⟩
  rw [List.nil_append] at extended
  refine extended.mono Set.subset_union_right fun v s holds => ?_
  obtain ⟨s0, same, keys0⟩ := holds
  intro p inside
  rw [same] at inside
  rcases List.mem_append.mp inside with new | old
  · exact Or.inr (keys0 p new)
  · exact Or.inl (keys p old)

/-- Sequencing into a set that contains both parts. -/
theorem bind' {S S' U : Set TagKey} {program : CM α} {next : α → CM β} (first : Tagged S program)
    (rest : ∀ value, Tagged S' (next value)) (disjoint : Disjoint S S') (sites : SiteDisjoint S S')
    (sub : S ∪ S' ⊆ U) : Tagged U (program >>= next) :=
  (bind first rest disjoint sites).mono sub

/-- A query-free continuation. -/
theorem bind_pure {S : Set TagKey} {program : CM α} (first : Tagged S program) (f : α → β) :
    Tagged S (program >>= fun value => Pure.pure (f value)) :=
  KeyRun.bind first fun value _ keys => KeyRun.pure _ (f value) keys

/-- A continuation without queries. -/
theorem bind_empty {S : Set TagKey} {program : CM α} {next : α → CM β} (first : Tagged S program)
    (rest : ∀ value, Tagged ∅ (next value)) : Tagged S (program >>= next) :=
  (bind first rest (Set.disjoint_empty S) fun _ _ _ inside => absurd inside id).mono (by simp)

/-- A branch. -/
theorem ite {S : Set TagKey} {c : Prop} [Decidable c] {yes no : CM α} (onYes : c → Tagged S yes)
    (onNo : ¬ c → Tagged S no) : Tagged S (if c then yes else no) := by
  split
  · exact onYes ‹c›
  · exact onNo ‹¬ c›

/-- **A loop** whose iterations have pairwise disjoint key sets without shared sites. -/
theorem vector {S : Nat → Set TagKey} :
    ∀ (count : Nat) {program : Fin count → CM α},
      (∀ index : Fin count, Tagged (S index.val) (program index)) →
      (∀ i j, i < count → j < count → i ≠ j → Disjoint (S i) (S j) ∧ SiteDisjoint (S i) (S j)) →
      Tagged {k | ∃ i < count, k ∈ S i} (FreeQuery.vector count program)
  | 0, _, _, _ => pure _ _
  | count + 1, program, each, disjoint => by
      simp only [FreeQuery.vector]
      have front := vector count (program := fun index => program index.castSucc)
        (fun index => each index.castSucc) fun i j hi hj => disjoint i j (by omega) (by omega)
      refine bind' front (fun values => bind_pure (each (Fin.last count)) _) ?_ ?_ ?_
      · refine Set.disjoint_left.mpr fun k inFront inLast => ?_
        obtain ⟨i, small, inS⟩ := inFront
        exact Set.disjoint_left.mp (disjoint i count (by omega) (by omega) (by omega)).1 inS inLast
      · intro k inFront k' inLast sameSite
        obtain ⟨i, small, inS⟩ := inFront
        exact (disjoint i count (by omega) (by omega) (by omega)).2 k inS k' inLast sameSite
      · rintro k (⟨i, small, inS⟩ | inLast)
        · exact ⟨i, by omega, inS⟩
        · exact ⟨count, by omega, inLast⟩

/-- A loop stored as a function. -/
theorem tableM {S : Nat → Set TagKey} (count : Nat) {program : Fin count → CM α}
    (each : ∀ index : Fin count, Tagged (S index.val) (program index))
    (disjoint : ∀ i j, i < count → j < count → i ≠ j → Disjoint (S i) (S j) ∧ SiteDisjoint (S i) (S j)) :
    Tagged {k | ∃ i < count, k ∈ S i} (CRT.tableM count program) :=
  bind_pure (vector count each disjoint) _

/-- One query. -/
theorem askN (S : Set TagKey) (label : Block) (tag : Nat) (key : TagKey) (coded : key.code = tag)
    (member : key ∈ S) (range : key.InRange) : Tagged S (CRT.askN (hashInput label tag)) :=
  KeyRun.query _ label tag key _ coded member range List.not_mem_nil
    (fun _ inside => absurd inside List.not_mem_nil) fun answer =>
      KeyRun.pure _ answer fun p inside => by
        rw [List.mem_singleton.mp inside]
        exact member

/-- The one-block hash. -/
theorem h128M (S : Set TagKey) (label : Block) (tag : Nat) (key : TagKey) (coded : key.code = tag)
    (member : key ∈ S) (range : key.InRange) : Tagged S (CRT.h128M label tag) :=
  KeyRun.bind (askN S label tag key coded member range) fun answer _ keys =>
    KeyRun.pure _ answer.1 keys

/-- The history of `count` queries at one label. -/
def oneLabel (key : Nat → TagKey) (label : Block) : Nat → List (TagKey × Block)
  | 0 => []
  | n + 1 => (key n, label) :: oneLabel key label n

theorem mem_oneLabel {key : Nat → TagKey} {label : Block} {n : Nat} {p : TagKey × Block}
    (inside : p ∈ oneLabel key label n) : ∃ j < n, p = (key j, label) := by
  induction n with
  | zero => exact absurd inside List.not_mem_nil
  | succ n ih =>
      rcases List.mem_cons.mp inside with first | old
      · exact ⟨n, by omega, first⟩
      · obtain ⟨j, small, same⟩ := ih old
        exact ⟨j, by omega, same⟩

/-- **`count` queries at one label** at keys `key 0, …, key (count − 1)` (pairwise distinct, possibly of one site). -/
theorem vector_oneLabel (label : Block) (tagOf : Nat → Nat) (key : Nat → TagKey) (bound : Nat)
    (coded : ∀ j, j < bound → (key j).code = tagOf j) (range : ∀ j, j < bound → (key j).InRange)
    (injective : ∀ i j, i < bound → j < bound → key i = key j → i = j) :
    ∀ n, n ≤ bound → KeyRun {k | ∃ j < bound, k = key j} (fun _ seen => seen = oneLabel key label n) []
      (FreeQuery.vector n fun j : Fin n => CRT.askN (hashInput label (tagOf j.val)))
  | 0, _ => KeyRun.pure _ _ rfl
  | n + 1, small => by
      simp only [FreeQuery.vector]
      refine KeyRun.bind (vector_oneLabel label tagOf key bound coded range injective n (by omega))
        fun values seen' same => ?_
      subst same
      refine KeyRun.query _ label (tagOf n) (key n) _ (coded n (by omega)) ⟨n, by omega, rfl⟩
        (range n (by omega)) (fun inside => ?_) (fun p inside _ _ => ?_) fun answer => ?_
      · obtain ⟨p, inSeen, same⟩ := List.mem_map.mp inside
        obtain ⟨j, jSmall, pIs⟩ := mem_oneLabel inSeen
        rw [pIs] at same
        exact absurd (injective j n (by omega) (by omega) same) (by omega)
      · obtain ⟨j, jSmall, pIs⟩ := mem_oneLabel inside
        rw [pIs]
      · exact KeyRun.pure _ _ rfl

/-- **The long hash**: `count` answers at one label, the codes of `key 0, …, key (count − 1)`. -/
theorem hlongM (label : Block) (tagOf : Nat → Nat) (count : Nat) (key : Nat → TagKey)
    (coded : ∀ j, j < count → (key j).code = tagOf j) (range : ∀ j, j < count → (key j).InRange)
    (injective : ∀ i j, i < count → j < count → key i = key j → i = j) :
    Tagged {k | ∃ j < count, k = key j} (CRT.hlongM label tagOf count) := by
  unfold CRT.hlongM
  refine KeyRun.bind (vector_oneLabel label tagOf key count coded range injective count le_rfl)
    fun values seen' same => KeyRun.pure _ _ fun p inside => ?_
  rw [same] at inside
  obtain ⟨j, small, pIs⟩ := mem_oneLabel inside
  exact ⟨j, small, by rw [pIs]⟩

/-- **`count` answers at one label, stored** (`siteAnswersM`): the codes of `key 0, …, key (count − 1)`. -/
theorem oneLabelTable (label : Block) (tagOf : Nat → Nat) (count : Nat) (key : Nat → TagKey)
    (coded : ∀ j, j < count → (key j).code = tagOf j) (range : ∀ j, j < count → (key j).InRange)
    (injective : ∀ i j, i < count → j < count → key i = key j → i = j) :
    Tagged {k | ∃ j < count, k = key j}
      (CRT.tableM count fun j => CRT.askN (hashInput label (tagOf j.val))) := by
  unfold CRT.tableM
  refine KeyRun.bind (vector_oneLabel label tagOf key count coded range injective count le_rfl)
    fun values seen' same => KeyRun.pure _ _ fun p inside => ?_
  rw [same] at inside
  obtain ⟨j, small, pIs⟩ := mem_oneLabel inside
  exact ⟨j, small, by rw [pIs]⟩

end Tagged

end Kriterion.CRT.Paths
