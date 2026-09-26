/-
**P8, the wrap event read on a private state against the table** (for `CrtWrapGuess` and for `CrtMiddleFactor` flag input).

`H8.replayWraps source u table` reads the table only through the two `coordEvalM` programs of the replay's conversion
blocks, which are `Entry.replayConv`'s queries. So:

* `eval_congr`: a program's value depends only on the hash at the inputs its path asks (`queriesAlong`);
* `replayWraps_congr`: two tables whose `tagHash` agree at `replayConv`'s queries have the same wrap event;
* `tagHash_stateTable`: a state that stores a labelled query `n` (below `p`), every stored point of that tag
  holding `T`'s answer, reads `tagHash T n` through `stateTable`;
* `programmedTable_tagHash`: the programmed table agrees with the table off the collector tags, so at
  `replayConv`'s queries (families 0 to 6).
-/

import Proof.Privacy.CRT.Flags.NoAbort
import Proof.Privacy.CRT.Laws.TableRun
import Proof.Privacy.CRT.Paths.Refill
import Proof.Privacy.CRT.Paths.Reach
import Proof.Privacy.CRT.Laws.MiddleOn

namespace Kriterion.CRT.Privacy.Flags

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT Kriterion.CRT.Privacy
open Kriterion.CRT.Privacy.PublicFirst Kriterion.CRT.Privacy.H8 Kriterion.CRT.Privacy.Instance
open Kriterion.CRT.Paths (TagKey KeyRun Tagged)
open scoped ENNReal

noncomputable section

/-! ### 1. Paths and evaluation -/

/-- **The inputs a program asks along its path under a hash.** -/
def queriesAlong (H : HashN) {α : Type} : CM α → List ℕ
  | .pure _ => []
  | .query n next => n :: queriesAlong H (next (H n))

/-- **A program's value depends only on the hash at the inputs its path asks.** -/
theorem eval_congr (H H' : HashN) {α : Type} :
    ∀ R : CM α, (∀ n ∈ queriesAlong H R, H n = H' n) → R.eval H = R.eval H'
  | .pure _, _ => rfl
  | .query n next, agree => by
    have head : H n = H' n := agree n List.mem_cons_self
    show (next (H n)).eval H = (next (H' n)).eval H'
    rw [← head]
    exact eval_congr H H' (next (H n)) fun m member => agree m (List.mem_cons_of_mem _ member)

theorem queriesAlong_bind (H : HashN) {α β : Type} (A : CM α) (f : α → CM β) :
    queriesAlong H (A >>= f) = queriesAlong H A ++ queriesAlong H (f (A.eval H)) := by
  induction A with
  | pure value => rfl
  | query n next ih =>
    show n :: queriesAlong H (FreeQuery.bind (next (H n)) f) = n :: (queriesAlong H (next (H n)) ++ _)
    rw [show FreeQuery.bind (next (H n)) f = next (H n) >>= f from rfl, ih]
    rfl

theorem queriesAlong_pure (H : HashN) {α : Type} (value : α) : queriesAlong H (pure value : CM α) = [] := rfl

theorem queriesAlong_bind_bind_pure (H : HashN) {α β γ : Type} (A : CM α) (B : CM β) (c : α → β → γ) :
    queriesAlong H (A >>= fun a => B >>= fun b => pure (c a b)) = queriesAlong H A ++ queriesAlong H B := by
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil]

/-! ### 2. The wrap event depends on the table only at `replayConv`'s queries -/

section Wrap

variable [FieldCertificate] [GroupCertificate]

/-- `replayConv`'s queries are those of its two coordinate programs. -/
theorem queriesAlong_replayConv (H : HashN) (published : Kriterion.CRT.Entry.Public) (u : AffineInput)
    (labels : LamportSignature) :
    queriesAlong H (Kriterion.CRT.Entry.replayConv published u labels) =
      queriesAlong H (coordEvalM Kriterion.CRT.Entry.table Kriterion.CRT.Entry.xCount 0
          (Kriterion.CRT.Entry.convOf published.crtX) (fun e => (published.recX.get e).val) u.x.val
          (Kriterion.CRT.Entry.labelX labels)) ++
        queriesAlong H (coordEvalM Kriterion.CRT.Entry.table Kriterion.CRT.Entry.yCount 1
          (Kriterion.CRT.Entry.convOf published.crtY) (fun e => (published.recY.get e).val) u.y.val
          (Kriterion.CRT.Entry.labelY labels)) := by
  unfold Kriterion.CRT.Entry.replayConv
  exact queriesAlong_bind_bind_pure H _ _ _

/-- **The CRT values depend on the table only at `replayConv`'s queries.** -/
theorem replayCrtValues_congr (source : (view).Source) (u : AffineInput) (T T' : TagTable)
    (agree : ∀ n ∈ queriesAlong (tagHash T)
      (Kriterion.CRT.Entry.replayConv ((view).publish source) u ((view).labels source u)),
      tagHash T n = tagHash T' n) :
    replayCrtValues source u T = replayCrtValues source u T' := by
  rw [queriesAlong_replayConv] at agree
  unfold replayCrtValues
  simp only
  rw [eval_congr (tagHash T) (tagHash T') _ fun n member => agree n (List.mem_append_left _ member),
    eval_congr (tagHash T) (tagHash T') _ fun n member => agree n (List.mem_append_right _ member)]

/-- **The wrap event depends on the table only at `replayConv`'s queries.** -/
theorem replayWraps_congr (source : (view).Source) (u : AffineInput) (T T' : TagTable)
    (agree : ∀ n ∈ queriesAlong (tagHash T)
      (Kriterion.CRT.Entry.replayConv ((view).publish source) u ((view).labels source u)),
      tagHash T n = tagHash T' n) :
    replayWraps source u T ↔ replayWraps source u T' := by
  unfold replayWraps
  rw [replayCrtValues_congr source u T T' agree]

end Wrap

/-! ### 3. Reading a state's table -/

section StateTable

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- **A state's table at a tag it stores** is the answer of its first stored point of that tag; if every stored
point of the tag holds `value`, it is `value`. -/
theorem stateTable_eq (st : LazyOracle.State FI EI) (tag : Fin (2 ^ 40)) (value : Block × Block)
    (present : ∃ x ∈ storedPoints st, tagOfInput x = tag)
    (holds : ∀ x v, st.hash.lookup x = some v → tagOfInput x = tag → Refill.hashCode.symm v = value) :
    stateTable st tag = value := by
  obtain ⟨x, xStored, xTag⟩ := present
  unfold stateTable
  cases found : st.hash.find? (fun pair => decide (tagOfInput pair.1 = tag)) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at found
    obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp xStored
    exact found pair pairMember (by simpa using xTag)
  | some pair =>
    have pairMember := List.mem_of_find?_eq_some found
    have pairTag : tagOfInput pair.1 = tag := by simpa using List.find?_some found
    obtain ⟨v, lookup⟩ := Option.isSome_iff_exists.mp
      (lookup_isSome_of_mem st.hash pair.1 (List.mem_map_of_mem pairMember))
    show ((st.hash.lookup pair.1).map Refill.hashCode.symm).getD (0, 0) = value
    rw [lookup]
    exact holds pair.1 v lookup pairTag

/-- **Reading a stored labelled query through `stateTable`.** -/
theorem tagHash_stateTable (st : LazyOracle.State FI EI) (T : TagTable) (n : ℕ)
    (small : ((n : BaseField)).val = n) (stored : (n : BaseField) ∈ storedPoints st)
    (holds : ∀ x v, st.hash.lookup x = some v → tagOfInput x = tagOfInput (n : BaseField) →
      Refill.hashCode.symm v = T (tagOfInput (n : BaseField))) :
    tagHash (stateTable st) n = tagHash T n := by
  have tagEq : tagOfInput (n : BaseField) = ⟨n / 2 ^ 128 % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ :=
    Laws.tagOfInput_small small
  show stateTable st ⟨n / 2 ^ 128 % 2 ^ 40, _⟩ = T ⟨n / 2 ^ 128 % 2 ^ 40, _⟩
  rw [← tagEq]
  exact stateTable_eq st _ _ ⟨(n : BaseField), stored, rfl⟩ holds

end StateTable

/-! ### 4. The programmed table off the collector tags -/

theorem programmedTable_apply (table : TagTable) :
    ∀ (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (tag : Fin (2 ^ 40)),
      (∀ entry ∈ drawn, tag ≠ collectorTag (collectorIndex entry.1) 0 ∧
        tag ≠ collectorTag (collectorIndex entry.1) 1) →
      programmedTable table drawn tag = table tag
  | [], _, _ => rfl
  | entry :: rest, tag, away => by
    unfold programmedTable
    rw [List.foldl_cons]
    have step : (Function.update (Function.update table (collectorTag (collectorIndex entry.1) 0)
        (entry.2.1.1, entry.2.1.2.1)) (collectorTag (collectorIndex entry.1) 1)
        (entry.2.1.2.2, entry.2.2)) tag = table tag := by
      rw [Function.update_of_ne (away entry List.mem_cons_self).2,
        Function.update_of_ne (away entry List.mem_cons_self).1]
    have rest' := programmedTable_apply (Function.update (Function.update table
        (collectorTag (collectorIndex entry.1) 0) (entry.2.1.1, entry.2.1.2.1))
        (collectorTag (collectorIndex entry.1) 1) (entry.2.1.2.2, entry.2.2)) rest tag
      fun other member => away other (List.mem_cons_of_mem _ member)
    unfold programmedTable at rest'
    rw [rest', step]

/-! ### 5. Tag runs: their queries and what their lazy runs store -/

section TagRuns

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- Every query along a tag run's path is a labelled input of one of its keys. -/
theorem keyRun_queries {α : Type} {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop}
    {seen : List (TagKey × Block)} {R : CM α} (run : KeyRun S Q seen R) (H : HashN) :
    ∀ n ∈ queriesAlong H R, ∃ key ∈ S, key.InRange ∧ ∃ label : Block, n = hashInput label key.code := by
  induction run with
  | pure seen value post =>
    intro n member
    simp [queriesAlong] at member
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
    intro n inPath
    rcases List.mem_cons.mp inPath with same | later
    · exact ⟨key, member, range, label, by rw [same, coded]⟩
    · exact ih (H (hashInput label tag)) n later

/-- A labelled input of a key in range is below `p` and has the key's tag. -/
theorem keyed_small {key : TagKey} (range : key.InRange) (label : Block) :
    ((hashInput label key.code : ℕ) : BaseField).val = hashInput label key.code :=
  Laws.val_natCast_small (hashInput_lt label (TagKey.code_lt range))

theorem keyed_tag {key : TagKey} (range : key.InRange) (label : Block) :
    tagOfInput ((hashInput label key.code : ℕ) : BaseField) = ⟨key.code, TagKey.code_lt range⟩ :=
  tagOfInput_hashInput label key.code (TagKey.code_lt range)

/-- **Two labelled inputs with the same tag have the same key.** -/
theorem keyed_tag_inj {key key' : TagKey} (range : key.InRange) (range' : key'.InRange) (label label' : Block)
    (same : tagOfInput ((hashInput label key.code : ℕ) : BaseField) =
      tagOfInput ((hashInput label' key'.code : ℕ) : BaseField)) : key = key' := by
  rw [keyed_tag range, keyed_tag range'] at same
  exact TagKey.code_injective range range' (Fin.mk.inj_iff.mp same)

/-- **What a lazy run of a tag run adds**: pairs prepended, each at a labelled input of one of its keys. -/
theorem keyRun_lazy_extra {α : Type} {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop}
    {seen : List (TagKey × Block)} {R : CM α} (run : KeyRun S Q seen R) :
    ∀ (σ : LazyOracle.State FI EI), ∀ p ∈ (runReader lazyReader R σ).support,
      ∃ extra : List (BaseField × Fin (Fintype.card (Block × Block))), p.2.hash = extra ++ σ.hash ∧
        ∀ x ∈ extra.map Prod.fst, ∃ key ∈ S, key.InRange ∧ ∃ label : Block, x = ((hashInput label key.code : ℕ) : BaseField) := by
  induction run with
  | pure seen value post =>
    intro σ p member
    simp only [runReader, PMF.mem_support_pure_iff] at member
    subst member
    exact ⟨[], rfl, fun x member => by simp at member⟩
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
    intro σ p pMember
    simp only [runReader] at pMember
    obtain ⟨a, aMember, pRest⟩ := (PMF.mem_support_bind_iff _ _ _).mp pMember
    obtain ⟨extra, hash, keys⟩ := ih a.1 a.2 p pRest
    unfold lazyReader LazyOracle.query at aMember
    simp only at aMember
    obtain ⟨b, inQuery, same⟩ := (PMF.mem_support_map_iff _ _ _).mp aMember
    subst same
    rcases hashQuery_support σ.hash _ b inQuery with ⟨kept, _⟩ | added
    · refine ⟨extra, ?_, keys⟩
      rw [hash]
      show extra ++ b.2 = extra ++ σ.hash
      rw [kept]
    · refine ⟨extra ++ [(((hashInput label tag : ℕ) : BaseField), b.1)], ?_, fun x xMember => ?_⟩
      · rw [hash]
        show extra ++ b.2 = _
        rw [added, List.append_assoc]
        rfl
      · rw [List.map_append, List.mem_append] at xMember
        rcases xMember with old | new
        · exact keys x old
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at new
          exact ⟨key, member, range, label, by rw [new, coded]⟩

/-- **What a successful program list adds**: pairs prepended at the requests' points. -/
theorem programHashAll_extra :
    ∀ (requests : List (BaseField × (Block × Block))) (σ σ' : LazyOracle.State FI EI),
      programHashAll requests σ = some σ' →
        ∃ extra : List (BaseField × Fin (Fintype.card (Block × Block))), σ'.hash = extra ++ σ.hash ∧
          ∀ x ∈ extra.map Prod.fst, x ∈ requests.map Prod.fst
  | [], σ, σ', done => by
    have same : σ = σ' := Option.some.inj done
    subst same
    exact ⟨[], rfl, fun x member => by simp at member⟩
  | (point, answer) :: rest, σ, σ', done => by
    have unfolded : programHashAll ((point, answer) :: rest) σ =
        (LazyOracle.program (.hash point) answer σ).bind (programHashAll rest) := rfl
    rw [unfolded] at done
    cases step : LazyOracle.program (.hash point) answer σ with
    | none =>
      rw [step] at done
      exact absurd done (by simp)
    | some middle =>
      rw [step] at done
      obtain ⟨extra, hash, keys⟩ := programHashAll_extra rest middle σ' done
      unfold LazyOracle.program at step
      simp only at step
      split at step
      · obtain rfl := Option.some.inj step
        refine ⟨extra ++ [(point, _)], by rw [hash, List.append_assoc]; rfl, fun x xMember => ?_⟩
        rw [List.map_append, List.mem_append] at xMember
        rcases xMember with old | new
        · exact List.mem_cons_of_mem _ (keys x old)
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at new
          rw [new]
          exact List.mem_cons_self
      · exact absurd step (by simp)

theorem lookup_append_of_not_mem {V : Type} (first second : List (BaseField × V)) (x : BaseField)
    (outside : x ∉ first.map Prod.fst) : (first ++ second).lookup x = second.lookup x := by
  rw [List.lookup_append]
  cases found : first.lookup x with
  | none => rfl
  | some v => exact absurd (mem_keys_of_lookup first x v found) outside

end TagRuns

/-! ### 6. The table run's points -/

/-- **A canonical program's queries along the table's path are among the table run's points.** -/
theorem mem_runPoints (layout : SiteLayout) (T : TagTable) {α : Type} {R : CM α}
    (canon : Laws.Canonical layout R) : ∀ n ∈ queriesAlong (tagHash T) R, (n : BaseField) ∈ Laws.runPoints layout T R := by
  induction canon with
  | pure value =>
    intro n member
    simp [queriesAlong] at member
  | query n next small onSite rest ih =>
    intro m inPath
    show (m : BaseField) ∈ Laws.pointsOf layout n ++ Laws.runPoints layout T (next (tagHash T n))
    rcases List.mem_cons.mp inPath with same | later
    · subst same
      refine List.mem_append_left _ ?_
      unfold Laws.pointsOf
      cases decode : siteOf (m / 2 ^ 128) with
      | none => exact List.mem_singleton_self _
      | some site => exact Laws.self_mem_sitePoints layout site m (onSite site decode).2
    · exact List.mem_append_right _ (ih (tagHash T n) m later)

/-! ### 7. The flag on the curve: the programmed table against the final private state -/

section OnCurve

variable [FieldCertificate] [GroupCertificate] [DecidableEq Empty]

theorem collectorKey_code (k j : ℕ) : (collectorKey k j).code = tagCode Family.mask 0 0 0 0 k j := rfl

theorem collectorTag_eq {k j : ℕ} (hk : k < 65536) (hj : j < 64) :
    collectorTag k j = ⟨(collectorKey k j).code, TagKey.code_lt (collectorKey_range hk hj)⟩ := by
  unfold collectorTag
  apply Fin.ext
  dsimp only
  rw [← collectorKey_code, Nat.mod_eq_of_lt (TagKey.code_lt (collectorKey_range hk hj))]

theorem collectorPoint_tag (K : Block) {k j : ℕ} (hk : k < 65536) (hj : j < 64) :
    tagOfInput (collectorPoint K k j) = ⟨(collectorKey k j).code, TagKey.code_lt (collectorKey_range hk hj)⟩ :=
  keyed_tag (collectorKey_range hk hj) K

/-- The request points are collector points. -/
theorem programRequests_points (K : Block) (drawn : List (BMR.Collector × ((Block × Block × Block) × Block)))
    (x : BaseField) (member : x ∈ (programRequests K drawn).map Prod.fst) :
    ∃ k j, k < 65536 ∧ j < 64 ∧ x = collectorPoint K k j := by
  unfold programRequests at member
  rw [List.map_flatMap, List.mem_flatMap] at member
  obtain ⟨entry, -, inPair⟩ := member
  have small : collectorIndex entry.1 < 65536 := lt_trans (Refill.collectorIndex_lt _) (by decide)
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at inPair
  rcases inPair with same | same
  · exact ⟨_, 0, small, by decide, same⟩
  · exact ⟨_, 1, small, by decide, same⟩

/-- **On the curve, the wrap event of the programmed table is that of the final private state.** -/
theorem replayWraps_final_iff (source : (view).Source) (u : AffineInput) (table : TagTable) (K : Block)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State Empty Empty)
    (programmed : programHashAll (programRequests K drawn)
      (Laws.tableFinal crtLayout table ((view).replayProgram ((view).publish source) u ((view).labels source u))
        LazyOracle.empty) = some installed)
    (shadowed : Unit × LazyOracle.State Empty Empty)
    (member : shadowed ∈ (runReader lazyReader (crtShadowOnCurve source u) installed).support) :
    replayWraps source u (programmedTable table drawn) ↔ replayWraps source u (stateTable shadowed.2) := by
  set R := (view).replayProgram ((view).publish source) u ((view).labels source u) with hR
  set conv := Kriterion.CRT.Entry.replayConv ((view).publish source) u ((view).labels source u) with hconv
  have tagged : Tagged Paths.replayConvKeys conv := Paths.replayConv_tagged _ u _
  have convInR : ∀ n ∈ queriesAlong (tagHash table) conv, n ∈ queriesAlong (tagHash table) R := by
    intro n inConv
    show n ∈ queriesAlong (tagHash table) ((view).replayConv _ u _ >>= _)
    rw [queriesAlong_bind]
    exact List.mem_append_left _ inConv
  have canon := Paths.replay_canonical ((view).publish source) u ((view).labels source u)
  have seen := (Laws.tableRun_empty (FI := Empty) (EI := Empty) crtLayout Laws.crtLayout_points table canon).2
  obtain ⟨extra₁, hash₁, keys₁⟩ := programHashAll_extra _ _ installed programmed
  have shadowTagged : Tagged Paths.digestKeys (crtShadowOnCurve source u) := by
    unfold crtShadowOnCurve
    exact Paths.Tagged.bind_pure (Paths.entryDigest_tagged _ u _) _
  obtain ⟨extra₂, hash₂, keys₂⟩ := keyRun_lazy_extra shadowTagged installed shadowed member
  -- the conversion queries: labelled inputs of conversion keys
  have convKey := keyRun_queries tagged (tagHash table)
  refine (replayWraps_congr source u table (programmedTable table drawn) ?_).symm.trans
    (replayWraps_congr source u table (stateTable shadowed.2) ?_)
  · intro n inConv
    obtain ⟨key, keyMember, range, label, rfl⟩ := convKey n inConv
    have fam : key.fam ≤ 6 := Paths.replayConvKeys_fam key keyMember
    show table _ = programmedTable table drawn _
    symm
    refine programmedTable_apply table drawn _ fun entry _ => ?_
    have small : collectorIndex entry.1 < 65536 := lt_trans (Refill.collectorIndex_lt _) (by decide)
    have tagEq : (⟨hashInput label key.code / 2 ^ 128 % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ :
        Fin (2 ^ 40)) = ⟨key.code, TagKey.code_lt range⟩ := by
      apply Fin.ext
      show hashInput label key.code / 2 ^ 128 % 2 ^ 40 = key.code
      rw [hashInput_div, Nat.mod_eq_of_lt (TagKey.code_lt range)]
    rw [tagEq]
    constructor <;> intro same <;>
      [rw [collectorTag_eq small (by decide)] at same; rw [collectorTag_eq small (by decide)] at same] <;>
      have keys := TagKey.code_injective range (collectorKey_range small (by decide)) (Fin.mk.inj_iff.mp same) <;>
      rw [keys] at fam <;> simp [collectorKey] at fam
  · intro n inConv
    obtain ⟨key, keyMember, range, label, rfl⟩ := convKey n inConv
    have fam : key.fam ≤ 6 := Paths.replayConvKeys_fam key keyMember
    have small := keyed_small range label
    symm
    refine tagHash_stateTable shadowed.2 table _ small ?_ ?_
    · -- stored: in the table run's points, then kept by the programs and the shadow
      have inPoints := mem_runPoints crtLayout table canon _ (convInR _ inConv)
      have finalLookup := seen.2.2 ((hashInput label key.code : ℕ) : BaseField)
      rw [if_pos inPoints] at finalLookup
      have inFinal : ((hashInput label key.code : ℕ) : BaseField) ∈
          storedPoints (Laws.tableFinal crtLayout table R LazyOracle.empty) :=
        mem_keys_of_lookup _ _ _ finalLookup
      show _ ∈ shadowed.2.hash.map Prod.fst
      rw [hash₂, hash₁, List.map_append, List.map_append]
      exact List.mem_append_right _ (List.mem_append_right _ inFinal)
    · intro x v found sameTag
      -- `x` has the conversion tag, so it is neither a digest point nor a collector point
      have notDigest : x ∉ extra₂.map Prod.fst := by
        intro inExtra
        obtain ⟨key', keyMember', range', label', rfl⟩ := keys₂ x inExtra
        have := keyed_tag_inj range' range label' label sameTag
        rw [this] at keyMember'
        rcases Paths.digestKeys_fam key keyMember' with eight | nine <;> omega
      have notCollector : x ∉ extra₁.map Prod.fst := by
        intro inExtra
        obtain ⟨k, j, hk, hj, rfl⟩ := programRequests_points K drawn x (keys₁ x inExtra)
        have := keyed_tag_inj (collectorKey_range hk hj) range K label sameTag
        rw [← this] at fam
        simp [collectorKey] at fam
      rw [hash₂, lookup_append_of_not_mem _ _ _ notDigest, hash₁,
        lookup_append_of_not_mem _ _ _ notCollector, seen.2.2 x] at found
      split at found
      · obtain rfl := Option.some.inj found
        rw [sameTag]
        exact (Fintype.equivFin (Block × Block)).symm_apply_apply _
      · simp [LazyOracle.empty] at found

end OnCurve

section Forms

variable [FieldCertificate] [GroupCertificate] [DecidableEq Empty]

/-- **The programmed table has the wrap event of the table** (the collector tags are no conversion tags). -/
theorem replayWraps_programmed_iff (source : (view).Source) (u : AffineInput) (table : TagTable)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) :
    replayWraps source u table ↔ replayWraps source u (programmedTable table drawn) := by
  have tagged : Tagged Paths.replayConvKeys
      (Kriterion.CRT.Entry.replayConv ((view).publish source) u ((view).labels source u)) :=
    Paths.replayConv_tagged _ u _
  refine replayWraps_congr source u table (programmedTable table drawn) fun n inConv => ?_
  obtain ⟨key, keyMember, range, label, rfl⟩ := keyRun_queries tagged (tagHash table) n inConv
  have fam : key.fam ≤ 6 := Paths.replayConvKeys_fam key keyMember
  show table _ = programmedTable table drawn _
  symm
  refine programmedTable_apply table drawn _ fun entry _ => ?_
  have small : collectorIndex entry.1 < 65536 := lt_trans (Refill.collectorIndex_lt _) (by decide)
  have tagEq : (⟨hashInput label key.code / 2 ^ 128 % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ :
      Fin (2 ^ 40)) = ⟨key.code, TagKey.code_lt range⟩ := by
    apply Fin.ext
    show hashInput label key.code / 2 ^ 128 % 2 ^ 40 = key.code
    rw [hashInput_div, Nat.mod_eq_of_lt (TagKey.code_lt range)]
  rw [tagEq]
  constructor <;> intro same <;>
    [rw [collectorTag_eq small (by decide)] at same; rw [collectorTag_eq small (by decide)] at same] <;>
    have keys := TagKey.code_injective range (collectorKey_range small (by decide)) (Fin.mk.inj_iff.mp same) <;>
    rw [keys] at fam <;> simp [collectorKey] at fam

/-- **On the curve, the reveal of the programmed table is that of the final private state.** -/
theorem crtRevealOn_programmed_iff (source : (view).Source) (u : AffineInput)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue) (table : TagTable) (K : Block)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State Empty Empty)
    (programmed : programHashAll (programRequests K drawn)
      (Laws.tableFinal crtLayout table ((view).replayProgram ((view).publish source) u ((view).labels source u))
        LazyOracle.empty) = some installed)
    (shadowed : Unit × LazyOracle.State Empty Empty)
    (member : shadowed ∈ (runReader lazyReader (crtShadowOnCurve source u) installed).support) :
    crtRevealOn source u targets (programmedTable table drawn) ↔
      crtRevealOn source u targets (stateTable shadowed.2) :=
  or_congr Iff.rfl (replayWraps_final_iff source u table K drawn installed programmed shadowed member)

/-- **On the curve, the wrap event of the table is that of the final private state.** -/
theorem replayWraps_table_iff (source : (view).Source) (u : AffineInput) (table : TagTable) (K : Block)
    (drawn : List (BMR.Collector × ((Block × Block × Block) × Block))) (installed : LazyOracle.State Empty Empty)
    (programmed : programHashAll (programRequests K drawn)
      (Laws.tableFinal crtLayout table ((view).replayProgram ((view).publish source) u ((view).labels source u))
        LazyOracle.empty) = some installed)
    (shadowed : Unit × LazyOracle.State Empty Empty)
    (member : shadowed ∈ (runReader lazyReader (crtShadowOnCurve source u) installed).support) :
    replayWraps source u table ↔ replayWraps source u (stateTable shadowed.2) :=
  (replayWraps_programmed_iff source u table drawn).trans
    (replayWraps_final_iff source u table K drawn installed programmed shadowed member)

end Forms

/-! ### 8. Off the curve: the table run of the shadow -/

section OffCurve

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- **A table run of a tag run**: every state it reaches stays consistent with the table, keeps the old points, and
stores every query along the table's path. -/
theorem tableRun_facts (T : TagTable) {α : Type} {S : Set TagKey} {Q : α → List (TagKey × Block) → Prop}
    {seen : List (TagKey × Block)} {R : CM α} (run : KeyRun S Q seen R) :
    ∀ σ : LazyOracle.State FI EI, Laws.TableConsistent T σ →
      ∀ p ∈ (runReader (tableReader T) R σ).support,
        Laws.TableConsistent T p.2 ∧ (∀ x ∈ storedPoints σ, x ∈ storedPoints p.2) ∧
          ∀ n ∈ queriesAlong (tagHash T) R, (n : BaseField) ∈ storedPoints p.2 := by
  induction run with
  | pure seen value post =>
    intro σ cons p member
    simp only [runReader, PMF.mem_support_pure_iff] at member
    subst member
    exact ⟨cons, fun x h => h, fun n inPath => by simp [queriesAlong] at inPath⟩
  | query seen label tag key next coded member range fresh sameLabel rest ih =>
    intro σ cons p pMember
    simp only [runReader] at pMember
    obtain ⟨a, aMember, pRest⟩ := (PMF.mem_support_bind_iff _ _ _).mp pMember
    have small : ((hashInput label tag : ℕ) : BaseField).val = hashInput label tag := by
      rw [← coded]; exact keyed_small range label
    have tagEq : tagOfInput ((hashInput label tag : ℕ) : BaseField) =
        ⟨hashInput label tag / 2 ^ 128 % 2 ^ 40, Nat.mod_lt _ (Nat.two_pow_pos 40)⟩ :=
      Laws.tagOfInput_small small
    -- one query: the answer is the table's at the tag, the state stays consistent and stores the point
    have step : a.1 = tagHash T (hashInput label tag) ∧ Laws.TableConsistent T a.2 ∧
        (∀ x ∈ storedPoints σ, x ∈ storedPoints a.2) ∧ ((hashInput label tag : ℕ) : BaseField) ∈ storedPoints a.2 := by
      cases found : σ.hash.lookup ((hashInput label tag : ℕ) : BaseField) with
      | some v =>
        rw [tableReader_stored T _ σ v found, PMF.mem_support_pure_iff] at aMember
        subst aMember
        refine ⟨?_, cons, fun x h => h, mem_keys_of_lookup _ _ v found⟩
        show Refill.hashCode.symm v = T ⟨_, _⟩
        rw [cons _ v found, ← tagEq]
        exact (Fintype.equivFin (Block × Block)).symm_apply_apply _
      | none =>
        rw [tableReader_fresh T _ σ found, PMF.mem_support_pure_iff] at aMember
        subst aMember
        refine ⟨by show T _ = T _; rw [tagEq], ?_, fun x h => ?_, ?_⟩
        · rw [program_fresh σ _ _ found]
          exact Laws.plant_consistent T cons _ _ rfl
        · rw [stored_program_fresh σ _ _ found]
          exact List.mem_cons_of_mem _ h
        · rw [stored_program_fresh σ _ _ found]
          exact List.mem_cons_self
    obtain ⟨answer, cons₁, keep₁, stored₁⟩ := step
    rw [answer] at pRest
    obtain ⟨cons₂, keep₂, stored₂⟩ := ih (tagHash T (hashInput label tag)) a.2 cons₁ p pRest
    refine ⟨cons₂, fun x h => keep₂ x (keep₁ x h), fun n inPath => ?_⟩
    rcases List.mem_cons.mp inPath with same | later
    · rw [same]
      exact keep₂ _ stored₁
    · exact stored₂ n later

theorem tableConsistent_empty (T : TagTable) : Laws.TableConsistent T (LazyOracle.empty : LazyOracle.State FI EI) :=
  fun x v found => by simp [LazyOracle.empty] at found

end OffCurve

section OffForms

variable [FieldCertificate] [GroupCertificate] [DecidableEq Empty]

/-- **Off the curve, the wrap event of the table is that of the table run's final state.** -/
theorem replayWraps_off_iff (source : (view).Source) (u : AffineInput) (T : TagTable)
    (p : Unit × LazyOracle.State Empty Empty)
    (member : p ∈ (runReader (tableReader T) (crtShadowOffCurve source u) LazyOracle.empty).support) :
    replayWraps source u T ↔ replayWraps source u (stateTable p.2) := by
  have tagged := Paths.crtShadowOffCurve_tagged source u
  obtain ⟨cons, -, stored⟩ := tableRun_facts T tagged LazyOracle.empty (tableConsistent_empty T) p member
  have convTagged : Tagged Paths.replayConvKeys
      (Kriterion.CRT.Entry.replayConv ((view).publish source) u ((view).labels source u)) :=
    Paths.replayConv_tagged _ u _
  refine replayWraps_congr source u T (stateTable p.2) fun n inConv => ?_
  obtain ⟨key, keyMember, range, label, rfl⟩ := keyRun_queries convTagged (tagHash T) n inConv
  have inShadow : hashInput label key.code ∈ queriesAlong (tagHash T) (crtShadowOffCurve source u) := by
    unfold crtShadowOffCurve EntryReading.reachOffCM
    rw [queriesAlong_bind, queriesAlong_bind]
    exact List.mem_append_left _ (List.mem_append_left _ inConv)
  symm
  refine tagHash_stateTable p.2 T _ (keyed_small range label) (stored _ inShadow) fun x v found sameTag => ?_
  rw [cons x v found, sameTag]
  exact (Fintype.equivFin (Block × Block)).symm_apply_apply _

/-- **Off the curve, the reveal of the table is that of the table run's final state.** -/
theorem crtRevealOff_final_iff (source : (view).Source) (u : AffineInput) (T : TagTable)
    (p : Unit × LazyOracle.State Empty Empty)
    (member : p ∈ (runReader (tableReader T) (crtShadowOffCurve source u) LazyOracle.empty).support) :
    crtRevealOff source u T ↔ crtRevealOff source u (stateTable p.2) :=
  replayWraps_off_iff source u T p member

end OffForms

/-! ### 9. `CrtWrapGuess` from the wrap mass on the swapped table -/

theorem tsum_le_of_support {α : Type} (μ : PMF α) (g : α → ℝ≥0∞) (c : ℝ≥0∞) (each : ∀ a ∈ μ.support, g a ≤ c) :
    ∑' a, μ a * g a ≤ c := by
  calc ∑' a, μ a * g a ≤ ∑' a, μ a * c := ENNReal.tsum_le_tsum fun a => by
        by_cases member : a ∈ μ.support
        · exact mul_le_mul' le_rfl (each a member)
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

section WrapGuess

variable [FieldCertificate] [GroupCertificate]

theorem crtWrapOn_merge (source : (viewHere crtEntry).Source) (u : AffineInput) (state : LazyOracle.State Empty Empty) :
    crtWrapOn source u (mergeState LazyOracle.empty state) ↔ replayWraps source u (stateTable state) := by
  unfold crtWrapOn
  rw [stateTable_merge_empty]

/-- **The wrap mass of `M'`'s private run is at most the wrap mass of the swapped table**, at every source. -/
theorem wrapAt_le_table (scalar : NonZeroScalar) (source : (viewHere crtEntry).Source) (u : AffineInput) :
    wrapAt crtEntry crtShadow (tableRun (swappedTableLaw crtEntry.layout)) scalar source u crtWrapOn ≤
      (swappedTableLaw crtLayout).toOuterMeasure {T | replayWraps source u T} := by
  have layoutEq : crtEntry.layout = crtLayout := rfl
  rw [@toOuterMeasure_eq_tsum _ _ _ (Classical.decPred _)]
  unfold wrapAt
  generalize (crtEntry.scheme inferInstance inferInstance).function scalar u = output
  cases output with
  | none =>
    simp only [middleStage2, withReveal, layoutEq]
    rw [tsum_bind_mul]
    refine tsum_le_of_support _ _ _ fun coin _ => ?_
    rw [tsum_map_mul]
    simp only [tableRun]
    rw [tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun T => mul_le_mul' le_rfl ?_
    refine tsum_le_of_support _ _ _ fun ran member => ?_
    unfold finishPrivate
    rw [if_neg (fun either => either.elim (not_meets_empty ran.2) id)]
    simp only [stateWeight]
    split
    · rename_i wraps
      rw [crtWrapOn_merge, ← replayWraps_off_iff source u T ran member] at wraps
      rw [if_pos (show T ∈ {T | replayWraps source u T} from wraps)]
    · exact zero_le
  | some target =>
    simp only [middleStage2, withReveal, layoutEq]
    erw [Laws.routeMReplay_pure (viewHere crtEntry) crtLayout Laws.crtLayout_refill Laws.crtLayout_points
      _ u _ (Paths.replay_keyNonSite _ u) (Paths.replay_refillPath _ u _ _) (Paths.replay_canonical _ u _)]
    rw [PMF.bind_bind]
    simp only [PMF.pure_bind]
    rw [tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun T => mul_le_mul' le_rfl ?_
    rw [if_neg (not_meets_empty _), tsum_bind_mul]
    refine tsum_le_of_support _ _ _ fun drawnRows _ => ?_
    rcases drawnRows with _ | targets
    · simp only [tsum_pure_mul_eq, stateWeight]
      exact zero_le
    · dsimp only
      rw [tsum_bind_mul]
      refine tsum_le_of_support _ _ _ fun drawn _ => ?_
      rcases drawn with _ | drawn
      · simp only [tsum_pure_mul_eq, stateWeight]
        exact zero_le
      · dsimp only
        cases programmed : programHashAll (programRequests _ drawn)
            (Laws.tableFinal (FI := Empty) (EI := Empty) crtLayout T _ _) with
        | none =>
          dsimp only
          simp only [tsum_pure_mul_eq, stateWeight]
          exact zero_le
        | some installed =>
          dsimp only
          rw [tsum_bind_mul]
          refine tsum_le_of_support _ _ _ fun coin _ => ?_
          rw [tsum_map_mul]
          refine tsum_le_of_support _ _ _ fun shadowed member => ?_
          unfold finishPrivate
          rw [if_neg (fun either => either.elim (not_meets_empty shadowed.2) id)]
          simp only [stateWeight]
          split
          · rename_i wraps
            rw [crtWrapOn_merge, ← replayWraps_table_iff source u T _ drawn installed programmed shadowed member]
              at wraps
            rw [if_pos (show T ∈ {T | replayWraps source u T} from wraps)]
          · exact zero_le

end WrapGuess

/-- **`CrtWrapGuess` from the wrap mass on the swapped table** (`crtWrapTable_le`, in the weight form). -/
theorem crtWrapGuess_of
    (table : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (u : AffineInput),
      letI := field
      letI := group
      letI := (viewHere crtEntry).sourceFintype
      haveI := (viewHere crtEntry).sourceNonempty
      ∀ weight : crtEntry.Public → ℝ≥0∞,
        ∑' source, PMF.uniformOfFintype (viewHere crtEntry).Source source *
            (weight ((viewHere crtEntry).publish source) *
              (swappedTableLaw crtLayout).toOuterMeasure {T | replayWraps source u T})
          ≤ ENNReal.ofReal smudgeError * ∑' source, PMF.uniformOfFintype (viewHere crtEntry).Source source *
              weight ((viewHere crtEntry).publish source)) :
    CrtWrapGuess := by
  intro field group scalar u
  letI := field
  letI := group
  letI := @Fintype.ofFinite Empty inferInstance
  letI := Classical.decEq Empty
  letI := (viewHere crtEntry).sourceFintype
  haveI := (viewHere crtEntry).sourceNonempty
  intro weight
  refine le_trans (ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
    (table field group u weight)
  have bound := wrapAt_le_table scalar source u
  convert bound using 3
  all_goals first | rfl | exact Subsingleton.elim _ _

/-! ### 10. the flag input on the curve (`Laws.OnFlag`) -/

/-- **`OnFlag` for `crtEntry` and `crtShadow`**: the ideal reveal on the programmed table implies the shadow's reveal on
every final private state. -/
theorem crtOnFlag [FieldCertificate] [GroupCertificate] [Fintype Empty] [DecidableEq Empty]
    (source : (viewHere crtEntry).Source) (u : AffineInput) :
    Laws.OnFlag crtEntry crtShadow crtRevealOn source u := by
  intro table targets drawn installed coin programmed shadowed member revealed
  exact (crtRevealOn_programmed_iff source u targets table _ drawn installed programmed shadowed member).mp revealed

end

end Kriterion.CRT.Privacy.Flags
