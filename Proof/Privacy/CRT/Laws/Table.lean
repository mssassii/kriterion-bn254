/-
**P6a1: the answer-table reading of the real game** (`G0 → G0T`, row H2).

`G0` (`realHybrid`) runs the garbler and both adversary stages on one uniform complete oracle. `G0T`
(`tablePlantedHybrid`) runs the garbler on the table oracle `tableOracle table` (every hash input is answered by its
tag) and installs the garbler's transcript into an empty lazy oracle, on which
both adversary stages run. The two games are **equal**, so the hop costs nothing: `crt_table_hop` proves row H2
with advantage `0 ≤ tCollisionError`. It uses two named facts of the entry (`GarblerTableFacts`): the scheme's garbler
is its query program read on the oracle (`garble_eval`), and along every path two hash inputs of the garbler with the
same tag are equal (`tagInjective`).

* `coordOracle c F`, `tableOracle_eq`: an oracle that answers `x` by `F (c x)` for a coordinate map `c`; the table
  oracle is the case `c = tagOfInput`.
* `CoordInjective c seen P`: the path property, relative to the inputs `seen` before `P`; `TagInjective` its case
  `c = tagOfInput`.
* `uniform_update_bind`: the value of a uniform table at one coordinate is uniform and independent of the rest.
* `run_table` (**the adaptive answer-table law on a lazy oracle**, for any finite coordinate type): for a
  coordinate-injective program and a lazy state whose stored inputs were seen, running on a table whose stored
  coordinates hold the stored answers and whose other coordinates are uniform, then installing the transcript, has the
  law of `LazyOracle.run`. By induction on the path: a stored input reads its stored answer on both sides; a new input
  reads an unread coordinate, uniform and independent of what was read (`uniform_update_bind`); the lazy query and the
  installation both prepend the new pair.
* `lazy_eq_real`, `lazy_eq_tablePlanted`, `realHybrid_eq_tablePlanted`, `crt_table_hop`.
-/

import Proof.Privacy.CRT.Hybrids
import Proof.Privacy.Phase3.Glue.OracleLaw

namespace Kriterion.CRT.Privacy.Laws

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC Kriterion.CRT
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (lazy_real_uniform public_run_tape uniform_product uniform_equiv)

noncomputable section

variable {FI EI : Type}

/-! ### 1. Oracles that read a table by coordinates -/

/-- The oracle that answers every hash input `x` by `F (c x)` (the permutation parts are irrelevant). -/
def coordOracle {C : Type} (c : BaseField → C) (F : C → Block × Block) : PublicOracle FI EI :=
  (Classical.arbitrary _, Classical.arbitrary _, fun x => F (c x))

/-- **The table oracle reads the tag table by tags**. -/
theorem tableOracle_eq (table : TagTable) :
    tableOracle (FI := FI) (EI := EI) table = coordOracle tagOfInput table := rfl

/-! ### 2. The path property -/

/-- **Coordinate injectivity along every path**, relative to the inputs `seen` before the program: every query is a
hash query, and an input that reads the same coordinate as a seen input is that input. -/
inductive CoordInjective {C : Type} (c : BaseField → C) {α : Type} :
    List BaseField → {budget : ℕ} → QueryProgram (publicOracleSpec FI EI) α budget → Prop
  | pure (seen : List BaseField) {budget : ℕ} (result : α) :
      CoordInjective c seen (QueryProgram.pure (budget := budget) result)
  | hash (seen : List BaseField) {budget : ℕ} (x : BaseField)
      (next : Block × Block → QueryProgram (publicOracleSpec FI EI) α budget)
      (fresh : ∀ y ∈ seen, c x = c y → x = y)
      (rest : ∀ answer, CoordInjective c (x :: seen) (next answer)) :
      CoordInjective c seen (QueryProgram.query (PublicQuery.hash x) next)

/-- **Tag injectivity along every path** (every hash input is read by its tag). -/
abbrev TagInjective {α : Type} (seen : List BaseField) {budget : ℕ}
    (P : QueryProgram (publicOracleSpec FI EI) α budget) : Prop :=
  CoordInjective tagOfInput seen P

/-- **The named facts of the entry that the table reading uses** (row H2's hypotheses; to be discharged on the
concrete entry: `garble_eval` from `eval_liftHash` and the program's `eval`, `tagInjective` from the tag layout). -/
structure GarblerTableFacts (E : CrtEntry FI EI) : Prop where
  /-- The scheme's garbler is its query program read on the oracle. -/
  garble_eval : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ)
    (scalar : NonZeroScalar) (coins : E.Coins) (oracle : PublicOracle FI EI),
    (E.scheme field group).garble parameter scalar (coins, oracle) =
      (E.garbleProgram field group parameter scalar coins).eval (publicAnswer oracle)
  /-- Along every path the garbler asks hash queries only, at inputs with pairwise distinct tags. -/
  tagInjective : ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ)
    (scalar : NonZeroScalar) (coins : E.Coins),
    TagInjective [] (E.garbleProgram field group parameter scalar coins)

/-! ### 3. A uniform table at one coordinate -/

/-- The value at `c` and the rest of a table, as a bijection. -/
def updateEquiv {C A : Type} [DecidableEq C] (c : C) : A × (C → A) ≃ (C → A) × A where
  toFun pair := (Function.update pair.2 c pair.1, pair.2 c)
  invFun pair := (pair.1 c, Function.update pair.1 c pair.2)
  left_inv pair := by
    obtain ⟨b, T⟩ := pair
    simp
  right_inv pair := by
    obtain ⟨T, a⟩ := pair
    simp

theorem uniform_map_fst {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] :
    (PMF.uniformOfFintype (X × Y)).map Prod.fst = PMF.uniformOfFintype X := by
  rw [← uniform_product (A := X) (B := Y), PMF.map_bind]
  have constant : ∀ a : X, ((PMF.uniformOfFintype Y).map fun b => (a, b)).map Prod.fst = PMF.pure a := by
    intro a
    rw [PMF.map_comp]
    exact PMF.map_const _ a
  simp only [constant]
  exact PMF.bind_pure _

/-- **The value of a uniform table at one coordinate is uniform and independent of the rest**: an average of
`F (T c) T`, where `F b` does not read the table at `c`, is the average over `b` of the average of `F b`. -/
theorem uniform_update_bind {C A β : Type} [Fintype C] [DecidableEq C] [Fintype A] [Nonempty A] (c : C)
    (F : A → (C → A) → β) (ignores : ∀ b T, F b (Function.update T c b) = F b T) :
    (PMF.uniformOfFintype (C → A)).map (fun T => F (T c) T) =
      (PMF.uniformOfFintype A).bind fun b => (PMF.uniformOfFintype (C → A)).map (F b) := by
  have pushed : (PMF.uniformOfFintype (A × (C → A))).map (fun pair => Function.update pair.2 c pair.1) =
      PMF.uniformOfFintype (C → A) := by
    have split : (fun pair : A × (C → A) => Function.update pair.2 c pair.1) = Prod.fst ∘ updateEquiv c := rfl
    rw [split, ← PMF.map_comp, uniform_equiv (updateEquiv c), uniform_map_fst]
  have rhs : ((PMF.uniformOfFintype A).bind fun b => (PMF.uniformOfFintype (C → A)).map (F b)) =
      (PMF.uniformOfFintype (A × (C → A))).map (fun pair => F pair.1 (Function.update pair.2 c pair.1)) := by
    rw [← uniform_product (A := A) (B := C → A), PMF.map_bind]
    refine congrArg _ (funext fun b => ?_)
    rw [PMF.map_comp]
    refine congrArg (fun f => PMF.map f _) (funext fun T => ?_)
    exact (ignores b T).symm
  rw [rhs, ← pushed, PMF.map_comp]
  refine congrArg (fun f => PMF.map f _) (funext fun pair => ?_)
  simp

/-! ### 4. The adaptive answer-table law on a lazy oracle -/

section Coordinates

variable {C : Type} [Fintype C] [DecidableEq C]


/-- The decoding of a stored hash value. -/
abbrev hashValue (v : Fin (Fintype.card (Block × Block))) : Block × Block := (Fintype.equivFin (Block × Block)).symm v

open Classical in
/-- The coordinates the stored inputs of a lazy state read. -/
def storedCoords (c : BaseField → C) (s : LazyOracle.State FI EI) : Set (C) :=
  {k | ∃ y v, s.hash.lookup y = some v ∧ c y = k}

open Classical in
/-- The table seen through a lazy state: at a stored coordinate the fixed value `T0`, elsewhere `T`. -/
def through (c : BaseField → C) (s : LazyOracle.State FI EI) (T0 T : C → Block × Block) :
    C → Block × Block :=
  fun k => if k ∈ storedCoords c s then T0 k else T k

/-- `T0` holds the stored answers at the stored coordinates. -/
def Consistent (c : BaseField → C) (s : LazyOracle.State FI EI) (T0 : C → Block × Block) : Prop :=
  ∀ y v, s.hash.lookup y = some v → T0 (c y) = hashValue v

theorem query_hash [DecidableEq FI] [DecidableEq EI] (s : LazyOracle.State FI EI) (x : BaseField) :
    LazyOracle.query (.hash x) s =
      (s.hash.query Fintype.card_pos x).distribution.map
        (fun answer => (hashValue answer.1, { s with hash := answer.2 })) := rfl

theorem program_hash [DecidableEq FI] [DecidableEq EI] (s : LazyOracle.State FI EI) (x : BaseField)
    (b : Block × Block) :
    LazyOracle.program (.hash x) b s =
      if s.hash.lookup x = none then
        some { s with hash := s.hash.program x (Fintype.equivFin (Block × Block) b) }
      else none := rfl

theorem query_hash_stored [DecidableEq FI] [DecidableEq EI] (s : LazyOracle.State FI EI) (x : BaseField) (v : Fin (Fintype.card (Block × Block)))
    (found : s.hash.lookup x = some v) :
    LazyOracle.query (.hash x) s = PMF.pure (hashValue v, s) := by
  rw [query_hash]
  simp only [HashTable.query, found, Draw.distribution, PMF.pure_map]
  rfl

theorem query_hash_fresh [DecidableEq FI] [DecidableEq EI] (s : LazyOracle.State FI EI) (x : BaseField)
    (missing : s.hash.lookup x = none) :
    LazyOracle.query (.hash x) s =
      (PMF.uniformOfFintype (Block × Block)).map
        (fun b => (b, { s with hash := (x, Fintype.equivFin (Block × Block) b) :: s.hash })) := by
  haveI : Nonempty (Fin (Fintype.card (Block × Block))) := ⟨⟨0, Fintype.card_pos⟩⟩
  rw [query_hash]
  simp only [HashTable.query, missing, Draw.distribution, PMF.map_comp]
  conv_rhs => rw [← uniform_equiv (Fintype.equivFin (Block × Block)).symm, PMF.map_comp]
  simp [Function.comp_def, hashValue]
  rfl

theorem lookup_cons (h : HashTable BaseField (Fintype.card (Block × Block))) (x y : BaseField)
    (v : Fin (Fintype.card (Block × Block))) :
    ((x, v) :: h).lookup y = if y = x then some v else h.lookup y := by
  by_cases same : y = x
  · subst same
    simp [List.lookup]
  · have different : (y == x) = false := by simp [same]
    simp [List.lookup, different, same]

theorem mem_storedCoords_cons (c : BaseField → C) (s : LazyOracle.State FI EI) (x : BaseField)
    (v : Fin (Fintype.card (Block × Block))) (k : C) :
    k ∈ storedCoords c { s with hash := (x, v) :: s.hash } ↔ k = c x ∨ k ∈ storedCoords c s := by
  unfold storedCoords
  simp only [Set.mem_ofPred_eq, lookup_cons]
  constructor
  · rintro ⟨y, w, found, rfl⟩
    by_cases same : y = x
    · exact Or.inl (by rw [same])
    · rw [if_neg same] at found
      exact Or.inr ⟨y, w, found, rfl⟩
  · rintro (rfl | ⟨y, w, found, rfl⟩)
    · exact ⟨x, v, by simp, rfl⟩
    · by_cases same : y = x
      · subst same
        exact ⟨y, v, by simp, rfl⟩
      · exact ⟨y, w, by rw [if_neg same]; exact found, rfl⟩

theorem through_empty (c : BaseField → C) (T0 T : C → Block × Block) :
    through c (LazyOracle.empty : LazyOracle.State FI EI) T0 T = T := by
  funext k
  have none : k ∉ storedCoords c (LazyOracle.empty : LazyOracle.State FI EI) := by
    rintro ⟨y, v, found, _⟩
    cases found
  unfold through
  rw [if_neg none]

/-- **The adaptive answer-table law on a lazy oracle.** A tag-injective program, run on a table whose stored
coordinates hold the stored answers and whose other coordinates are uniform, with its transcript installed into the
lazy state, has the law of the lazy run. -/
theorem run_table [DecidableEq FI] [DecidableEq EI] (c : BaseField → C) {α : Type} {seen : List BaseField}
    {budget : ℕ} {P : QueryProgram (publicOracleSpec FI EI) α budget} (inj : CoordInjective c seen P) :
    ∀ (s : LazyOracle.State FI EI) (T0 : C → Block × Block),
      (∀ y v, s.hash.lookup y = some v → y ∈ seen) → Consistent c s T0 →
      (PMF.uniformOfFintype (C → Block × Block)).map (fun T =>
          (P.eval (publicAnswer (coordOracle (FI := FI) (EI := EI) c (through c s T0 T))),
            installEntries (programTranscript (publicAnswer (coordOracle (FI := FI) (EI := EI) c
              (through c s T0 T))) P) s)) =
        LazyOracle.run P.toOracleProgram s := by
  induction inj with
  | pure seen result =>
      intro s T0 _ _
      show (PMF.uniformOfFintype _).map (fun _ => (result, s)) = (PMF.pure result).map (fun value => (value, s))
      rw [PMF.pure_map]
      exact PMF.map_const _ _
  | hash seen x next fresh rest ih =>
      intro s T0 seenKeys consistent
      show _ = (LazyOracle.query (.hash x) s).bind fun answer =>
        LazyOracle.run (next answer.1).toOracleProgram answer.2
      cases found : s.hash.lookup x with
      | some v =>
          -- a stored input reads its stored answer on both sides
          have stored : c x ∈ storedCoords c s := ⟨x, v, found, rfl⟩
          rw [query_hash_stored s x v found]
          erw [PMF.pure_bind]
          rw [← ih (hashValue v) s T0 (fun y w present => List.mem_cons_of_mem _ (seenKeys y w present))
            consistent]
          refine congrArg (fun f => PMF.map f _) (funext fun T => ?_)
          have answerEq : through c s T0 T (c x) = hashValue v := by
            unfold through
            rw [if_pos stored]
            exact consistent x v found
          have skip : LazyOracle.program (PublicQuery.hash x) (hashValue v) s = none := by
            rw [program_hash, found]
            rfl
          show ((next (through c s T0 T (c x))).eval _,
              installEntries (⟨PublicQuery.hash x, through c s T0 T (c x)⟩ :: programTranscript _
                (next (through c s T0 T (c x)))) s) = _
          rw [answerEq]
          show (_, installEntries _ ((LazyOracle.program (PublicQuery.hash x) (hashValue v) s).getD s)) = _
          rw [skip]
          rfl
      | none =>
          -- a new input reads an unread coordinate
          have unread : c x ∉ storedCoords c s := by
            rintro ⟨y, w, present, same⟩
            have yx : x = y := fresh y (seenKeys y w present) same.symm
            subst yx
            rw [found] at present
            cases present
          let after : Block × Block → LazyOracle.State FI EI := fun b =>
            { s with hash := (x, Fintype.equivFin (Block × Block) b) :: s.hash }
          let fixed : Block × Block → C → Block × Block := fun b =>
            Function.update T0 (c x) b
          have storedAfter : ∀ b k, k ∈ storedCoords c (after b) ↔ k = c x ∨ k ∈ storedCoords c s :=
            fun b k => mem_storedCoords_cons c s x _ k
          have seenAfter : ∀ b y w, (after b).hash.lookup y = some w → y ∈ x :: seen := by
            intro b y w present
            by_cases same : y = x
            · exact same ▸ List.mem_cons_self
            · have old : s.hash.lookup y = some w := by
                have := present
                simp only [after, lookup_cons, if_neg same] at this
                exact this
              exact List.mem_cons_of_mem _ (seenKeys y w old)
          have consistentAfter : ∀ b, Consistent c (after b) (fixed b) := by
            intro b y w present
            by_cases same : y = x
            · subst same
              have : w = Fintype.equivFin (Block × Block) b := by
                simp only [after, lookup_cons] at present
                exact (Option.some.inj present).symm
              subst this
              simp [fixed, hashValue]
            · have old : s.hash.lookup y = some w := by
                have := present
                simp only [after, lookup_cons, if_neg same] at this
                exact this
              have apart : c y ≠ c x := fun equal =>
                same (fresh y (seenKeys y w old) equal.symm).symm
              simp only [fixed, Function.update_of_ne apart]
              exact consistent y w old
          have throughEq : ∀ T, through c s T0 T = through c (after (T (c x))) (fixed (T (c x))) T := by
            intro T
            funext k
            unfold through
            by_cases inOld : k ∈ storedCoords c s
            · have apart : k ≠ c x := fun equal => unread (equal ▸ inOld)
              rw [if_pos inOld, if_pos ((storedAfter _ k).mpr (Or.inr inOld))]
              simp only [fixed, Function.update_of_ne apart]
            · rw [if_neg inOld]
              by_cases atX : k = c x
              · subst atX
                rw [if_pos ((storedAfter _ _).mpr (Or.inl rfl))]
                simp [fixed]
              · rw [if_neg fun inNew => ((storedAfter _ k).mp inNew).elim atX inOld]
          have ignores : ∀ b T, through c (after b) (fixed b) (Function.update T (c x) b) =
              through c (after b) (fixed b) T := by
            intro b T
            funext k
            unfold through
            by_cases inNew : k ∈ storedCoords c (after b)
            · rw [if_pos inNew, if_pos inNew]
            · have apart : k ≠ c x := fun equal => inNew ((storedAfter b k).mpr (Or.inl equal))
              rw [if_neg inNew, if_neg inNew, Function.update_of_ne apart]
          have installed : ∀ b : Block × Block, LazyOracle.program (PublicQuery.hash x) b s = some (after b) := by
            intro b
            rw [program_hash, found]
            rfl
          rw [query_hash_fresh s x found]
          erw [PMF.bind_map]
          show _ = (PMF.uniformOfFintype (Block × Block)).bind fun b =>
            LazyOracle.run (next b).toOracleProgram (after b)
          have step := fun b => ih b (after b) (fixed b) (seenAfter b) (consistentAfter b)
          simp_rw [← step]
          let G : Block × Block → (C → Block × Block) → _ := fun b T =>
            ((next b).eval (publicAnswer (coordOracle (FI := FI) (EI := EI) c (through c (after b) (fixed b) T))),
              installEntries (programTranscript (publicAnswer (coordOracle (FI := FI) (EI := EI) c
                (through c (after b) (fixed b) T))) (next b)) (after b))
          have law := uniform_update_bind (c x) G fun b T => by
            simp only [G, ignores]
          refine Eq.trans ?_ law
          refine congrArg (fun f => PMF.map f _) (funext fun T => ?_)
          have answerEq : through c s T0 T (c x) = T (c x) := by
            unfold through
            rw [if_neg unread]
          show ((next (through c s T0 T (c x))).eval _,
              installEntries (⟨PublicQuery.hash x, through c s T0 T (c x)⟩ :: programTranscript _
                (next (through c s T0 T (c x)))) s) = _
          rw [answerEq]
          show (_, installEntries _
            ((LazyOracle.program (PublicQuery.hash x) (T (c x)) s).getD s)) = _
          rw [installed, Option.getD_some, throughEq T]

end Coordinates

/-! ### 5. `G0 = G0T` -/

/-- An eager run with the identity projection never changes its oracle (xinshu's `eager_run_state`). -/
theorem eagerRun_state {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FI EI) Result budget)
    (oracle : PublicOracle FI EI) (result : Result × PublicOracle FI EI)
    (member : result ∈ (program.run (publicHandler id) oracle).support) : result.2 = oracle := by
  rw [public_run_tape (project := id), PMF.support_map] at member
  obtain ⟨value, _, equal⟩ := member
  exact (congrArg Prod.snd equal).symm

section Games

variable [FieldCertificate] [GroupCertificate] [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]
  (E : CrtEntry FI EI)

/-- **The library's lazy real game of the entry is `G0`** (xinshu's `planB_lazy_real`, from `lazy_real_uniform`). -/
theorem lazy_eq_real (facts : GarblerTableFacts E) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar) :
    letI : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
    haveI : Nonempty E.Coins := ⟨E.coinWitness⟩
    lazyRealGame (fun _ => PMF.uniformOfFintype E.Coins)
        (fun parameter scalar coins =>
          (E.garbleProgram inferInstance inferInstance parameter scalar coins).toOracleProgram)
        (E.scheme inferInstance inferInstance).encode adversary parameter scalar () =
      realHybrid E adversary parameter scalar := by
  letI : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
  haveI : Nonempty E.Coins := ⟨E.coinWitness⟩
  rw [lazy_real_uniform (fun _ => PMF.uniformOfFintype E.Coins)
    (fun parameter scalar coins => E.garbleProgram inferInstance inferInstance parameter scalar coins)]
  show _ = realGame (E.scheme inferInstance inferInstance)
    (fun _ => PMF.uniformOfFintype (E.Coins × PublicOracle FI EI)) (publicHandler Prod.snd) adversary parameter
    scalar ()
  unfold realGame
  beta_reduce
  rw [← uniform_product (A := E.Coins) (B := PublicOracle FI EI), PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr
  intro coins _
  apply PMF.bind_congr
  intro oracle _
  rw [facts.garble_eval, public_run_tape (project := Prod.snd)]
  simp only [PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr
  intro selected reached
  rw [public_run_tape (project := Prod.snd), eagerRun_state _ _ _ reached]
  simp only [PMF.map_comp, Function.comp_def]

/-- **The library's lazy real game of the entry is `G0T`**: `run_table` at the empty lazy state, with the tag table
read by tags. -/
theorem lazy_eq_tablePlanted (facts : GarblerTableFacts E) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar) :
    letI : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
    haveI : Nonempty E.Coins := ⟨E.coinWitness⟩
    lazyRealGame (fun _ => PMF.uniformOfFintype E.Coins)
        (fun parameter scalar coins =>
          (E.garbleProgram inferInstance inferInstance parameter scalar coins).toOracleProgram)
        (E.scheme inferInstance inferInstance).encode adversary parameter scalar () =
      tablePlantedHybrid E adversary parameter scalar := by
  letI : Fintype E.Coins := @Fintype.ofFinite _ E.coinsFinite
  haveI : Nonempty E.Coins := ⟨E.coinWitness⟩
  show _ = plantedGame E (uniformTableTape E) adversary parameter scalar
  unfold lazyRealGame plantedGame uniformTableTape
  beta_reduce
  rw [← uniform_product (A := E.Coins) (B := TagTable), PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr
  intro coins _
  -- the garbler's lazy run is its run on a uniform tag table
  have law := run_table tagOfInput
    (facts.tagInjective inferInstance inferInstance parameter scalar coins) LazyOracle.empty
    (fun _ => Classical.arbitrary _) (fun y v present => by cases present) (fun y v present => by cases present)
  simp only [through_empty] at law
  rw [← law, PMF.bind_map]
  apply PMF.bind_congr
  intro table _
  simp only [Function.comp_def, ← tableOracle_eq, facts.garble_eval]

/-- **`G0 = G0T`.** -/
theorem realHybrid_eq_tablePlanted (facts : GarblerTableFacts E) (adversary : ChainAdversary FI EI E.Public)
    (parameter : ℕ) (scalar : NonZeroScalar) :
    realHybrid E adversary parameter scalar = tablePlantedHybrid E adversary parameter scalar :=
  (lazy_eq_real E facts adversary parameter scalar).symm.trans
    (lazy_eq_tablePlanted E facts adversary parameter scalar)

end Games

/-- **Ledger H2 (P6a1): `G0 → G0T` costs nothing**, so in particular at most `tCollisionError`. -/
theorem crt_table_hop [Finite FI] [Finite EI] (E : CrtEntry FI EI) (facts : GarblerTableFacts E) :
    HopBound (crtChain E).real (crtChain E).tablePlanted fun _ _ => tCollisionError := by
  intro field group adversary parameter scalar _
  have same : atSolution (crtChain E).real field group adversary parameter scalar =
      atSolution (crtChain E).tablePlanted field group adversary parameter scalar :=
    @realHybrid_eq_tablePlanted FI EI field group (Fintype.ofFinite FI) (Fintype.ofFinite EI)
      (Classical.decEq FI) (Classical.decEq EI) E facts adversary parameter scalar
  rw [same]
  simp only [Kriterion.Cryptography.Assumptions.advantage, sub_self, abs_zero]
  exact frac_nonneg _ _

end

end Kriterion.CRT.Privacy.Laws
