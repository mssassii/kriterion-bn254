/-
**Reachability of the conversion and body tags** (H6's `ConvTagsReachable`).

`convTagsReachable : StageOneProof.ConvTagsReachable`: every input the garbler asks whose tag has family 0 to 6,
except the 30 casts 49 to 63 of chunk 31 (`NeverHotCast`), has a tag that is hot at some input.

* **Fine keys** (`KeysIn`, `garble_keysIn`): every input the garbler asks is a labelled input at a key of
  `garblerFine`, which keeps the level and slot ranges of every block (`Paths.treeKeys`, `castKeys`, `growKeys`,
  `foldKeys`, `bodyKeys`). `KeysIn` composes through `>>=` with no disjointness condition; each block's fact comes
  from its `Tagged` lemma.
* **Witnesses**: the input `inputAt κ v` (coordinate `κ` is `v`, the other is `0`). Chunk trees and casts:
  `v = s · 2^(8c)`; the body: `v = ρ`; families 2 to 5: a coordinate value whose word value is a target `t` (stage 0
  `t = y`, stage 1 `t = 2^width0 · y`, growth `t = s`, folds `t = ρ`), every target at most `need m ell`.
* **The many-chunk decomposition** (`word_target`): `v = Σ_{c<32} α_c · 256^c` with `α_c < 256` (`α_31 < 48`, so
  `v < 48 · 256^31 ≤ p`) has chunk values `α_c` and word value `Σ_c (α_c · 2^(8c) mod m)`; the reachable word values
  grow chunk by chunk (`reach_succ`) along a per-modulus certificate (`certs`) checked once over the 85 rows by
  `decide +kernel` (`rows_ok`: small closed arithmetic, no 623-bit number, no sum over lanes or moduli).
-/

import Proof.Privacy.CRT.Hidden.StageOne

set_option linter.unusedSectionVars false

namespace Kriterion.CRT.Privacy.ConvReach

open BN254 Cryptography Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB Kriterion.CRT Kriterion.CRT.Privacy.Align
open Kriterion.CRT.Paths (TagKey Tagged)

/-! ### Keys of the inputs a program asks -/

/-- Every input `p` asks, on every hash, is a labelled input at a key of `S`, in range. -/
def KeysIn {α : Type} (S : Set TagKey) (p : CM α) : Prop :=
  ∀ H : HashN, ∀ x ∈ asked H p, ∃ k ∈ S, k.InRange ∧ ∃ label, x = hashInput label k.code

namespace KeysIn

variable {α β : Type} {S S' U : Set TagKey}

theorem of_tagged {p : CM α} (tagged : Tagged S p) : KeysIn S p := fun H => asked_of_tagged tagged H

theorem mono {p : CM α} (keys : KeysIn S p) (sub : S ⊆ S') : KeysIn S' p := fun H x inside => by
  obtain ⟨k, member, range, label, same⟩ := keys H x inside
  exact ⟨k, sub member, range, label, same⟩

theorem of_pure (S : Set TagKey) (value : α) : KeysIn S (Pure.pure value : CM α) := fun H x inside => by
  rw [asked_pure] at inside
  exact absurd inside List.not_mem_nil

theorem bind {p : CM α} {next : α → CM β} (first : KeysIn S p) (rest : ∀ value, KeysIn S' (next value)) :
    KeysIn (S ∪ S') (p >>= next) := fun H x inside => by
  rw [asked_bind] at inside
  rcases List.mem_append.mp inside with early | late
  · exact (first.mono Set.subset_union_left) H x early
  · exact ((rest _).mono Set.subset_union_right) H x late

theorem bind_pure {p : CM α} (first : KeysIn S p) (f : α → β) :
    KeysIn S (p >>= fun value => Pure.pure (f value)) :=
  (bind first fun value => of_pure ∅ (f value)).mono (by simp)

theorem tableM {count : ℕ} {program : Fin count → CM α} {S : Fin count → Set TagKey}
    (each : ∀ index, KeysIn (S index) (program index)) :
    KeysIn {k | ∃ index, k ∈ S index} (CRT.tableM count program) := fun H x inside => by
  rw [asked_tableM] at inside
  obtain ⟨index, _, member⟩ := List.mem_flatMap.mp inside
  obtain ⟨k, inS, range, label, same⟩ := each index H x member
  exact ⟨k, ⟨index, inS⟩, range, label, same⟩

end KeysIn

/-! ### The fine keys of the garbler's blocks -/

/-- The keys of a tree over `width` bits and of its leaf casts of width `l`. -/
def pairFine (treeFam castFam coord idx stage width l : ℕ) : Set TagKey :=
  Paths.treeKeys treeFam coord idx stage width ∪ Paths.castKeys castFam coord idx stage (2 ^ width) (castAnswers l)

theorem treeCasts_keysIn {α : Type} (treeFam castFam coord idx stage width l : ℕ)
    (treeFields : Paths.Fields treeFam coord idx stage) (castFields : Paths.Fields castFam coord idx stage)
    (widthSmall : width ≤ 16) (answers : castAnswers l ≤ 64)
    (delta bit0 : Block) (finish : _ → (Fin (2 ^ width) → Lanes l) → α) :
    KeysIn (pairFine treeFam castFam coord idx stage width l)
      (treeGarbleM (fun level slot => tagCode treeFam coord idx stage level slot 0) delta bit0 width >>= fun tree =>
        CRT.tableM (2 ^ width) (fun leaf => castM l (tree.1 leaf) fun part =>
          tagCode castFam coord idx stage 0 leaf.val part) >>= fun casts => pure (finish tree casts)) :=
  KeysIn.bind (KeysIn.of_tagged (Paths.treeGarbleM_tagged treeFam coord idx stage treeFields delta bit0 width
    widthSmall)) fun _ => KeysIn.bind_pure (KeysIn.of_tagged (Paths.leafCasts_tagged castFam coord idx stage width l
      castFields widthSmall answers _)) _

/-- The keys of chunk `c`: its tree (family 0) and its casts (family 1). -/
def chunkFine (T : CrtTable) (coord c : ℕ) : Set TagKey := pairFine 0 1 coord c 0 (T.chunkWidth c) T.castWidth

theorem chunk_keysIn (T : CrtTable) (coord : ℕ) (delta : Block) (zeroLabel : ℕ → Block) (c : ℕ)
    (coordLt : coord < 2) (cLt : c < 128) (widthSmall : T.chunkWidth c ≤ 16)
    (answers : castAnswers T.castWidth ≤ 64) :
    KeysIn (chunkFine T coord c) (chunkGarbleM T coord delta zeroLabel c) :=
  treeCasts_keysIn 0 1 coord c 0 (T.chunkWidth c) T.castWidth
    ⟨by norm_num, coordLt, cLt, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, coordLt, cLt, by norm_num, by norm_num, by norm_num⟩ widthSmall answers _ _ _

theorem stage_keysIn {rb : ℕ} (coord idx stage w : ℕ) (coordLt : coord < 2) (idxLt : idx < 128)
    (stageLt : stage < 4) (widthSmall : w ≤ 16) (answers : castAnswers rb ≤ 64) (delta : Block)
    (remainder : Lanes rb) :
    KeysIn (pairFine 2 3 coord idx stage w rb)
      (extStageGarbleM w (fun level slot => tagCode 2 coord idx stage level slot 0)
        (fun leaf part => tagCode 3 coord idx stage 0 leaf part) delta remainder) :=
  treeCasts_keysIn 2 3 coord idx stage w rb
    ⟨by norm_num, coordLt, idxLt, stageLt, by norm_num, by norm_num⟩
    ⟨by norm_num, coordLt, idxLt, stageLt, by norm_num, by norm_num⟩ widthSmall answers _ _ _

/-- The keys of an odd modulus's conversion: the two stages, the growth and the folds. -/
def convFine (coord idx : ℕ) (row : OddRow) (m : ℕ) : Set TagKey :=
  pairFine 2 3 coord idx 0 row.width0 row.ell ∪ (pairFine 2 3 coord idx 1 row.width1 (row.ell - row.width0) ∪
    (Paths.growKeys 4 coord idx 0 row.width0 (row.keep - row.width0) ∪
      Paths.foldKeys coord idx row.keep (row.ell - row.keep) m))

theorem conversion_keysIn (coord idx : ℕ) (row : OddRow) (m : ℕ) (coordLt : coord < 2) (idxLt : idx < 128)
    (ranges : Paths.RowRanges row) (mSmall : m ≤ 65536) (delta : Block) (word : Lanes row.ell) :
    KeysIn (convFine coord idx row m) (conversionGarbleM coord idx row m delta word) := by
  unfold conversionGarbleM convFine
  obtain ⟨w0, w1, keep, ell, cast0, cast1⟩ := ranges
  have growFields : Paths.Fields 4 coord idx 0 :=
    ⟨by norm_num, coordLt, idxLt, by norm_num, by norm_num, by norm_num⟩
  refine KeysIn.bind (stage_keysIn coord idx 0 row.width0 coordLt idxLt (by norm_num) w0 cast0 delta word)
    fun g0 => ?_
  refine KeysIn.bind (stage_keysIn coord idx 1 row.width1 coordLt idxLt (by norm_num) w1 cast1 delta g0.next)
    fun g1 => ?_
  refine KeysIn.bind (KeysIn.of_tagged (Paths.growGarbleM_tagged 4 coord idx 0 row.width0 growFields _
    (row.keep - row.width0) (by omega))) fun grown => ?_
  exact KeysIn.bind_pure (KeysIn.of_tagged (Paths.foldsGarbleM_tagged coord idx m coordLt idxLt mSmall _
    (row.ell - row.keep) row.keep _ (by omega))) _

/-- The keys of modulus `i`: its body (family 6) and, for an odd row, its conversion. -/
def modFine (T : CrtTable) (S coord : ℕ) (i : Fin T.count) : Set TagKey :=
  Paths.bodyKeys coord i.val (T.modulus i) (T.padAnswers S i) ∪
    {k | ∃ row, T.kind i = .odd row ∧ k ∈ convFine coord i.val row (T.modulus i)}

theorem mod_keysIn (T : CrtTable) (S coord : ℕ) (ranges : Paths.TableRanges T S) (coordLt : coord < 2)
    (delta : Block) (chunks : ℕ → ChunkGarbled T.castWidth) (i : Fin T.count) :
    KeysIn (modFine T S coord i) (modGarbleM T S coord delta chunks i) := by
  have idxLt : i.val < 128 := lt_of_lt_of_le i.isLt ranges.count
  unfold modGarbleM
  split
  · exact (KeysIn.bind_pure (KeysIn.of_tagged (Paths.bodyGarbleM_tagged coord i.val _ S _ coordLt idxLt
      (ranges.modulus i) (ranges.pads i) _)) _).mono Set.subset_union_left
  · rename_i row kind
    refine (KeysIn.bind (KeysIn.of_tagged (Paths.materializeM_tagged _)) fun word =>
      KeysIn.bind (conversion_keysIn coord i.val row _ coordLt idxLt (ranges.rows i row kind) (ranges.modulus i)
        delta word) fun _ => KeysIn.bind_pure (KeysIn.of_tagged (Paths.bodyGarbleM_tagged coord i.val _ S _
          coordLt idxLt (ranges.modulus i) (ranges.pads i) _)) _).mono ?_
    rintro k (empty | conv | body)
    · simp at empty
    · exact Or.inr ⟨row, kind, conv⟩
    · exact Or.inl body

/-- The keys of one coordinate: its chunks and its moduli. -/
def coordFine (T : CrtTable) (S coord : ℕ) : Set TagKey :=
  {k | ∃ c : Fin T.chunkCount, k ∈ chunkFine T coord c.val} ∪ {k | ∃ i : Fin T.count, k ∈ modFine T S coord i}

theorem coord_keysIn (T : CrtTable) (S coord : ℕ) (ranges : Paths.TableRanges T S) (coordLt : coord < 2)
    (delta : Block) (zeroLabel : ℕ → Block) :
    KeysIn (coordFine T S coord) (coordGarbleM T S coord delta zeroLabel) := by
  unfold coordGarbleM coordFine
  refine KeysIn.bind (KeysIn.tableM (S := fun c => chunkFine T coord c.val) fun c =>
    chunk_keysIn T coord delta zeroLabel c.val coordLt (lt_of_lt_of_le c.isLt ranges.chunkCount)
      (ranges.chunkWidth c.val c.isLt) ranges.castAnswers) fun chunkTable => ?_
  exact (KeysIn.bind (KeysIn.tableM (S := fun i => modFine T S coord i) fun i =>
    mod_keysIn T S coord ranges coordLt delta _ i) fun _ => KeysIn.of_pure ∅ _).mono (by simp)

/-- **The fine keys of the garbler**: both coordinates' fine keys, then the key, the masks and the digest. -/
def garblerFine : Set TagKey :=
  coordFine Entry.table Entry.xCount 0 ∪ (coordFine Entry.table Entry.yCount 1 ∪ Paths.tailKeys)

theorem garble_keysIn (scalar : NonZeroScalar) (coins : Entry.Coins) :
    KeysIn garblerFine (Entry.garbleCM scalar coins) := by
  unfold Entry.garbleCM garblerFine Paths.tailKeys Paths.digestKeys
  dsimp only
  have ranges : ∀ S, S ≤ 1000 → Paths.TableRanges Entry.table S := Paths.bn254_ranges
  refine KeysIn.bind (coord_keysIn Entry.table Entry.xCount 0 (ranges _ (by decide)) (by norm_num) _ _)
    fun gx => ?_
  refine KeysIn.bind (coord_keysIn Entry.table Entry.yCount 1 (ranges _ (by decide)) (by norm_num) _ _)
    fun gy => ?_
  refine KeysIn.bind (KeysIn.of_tagged (Paths.keyM_tagged _)) fun K => ?_
  refine KeysIn.bind (KeysIn.of_tagged (Paths.maskAnswersM_tagged K digitCount (by decide) (by decide)))
    fun masks => ?_
  exact KeysIn.bind_pure (KeysIn.of_tagged (Paths.digestGarbleM_tagged coordinateBitCount digitCount (by decide)
    (by decide) _ _ _ _ _)) _

/-! ### The many-chunk decomposition -/

/-- The bound on chunk `c`'s value in a witness: a byte, and below `48` at chunk 31 (the top chunk of `p` is `48`,
so every lower chunk stays free). -/
def chunkBound (c : ℕ) : ℕ := if c = 31 then 48 else 256

theorem chunkBound_pos (c : ℕ) : 0 < chunkBound c := by
  unfold chunkBound
  split <;> norm_num

theorem chunkBound_le (c : ℕ) : chunkBound c ≤ 256 := by
  unfold chunkBound
  split <;> norm_num

/-- Chunk values within their bounds on the chunks below `n`. -/
def Admissible (α : ℕ → ℕ) (n : ℕ) : Prop := ∀ c < n, α c < chunkBound c

/-- The word value of modulus `m` of chunk values `α` on the chunks below `n`. -/
def wordOf (m : ℕ) (α : ℕ → ℕ) (n : ℕ) : ℕ := ∑ c ∈ Finset.range n, α c * 2 ^ (8 * c) % m

/-- Every `t ≤ B` is a word value on the chunks below `n`. -/
def Reach (m n B : ℕ) : Prop := ∀ t ≤ B, ∃ α : ℕ → ℕ, Admissible α n ∧ wordOf m α n = t

theorem wordOf_update (m n a : ℕ) (α : ℕ → ℕ) :
    wordOf m (Function.update α n a) (n + 1) = wordOf m α n + a * 2 ^ (8 * n) % m := by
  unfold wordOf
  rw [Finset.sum_range_succ, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Function.update_of_ne (by rw [Finset.mem_range] at hc; omega)]

theorem admissible_update {α : ℕ → ℕ} {n a : ℕ} (adm : Admissible α n) (ha : a < chunkBound n) :
    Admissible (Function.update α n a) (n + 1) := by
  intro c hc
  rcases Nat.lt_succ_iff_lt_or_eq.mp hc with lt | eq
  · rw [Function.update_of_ne (by omega)]
    exact adm c lt
  · subst eq
    rw [Function.update_self]
    exact ha

/-- **Chunk 0 alone** gives every value below `min m 256`. -/
theorem reach_one (m : ℕ) (hm : 0 < m) : Reach m 1 (min m 256 - 1) := by
  intro t ht
  refine ⟨fun _ => t, fun c hc => ?_, ?_⟩
  · have hc0 : c = 0 := by omega
    subst hc0
    unfold chunkBound
    rw [if_neg (by norm_num)]
    show t < 256
    omega
  · unfold wordOf
    rw [Finset.sum_range_one, Nat.mul_zero, pow_zero, Nat.mul_one]
    show t % m = t
    exact Nat.mod_eq_of_lt (by omega)

/-- **One more chunk**: with an admissible value `a` at chunk `n` whose term is at most `B + 1`, the reachable
values grow from `[0, B]` to `[0, B + term]`. -/
theorem reach_succ {m n B a : ℕ} (reach : Reach m n B) (ha : a < chunkBound n)
    (hx : a * 2 ^ (8 * n) % m ≤ B + 1) : Reach m (n + 1) (B + a * 2 ^ (8 * n) % m) := by
  intro t ht
  by_cases small : t ≤ B
  · obtain ⟨α, adm, sum⟩ := reach t small
    refine ⟨Function.update α n 0, admissible_update adm (chunkBound_pos n), ?_⟩
    rw [wordOf_update, sum, Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
  · obtain ⟨α, adm, sum⟩ := reach (t - a * 2 ^ (8 * n) % m) (by omega)
    refine ⟨Function.update α n a, admissible_update adm ha, ?_⟩
    rw [wordOf_update, sum]
    omega

/-- Run a certificate: the chunk values of chunks `n, n + 1, ...` from the bound `B`; `none` if a step fails. -/
def run (m : ℕ) : List ℕ → ℕ → ℕ → Option ℕ
  | [], _, B => some B
  | a :: rest, n, B =>
    if a < chunkBound n ∧ a * 2 ^ (8 * n) % m ≤ B + 1 then run m rest (n + 1) (B + a * 2 ^ (8 * n) % m)
    else none

theorem reach_run (m : ℕ) :
    ∀ (cert : List ℕ) (n B B' : ℕ), Reach m n B → run m cert n B = some B' → Reach m (n + cert.length) B'
  | [], n, B, B', reach, ran => by
    simp only [run, Option.some.injEq] at ran
    subst ran
    simpa using reach
  | a :: rest, n, B, B', reach, ran => by
    simp only [run] at ran
    split at ran
    · rename_i ok
      have next := reach_run m rest (n + 1) _ B' (reach_succ reach ok.1 ok.2) ran
      rw [List.length_cons, show n + (rest.length + 1) = n + 1 + rest.length by omega]
      exact next
    · simp at ran

/-- The chunk values of chunks `1 .. 31` packed in bytes. -/
def unpack (packed : ℕ) : List ℕ := (List.range 31).map fun j => packed / 256 ^ j % 256

theorem unpack_length (packed : ℕ) : (unpack packed).length = 31 := by
  unfold unpack
  rw [List.length_map, List.length_range]

/-- The largest target of an odd row of word width `ell`: `255`, `m − 1` and `2^(ell − 1) − 128`. -/
def need (m ell : ℕ) : ℕ := max 255 (max (m - 1) (2 ^ (ell - 1) - 128))

/-- The certificate check of one odd modulus. -/
def rowOK (m packed : ℕ) : Bool :=
  match run m (unpack packed) 1 (min m 256 - 1) with
  | some B => decide (need m (t9Row 32 m).ell ≤ B)
  | none => false


def certs : List ℕ :=
  [28380414028753969466561515933501938199330878594519746088102349021547335696,
    5356159782354996159058407140328605834666614213386387414388290269938716418,
    24867289702936142177752702957698539574018934046971618254123839226060539151,
    23121014972235923574959129362337296924313416753440270628126013273081189894,
    47912546278464114962189002777923851147714813538444749835165452940840079131,
    37179818057569265693191474049284561022041287900195561463758529279889703961,
    7344296303805632998313608453860390196495833599429535290305853994284030212,
    47926324174942076077736212738184870490681454585860882198862966390007734294,
    26731410366475142638632453163003769114486648868060723623162871016536345894,
    58444637109696281027496267625038564641416243487214074880654833110407844136,
    67340448738283032567064741782548767851630943765068607351665353359473512710,
    72828795240806606468214412700050169948743330675738451017103555649276490296,
    9249665266138572359720313898602225522132623008122415919388790458293625861,
    83408527665268881469478803636518654703015849177737689825561827262849553436,
    78011630064994382032111011105397895098036075434803096359071351458243489569,
    72891210911624931034638612939856535965903461733828023662353194930891998535,
    49874041437384187698232368803596619566212241414991190687664075465194276662,
    67196028441634436121328798443435833543981476016482850649329795497554614072,
    72573212747230322856906737004137027926546803004768411803512508200520717895,
    44759016592375144715514829076413660018159792716143357973785372792813132113,
    44834691658638744262186881828644382800507223474414636307074016033149894205,
    7165335880467185916766496039459890585018341300612539965300493763896165931,
    50086541533888282025863937854605505934305279484165656109145651336556776227,
    83650738043990482740788995950573967561462738405643906789804424853990754332,
    79825710659738103059712695692073320295998429796742846138234538239011456043,
    58894338842877938960435321060832686422782069643905370035872549751457142080,
    57293398665221155362437795942334673782618896726252386645907842954002313823,
    7233554440463531991021771629356512214262223037475094472926336152784485224,
    83699189745138368280406956753401049101631680901508594109246589975093272383,
    46484619477032261843319705688484645345031646666973183248332087541826398230,
    34282708091672978057561912551684943667426414219379231133699577045732900707,
    83314092260435853038364629959291354758162423399084786449955685696948680723,
    30348257625866647067530259462470540027632191395828823651227222425129481838,
    41674000329082607060955551573368247064790358276164333446464965052563147543,
    79694581587699025568345897249901699921115188105520031020157414128599978607,
    81332667734089488751445004443936408488473586112700516584089018442865275399,
    84119109144971465301155721839664441316676056509857911534305792570039692559,
    66084330173950575374099886978389748071188343463169307055880049077158505573,
    83382374109259572579872729982662036171139566635095342309422587393644905241,
    83921391849163155823438139103217260983568227294933493660779753994180721238,
    81614648426464435180449033005717197605906823015293150671578887706232531055,
    39087435150859626589611922162599371585248265597398031601491404419029160751,
    81283576728080281299727682773370464396239132981894094217444762566018493489,
    78732632022393848366454102343304316079625501397360082794671440394661617930,
    69097336052273882769711580221815687062035292213959070995810411830417266368,
    31095961111189989715519796496930361128560204176629336531056446087458342987,
    33243519089615220790182040229757884826674105829491263778694607099228037915,
    16020028239190939406286130130166454763741321830737069266712689764809522612,
    82556825046281141569951568661965713027856041161522872581342507727249582548,
    20000636060088112615912653792819358853198023340486864889675279406851540049,
    13608071368815733239346862246427589968604461624125078667271134073813412622,
    29932066891720875101164058650847220515766792546829442281423297484516549136,
    84640186617459690433581868967515007654947256324855321804946907356901542450,
    0,
    3526846198612178598592639747572833273311789630787838096065248139594039041,
    51379936092987335233955262838323373419244623515113434592366734932618289409,
    80765728297582270608744337147378188228705036431105796980463966478215331585,
    21293959089266322033494777371511113934789424378195096422830284652499098113,
    53853039423817226902256888271333835005159353450987918598154692245283359745,
    63828514727583001980268304196032385438481547470181106035993554193797472001,
    66167265033203189235376269837282281655080526946813201560428763964364389633,
    34036772410139107217505401690757750415366898150982895105685899227410741761,
    47501616778321449029446287188645909774142510239623377811215727513810234113,
    83464608773389095431954605692144724044344550251236907116704725702019096833,
    52791574665147454613990078510126942172950209859062232029959762565359714305,
    84785393397573679875565521621463096809360772375078898754533203725893101825,
    56534226608056472190452759067648431201623685669520983414027309402930521601,
    59918611391842353760014805958636807079143882931943136636774267986054410497,
    19578135260004374736563401040598507007271724256979676545079849071333236737,
    53698910896692109172861546193288801751801304802206314487031529385453911041,
    24134920333552142549568895303990216857284243470617771639749515253089994753,
    84110826674711183088488829034901544919014760274774663272246669483995480577,
    38785902190127853190874078198705602060671651640644607442606987683257889793,
    67356934543920459725090169392471912955051345384563218157772408542512876033,
    84794416985152820635855120099170737190551282016607715454179449303020838657,
    59074060707431652790500965529867200986091296794611351512088072956232383233,
    44170892799047458639871445255190826208349464075686437194475799692513177857,
    44204997555616802032824890259566602486945854790247955600341003438073004033,
    83247538128981529752274068759577974631899249561677207735972985360601708545,
    10431778690998467480845732307209352942810468550286480124126362443372811521,
    56768721193563245205232109887123331569987785822656791809278198600210931457,
    12622783144470356454365916720530058644646428273483339316568751820236586241,
    82931263398565535488511155764941315218473843998179472629365398706012027649,
    29646600765342307635000733896715907805719852812984324900025695415390668033,
    84530146115462480339348247492334092200132410577346111770347391072018339585]


/-- **The certificate check over the 85 rows** (small closed arithmetic, by the kernel). -/
theorem rows_ok : ∀ i : Fin bn254Table.count, bn254Table.modulus i ≠ 256 →
    rowOK (bn254Table.modulus i) (certs.getD i.val 0) = true := by
  decide +kernel

/-- `48 · 256^31 ≤ p` (the top chunk of `p` is `48`). -/
theorem top_le : 48 * 256 ^ 31 ≤ baseFieldModulus := by
  unfold baseFieldModulus
  decide +kernel

/-! ### Coordinate values from chunk values -/

/-- The coordinate value of chunk values `α` on the chunks below `n`. -/
def valueOf (α : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => valueOf α n + α n * 256 ^ n

theorem valueOf_lt (α : ℕ → ℕ) : ∀ n, (∀ c < n, α c < 256) → valueOf α n < 256 ^ n
  | 0, _ => by simp [valueOf]
  | n + 1, small => by
    have ih := valueOf_lt α n fun c hc => small c (by omega)
    have top := small n (by omega)
    have step : α n * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    simp only [valueOf, pow_succ]
    omega

theorem valueOf_split (α : ℕ → ℕ) (c : ℕ) :
    ∀ k, valueOf α (c + k) = valueOf α c + 256 ^ c * valueOf (fun d => α (c + d)) k
  | 0 => by simp [valueOf]
  | k + 1 => by
    rw [← Nat.add_assoc]
    simp only [valueOf]
    rw [valueOf_split α c k, pow_add]
    ring

theorem admissible_byte {α : ℕ → ℕ} {n : ℕ} (adm : Admissible α n) : ∀ c < n, α c < 256 :=
  fun c hc => lt_of_lt_of_le (adm c hc) (chunkBound_le c)

theorem table_chunkBits : Entry.table.chunkBits = 8 := rfl

theorem table_inputBits' : Entry.table.inputBits = 254 := rfl

theorem table_chunkCount : Entry.table.chunkCount = 32 := Paths.bn254_chunkCount

/-- The chunk values of `valueOf α 32` are the `α c`. -/
theorem chunkValue_valueOf (α : ℕ → ℕ) (adm : Admissible α 32) (c : ℕ) (hc : c < 32) :
    Entry.table.chunkValue (valueOf α 32) c = α c := by
  unfold CrtTable.chunkValue CrtTable.chunkOffset CrtTable.chunkWidth
  rw [table_chunkBits, table_inputBits', Nat.shiftRight_eq_div_pow, pow_mul]
  have split := valueOf_split α c (32 - c)
  rw [show c + (32 - c) = 32 by omega] at split
  have split' := valueOf_split (fun d => α (c + d)) 1 (31 - c)
  rw [show 1 + (31 - c) = 32 - c by omega] at split'
  have low : valueOf α c < 256 ^ c := valueOf_lt α c fun d hd => admissible_byte adm d (by omega)
  have one : valueOf (fun d => α (c + d)) 1 = α c := by simp [valueOf]
  rw [split, split', one, show (2 : ℕ) ^ 8 = 256 by norm_num,
    Nat.add_mul_div_left _ _ (pow_pos (by norm_num : (0 : ℕ) < 256) c), Nat.div_eq_of_lt low, Nat.zero_add]
  rcases Nat.lt_or_ge c 31 with lt | ge
  · rw [show min 8 (254 - 8 * c) = 8 by omega, show (2 : ℕ) ^ 8 = 256 by norm_num, pow_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (admissible_byte adm c hc)]
  · have c31 : c = 31 := by omega
    subst c31
    have top : α 31 < 48 := by
      have := adm 31 (by norm_num)
      unfold chunkBound at this
      simpa using this
    simp only [valueOf, show 31 - 31 = 0 by rfl, Nat.mul_zero, Nat.add_zero]
    rw [show min 8 (254 - 8 * 31) = 6 by norm_num]
    exact Nat.mod_eq_of_lt (by norm_num; omega)

/-- `valueOf α 32 < 48 · 256^31 ≤ p`. -/
theorem valueOf_lt_p (α : ℕ → ℕ) (adm : Admissible α 32) : valueOf α 32 < baseFieldModulus := by
  have low : valueOf α 31 < 256 ^ 31 := valueOf_lt α 31 fun d hd => admissible_byte adm d (by omega)
  have top : α 31 < 48 := by
    have := adm 31 (by norm_num)
    unfold chunkBound at this
    simpa using this
  have step : α 31 * 256 ^ 31 ≤ 47 * 256 ^ 31 := Nat.mul_le_mul_right _ (by omega)
  have whole : valueOf α 32 = valueOf α 31 + α 31 * 256 ^ 31 := rfl
  have := top_le
  omega

/-- The word value of `valueOf α 32` is `wordOf m α 32`. -/
theorem wordValue_valueOf (m : ℕ) (α : ℕ → ℕ) (adm : Admissible α 32) :
    Entry.table.wordValue m (valueOf α 32) = wordOf m α 32 := by
  unfold CrtTable.wordValue CrtTable.truth wordOf
  rw [Fin.sum_univ_eq_sum_range (fun c => Entry.table.chunkValue (valueOf α 32) c *
    2 ^ Entry.table.chunkOffset c % m) Entry.table.chunkCount, table_chunkCount]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [chunkValue_valueOf α adm c (Finset.mem_range.mp hc)]
  unfold CrtTable.chunkOffset
  rw [table_chunkBits]

/-! ### The rows -/

/-- An odd row of the real table uses the selected fallback schedule. -/
theorem row_eq (i : Fin Entry.table.count) (row : OddRow) (hk : Entry.table.kind i = .odd row) :
    row = fallbackRow 32 (Entry.table.modulus i) ∧ Entry.table.modulus i ≠ 256 := by
  change fallbackKind (bn254Table.modulus i) = .odd row at hk
  unfold fallbackKind at hk
  split at hk
  · cases hk
  · rename_i notPow
    cases hk
    exact ⟨rfl, notPow⟩

/-- The shape of an odd row of the real table. -/
theorem row_shape (i : Fin Entry.table.count) (row : OddRow) (hk : Entry.table.kind i = .odd row) :
    7 ≤ row.width0 ∧ row.width0 ≤ 8 ∧ row.width1 = row.ell - row.width0 - 1 ∧
      row.keep = max row.width0 (row.ell - 5) ∧ 9 ≤ row.ell ∧ row.ell ≤ 14 ∧
      32 * (Entry.table.modulus i - 1) < 2 ^ row.ell := by
  have facts := SliceC.bn254_odd i row hk
  obtain ⟨_, w1, sum, _, _, cast, lt⟩ := facts
  obtain ⟨rfl, _⟩ := row_eq i row hk
  have castW : bn254Table.castWidth = 14 := rfl
  rw [table_chunkCount] at lt
  have w0lo : 7 ≤ (fallbackRow 32 (Entry.table.modulus i)).width0 := fallbackWidth0_lower _
  have w0hi : (fallbackRow 32 (Entry.table.modulus i)).width0 ≤ 8 := fallbackWidth0_upper _
  refine ⟨w0lo, w0hi, rfl, rfl, ?_, by rw [castW] at cast; exact cast, lt⟩
  omega

/-- **The many-chunk decomposition**: every target up to `need` is the word value of a coordinate value below
`p`. -/
theorem word_target (i : Fin Entry.table.count) (row : OddRow) (hk : Entry.table.kind i = .odd row) (t : ℕ)
    (ht : t ≤ need (Entry.table.modulus i) row.ell) :
    ∃ v < baseFieldModulus, Entry.table.wordValue (Entry.table.modulus i) v = t := by
  obtain ⟨rowEq, notPow⟩ := row_eq i row hk
  have ok := rows_ok i notPow
  have pos : 0 < Entry.table.modulus i := SliceC.bn254_modulus_pos i
  unfold rowOK at ok
  split at ok
  · rename_i B ran
    have enough : need (Entry.table.modulus i) (t9Row 32 (Entry.table.modulus i)).ell ≤ B := of_decide_eq_true ok
    -- The certificate depends only on ell, which the schedule selector preserves.
    have ellEq : row.ell = (t9Row 32 (Entry.table.modulus i)).ell := congrArg OddRow.ell rowEq
    rw [← ellEq] at enough
    have reach := reach_run (Entry.table.modulus i) _ 1 _ B (reach_one _ pos) ran
    rw [unpack_length] at reach
    obtain ⟨α, adm, sum⟩ := reach t (le_trans ht enough)
    exact ⟨valueOf α 32, valueOf_lt_p α adm, by rw [wordValue_valueOf _ α adm]; exact sum⟩
  · simp at ok

theorem le_need_255 {m ell t : ℕ} (h : t ≤ 255) : t ≤ need m ell := le_trans h (le_max_left _ _)

theorem le_need_m {m ell t : ℕ} (h : t ≤ m - 1) : t ≤ need m ell :=
  le_trans h (le_trans (le_max_left _ _) (le_max_right _ _))

theorem le_need_top {m ell t : ℕ} (h : t ≤ 2 ^ (ell - 1) - 128) : t ≤ need m ell :=
  le_trans h (le_trans (le_max_right _ _) (le_max_right _ _))

/-! ### Witness inputs -/

/-- The input whose coordinate `κ` is `v` and whose other coordinate is `0`. -/
def inputAt (κ v : ℕ) : AffineInput := if κ = 0 then ⟨(v : BaseField), 0⟩ else ⟨0, (v : BaseField)⟩

theorem coordValue_inputAt {κ v : ℕ} (hκ : κ < 2) (hv : v < baseFieldModulus) :
    coordValue (inputAt κ v) κ = v := by
  unfold coordValue inputAt
  rcases (by omega : κ = 0 ∨ κ = 1) with rfl | rfl
  · simp only [if_true]
    exact val_natCast_of_lt hv
  · simp only [one_ne_zero, if_false]
    exact val_natCast_of_lt hv

/-! ### The families -/

theorem chunkValue_single {c s : ℕ} (hs : s < 2 ^ Entry.table.chunkWidth c) :
    Entry.table.chunkValue (s * 2 ^ (8 * c)) c = s := by
  unfold CrtTable.chunkValue CrtTable.chunkOffset
  rw [table_chunkBits, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mod_eq_of_lt hs]

theorem chunkWidth_le (c : ℕ) : Entry.table.chunkWidth c ≤ 254 - 8 * c := by
  unfold CrtTable.chunkWidth
  rw [table_chunkBits, table_inputBits']
  exact Nat.min_le_right _ _

theorem chunkWidth_le_eight (c : ℕ) : Entry.table.chunkWidth c ≤ 8 := Paths.bn254_chunkWidth c

theorem single_lt {c s w : ℕ} (hs : s < 2 ^ w) (hw : 8 * c + w ≤ 253) : s * 2 ^ (8 * c) < baseFieldModulus := by
  have lt : s * 2 ^ (8 * c) < 2 ^ 253 := by
    calc s * 2 ^ (8 * c) < 2 ^ w * 2 ^ (8 * c) := Nat.mul_lt_mul_of_pos_right hs (Nat.two_pow_pos _)
      _ = 2 ^ (w + 8 * c) := (pow_add 2 w (8 * c)).symm
      _ ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact lt_trans lt StageOneProof.pow253_lt

/-- **Chunk trees and casts.** -/
theorem reach_chunk (S κ : ℕ) (hκ : κ < 2) (c : Fin Entry.table.chunkCount) (k : TagKey)
    (member : k ∈ chunkFine Entry.table κ c.val) (range : k.InRange)
    (never : ¬ StageOneProof.NeverHotCast k.code) : ∃ u, hotTag Entry.table u k.code = true := by
  have hc : c.val < 32 := lt_of_lt_of_le c.isLt table_chunkCount.le
  have wide := chunkWidth_le c.val
  have eight := chunkWidth_le_eight c.val
  have trange := tagInRange_of_key range
  obtain ⟨fam, κ, idx, stage, level, slot, part⟩ := k
  simp only [chunkFine, pairFine, Paths.treeKeys, Paths.castKeys, Set.mem_union, Set.mem_ofPred_eq] at member
  rcases member with ⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3⟩ | ⟨rfl, rfl, rfl, rfl, rfl, h1, _⟩
  · have hs : slot < 2 ^ Entry.table.chunkWidth c.val :=
      lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hv : slot * 2 ^ (8 * c.val) < baseFieldModulus := single_lt h3 (by omega)
    refine ⟨inputAt κ (slot * 2 ^ (8 * c.val)), ?_⟩
    show hotTag Entry.table _ (chunkTreeTag κ c.val level slot) = true
    rw [hotTag_chunkTree Entry.table _ trange, coordValue_inputAt hκ hv, chunkValue_single hs,
      Nat.mod_eq_of_lt h3]
    exact beq_self_eq_true slot
  · have hv : slot * 2 ^ (8 * c.val) < baseFieldModulus := by
      rcases Nat.lt_or_ge c.val 31 with lt | ge
      · exact single_lt h1 (by omega)
      · have c31 : c.val = 31 := by omega
        have small : slot < 49 := by
          by_contra big
          apply never
          show StageOneProof.NeverHotCast (tagCode 1 κ c.val 0 0 slot part)
          exact ⟨tagFamily_tagCode trange, by rw [tagIdx_tagCode trange]; exact c31,
            by rw [tagSlot_tagCode trange]; dsimp only; omega⟩
        rw [c31]
        have step : slot * 2 ^ (8 * 31) ≤ 48 * 2 ^ (8 * 31) := Nat.mul_le_mul_right _ (by omega)
        have strict : 48 * 2 ^ (8 * 31) < baseFieldModulus := by
          unfold baseFieldModulus
          decide +kernel
        exact lt_of_le_of_lt step strict
    refine ⟨inputAt κ (slot * 2 ^ (8 * c.val)), ?_⟩
    show hotTag Entry.table _ (chunkCastTag κ c.val slot part) = true
    rw [hotTag_chunkCast Entry.table _ trange, coordValue_inputAt hκ hv, chunkValue_single h1]
    exact beq_self_eq_true slot

/-- The word value `t` makes a tag of families 2 to 5 hot when the matching condition holds. -/
theorem hot_of_word {κ : ℕ} (hκ : κ < 2) (i : Fin Entry.table.count) (row : OddRow)
    (hk : Entry.table.kind i = .odd row) {fam stage level slot part : ℕ}
    (range : TagInRange κ i.val stage level slot part) (two : 2 ≤ fam) (five : fam ≤ 5) (t : ℕ)
    (ht : t ≤ need (Entry.table.modulus i) row.ell)
    (cond : (match fam with
       | 2 => slot == stageValue row t stage % 2 ^ level
       | 3 => slot == stageValue row t stage
       | 4 => slot == t % 2 ^ level
       | 5 => slot == t % 2 ^ level % Entry.table.modulus i
       | _ => false) = true) :
    ∃ u, hotTag Entry.table u (tagCode fam κ i.val stage level slot part) = true := by
  obtain ⟨v, hv, word⟩ := word_target i row hk t ht
  refine ⟨inputAt κ v, ?_⟩
  rw [hotTag_odd Entry.table _ i row hk range two five]
  simp only [coordValue_inputAt hκ hv, word]
  exact cond

/-- **One modulus**: the body and, for an odd row, the conversion. -/
theorem reach_mod (S κ : ℕ) (hκ : κ < 2) (i : Fin Entry.table.count) (k : TagKey)
    (member : k ∈ modFine Entry.table S κ i) (range : k.InRange) : ∃ u, hotTag Entry.table u k.code = true := by
  have trange := tagInRange_of_key range
  have mLe : Entry.table.modulus i ≤ 439 := Paths.bn254_modulus_le i
  obtain ⟨fam, κ, idx, stage, level, slot, part⟩ := k
  rcases member with body | ⟨row, hk, conv⟩
  · simp only [Paths.bodyKeys, Set.mem_ofPred_eq] at body
    obtain ⟨rfl, rfl, rfl, rfl, rfl, h1, _⟩ := body
    have hv : slot < baseFieldModulus := lt_of_lt_of_le h1 (le_trans mLe (by unfold baseFieldModulus; norm_num))
    refine ⟨inputAt κ slot, ?_⟩
    show hotTag Entry.table _ (bodyTag κ i.val slot part) = true
    rw [hotTag_body Entry.table _ i trange, coordValue_inputAt hκ hv, Nat.mod_eq_of_lt h1]
    exact beq_self_eq_true slot
  · obtain ⟨w0lo, w0hi, w1, keep, ell9, ell14, big⟩ := row_shape i row hk
    -- CHECK: Elaborate the generalized Nat-subtraction/power identity and the omega
    -- side goals below; they previously specialized width0 to the numeral 7.
    have p1 : 2 ^ (row.ell - 1) = 2 ^ row.width0 * 2 ^ row.width1 := by
      rw [← pow_add]; congr 1; omega
    have powLo : 128 ≤ 2 ^ row.width0 := by
      calc 128 = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ row.width0 := Nat.pow_le_pow_right (by norm_num) w0lo
    have powHi : 2 ^ row.width0 ≤ 256 := by
      calc 2 ^ row.width0 ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) w0hi
        _ = 256 := by norm_num
    have keepLe : row.keep ≤ 9 := by rw [keep]; omega
    have widthLeKeep : row.width0 ≤ row.keep := by rw [keep]; exact le_max_left _ _
    have ellKeep : row.ell ≤ 5 + row.keep := by rw [keep]; omega
    -- Multiplying the successor inequality retains the gap of at least 128 needed by
    -- the original certificate, for both width0 = 7 and width0 = 8.
    have stageOneBound : ∀ s < 2 ^ row.width1,
        2 ^ row.width0 * s ≤ 2 ^ (row.ell - 1) - 128 := by
      intro s small
      have scaled : 2 ^ row.width0 * (s + 1) ≤ 2 ^ (row.ell - 1) := by
        calc 2 ^ row.width0 * (s + 1) ≤ 2 ^ row.width0 * 2 ^ row.width1 :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ (row.ell - 1) := p1.symm
      rw [Nat.mul_add, Nat.mul_one] at scaled
      omega
    simp only [convFine, pairFine, Paths.treeKeys, Paths.castKeys, Paths.growKeys, Paths.foldKeys,
      Set.mem_union, Set.mem_ofPred_eq] at conv
    rcases conv with ((⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3⟩ | ⟨rfl, rfl, rfl, rfl, rfl, h1, _⟩) |
      ((⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3⟩ | ⟨rfl, rfl, rfl, rfl, rfl, h1, _⟩) |
      (⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3⟩ | ⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3⟩)))
    · -- stage 0 tree: `t = slot`
      have small : slot < 2 ^ row.width0 :=
        lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact hot_of_word hκ i row hk trange (by norm_num) (by norm_num) slot (le_need_255 (by omega)) (by
        simp only [stageValue, if_true, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt h3]
        exact beq_self_eq_true slot)
    · -- stage 0 cast: `t = slot`
      exact hot_of_word hκ i row hk trange (by norm_num) (by norm_num) slot (le_need_255 (by omega)) (by
        simp only [stageValue, if_true, Nat.mod_eq_of_lt h1]
        exact beq_self_eq_true slot)
    · -- stage 1 tree: `t = 2^width0 · slot`
      have small : slot < 2 ^ row.width1 := lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact hot_of_word hκ i row hk trange (by norm_num) (by norm_num) (2 ^ row.width0 * slot)
        (le_need_top (stageOneBound slot small)) (by
        simp only [stageValue, one_ne_zero, if_false,
          Nat.mul_div_cancel_left slot (Nat.two_pow_pos row.width0), Nat.mod_eq_of_lt small,
          Nat.mod_eq_of_lt h3]
        exact beq_self_eq_true slot)
    · -- stage 1 cast: `t = 2^width0 · slot`
      exact hot_of_word hκ i row hk trange (by norm_num) (by norm_num) (2 ^ row.width0 * slot)
        (le_need_top (stageOneBound slot h1)) (by
        simp only [stageValue, one_ne_zero, if_false,
          Nat.mul_div_cancel_left slot (Nat.two_pow_pos row.width0), Nat.mod_eq_of_lt h1]
        exact beq_self_eq_true slot)
    · -- growth: `t = slot`
      have small : slot < 2 ^ 8 := lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact hot_of_word hκ i row hk trange (by norm_num) (by norm_num) slot (le_need_255 (by omega)) (by
        simp only [Nat.mod_eq_of_lt h3]
        exact beq_self_eq_true slot)
    · -- fold: `t = slot < m ≤ 2^keep ≤ 2^level`
      have mPow : Entry.table.modulus i ≤ 2 ^ level := by
        have ellLe : 2 ^ row.ell ≤ 2 ^ 5 * 2 ^ level := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have pos := SliceC.bn254_modulus_pos i
        omega
      have small : slot < 2 ^ level := lt_of_lt_of_le h3 mPow
      exact hot_of_word hκ i row hk trange (by norm_num) (by norm_num) slot (le_need_m (by omega)) (by
        simp only [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt h3]
        exact beq_self_eq_true slot)

/-- **One coordinate.** -/
theorem reach_coord (S κ : ℕ) (hκ : κ < 2) (k : TagKey) (member : k ∈ coordFine Entry.table S κ)
    (range : k.InRange) (never : ¬ StageOneProof.NeverHotCast k.code) :
    ∃ u, hotTag Entry.table u k.code = true := by
  rcases member with ⟨c, inC⟩ | ⟨i, inM⟩
  · exact reach_chunk S κ hκ c k inC range never
  · exact reach_mod S κ hκ i k inM range

/-- **`ConvTagsReachable`**: every garbler tag of families 0 to 6, except the 30 never-hot casts, is hot at some
input. -/
theorem convTagsReachable : StageOneProof.ConvTagsReachable := by
  intro scalar tape N inside fam never
  unfold StageTwo.gAsked at inside
  obtain ⟨k, member, range, label, same⟩ := garble_keysIn scalar tape.1 _ N inside
  have tag : N / 2 ^ 128 = k.code := StageOneProof.tag_of_gAsked same
  rw [tag] at fam never ⊢
  rw [tagFamily_key range] at fam
  rcases member with inX | inY | inTail
  · exact reach_coord Entry.xCount 0 (by norm_num) k inX range never
  · exact reach_coord Entry.yCount 1 (by norm_num) k inY range never
  · have := Paths.tail_fams k inTail
    omega

end Kriterion.CRT.Privacy.ConvReach
