/- Isolated nine-bit candidate feasibility proof; production definitions are unchanged.
Reach-walk and value decomposition proofs are adapted from the inherited Hidden/Reach.lean.
The generic CRT delivery proof is reused only for this explicit research table. -/
import Proof.Privacy.CRT.Hidden.Reach
import Proof.Correctness.CRT.Record

namespace Kriterion.CRT.Chunk9Research
open BN254
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

def moduli : Array Nat := #[19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59, 61, 67, 71, 73, 79, 81, 83, 89, 97, 101, 103, 107, 109, 113, 121, 125, 127, 131, 137, 139, 149, 151, 157, 163, 167, 169, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 512, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439]

def rowFor (m : Nat) : OddRow :=
  let ell := bitLength (29 * (m - 1))
  let w0 := if m ∈ ([73, 79, 81, 83, 89, 97, 101] : List Nat) then 7 else 8
  {ell, width0 := w0, width1 := ell - w0 - 1, keep := max w0 (bitLength (m - 1))}

def kindOf (m : Nat) : Kind := if m = 512 then .chunkZero else .odd (rowFor m)
def table : CrtTable := CrtTable.ofModuli 254 9 14 moduli kindOf padSlack (wrapBound baseFieldModulus)

theorem modulus_pos : ∀ i, 0 < table.modulus i := by decide +kernel

theorem odd_facts : ∀ i, table.modulus i ≠ 512 →
    1 ≤ (rowFor (table.modulus i)).width0 ∧ 1 ≤ (rowFor (table.modulus i)).width1 ∧
    (rowFor (table.modulus i)).width0 + (rowFor (table.modulus i)).width1 + 1 =
      (rowFor (table.modulus i)).ell ∧
    (rowFor (table.modulus i)).width0 ≤ (rowFor (table.modulus i)).keep ∧
    (rowFor (table.modulus i)).keep ≤ (rowFor (table.modulus i)).ell ∧
    (rowFor (table.modulus i)).ell ≤ table.castWidth ∧
    table.chunkCount * (table.modulus i - 1) < 2 ^ (rowFor (table.modulus i)).ell := by decide +kernel

theorem correctTable : SliceC.CorrectTable table where
  chunkBits_pos := by decide
  inputBits_pos := by decide
  castWidth_pos := by decide
  modulus_pos := modulus_pos
  coprime := by unfold Pairwise Function.onFun; decide +kernel
  wrap := by decide +kernel
  chunkZero := by decide +kernel
  odd := by
    intro i row hk
    change kindOf (table.modulus i) = .odd row at hk
    unfold kindOf at hk
    split at hk
    · cases hk
    · cases hk
      exact odd_facts i ‹_›

theorem records_fit : 2 * table.product ≤ 2 ^ 621 := by decide +kernel

def chunkBound (c : ℕ) : ℕ := if c = 28 then 3 else 512

theorem chunkBound_pos (c : ℕ) : 0 < chunkBound c := by
  unfold chunkBound
  split <;> norm_num

theorem chunkBound_le (c : ℕ) : chunkBound c ≤ 512 := by
  unfold chunkBound
  split <;> norm_num

/-- Chunk values within their bounds on the chunks below `n`. -/
def Admissible (α : ℕ → ℕ) (n : ℕ) : Prop := ∀ c < n, α c < chunkBound c

/-- The word value of modulus `m` of chunk values `α` on the chunks below `n`. -/
def wordOf (m : ℕ) (α : ℕ → ℕ) (n : ℕ) : ℕ := ∑ c ∈ Finset.range n, α c * 2 ^ (9 * c) % m

/-- Every `t ≤ B` is a word value on the chunks below `n`. -/
def Reach (m n B : ℕ) : Prop := ∀ t ≤ B, ∃ α : ℕ → ℕ, Admissible α n ∧ wordOf m α n = t

theorem wordOf_update (m n a : ℕ) (α : ℕ → ℕ) :
    wordOf m (Function.update α n a) (n + 1) = wordOf m α n + a * 2 ^ (9 * n) % m := by
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

/-- **Chunk 0 alone** gives every value below `min m 512`. -/
theorem reach_one (m : ℕ) (hm : 0 < m) : Reach m 1 (min m 512 - 1) := by
  intro t ht
  refine ⟨fun _ => t, fun c hc => ?_, ?_⟩
  · have hc0 : c = 0 := by omega
    subst hc0
    unfold chunkBound
    rw [if_neg (by norm_num)]
    show t < 512
    omega
  · unfold wordOf
    rw [Finset.sum_range_one, Nat.mul_zero, pow_zero, Nat.mul_one]
    show t % m = t
    exact Nat.mod_eq_of_lt (by omega)

/-- **One more chunk**: with an admissible value `a` at chunk `n` whose term is at most `B + 1`, the reachable
values grow from `[0, B]` to `[0, B + term]`. -/
theorem reach_succ {m n B a : ℕ} (reach : Reach m n B) (ha : a < chunkBound n)
    (hx : a * 2 ^ (9 * n) % m ≤ B + 1) : Reach m (n + 1) (B + a * 2 ^ (9 * n) % m) := by
  intro t ht
  by_cases small : t ≤ B
  · obtain ⟨α, adm, sum⟩ := reach t small
    refine ⟨Function.update α n 0, admissible_update adm (chunkBound_pos n), ?_⟩
    rw [wordOf_update, sum, Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
  · obtain ⟨α, adm, sum⟩ := reach (t - a * 2 ^ (9 * n) % m) (by omega)
    refine ⟨Function.update α n a, admissible_update adm ha, ?_⟩
    rw [wordOf_update, sum]
    omega

/-- Run a certificate: the chunk values of chunks `n, n + 1, ...` from the bound `B`; `none` if a step fails. -/
def run (m : ℕ) : List ℕ → ℕ → ℕ → Option ℕ
  | [], _, B => some B
  | a :: rest, n, B =>
    if a < chunkBound n ∧ a * 2 ^ (9 * n) % m ≤ B + 1 then run m rest (n + 1) (B + a * 2 ^ (9 * n) % m)
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

/-- The chunk values of chunks `1 .. 28` packed in bytes. -/
def unpack (packed : ℕ) : List ℕ := (List.range 28).map fun j => packed / 512 ^ j % 512

theorem unpack_length (packed : ℕ) : (unpack packed).length = 28 := by
  unfold unpack
  rw [List.length_map, List.length_range]

/-- The largest target of an odd row of word width `ell`: `255`, `m − 1` and `2^(ell − 1) − 128`. -/
def need (m ell : ℕ) : ℕ := max 255 (max (m - 1) (2 ^ (ell - 1) - 128))

/-- The certificate check of one odd modulus. -/
def rowOK (m packed : ℕ) : Bool :=
  match run m (unpack packed) 1 (min m 512 - 1) with
  | some B => decide (need m (t9Row 29 m).ell ≤ B)
  | none => false


def certs : List Nat := [28577652482272460288595085137310454626324302852842244051664970239452161, 304755765134395906503344996283188834706141539825467408834758741861862931, 276934047568714474714225876979445576660444501146230875773684096560801795, 746955444823407851349006009737896525554138840723842297017548152296453661, 165699104304531304715494156339307123704645529574128566509597526391783967, 139008860154606745108930665832560336247262755471701691328224056829823490, 111885990652262152122620378920348406796258133771225741614229215466754059, 278443912789263904300431651961839973239205442388126707810458514681241107, 745715708121735214660426922690824217298492170934241849799331183240434196, 1380406876436300646125579667483253269991551896113806236609008571668781059, 195626536012390135210555319702900390843354045003292447777268361107362844, 1052198072576570442616909278065046442685747142150083691067812506366906913, 416376157348257723079600109195350597223562859212873037809986884375415310, 1850263574521555642372106615248215919743571379531863120095236252519924276, 1991592777519274704187826537040941419014932924853926653381693095781896264, 749598686674946172515172994279739852537276798884613317205970051738401307, 29011867835203366750389907438101202609178739587931819090314555660973084, 2073436534940905226532511540394822318169791758589342177562528543001566797, 1215303123718553855574158901435263586800550103054622122205370187140862549, 333065076963803308019509404925184666771270911481904808950308764378234959, 750134623622506353479724729154906955013631103611643226899477659395590216, 664240234159590077773949455367028416365057207413930888115681185208246341, 307347713953441072577854560935189638413587860075541454984393879767491598, 911092463631425195699416127113870382373748942022175661602916318306370124, 1464038858376627560960775221874449149550641138691580301688972217759355936, 1633075411645640776185170757848979545068251007078799101084337054179431020, 84768087291181853249427557435217976382951144469644267444598120041700404, 3401650971214329793561980903032992751627059052330680491434229771382615647, 1633029704457148645659724298590509789547859587933526397401190010922996747, 829083769033610698406144671312699537870347445908585727655084432438617206, 1580782689259929836133413278974543218636136939093783153083784689327021135, 3757197998134944604840212926912523039344240891418701426049753736106790967, 3648828917650106324899214937618720248038267999229645299007289183786829911, 635018924495728151445385236995684375620423203446332305757376772627547782, 28851377076294171104099872004410051550988201000245861506121895581375573, 2850594090170740464740045721203505348538839108425167482410815817721350747, 938691954810820589346987275836179238242085295788314139551443660900152967, 1961284209329498619030445070804275199791534814239471566157153222112606307, 2295331137079344582148152955477629663050302566967003327853568636682563627, 2046115262418503505748473060562970668577443343503291157623362477155177618, 4724791970526608089107026061518904395668720072371604191386530359457171575, 4669047328806164688461024976052274179523646401654763347247223036498687609, 3897456589794657753948743967297761362438582808233017619564848596487854085, 2160697055434900430685647044317032551319687725726487713365803331721957984, 4173307087646138599140584444937847174143012032168062517917610032322847887, 726159772139684943676230694072980464942780929735681582012546651695980669, 3985135194681651908309491410880379392206741972642025679218030508204920922, 3017865789403922257329624325749830337206350822192987128407898206358318186, 5911033319476494294911632197998057557561948320856941611170852862292157085, 3104024748706591055622115673770445040052634655813849919609915633471421447, 837754274683325604796334083761741799488019563222611121548750297557983752, 3407845205924049418098294780149186972182592322768626087067535021841383449, 0, 893843552084179777250412876748893445790666225245254525739384486322536577, 3711653733039199460460121076197204301507319053160748172633392858493670494, 2489001071282392590023752324865429683362347909695204096488693740879275758, 4721844575619898318302355389085408575024844859732640572135063726127676678, 6159164954304308774589294529274731927696114317317258354861582474355418657, 114812866570472525461300109897836907212309952481959901397086948506533027, 7233156476273117740399283319531826646664298858121364825371473860109847704, 1252344193852734502839248967388074467420180674982072812454700456393917027, 2900632675382524458253901409972723208225539070387468893590922889076561200, 5585890702318444576811197167235887773301674443620172992997363845608565842, 4168729704107793058902534430784826386561470562273213330429114188636119202, 5260317325078393008569184031442673106050975426675272829182274014143129613, 3437662942200133124317113967628633484378190023604167867343379754851868224, 4474625071695868269014603873125407003517421923097157616236608599471330077, 4871739909302603520215320417217844623709326888238819115252703198409404559, 5168872937422970667907422852021922683507024440612960908370173758662000295, 588517735974894612786043143731213614329997059308542576885128840357364847, 3017968086592993986070199053974113742789765579260351619236801289941010493, 4645434775142507015038685943267752037155459203516336703800272758465125150, 6549285594912846683926419004743117467262165311682530468527722055301692065, 2615232510201451742944566950602347098781299310300969805123076580906190146, 9646190589547482812023183796100795828424540238277043715430436345589616223, 9186015104574103076293751200169082965791513461658736201991835767673807101, 5507600192526360360693329094509148544593190910623994445827077931089535228, 4265095544500957237989197754486953541738325241350726587491858950509445409, 1105920932184276458515084737275620597003420503376000913002179793480935559, 7344408951134773474911306468450191401841139329703814424718580530105984009, 5946232574601624523399088520021777225010883630397920341376988562729629221, 11584650056307960565855195221097015781649130424787728631388288898291312410, 2190633609495443261729025081602090245463752281303374137455674357700192029, 11354618041777141004555546238401512089937519857586945938242257568462480902]

theorem rows_ok : ∀ i : Fin table.count, table.modulus i ≠ 512 →
    rowOK (table.modulus i) (certs.getD i.val 0) = true := by decide +kernel

theorem top_le : 3 * 512 ^ 28 ≤ baseFieldModulus := by decide +kernel

def valueOf (α : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => valueOf α n + α n * 512 ^ n

theorem valueOf_lt (α : ℕ → ℕ) : ∀ n, (∀ c < n, α c < 512) → valueOf α n < 512 ^ n
  | 0, _ => by simp [valueOf]
  | n + 1, small => by
    have ih := valueOf_lt α n fun c hc => small c (by omega)
    have top := small n (by omega)
    have step : α n * 512 ^ n ≤ 511 * 512 ^ n := Nat.mul_le_mul_right _ (by omega)
    simp only [valueOf, pow_succ]
    omega

theorem valueOf_split (α : ℕ → ℕ) (c : ℕ) :
    ∀ k, valueOf α (c + k) = valueOf α c + 512 ^ c * valueOf (fun d => α (c + d)) k
  | 0 => by simp [valueOf]
  | k + 1 => by
    rw [← Nat.add_assoc]
    simp only [valueOf]
    rw [valueOf_split α c k, pow_add]
    ring

theorem admissible_byte {α : ℕ → ℕ} {n : ℕ} (adm : Admissible α n) : ∀ c < n, α c < 512 :=
  fun c hc => lt_of_lt_of_le (adm c hc) (chunkBound_le c)

theorem table_chunkBits : table.chunkBits = 9 := rfl

theorem table_inputBits' : table.inputBits = 254 := rfl

theorem table_chunkCount : table.chunkCount = 29 := by rfl

/-- The chunk values of `valueOf α 29` are the `α c`. -/
theorem chunkValue_valueOf (α : ℕ → ℕ) (adm : Admissible α 29) (c : ℕ) (hc : c < 29) :
    table.chunkValue (valueOf α 29) c = α c := by
  unfold CrtTable.chunkValue CrtTable.chunkOffset CrtTable.chunkWidth
  rw [table_chunkBits, table_inputBits', Nat.shiftRight_eq_div_pow, pow_mul]
  have split := valueOf_split α c (29 - c)
  rw [show c + (29 - c) = 29 by omega] at split
  have split' := valueOf_split (fun d => α (c + d)) 1 (28 - c)
  rw [show 1 + (28 - c) = 29 - c by omega] at split'
  have low : valueOf α c < 512 ^ c := valueOf_lt α c fun d hd => admissible_byte adm d (by omega)
  have one : valueOf (fun d => α (c + d)) 1 = α c := by simp [valueOf]
  rw [split, split', one, show (2 : ℕ) ^ 9 = 512 by norm_num,
    Nat.add_mul_div_left _ _ (pow_pos (by norm_num : (0 : ℕ) < 512) c), Nat.div_eq_of_lt low, Nat.zero_add]
  rcases Nat.lt_or_ge c 28 with lt | ge
  · rw [show min 9 (254 - 9 * c) = 9 by omega, show (2 : ℕ) ^ 9 = 512 by norm_num, pow_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (admissible_byte adm c hc)]
  · have c31 : c = 28 := by omega
    subst c31
    have top : α 28 < 3 := by
      have := adm 28 (by norm_num)
      unfold chunkBound at this
      simpa using this
    simp only [valueOf, show 28 - 28 = 0 by rfl, Nat.mul_zero, Nat.add_zero]
    rw [show min 9 (254 - 9 * 28) = 2 by norm_num]
    exact Nat.mod_eq_of_lt (by norm_num; omega)

/-- `valueOf α 29 < 3 · 512^28 ≤ p`. -/
theorem valueOf_lt_p (α : ℕ → ℕ) (adm : Admissible α 29) : valueOf α 29 < baseFieldModulus := by
  have low : valueOf α 28 < 512 ^ 28 := valueOf_lt α 28 fun d hd => admissible_byte adm d (by omega)
  have top : α 28 < 3 := by
    have := adm 28 (by norm_num)
    unfold chunkBound at this
    simpa using this
  have step : α 28 * 512 ^ 28 ≤ 2 * 512 ^ 28 := Nat.mul_le_mul_right _ (by omega)
  have whole : valueOf α 29 = valueOf α 28 + α 28 * 512 ^ 28 := rfl
  have := top_le
  omega

/-- The word value of `valueOf α 29` is `wordOf m α 29`. -/
theorem wordValue_valueOf (m : ℕ) (α : ℕ → ℕ) (adm : Admissible α 29) :
    table.wordValue m (valueOf α 29) = wordOf m α 29 := by
  unfold CrtTable.wordValue CrtTable.truth wordOf
  rw [Fin.sum_univ_eq_sum_range (fun c => table.chunkValue (valueOf α 29) c *
    2 ^ table.chunkOffset c % m) table.chunkCount, table_chunkCount]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [chunkValue_valueOf α adm c (Finset.mem_range.mp hc)]
  unfold CrtTable.chunkOffset
  rw [table_chunkBits]

theorem word_target (i : Fin table.count) (notPow : table.modulus i ≠ 512) (t : Nat)
    (ht : t ≤ need (table.modulus i) (rowFor (table.modulus i)).ell) :
    ∃ v < baseFieldModulus, table.wordValue (table.modulus i) v = t := by
  have ok := rows_ok i notPow
  have pos := modulus_pos i
  unfold rowOK at ok
  split at ok
  · rename_i B ran
    have enough : need (table.modulus i) (t9Row 29 (table.modulus i)).ell ≤ B := of_decide_eq_true ok
    have ellEq : (rowFor (table.modulus i)).ell = (t9Row 29 (table.modulus i)).ell := rfl
    rw [← ellEq] at enough
    have reach := reach_run (table.modulus i) _ 1 _ B (reach_one _ pos) ran
    rw [unpack_length] at reach
    obtain ⟨α, adm, sum⟩ := reach t (le_trans ht enough)
    exact ⟨valueOf α 29, valueOf_lt_p α adm, by rw [wordValue_valueOf _ α adm]; exact sum⟩
  · simp at ok

#print axioms correctTable
#print axioms rows_ok
#print axioms records_fit
#print axioms word_target
#eval table.chunkCount
#eval table.product
#eval Entry.garbleBudgetOf table
#eval Entry.evaluateBudgetOf table
#guard table.convBlocks == 2864
#guard Entry.garbleBudgetOf table == 1062388
#guard Entry.evaluateBudgetOf table == 1055556
#guard Entry.evaluateBudgetOf table ≤ 1055879
#guard Entry.garbleBudgetOf table ≤ 1759967
example : table.product = 2 * Entry.table.product := by decide +kernel
example : (1284 * (baseFieldModulus - 1) ^ 2 + 273 * baseFieldModulus) * 2 ^ 100 * 10 ≤
    7 * table.product := by decide +kernel
end Kriterion.CRT.Chunk9Research
