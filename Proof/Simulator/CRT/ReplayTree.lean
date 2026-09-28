/-
**The replay of one tree level agrees with the evaluator's step** (`agree_treeStep`).

The machine block `treeStep cells tagOf n` (`Construction/Simulator/CRT/ReplayTree.lean`), read as a
query tree at any index types (the CRT's are empty), asks exactly the questions of the lifted
evaluator step `liftHash (evalStepM n tagOf (activeAt α n) L J parent)` of
`Construction/CRT/Tree.lean`, in the same order, and ends with the new level's labels in the level
region, under the frame `Frame (treeStepWrites cells n) treeStepClobbers` of the schema.

The proof follows `agree_wideStep`, generalized to
any index types and to the CRT's hash: the pure pieces are proved on `Prog.exec`
(`Proof/Simulator/CRT/Exec.lean`) and read into the tree by `tree_seq_exec` and `tree_eq_exec`; the
one query per paid slot is `tree_query_hash`.
-/

import Proof.Simulator.CRT.Barrett
import Proof.Simulator.ReplayBase
import Construction.Simulator.CRT.ReplayTree
import Construction.CRT.Tree

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC

/-! ### `liftHash` distributes over the program combinators -/

section Lift

variable {FixedIndex EncIndex : Type}

theorem liftHash_pure {α : Type} (value : α) :
    liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (FreeQuery.pure value : CM α) =
      .pure value := rfl

theorem liftHash_bind {α β : Type} :
    ∀ (program : CM α) (next : α → CM β),
      liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (FreeQuery.bind program next) =
        FreeQuery.bind (liftHash program) fun value => liftHash (next value)
  | .pure _, _ => rfl
  | .query input rest, next => by
      show FreeQuery.query _ _ = FreeQuery.query _ _
      congr 1
      funext answer
      exact liftHash_bind (rest answer) next

theorem liftHash_vector {α : Type} :
    ∀ (count : Nat) (program : Fin count → CM α),
      liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (FreeQuery.vector count program) =
        FreeQuery.vector count fun index => liftHash (program index)
  | 0, _ => rfl
  | count + 1, program => by
      simp only [FreeQuery.vector, TreeLaws.monad_bind, TreeLaws.monad_pure, liftHash_bind,
        liftHash_vector count]
      rfl

theorem liftHash_ite {α : Type} (condition : Prop) [Decidable condition] (first second : CM α) :
    liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (if condition then first else second) =
      if condition then liftHash first else liftHash second := by
  split <;> rfl

theorem liftHash_h128M (label : Block) (tag : Nat) :
    liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (h128M label tag) =
      .query (.hash ((hashInput label tag : Nat) : BN254.BaseField)) fun answer => .pure answer.1 :=
  rfl

end Lift

theorem liftHash_hLabelM {FixedIndex EncIndex : Type} (label : Label) (tag : Nat) :
    liftHash (FixedIndex := FixedIndex) (EncIndex := EncIndex) (hLabelM label tag) =
      .query (.hash ((hashInput (embed label) tag : Nat) : BN254.BaseField))
        fun answer => .pure (clip answer.1) := rfl

/-! ### Generic tree steps -/

section Trees

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

theorem tree_seq (first second : Prog) (memory : Memory) :
    (Prog.seq first second).tree (FixedIndex := FixedIndex) (EncIndex := EncIndex) memory =
      bindOpt (first.tree memory) second.tree := rfl

theorem tree_ite (source : Register) (whenSet whenClear : Prog) (memory : Memory) :
    (Prog.ite source whenSet whenClear).tree (FixedIndex := FixedIndex) (EncIndex := EncIndex) memory =
      if memory.registers source = 0 then whenClear.tree memory else whenSet.tree memory := rfl

/-- **One hash query**: a kind-4 query on `rInput = word input` asks `.hash input`. -/
theorem tree_query_hash (rest : Prog) (memory : Memory) (input : Nat) (small : input < 2 ^ 256)
    (inputReg : memory.registers rInput = word input) :
    (Prog.seq (.op (.query 4 rIndex rInput rFirst rSecond)) rest).tree
        (FixedIndex := FixedIndex) (EncIndex := EncIndex) memory =
      .query (.hash ((input : Nat) : BN254.BaseField)) fun answer =>
        rest.tree (writePair memory rFirst rSecond (blockWord answer.1, blockWord answer.2)) := by
  have decode : queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) 4
      (memory.registers rIndex) (memory.registers rInput) =
        some (.hash (((memory.registers rInput).toNat : Nat) : BN254.BaseField)) := by
    unfold queryFromRegisters; rfl
  show bindOpt (Op.tree (.query 4 rIndex rInput rFirst rSecond) memory) rest.tree = _
  simp only [Op.tree]
  rw [decode, inputReg, word_toNat small]
  rfl

/-- **A machine `rep` against a plain abstract vector** (`agree_rep_vector_plain` at any
index types). -/
theorem agree_rep_vector_plain {α : Type} (body : Nat → Prog)
    (Inv : (count : Nat) → Vector α count → Memory → Prop) :
    ∀ (count : Nat) (program : Fin count → FreeQuery (publicOracleSpec FixedIndex EncIndex) α),
      (∀ (index : Fin count) (values : Vector α index.val) (memory : Memory),
        Inv index.val values memory →
          Agree (fun (result : α) after => Inv (index.val + 1) (values.push result) after)
            ((body index.val).tree memory) (program index)) →
      ∀ (memory : Memory), Inv 0 #v[] memory →
        Agree (Inv count) ((Prog.rep count body).tree memory) (FreeQuery.vector count program)
  | 0, _, _, memory, start => by
      rw [Prog.rep]
      exact .leaf start
  | count + 1, program, step, memory, start => by
      rw [Prog.rep, tree_seq]
      simp only [FreeQuery.vector, TreeLaws.monad_bind, TreeLaws.monad_pure]
      refine Agree.bindOpt (fun collected middle holds => ?_)
        (agree_rep_vector_plain body Inv count (fun index => program index.castSucc)
          (fun index values memory holds => step index.castSucc values memory holds) memory start)
      exact agree_map (fun result => collected.push result) (fun _ _ holds => holds)
        (step (Fin.last count) collected middle holds)
where
  agree_map {β γ : Type} {Post : β → Memory → Prop} {Post' : γ → Memory → Prop}
      (f : β → γ) (related : ∀ value memory, Post value memory → Post' (f value) memory) :
      ∀ {tree : FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)}
        {tree' : FreeQuery (publicOracleSpec FixedIndex EncIndex) β},
        Agree Post tree tree' → Agree Post' tree (FreeQuery.bind tree' fun value => .pure (f value))
    | _, _, .leaf holds => .leaf (related _ _ holds)
    | _, _, .node request each => .node request fun answer => agree_map f related (each answer)

end Trees

/-! ### Words and blocks -/

theorem blockWord_eq_word (block : Block) : blockWord block = word block.toNat := rfl

/-- A conversion label zero-extended to a machine word. -/
def labelWord (label : Label) : Word := BitVec.ofNat 256 label.toNat

theorem labelWord_eq_word (label : Label) : labelWord label = word label.toNat := rfl

theorem labelWord_toNat (label : Label) : (labelWord label).toNat = label.toNat := by
  unfold labelWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans label.isLt (by decide))]

theorem labelWord_xor (first second : Label) :
    labelWord first ^^^ labelWord second = labelWord (first ^^^ second) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, labelWord_toNat, labelWord_toNat, labelWord_toNat, BitVec.toNat_xor]

theorem labelWord_zero : labelWord 0 = 0 := rfl

theorem labelWord_embed (label : Label) : blockWord (embed label) = labelWord label := by
  unfold blockWord labelWord
  rw [show (embed label).toNat = label.toNat from Narrow.embed_toNat label]

theorem blockWord_embed (label : Label) : blockWord (embed label) = labelWord label :=
  labelWord_embed label

theorem eval_xor (first second : Word) : Arithmetic.xor.eval first second = first ^^^ second := rfl

theorem eval_and_pow (value n : Nat) (small : value < 2 ^ 256) (nSmall : n < 256) :
    Arithmetic.and.eval (word value) (word (2 ^ n - 1)) = word (value % 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  show (word value &&& word (2 ^ n - 1)).toNat = _
  have maskSmall : 2 ^ n - 1 < 2 ^ 256 := by
    have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) nSmall
    omega
  rw [BitVec.toNat_and, word_toNat small, word_toNat maskSmall,
    word_toNat (lt_of_le_of_lt (Nat.mod_le _ _) small)]
  exact Nat.and_two_pow_sub_one_eq_mod value n

theorem blockWord_clip (block : Block) :
    Arithmetic.and.eval (blockWord block) (word (2 ^ labelBits - 1)) = labelWord (clip block) := by
  rw [blockWord_eq_word, eval_and_pow _ _ (lt_trans block.isLt (by decide)) (by decide)]
  change word (block.toNat % 2 ^ labelBits) = word (clip block).toNat
  rw [show (clip block).toNat = block.toNat % 2 ^ labelBits from Narrow.clip_toNat block]

theorem exec_clipReg (register : Register) (notB : register ≠ rB) (memory : Memory)
    (block : Block) (holds : memory.registers register = blockWord block) :
    ∃ after, (clipReg register).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers register = labelWord (clip block) ∧
      ∀ other, other ≠ register → other ≠ rB → after.registers other = memory.registers other := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun other notReg notB => ?_⟩
  · simp only [reg_setReg, if_pos rfl, if_neg notB, holds]
    exact blockWord_clip block
  · simp only [reg_setReg, if_neg notReg, if_neg notB]

theorem det_clipReg (register : Register) : (clipReg register).OpsSatisfy Op.Det :=
  ⟨trivial, trivial⟩

theorem word_xor_eq_zero {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) : word first ^^^ word second = 0 ↔ first = second := by
  constructor
  · intro zero
    have same : word first = word second := by
      have := congrArg (· ^^^ word second) zero
      simpa [BitVec.xor_assoc] using this
    exact word_inj firstSmall secondSmall same
  · intro same
    rw [same, BitVec.xor_self]
    rfl

/-- The XOR of the collected materials, the active entry skipped (`xorSkip`). -/
def xorSkip {count : Nat} (skip : Nat) (values : Vector Label count) : Label :=
  Fin.foldl count (fun acc (i : Fin count) => if i.val = skip then acc else acc ^^^ values[i]) 0

theorem xorSkip_push {count : Nat} (skip : Nat) (values : Vector Label count) (value : Label) :
    xorSkip skip (values.push value) =
      if count = skip then xorSkip skip values else xorSkip skip values ^^^ value := by
  unfold xorSkip
  rw [Fin.foldl_succ_last]
  simp only [Fin.val_last, Fin.val_castSucc, Fin.getElem_fin, Vector.getElem_push_eq]
  have prefixEq : Fin.foldl count (fun acc (i : Fin count) =>
        if i.val = skip then acc else acc ^^^ (values.push value)[i.val]) 0 =
      Fin.foldl count (fun acc (i : Fin count) =>
        if i.val = skip then acc else acc ^^^ values[i.val]) 0 := by
    congr 1
    funext acc i
    rw [Vector.getElem_push_lt i.isLt]
  rw [prefixEq]

theorem xorSkip_eq {count : Nat} (skip : Fin count) (values : Vector Label count) :
    xorSkip skip.val values = xorFoldExcept skip values.get := by
  unfold xorSkip xorFoldExcept
  congr 1
  funext acc i
  simp only [Fin.ext_iff, Fin.getElem_fin, Vector.get_eq_getElem]

/-! ### The layout of one level -/

/-- An address outside both regions of level `n`. -/
def TreeOutside (cells : TreeCells) (n address : Nat) : Prop :=
  address < 2 ^ 256 ∧ (∀ j, j < 2 ^ (n + 1) → address ≠ cells.levelBase + j) ∧
    ∀ r, r < 2 ^ n → address ≠ cells.matBase + r

/-- The layout facts one level needs: the level region below the material region, both in range,
and the value, join and bit cells outside both. -/
structure TreeLayout (cells : TreeCells) (n : Nat) : Prop where
  levelBelow : cells.levelBase + 2 ^ (n + 1) ≤ cells.matBase
  matFits : cells.matBase + 2 ^ n < 2 ^ 256
  alphaOut : TreeOutside cells n cells.alpha
  joinOut : TreeOutside cells n (cells.join n)
  bitOut : TreeOutside cells n (cells.bit n)

/-! ### The pure pieces -/

theorem exec_entryTest (cells : TreeCells) (n s : Nat) (memory : Memory) (alpha : Nat)
    (alphaCell : memory.ram (word cells.alpha) = word alpha) (alphaSmall : alpha < 2 ^ 256)
    (nSmall : n < 256) :
    ∃ after, (entryTest cells n s).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rA = word (alpha % 2 ^ n) ^^^ word s ∧
      ∀ register, register ≠ rA → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notA notB notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, alphaCell]
    rw [eval_and_pow _ _ alphaSmall nSmall]
    rfl
  · simp only [reg_setReg, if_neg notA, if_neg notB, if_neg notAddr]

theorem det_entryTest (cells : TreeCells) (n s : Nat) : (entryTest cells n s).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial⟩

theorem exec_entryInput (cells : TreeCells) (tag s : Nat) (memory : Memory) (label : Label)
    (labelCell : memory.ram (word (cells.levelBase + s)) = labelWord label) (tagSmall : tag < 2 ^ 127) :
    ∃ after, (entryInput cells tag s).exec memory = some after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ after.registers rInput = word (hashInput (embed label) tag) ∧
      ∀ register, register ≠ rInput → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  have sum : label.toNat + 2 ^ 128 * tag < 2 ^ 256 := by
    have : label.toNat < 2 ^ 101 := label.isLt
    omega
  refine ⟨_, rfl, rfl, rfl, ?_, fun register notI notB notAddr => ?_⟩
  · simp (config := { decide := true }) only [reg_setReg, ram_setReg, reduceIte, labelCell]
    rw [labelWord_eq_word, eval_add_word _ _ sum]
    simp only [hashInput, show (embed label).toNat = label.toNat from Narrow.embed_toNat label]
  · simp only [reg_setReg, if_neg notI, if_neg notB, if_neg notAddr]

theorem det_entryInput (cells : TreeCells) (tag s : Nat) : (entryInput cells tag s).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, trivial⟩

theorem exec_entryStore (cells : TreeCells) (s : Nat) (memory : Memory) :
    ∃ after, (entryStore cells s).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.matBase + s)) (memory.registers rFirst) ∧
      after.bits = memory.bits ∧
      after.registers rD = memory.registers rD ^^^ memory.registers rFirst ∧
      ∀ register, register ≠ rD → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, ?_, fun register notD notAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte]
  · simp (config := { decide := true }) only [reg_setReg, reg_storeRam, reduceIte]
    rfl
  · simp only [reg_setReg, reg_storeRam, if_neg notD, if_neg notAddr]

theorem det_entryStore (cells : TreeCells) (s : Nat) : (entryStore cells s).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial⟩

set_option maxHeartbeats 800000 in
theorem exec_treeRecover (cells : TreeCells) (n : Nat) (memory : Memory) (alpha : Nat) (X J : Label) (L : Block)
    (nSmall : n < 256) (alphaSmall : alpha < 2 ^ 256) (matSmall : cells.matBase + 2 ^ n < 2 ^ 256)
    (xorReg : memory.registers rD = labelWord X)
    (joinCell : memory.ram (word (cells.join n)) = labelWord J)
    (bitCell : memory.ram (word (cells.bit n)) = blockWord L)
    (alphaCell : memory.ram (word cells.alpha) = word alpha) :
    ∃ after, (treeRecover cells n).exec memory = some after ∧
      after.ram = Function.update memory.ram (word (cells.matBase + alpha % 2 ^ n))
        (labelWord (X ^^^ J ^^^ clip L)) ∧ after.bits = memory.bits ∧
      ∀ register, ¬ treeStepClobbers register →
        after.registers register = memory.registers register := by
  have modSmall : alpha % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨_, rfl, ?_, rfl, fun register outside => ?_⟩
  · simp (config := { decide := true }) only [ram_setReg, ram_storeRam, reg_setReg, reduceIte,
      joinCell, bitCell, alphaCell, blockWord_clip]
    rw [eval_and_pow _ _ alphaSmall nSmall, eval_add_word _ _ (by omega), Nat.add_comm, eval_xor,
      eval_xor, xorReg, labelWord_xor, labelWord_xor]
  · have notIn : ∀ other : Register, other ∈ [rA, rB, rC, rD, rE, rAddr, rInput, rFirst, rSecond] →
        register ≠ other := fun other inside same => outside (by rw [same]; exact inside)
    simp only [reg_setReg, reg_storeRam, if_neg (notIn rA (by simp)), if_neg (notIn rB (by simp)),
      if_neg (notIn rD (by simp)), if_neg (notIn rE (by simp)), if_neg (notIn rAddr (by simp))]

theorem det_treeRecover (cells : TreeCells) (n : Nat) : (treeRecover cells n).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, trivial,
    trivial, trivial, trivial⟩

/-- **The extension in place**: after `count` entries, entry `r < count` holds `E_r ⊕ y_r` and
entry `r + 2 ^ n` holds `y_r`. -/
theorem exec_treeLevel (cells : TreeCells) (n : Nat) (memory : Memory)
    (below : cells.levelBase + 2 ^ (n + 1) ≤ cells.matBase) (fits : cells.matBase + 2 ^ n < 2 ^ 256) :
    ∀ count, count ≤ 2 ^ n → ∃ after,
      (Prog.rep count (treeLevelBody cells n)).exec memory = some after ∧
      (∀ r, r < count →
        after.ram (word (cells.levelBase + r)) =
            memory.ram (word (cells.levelBase + r)) ^^^ memory.ram (word (cells.matBase + r)) ∧
          after.ram (word (cells.levelBase + r + 2 ^ n)) = memory.ram (word (cells.matBase + r))) ∧
      (∀ address, (∀ r, r < count → address ≠ word (cells.levelBase + r) ∧
          address ≠ word (cells.levelBase + r + 2 ^ n)) → after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rE → register ≠ rC → register ≠ rAddr →
        after.registers register = memory.registers register
  | 0, _ => ⟨memory, Prog.exec_rep_zero _ _, fun r bound => absurd bound (by omega), fun _ _ => rfl,
      rfl, fun _ _ _ _ => rfl⟩
  | count + 1, bound => by
      obtain ⟨middle, run, cells', frame, bitsSame, regs⟩ :=
        exec_treeLevel cells n memory below fits count (by omega)
      have twice : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
      have wne : ∀ x y : Nat, x < 2 ^ 256 → y < 2 ^ 256 → x ≠ y → word x ≠ word y :=
        fun x y hx hy hne => word_ne hx hy hne
      have labelNow : middle.ram (word (cells.levelBase + count)) =
          memory.ram (word (cells.levelBase + count)) :=
        frame _ fun r small => ⟨wne _ _ (by omega) (by omega) (by omega),
          wne _ _ (by omega) (by omega) (by omega)⟩
      have matNow : middle.ram (word (cells.matBase + count)) =
          memory.ram (word (cells.matBase + count)) :=
        frame _ fun r small => ⟨wne _ _ (by omega) (by omega) (by omega),
          wne _ _ (by omega) (by omega) (by omega)⟩
      refine ⟨_, by rw [Prog.exec_rep_succ, run, Option.bind_some]; rfl, fun r small => ?_,
        fun address off => ?_, ?_, fun register notE notC notAddr => ?_⟩
      · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg,
          reg_storeRam, reduceIte]
        rw [eval_xor]
        by_cases last : r = count
        · subst last
          refine ⟨?_, ?_⟩
          · rw [Function.update_self, labelNow, matNow]
          · rw [Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)),
              Function.update_self, matNow]
        · have rSmall : r < count := by omega
          obtain ⟨cell1, cell2⟩ := cells' r rSmall
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)),
              Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)), cell1]
          · rw [Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)),
              Function.update_of_ne (wne _ _ (by omega) (by omega) (by omega)), cell2]
      · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg,
          reg_storeRam, reduceIte]
        rw [Function.update_of_ne (off count (by omega)).1, Function.update_of_ne (off count (by omega)).2,
          frame address fun r small => off r (by omega)]
      · exact bitsSame
      · simp only [reg_setReg, reg_storeRam, if_neg notE, if_neg notC, if_neg notAddr]
        exact regs register notE notC notAddr

theorem det_treeLevel (cells : TreeCells) (n : Nat) : (treeLevel cells n).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ =>
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩

/-! ### The agreement -/

theorem writePair_ram (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).ram = memory.ram := rfl

theorem writePair_bits (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).bits = memory.bits := rfl

theorem writePair_reg (memory : Memory) (first second : Register) (values : Word × Word)
    (index : Register) :
    (writePair memory first second values).registers index =
      if index = second then values.2 else if index = first then values.1 else
        memory.registers index := by
  simp only [writePair, Function.update_apply]

/-- A register outside `treeStepClobbers` is none of the clobbered ones. -/
theorem ne_of_not_clobbered {register : Register} (outside : ¬ treeStepClobbers register)
    (other : Register) (inside : other ∈ [rA, rB, rC, rD, rE, rAddr, rInput, rFirst, rSecond]) :
    register ≠ other := fun same => outside (by rw [same]; exact inside)

theorem level_ne_mat (cells : TreeCells) (n : Nat) (layout : TreeLayout cells n) (j r : Nat)
    (jBound : j < 2 ^ (n + 1)) (rBound : r < 2 ^ n) :
    word (cells.levelBase + j) ≠ word (cells.matBase + r) := by
  have below := layout.levelBelow
  have fits := layout.matFits
  exact word_ne (by omega) (by omega) (by omega)

theorem outside_ne_mat (cells : TreeCells) (n address : Nat) (layout : TreeLayout cells n)
    (outside : TreeOutside cells n address) (r : Nat) (rBound : r < 2 ^ n) :
    word address ≠ word (cells.matBase + r) := by
  have fits := layout.matFits
  exact word_ne outside.1 (by omega) (outside.2.2 r rBound)

theorem outside_ne_level (cells : TreeCells) (n address : Nat) (layout : TreeLayout cells n)
    (outside : TreeOutside cells n address) (j : Nat) (jBound : j < 2 ^ (n + 1)) :
    word address ≠ word (cells.levelBase + j) := by
  have below := layout.levelBelow
  have fits := layout.matFits
  exact word_ne outside.1 (by omega) (outside.2.1 j jBound)

section Agreement

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The invariant of the entry loop of level `n` after `count` slots: the materials asked so far
in the material region, their XOR (the active slot skipped) in `rD`, and the frame. -/
def EntryInv (cells : TreeCells) (n active : Nat) (start : Memory) (count : Nat)
    (values : Vector Label count) (memory : Memory) : Prop :=
  (∀ r (bound : r < count), r ≠ active →
      memory.ram (word (cells.matBase + r)) = labelWord (values[r]'bound)) ∧
    memory.registers rD = labelWord (xorSkip active values) ∧
    (∀ address, (∀ r, r < 2 ^ n → address ≠ word (cells.matBase + r)) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧
    ∀ register, ¬ treeStepClobbers register → memory.registers register = start.registers register

/-- **One slot of a level**: the active slot is skipped, every other slot asks its hash. -/
theorem agree_treeEntry (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) (nSmall : n < 20)
    (alpha : Nat) (alphaSmall : alpha < 2 ^ 256) (parent : Fin (2 ^ n) → Label) (start : Memory)
    (layout : TreeLayout cells n)
    (alphaCell : start.ram (word cells.alpha) = word alpha)
    (levelCells : ∀ j : Fin (2 ^ n),
      start.ram (word (cells.levelBase + j.val)) = labelWord (parent j))
    (tagSmall : ∀ s, s < 2 ^ n → tagOf s < 2 ^ 127)
    (index : Fin (2 ^ n)) (values : Vector Label index.val) (memory : Memory)
    (holds : EntryInv cells n (alpha % 2 ^ n) start index.val values memory) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (result : Label) after =>
        EntryInv cells n (alpha % 2 ^ n) start (index.val + 1) (values.push result) after)
      ((treeEntry cells tagOf n index.val).tree memory)
      (liftHash (if index = activeAt alpha n then pure 0
        else hLabelM (parent index) (tagOf index.val))) := by
  obtain ⟨mats, xorReg, frame, bitsSame, regs⟩ := holds
  have powLe : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have alphaNow : memory.ram (word cells.alpha) = word alpha := by
    rw [frame _ fun r bound => outside_ne_mat cells n _ layout layout.alphaOut r bound, alphaCell]
  have levelNow : memory.ram (word (cells.levelBase + index.val)) = labelWord (parent index) := by
    rw [frame _ fun r bound => level_ne_mat cells n layout _ r (by omega) bound, levelCells index]
  have activeSmall : alpha % 2 ^ n < 2 ^ 256 := lt_of_le_of_lt (Nat.mod_le _ _) alphaSmall
  have indexSmall : index.val < 2 ^ 256 := by
    have := index.isLt
    have := layout.matFits
    omega
  obtain ⟨m1, run1, ram1, bits1, rA1, regs1⟩ :=
    exec_entryTest cells n index.val memory alpha alphaNow alphaSmall (by omega)
  unfold treeEntry
  rw [tree_seq_exec _ _ (det_entryTest cells n index.val) memory m1 run1, tree_ite, rA1,
    liftHash_ite]
  by_cases same : index = activeAt alpha n
  · have sameVal : index.val = alpha % 2 ^ n := by rw [same]; rfl
    rw [if_pos ((word_xor_eq_zero activeSmall indexSmall).mpr sameVal.symm), if_pos same]
    refine .leaf ⟨fun r bound notSkip => ?_, ?_, fun address off => ?_, ?_,
      fun register outside => ?_⟩
    · have rSmall : r < index.val := by omega
      rw [ram1, Vector.getElem_push_lt rSmall]
      exact mats r rSmall notSkip
    · rw [regs1 rD (by decide) (by decide) (by decide), xorReg, xorSkip_push, if_pos sameVal]
    · rw [ram1]
      exact frame address off
    · rw [bits1]
      exact bitsSame
    · rw [regs1 register (ne_of_not_clobbered outside rA (by simp))
        (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp))]
      exact regs register outside
  · have different : index.val ≠ alpha % 2 ^ n := fun equal => same (Fin.ext equal)
    rw [if_neg (fun zero => different ((word_xor_eq_zero activeSmall indexSmall).mp zero).symm),
      if_neg same]
    obtain ⟨m2, run2, ram2, bits2, input2, regs2⟩ :=
      exec_entryInput cells (tagOf index.val) index.val m1 (parent index)
        (by rw [ram1]; exact levelNow) (tagSmall _ index.isLt)
    have hashSmall : hashInput (embed (parent index)) (tagOf index.val) < 2 ^ 256 := by
      unfold hashInput
      simp only [show ∀ l : Label, (embed l).toNat = l.toNat from Narrow.embed_toNat]
      have : (parent index).toNat < 2 ^ 101 := (parent index).isLt
      have := tagSmall _ index.isLt
      omega
    unfold entryHash
    rw [tree_seq_exec _ _ (det_entryInput cells (tagOf index.val) index.val) m1 m2 run2,
      tree_query_hash _ m2 _ hashSmall input2, liftHash_hLabelM]
    refine .node _ fun answer => ?_
    have rawFirst : (writePair m2 rFirst rSecond (blockWord answer.1, blockWord answer.2)).registers
        rFirst = blockWord answer.1 := by
      rw [writePair_reg, if_neg (by decide), if_pos rfl]
    obtain ⟨mClip, runClip, ramClip, bitsClip, firstReg, regsClip⟩ :=
      exec_clipReg rFirst (by decide)
        (writePair m2 rFirst rSecond (blockWord answer.1, blockWord answer.2)) answer.1 rawFirst
    rw [tree_seq_exec _ _ (det_clipReg rFirst) _ mClip runClip,
      tree_eq_exec _ (det_entryStore cells index.val)]
    obtain ⟨m3, run3, ram3, bits3, rD3, regs3⟩ := exec_entryStore cells index.val mClip
    rw [run3]
    have matSmall : cells.matBase + index.val < 2 ^ 256 := by
      have := index.isLt
      have := layout.matFits
      omega
    refine .leaf ⟨fun r bound notSkip => ?_, ?_, fun address off => ?_, ?_,
      fun register outside => ?_⟩
    · rw [ram3, firstReg, ramClip, writePair_ram, ram2, ram1]
      by_cases last : r = index.val
      · subst last
        rw [Function.update_self, Vector.getElem_push_eq]
      · have rSmall : r < index.val := by omega
        rw [Function.update_of_ne (word_ne (by omega) matSmall (by omega)), Vector.getElem_push_lt rSmall]
        exact mats r rSmall notSkip
    · rw [rD3, firstReg, regsClip rD (by decide) (by decide), writePair_reg, if_neg (by decide), if_neg (by decide),
        regs2 rD (by decide) (by decide) (by decide), regs1 rD (by decide) (by decide) (by decide),
        xorReg, labelWord_xor, xorSkip_push, if_neg different]
    · rw [ram3, Function.update_of_ne (off index.val index.isLt), ramClip, writePair_ram, ram2, ram1]
      exact frame address off
    · rw [bits3, bitsClip, writePair_bits, bits2, bits1]
      exact bitsSame
    · rw [regs3 register (ne_of_not_clobbered outside rD (by simp))
          (ne_of_not_clobbered outside rAddr (by simp)),
        regsClip register (ne_of_not_clobbered outside rFirst (by simp))
          (ne_of_not_clobbered outside rB (by simp)), writePair_reg,
        if_neg (ne_of_not_clobbered outside rSecond (by simp)),
        if_neg (ne_of_not_clobbered outside rFirst (by simp)),
        regs2 register (ne_of_not_clobbered outside rInput (by simp))
          (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp)),
        regs1 register (ne_of_not_clobbered outside rA (by simp))
          (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp))]
      exact regs register outside

/-- The materials of a level after the recovery: the asked ones, and the recovered active one. -/
def treeRight (n alpha : Nat) (bitLabel join : Label) (materials : Vector Label (2 ^ n)) :
    Fin (2 ^ n) → Label := fun slot =>
  if slot = activeAt alpha n then join ^^^ bitLabel ^^^ xorFoldExcept (activeAt alpha n) materials.get
  else materials.get slot

/-- **One paid tree level** against the evaluator's `evalStepM`: the machine asks the same hash
questions in the same order, leaves the new level in the level region, and has the frame of the
schema. -/
theorem agree_treeStep (cells : TreeCells) (tagOf : Nat → Nat) (n : Nat) (nSmall : n < 20)
    (alpha : Nat) (alphaSmall : alpha < 2 ^ 256) (bitLabel : Block) (join : Label)
    (parent : Fin (2 ^ n) → Label) (memory : Memory) (layout : TreeLayout cells n)
    (alphaCell : memory.ram (word cells.alpha) = word alpha)
    (levelCells : ∀ j : Fin (2 ^ n),
      memory.ram (word (cells.levelBase + j.val)) = labelWord (parent j))
    (joinCell : memory.ram (word (cells.join n)) = labelWord join)
    (bitCell : memory.ram (word (cells.bit n)) = blockWord bitLabel)
    (tagSmall : ∀ s, s < 2 ^ n → tagOf s < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (fun (level : Fin (2 ^ (n + 1)) → Label) after =>
        (∀ j : Fin (2 ^ (n + 1)),
          after.ram (word (cells.levelBase + j.val)) = labelWord (level j)) ∧
          Frame (treeStepWrites cells n) treeStepClobbers memory after)
      ((treeStep cells tagOf n).tree memory)
      (liftHash (evalStepM n tagOf (activeAt alpha n) (clip bitLabel) join parent)) := by
  have below := layout.levelBelow
  have fits := layout.matFits
  have powLe : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have twice : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
  have activeLt : alpha % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos _)
  set m0 := setReg memory rD (word 0) with m0Def
  unfold treeStep evalStepM tableM
  rw [tree_seq_exec (cst rD 0) _ trivial memory m0 rfl, tree_seq, TreeLaws.monad_bind,
    TreeLaws.monad_bind, liftHash_bind, liftHash_bind, liftHash_vector, TreeLaws.bind_assoc]
  refine Agree.bindOpt (fun materials after inv => ?_)
    (agree_rep_vector_plain (treeEntry cells tagOf n) (EntryInv cells n (alpha % 2 ^ n) m0) (2 ^ n) _
      (fun index values current holds =>
        agree_treeEntry cells tagOf n nSmall alpha alphaSmall parent m0 layout alphaCell levelCells
          tagSmall index values current holds)
      m0 ⟨fun r bound => absurd bound (Nat.not_lt_zero _), by
        rw [m0Def, reg_setReg, if_pos rfl]
        unfold xorSkip
        rw [Fin.foldl_zero]
        rfl,
        fun _ _ => rfl, rfl, fun _ _ => rfl⟩)
  obtain ⟨mats, xorReg, frame, bitsSame, regs⟩ := inv
  have joinNow : after.ram (word (cells.join n)) = labelWord join := by
    rw [frame _ fun r bound => outside_ne_mat cells n _ layout layout.joinOut r bound]
    exact joinCell
  have bitNow : after.ram (word (cells.bit n)) = blockWord bitLabel := by
    rw [frame _ fun r bound => outside_ne_mat cells n _ layout layout.bitOut r bound]
    exact bitCell
  have alphaNow : after.ram (word cells.alpha) = word alpha := by
    rw [frame _ fun r bound => outside_ne_mat cells n _ layout layout.alphaOut r bound]
    exact alphaCell
  obtain ⟨m3, run3, ram3, bits3, regs3⟩ := exec_treeRecover cells n after alpha
    (xorSkip (alpha % 2 ^ n) materials) join bitLabel (by omega) alphaSmall fits xorReg joinNow
    bitNow alphaNow
  rw [tree_seq_exec _ _ (det_treeRecover cells n) after m3 run3,
    tree_eq_exec _ (det_treeLevel cells n)]
  obtain ⟨m4, run4, cells4, frame4, bits4, regs4⟩ :=
    exec_treeLevel cells n m3 below fits (2 ^ n) le_rfl
  unfold treeLevel
  rw [run4]
  have matCell : ∀ r (bound : r < 2 ^ n), m3.ram (word (cells.matBase + r)) =
      labelWord (treeRight n alpha (clip bitLabel) join materials ⟨r, bound⟩) := by
    intro r bound
    rw [ram3]
    unfold treeRight
    by_cases active : r = alpha % 2 ^ n
    · have sameFin : (⟨r, bound⟩ : Fin (2 ^ n)) = activeAt alpha n := Fin.ext active
      rw [if_pos sameFin, show word (cells.matBase + r) = word (cells.matBase + alpha % 2 ^ n) by
          rw [active], Function.update_self,
        show alpha % 2 ^ n = (activeAt alpha n).val from rfl, xorSkip_eq, BitVec.xor_assoc,
        BitVec.xor_comm (xorFoldExcept _ _)]
    · have differentFin : (⟨r, bound⟩ : Fin (2 ^ n)) ≠ activeAt alpha n :=
        fun sameFin => active (congrArg Fin.val sameFin)
      rw [if_neg differentFin, Function.update_of_ne (word_ne (by omega) (by omega) (by omega)),
        mats r bound active, Vector.get_eq_getElem]
  have labelCell3 : ∀ r (bound : r < 2 ^ n),
      m3.ram (word (cells.levelBase + r)) = labelWord (parent ⟨r, bound⟩) := by
    intro r bound
    rw [ram3, Function.update_of_ne (level_ne_mat cells n layout r _ (by omega) activeLt),
      frame _ fun r' small => level_ne_mat cells n layout r r' (by omega) small]
    exact levelCells ⟨r, bound⟩
  refine .leaf ⟨fun j => ?_, ⟨fun address outside => ?_, ?_, fun register outside => ?_⟩⟩
  · have jBound := j.isLt
    rw [stored_eq]
    unfold extendLevel
    split
    · rename_i lower
      rw [(cells4 j.val lower).1, labelCell3 j.val lower, matCell j.val lower, labelWord_xor]
      rfl
    · rename_i upper
      obtain ⟨_, cell2⟩ := cells4 (j.val - 2 ^ n) (by omega)
      rw [show cells.levelBase + j.val = cells.levelBase + (j.val - 2 ^ n) + 2 ^ n by omega, cell2,
        matCell _ (by omega)]
      rfl
  · have notLevel : ∀ k, k < 2 ^ (n + 1) → address ≠ word (cells.levelBase + k) :=
      fun k bound same => outside (Or.inl ⟨k, bound, same⟩)
    have notMat : ∀ r, r < 2 ^ n → address ≠ word (cells.matBase + r) :=
      fun r bound same => outside (Or.inr ⟨r, bound, same⟩)
    rw [frame4 address fun r small => ⟨notLevel r (by omega), by
        rw [Nat.add_assoc]; exact notLevel _ (by omega)⟩, ram3,
      Function.update_of_ne (notMat _ activeLt), frame address notMat]
    rfl
  · rw [bits4, bits3, bitsSame]
    rfl
  · rw [regs4 register (ne_of_not_clobbered outside rE (by simp))
        (ne_of_not_clobbered outside rC (by simp)) (ne_of_not_clobbered outside rAddr (by simp)),
      regs3 register outside, regs register outside, m0Def, reg_setReg,
      if_neg (ne_of_not_clobbered outside rD (by simp))]

/-! ### The whole tree -/

theorem tree_seq_assoc (first second third : Prog) (memory : Memory) :
    (Prog.seq (.seq first second) third).tree (FixedIndex := FixedIndex) (EncIndex := EncIndex) memory =
      (Prog.seq first (.seq second third)).tree memory := by
  simp only [tree_seq]
  exact bindOpt_assoc _ _ _

theorem exec_treePrefix (cells : TreeCells) (memory : Memory) (label : Block)
    (bitCell : memory.ram (word (cells.bit 0)) = blockWord label) :
    ∃ after, (treePrefix cells).exec memory = some after ∧
      after.ram = Function.update (Function.update memory.ram (word cells.levelBase) (labelWord (clip label)))
        (word (cells.levelBase + 1)) (labelWord (clip label)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ≠ rInput → register ≠ rB → register ≠ rAddr →
        after.registers register = memory.registers register := by
  refine ⟨_, rfl, ?_, rfl, fun register notI notB notAddr => ?_⟩
  · simp (config := { decide := true }) only [ram_storeRam, ram_setReg, reg_setReg, reg_storeRam,
      reduceIte, bitCell, blockWord_clip]
  · simp only [reg_storeRam, reg_setReg, if_neg notI, if_neg notB, if_neg notAddr]

theorem det_treePrefix (cells : TreeCells) : (treePrefix cells).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- What a whole tree leaves after `levels` levels: the level's labels, and the frame. -/
def TreeEvalPost (cells : TreeCells) (start : Memory) (levels : Nat)
    (level : Fin (2 ^ levels) → Label) (after : Memory) : Prop :=
  (∀ j : Fin (2 ^ levels), after.ram (word (cells.levelBase + j.val)) = labelWord (level j)) ∧
    Frame (treeEvalWrites cells levels) treeStepClobbers start after

theorem not_treeEvalWrites (cells : TreeCells) (n address : Nat) (layout : TreeLayout cells n)
    (outside : TreeOutside cells n address) : ¬ treeEvalWrites cells n (word address) := by
  have below := layout.levelBelow
  have fits := layout.matFits
  have powLe : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rintro (⟨k, kb, same⟩ | ⟨k, kb, same⟩)
  · have kb' : k < 2 ^ n := kb
    exact outside_ne_level cells n address layout outside k (by omega) same
  · have kb' : k < 2 ^ n := kb
    exact outside_ne_mat cells n address layout outside k kb' same

/-- **The whole tree** (the known-bit trees of growth):
after the prefix and `n` paid levels the machine agrees with `liftHash (treeEvalM … (n + 1))`, with
the frame of `treeEvalWrites cells (n + 1)`, composed from the levels' frames by `Frame.trans` and
`Frame.mono`. -/
theorem agree_treeEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (levels : Nat)
    (levelsSmall : levels ≤ 20) (value : Nat) (valueSmall : value < 2 ^ 256)
    (bitLabel : Nat → Block) (join : Nat → Label) (memory : Memory)
    (layouts : ∀ k, k < levels → TreeLayout cells k)
    (alphaCell : memory.ram (word cells.alpha) = word value)
    (joinCells : ∀ k, 1 ≤ k → k < levels → memory.ram (word (cells.join k)) = labelWord (join k))
    (bitCells : ∀ k, k < levels → memory.ram (word (cells.bit k)) = blockWord (bitLabel k))
    (tagSmall : ∀ k s, k < levels → s < 2 ^ k → tagOf k s < 2 ^ 127) :
    ∀ n, n + 1 ≤ levels →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex) (TreeEvalPost cells memory (n + 1))
        ((Prog.seq (treePrefix cells)
          (Prog.rep n fun k => treeStep cells (tagOf (k + 1)) (k + 1))).tree memory)
        (liftHash (treeEvalM tagOf value (fun k => clip (bitLabel k)) join (n + 1)))
  | 0, bound => by
      have layout := layouts 0 (by omega)
      have below := layout.levelBelow
      have fits := layout.matFits
      obtain ⟨after, run, ram, bits, regs⟩ :=
        exec_treePrefix cells memory (bitLabel 0) (bitCells 0 (by omega))
      rw [Prog.rep, tree_seq_exec _ _ (det_treePrefix cells) memory after run]
      simp only [treeEvalM, TreeLaws.monad_bind, TreeLaws.monad_pure, if_pos rfl]
      refine .leaf ⟨fun j => ?_, ⟨fun address outside => ?_, bits, fun register outside => ?_⟩⟩
      · have jb := j.isLt
        rw [stored_eq]
        unfold extendLevel
        simp only [pow_zero] at jb ⊢
        rw [ram]
        split
        · rename_i lower
          have jZero : j.val = 0 := by omega
          rw [jZero]
          simp only [Nat.add_zero]
          rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega)), Function.update_self]
          show _ = labelWord (0 ^^^ clip (bitLabel 0))
          congr 1
          exact (BitVec.zero_xor (x := clip (bitLabel 0))).symm
        · rename_i upper
          have jOne : j.val = 1 := by omega
          rw [jOne, Function.update_self]
      · have notLevel : ∀ k, k < 2 → address ≠ word (cells.levelBase + k) :=
          fun k kb same => outside (Or.inl ⟨k, by simpa using kb, same⟩)
        rw [ram, Function.update_of_ne (notLevel 1 (by norm_num)),
          Function.update_of_ne (by simpa using notLevel 0 (by norm_num))]
      · exact regs register (ne_of_not_clobbered outside rInput (by simp))
          (ne_of_not_clobbered outside rB (by simp)) (ne_of_not_clobbered outside rAddr (by simp))
  | n + 1, bound => by
      have layout := layouts (n + 1) (by omega)
      rw [Prog.rep, ← tree_seq_assoc, tree_seq]
      rw [show treeEvalM tagOf value (fun k => clip (bitLabel k)) join (n + 1 + 1) =
          (treeEvalM tagOf value (fun k => clip (bitLabel k)) join (n + 1) >>= fun previous =>
            if n + 1 = 0 then pure (stored (extendLevel (n + 1) previous fun _ => clip (bitLabel 0)))
            else evalStepM (n + 1) (tagOf (n + 1)) (activeAt value (n + 1)) (clip (bitLabel (n + 1)))
              (join (n + 1)) previous) from rfl,
        TreeLaws.monad_bind, liftHash_bind]
      refine Agree.bindOpt (fun previous after post => ?_)
        (agree_treeEval cells tagOf levels levelsSmall value valueSmall bitLabel join memory layouts
          alphaCell joinCells bitCells tagSmall n (by omega))
      rw [liftHash_ite, if_neg (Nat.succ_ne_zero n)]
      obtain ⟨levelCells, frame⟩ := post
      have alphaNow : after.ram (word cells.alpha) = word value := by
        rw [frame.ram _ (not_treeEvalWrites cells (n + 1) _ layout layout.alphaOut)]
        exact alphaCell
      have joinNow : after.ram (word (cells.join (n + 1))) = labelWord (join (n + 1)) := by
        rw [frame.ram _ (not_treeEvalWrites cells (n + 1) _ layout layout.joinOut)]
        exact joinCells (n + 1) (by omega) (by omega)
      have bitNow : after.ram (word (cells.bit (n + 1))) = blockWord (bitLabel (n + 1)) := by
        rw [frame.ram _ (not_treeEvalWrites cells (n + 1) _ layout layout.bitOut)]
        exact bitCells (n + 1) (by omega)
      refine (agree_treeStep cells (tagOf (n + 1)) (n + 1) (by omega) value valueSmall (bitLabel (n + 1))
        (join (n + 1)) previous after layout alphaNow levelCells joinNow bitNow
        (fun s sb => tagSmall (n + 1) s (by omega) sb)).mono fun level final post => ?_
      obtain ⟨cells', frame'⟩ := post
      refine ⟨cells', (frame.trans frame').mono ?_ fun register inside => ?_⟩
      · have powLe : 2 ^ (n + 1) ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rintro address ((⟨k, kb, same⟩ | ⟨k, kb, same⟩) | (⟨k, kb, same⟩ | ⟨k, kb, same⟩))
        · exact Or.inl ⟨k, by have : k < 2 ^ (n + 1) := kb; show k < 2 ^ (n + 1 + 1); omega, same⟩
        · exact Or.inr ⟨k, by have : k < 2 ^ (n + 1) := kb; show k < 2 ^ (n + 1 + 1); omega, same⟩
        · exact Or.inl ⟨k, kb, same⟩
        · exact Or.inr ⟨k, by have : k < 2 ^ (n + 1) := kb; show k < 2 ^ (n + 1 + 1); omega, same⟩
      · rcases inside with inside | inside <;> exact inside

/-- **The block `treeEval`** against `treeEvalM` for any `1 ≤ levels ≤ 20`. -/
theorem agree_treeEvalBlock (cells : TreeCells) (tagOf : Nat → Nat → Nat) (levels : Nat)
    (levelsPos : 1 ≤ levels) (levelsSmall : levels ≤ 20) (value : Nat) (valueSmall : value < 2 ^ 256)
    (bitLabel : Nat → Block) (join : Nat → Label) (memory : Memory)
    (layouts : ∀ k, k < levels → TreeLayout cells k)
    (alphaCell : memory.ram (word cells.alpha) = word value)
    (joinCells : ∀ k, 1 ≤ k → k < levels → memory.ram (word (cells.join k)) = labelWord (join k))
    (bitCells : ∀ k, k < levels → memory.ram (word (cells.bit k)) = blockWord (bitLabel k))
    (tagSmall : ∀ k s, k < levels → s < 2 ^ k → tagOf k s < 2 ^ 127) :
    Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex) (TreeEvalPost cells memory levels)
      ((treeEval cells tagOf levels).tree memory)
      (liftHash (treeEvalM tagOf value (fun k => clip (bitLabel k)) join levels)) := by
  obtain ⟨n, rfl⟩ : ∃ n, levels = n + 1 := ⟨levels - 1, by omega⟩
  exact agree_treeEval cells tagOf (n + 1) levelsSmall value valueSmall bitLabel join memory layouts
    alphaCell joinCells bitCells tagSmall n le_rfl

/-- **The growth**: after `count` paid levels from level `start`
the machine agrees with `liftHash (growEvalM tagOf α L J start labels count)`, with the frame of
`treeEvalWrites cells (start + count)`, composed level by level. -/
theorem agree_growEval (cells : TreeCells) (tagOf : Nat → Nat → Nat) (start : Nat)
    (value : Nat) (valueSmall : value < 2 ^ 256) (bitLabel join : Nat → Label)
    (labels : Fin (2 ^ start) → Label) (memory : Memory) (total : Nat) (totalSmall : start + total ≤ 20)
    (layouts : ∀ k, k < total → TreeLayout cells (start + k))
    (alphaCell : memory.ram (word cells.alpha) = word value)
    (joinCells : ∀ k, k < total →
      memory.ram (word (cells.join (start + k))) = labelWord (join (start + k)))
    (bitCells : ∀ k, k < total →
      memory.ram (word (cells.bit (start + k))) = labelWord (bitLabel (start + k)))
    (startCells : ∀ j : Fin (2 ^ start),
      memory.ram (word (cells.levelBase + j.val)) = labelWord (labels j))
    (tagSmall : ∀ k s, k < total → s < 2 ^ (start + k) → tagOf (start + k) s < 2 ^ 127) :
    ∀ count, count ≤ total →
      Agree (FixedIndex := FixedIndex) (EncIndex := EncIndex) (fun (level : Fin (2 ^ (start + count)) → Label) after =>
          (∀ j : Fin (2 ^ (start + count)),
            after.ram (word (cells.levelBase + j.val)) = labelWord (level j)) ∧
          Frame (treeEvalWrites cells (start + count)) treeStepClobbers memory after)
        ((growEval cells tagOf start count).tree memory)
        (liftHash (growEvalM tagOf value bitLabel join start labels count))
  | 0, _ => by
      unfold growEval
      rw [Prog.rep]
      exact .leaf ⟨startCells, Frame.refl _ _ memory⟩
  | count + 1, bound => by
      have layout := layouts count (by omega)
      unfold growEval
      rw [Prog.rep, tree_seq]
      rw [show growEvalM tagOf value bitLabel join start labels (count + 1) =
          (growEvalM tagOf value bitLabel join start labels count >>= fun previous =>
            evalStepM (start + count) (tagOf (start + count)) (activeAt value (start + count))
              (bitLabel (start + count)) (join (start + count)) previous) from rfl,
        TreeLaws.monad_bind, liftHash_bind]
      refine Agree.bindOpt (fun previous after post => ?_)
        (agree_growEval cells tagOf start value valueSmall bitLabel join labels memory total totalSmall
          layouts alphaCell joinCells bitCells startCells tagSmall count (by omega))
      obtain ⟨levelCells, frame⟩ := post
      have alphaNow : after.ram (word cells.alpha) = word value := by
        rw [frame.ram _ (not_treeEvalWrites cells (start + count) _ layout layout.alphaOut)]
        exact alphaCell
      have joinNow : after.ram (word (cells.join (start + count))) = labelWord (join (start + count)) := by
        rw [frame.ram _ (not_treeEvalWrites cells (start + count) _ layout layout.joinOut)]
        exact joinCells count (by omega)
      have bitNow : after.ram (word (cells.bit (start + count))) =
          labelWord (bitLabel (start + count)) := by
        rw [frame.ram _ (not_treeEvalWrites cells (start + count) _ layout layout.bitOut)]
        exact bitCells count (by omega)
      have bitNowRaw : after.ram (word (cells.bit (start + count))) =
          blockWord (embed (bitLabel (start + count))) := by rw [blockWord_embed]; exact bitNow
      have stepAgree := agree_treeStep (FixedIndex := FixedIndex) (EncIndex := EncIndex) cells (tagOf (start + count)) (start + count) (by omega) value valueSmall
        (embed (bitLabel (start + count))) (join (start + count)) previous after layout alphaNow levelCells
        joinNow bitNowRaw (fun s sb => tagSmall count s (by omega) sb)
      simp only [show ∀ l : Label, clip (embed l) = l from Narrow.clip_embed] at stepAgree
      refine stepAgree.mono fun level final post => ?_
      obtain ⟨cells', frame'⟩ := post
      refine ⟨cells', (frame.trans frame').mono ?_ fun register inside => ?_⟩
      · have powLe : 2 ^ (start + count) ≤ 2 ^ (start + (count + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        rintro address ((⟨k, kb, same⟩ | ⟨k, kb, same⟩) | (⟨k, kb, same⟩ | ⟨k, kb, same⟩))
        · exact Or.inl ⟨k, by have : k < 2 ^ (start + count) := kb; show k < 2 ^ (start + (count + 1)); omega, same⟩
        · exact Or.inr ⟨k, by have : k < 2 ^ (start + count) := kb; show k < 2 ^ (start + (count + 1)); omega, same⟩
        · exact Or.inl ⟨k, kb, same⟩
        · exact Or.inr ⟨k, by have : k < 2 ^ (start + count) := kb; show k < 2 ^ (start + (count + 1)); omega, same⟩
      · rcases inside with inside | inside <;> exact inside

end Agreement

end Kriterion.CRT.SimMachine
