from pathlib import Path
import re,json
root=Path(__file__).resolve().parents[1]
r=json.loads((root/'evidence/chunk9-feasibility/model.json').read_text())
s=(root/'Proof/Privacy/CRT/Hidden/Reach.lean').read_text()
walk=s[s.index('def chunkBound'):s.index('def certs :')]
values=s[s.index('def valueOf ('):s.index('/-! ### The rows -/')]
# These are copies of the existing soundness lemmas, with the radix/count changed.
def convert(s):
    replacements={'256':'512','32':'29','31':'28','48':'3','47':'2','8':'9'}
    s=re.sub(r'\b(256|32|31|48|47|8)\b',lambda m:replacements[m[0]],s)
    s=s.replace('Entry.table','table').replace('Paths.bn254_chunkCount','by rfl')
    s=s.replace('≤ 255 * 512','≤ 511 * 512').replace('min 9 (254 - 9 * 28) = 6','min 9 (254 - 9 * 28) = 2')
    return s
head='''/- Isolated nine-bit candidate feasibility proof; production definitions are unchanged.
Reach-walk and value decomposition proofs are adapted from the inherited Hidden/Reach.lean.
The generic CRT delivery proof is reused only for this explicit research table. -/
import Proof.Privacy.CRT.Hidden.Reach
import Proof.Correctness.CRT.Record

namespace Kriterion.CRT.Chunk9Research
open BN254
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

def moduli : Array Nat := #MODULI

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

'''.replace('#MODULI','#'+str(r['moduli']))
cert='def certs : List Nat := '+str(r['certificates'])+'\n\n'
cert+='''theorem rows_ok : ∀ i : Fin table.count, table.modulus i ≠ 512 →
    rowOK (table.modulus i) (certs.getD i.val 0) = true := by decide +kernel

theorem top_le : 3 * 512 ^ 28 ≤ baseFieldModulus := by decide +kernel

'''
end='''theorem word_target (i : Fin table.count) (notPow : table.modulus i ≠ 512) (t : Nat)
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
'''
(root/'Scratch/Chunk9Feasibility.lean').write_text(head+convert(walk)+cert+convert(values)+end)
