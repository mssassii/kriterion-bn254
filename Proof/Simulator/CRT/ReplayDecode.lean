/-
**The decoding on the machine** (`exec_decodeAll`): for every encoding `e < S`, the cell
`decodedBase + e` holds `wrapDecode M B h_e (crt L_e) mod p` as a `fieldWord`, from the residues the
moduli's bodies left in RAM and the published hints. Also the determinism of Garner's blocks, so
that the decoding composes after an agreement (`agree_seq_det`).
-/

import Proof.Simulator.CRT.Garner
import Construction.Simulator.CRT.ReplayDecode

namespace Kriterion.CRT.SimMachine

open Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine
open Kriterion.ArgoMAC.PlanB.SimMachine.Blocks Kriterion.CRT
open Kriterion.ArgoMAC Finset

/-! ### Determinism of Garner's blocks -/

theorem det_garnerTerm (mods : Nat → Nat) (vaddr i j : Nat) :
    (garnerTerm mods vaddr i j).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, trivial, trivial⟩

theorem det_garnerDigitProg (mods : Nat → Nat) (laddr vaddr i : Nat) :
    (garnerDigitProg mods laddr vaddr i).OpsSatisfy Op.Det :=
  ⟨trivial, det_rep _ _ (fun j _ => det_garnerTerm mods vaddr i j), ⟨trivial, trivial⟩, trivial,
    det_barrett _ _ _ _, trivial, trivial, det_barrett _ _ _ _, ⟨trivial, trivial⟩⟩

theorem det_garnerDigits (mods : Nat → Nat) (count laddr vaddr : Nat) :
    (garnerDigits mods count laddr vaddr).OpsSatisfy Op.Det :=
  det_rep _ _ fun i _ => det_garnerDigitProg mods laddr vaddr i

theorem det_zeroLimbs (zbase nz : Nat) : (zeroLimbs zbase nz).OpsSatisfy Op.Det :=
  ⟨trivial, det_rep _ _ fun _ _ => ⟨trivial, trivial⟩⟩

theorem det_garnerHorner (mods : Nat → Nat) (count vaddr zbase nz : Nat) :
    (garnerHorner mods count vaddr zbase nz).OpsSatisfy Op.Det :=
  ⟨trivial, trivial, det_zeroLimbs zbase nz,
    det_rep _ _ fun _ _ => ⟨trivial, ⟨trivial, trivial⟩, det_mulSmallAdd _ _⟩⟩

theorem det_limbLess (bound zbase nz : Nat) : (limbLess bound zbase nz).OpsSatisfy Op.Det :=
  ⟨trivial, trivial, det_rep _ _ fun _ _ =>
    ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩⟩

theorem det_limbModP (zbase nz : Nat) : (limbModP zbase nz).OpsSatisfy Op.Det :=
  ⟨trivial, det_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, trivial, trivial, trivial⟩⟩

theorem det_wrapCombine (modulusModP hintCell outCell : Nat) :
    (wrapCombine modulusModP hintCell outCell).OpsSatisfy Op.Det :=
  ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩⟩

theorem det_reconstruct (mods : Nat → Nat) (count modulus wrapB laddr vaddr zbase nz hintCell outCell : Nat) :
    (reconstruct mods count modulus wrapB laddr vaddr zbase nz hintCell outCell).OpsSatisfy Op.Det :=
  ⟨det_garnerDigits _ _ _ _, det_garnerHorner _ _ _ _ _, det_limbLess _ _ _, det_limbModP _ _,
    det_wrapCombine _ _ _⟩

theorem det_gatherResidues (outOf : Nat → Nat) (count gbase e : Nat) :
    (gatherResidues outOf count gbase e).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

theorem det_decodeAll (dc : DecodeCells) (mods : Nat → Nat) (count wrapB nz S : Nat) :
    (decodeAll dc mods count wrapB nz S).OpsSatisfy Op.Det :=
  det_rep _ _ fun _ _ => ⟨det_gatherResidues _ _ _ _, det_reconstruct _ _ _ _ _ _ _ _ _ _⟩

/-! ### Gathering -/

theorem exec_gatherResidues (outOf : Nat → Nat) (count gbase e : Nat) (memory : Memory)
    (below : ∀ i, i < count → outOf i + e < gbase) (fits : gbase + count < 2 ^ 256) :
    ∃ after, (gatherResidues outOf count gbase e).exec memory = some after ∧
      (∀ i, i < count → after.ram (word (gbase + i)) = memory.ram (word (outOf i + e))) ∧
      Frame (Writes.region ⟨gbase, count⟩) (Clobbers.ofList [rA, rAddr]) memory after := by
  obtain ⟨after, run, done, frame, bits, regs⟩ := Prog.exec_rep
    (fun i => .seq (loadAt rA (outOf i + e)) (storeAt (gbase + i) rA))
    (fun k current =>
      (∀ i, i < k → current.ram (word (gbase + i)) = memory.ram (word (outOf i + e))) ∧
      (∀ address, (∀ i, i < k → address ≠ word (gbase + i)) →
        current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧
      ∀ register, register ≠ rA → register ≠ rAddr →
        current.registers register = memory.registers register)
    count
    (fun k kb current ⟨done, frame, bits, regs⟩ => by
      have src := below k kb
      have source : current.ram (word (outOf k + e)) = memory.ram (word (outOf k + e)) :=
        frame _ fun i ib same => by
          have := word_inj (by omega) (by omega) same
          omega
      refine ⟨_, by rw [exec_loadAt_seq, exec_storeAt _ _ _ (by decide)], fun i ib => ?_,
        fun address off => ?_, ?_, fun register n1 n2 => ?_⟩
      · simp only [ram_storeRam, ram_setReg, reg_setReg, ↓reduceIte]
        rcases Nat.lt_or_ge i k with lt | ge
        · rw [Function.update_of_ne (word_ne (by omega) (by omega) (by omega))]
          exact done i lt
        · have : i = k := by omega
          subst this
          rw [Function.update_self, source]
      · simp only [ram_storeRam, ram_setReg]
        rw [Function.update_of_ne (off k (by omega))]
        exact frame address fun i ib => off i (by omega)
      · simp only [bits_storeRam, bits_setReg]
        exact bits
      · simp only [reg_storeRam, reg_setReg, if_neg n1, if_neg n2]
        exact regs register n1 n2)
    memory ⟨fun i ib => absurd ib (Nat.not_lt_zero _), fun _ _ => rfl, rfl, fun _ _ _ => rfl⟩
  refine ⟨after, run, done, ⟨fun address outside => frame address fun i ib same => outside ⟨i, ib, same⟩,
    bits, fun register outside => regs register (fun h => outside (by simp [Clobbers.ofList, h]))
      (fun h => outside (by simp [Clobbers.ofList, h]))⟩⟩

/-! ### The decoding -/

/-- The layout of the decoding: the hints below the decoded cells below every modulus's residue
cells below the scratch (gathered residues, digits, limbs). -/
structure DecodeChain (dc : DecodeCells) (count nz S : Nat) : Prop where
  hintBelow : dc.hintBase + S ≤ dc.decodedBase
  outAbove : ∀ i, i < count → dc.decodedBase + S ≤ dc.outOf i
  outBelow : ∀ i, i < count → dc.outOf i + S ≤ dc.gbase
  decodedBelow : dc.decodedBase + S ≤ dc.gbase
  gatherBelow : dc.gbase + count ≤ dc.vaddr
  digitsBelow : dc.vaddr + count ≤ dc.zbase
  limbsFit : dc.zbase + nz < 2 ^ 256

/-- The decoded value of one encoding. -/
def decodedValue (mods : Nat → Nat) (count wrapB : Nat) (hint : Bool) (L : Nat → Nat) :
    BN254.BaseField :=
  ((Kriterion.CRT.wrapDecode (prefixProd mods count) wrapB hint (garnerValue mods L count) : Nat) :
    BN254.BaseField)

/-- **The decoding of `S` encodings.** -/
theorem exec_decodeAll [BN254.FieldCertificate] (dc : DecodeCells) (mods : Nat → Nat) (count wrapB nz S : Nat)
    (chain : DecodeChain dc count nz S) (table : GarnerTable mods count)
    (valueFits : prefixProd mods count ≤ 2 ^ (128 * nz)) (boundFits : wrapB < 2 ^ (128 * nz))
    (L : Nat → Nat → Nat) (hint : Nat → Bool) (memory : Memory)
    (residues : ∀ i, i < count → ∀ e, e < S → memory.ram (word (dc.outOf i + e)) = word (L i e))
    (residuesSmall : ∀ i, i < count → ∀ e, e < S → L i e < mods i)
    (hints : ∀ e, e < S → memory.ram (word (dc.hintBase + e)) = word (if hint e then 1 else 0)) :
    ∃ after, (decodeAll dc mods count wrapB nz S).exec memory = some after ∧
      (∀ e, e < S → after.ram (word (dc.decodedBase + e)) =
        fieldWord (decodedValue mods count wrapB (hint e) fun i => L i e)) ∧
      Frame (decodeWrites dc nz S) reconstructClobbers memory after := by
  have := chain.hintBelow; have := chain.gatherBelow; have := chain.digitsBelow
  have := chain.limbsFit; have := chain.decodedBelow
  obtain ⟨after, run, done, frame⟩ := Prog.exec_rep (decodeOne dc mods count wrapB nz)
    (fun k current =>
      (∀ e, e < k → current.ram (word (dc.decodedBase + e)) =
        fieldWord (decodedValue mods count wrapB (hint e) fun i => L i e)) ∧
      Frame (decodeWrites dc nz k) reconstructClobbers memory current)
    S
    (fun k kb current ⟨done, frame⟩ => by
      -- the inputs are intact
      have untouched : ∀ x, x < dc.gbase → (x < dc.decodedBase ∨ dc.decodedBase + S ≤ x) →
          current.ram (word x) = memory.ram (word x) := fun x xb side =>
        frame.ram _ fun inside => by
          rcases inside with ⟨y, yLow, yHigh, same⟩ | ⟨j, jb, same⟩
          · have := word_inj (by omega) (by omega) same
            omega
          · dsimp only at jb same
            have := word_inj (by omega) (by omega) same
            omega
      obtain ⟨m1, run1, gathered, frame1⟩ := exec_gatherResidues dc.outOf count dc.gbase k current
        (fun i ib => by have := chain.outBelow i ib; omega) (by omega)
      have layout : ReconLayout count dc.gbase dc.vaddr dc.zbase nz (dc.hintBase + k)
          (dc.decodedBase + k) :=
        ⟨by omega, by omega, by omega, fun i _ j _ => by omega, fun i _ j _ => by omega, by omega,
          fun j _ => by omega, fun j _ => by omega, by omega⟩
      obtain ⟨m2, run2, out2, frame2⟩ := exec_reconstruct mods (fun i => L i k) count table wrapB
        dc.gbase dc.vaddr dc.zbase nz (dc.hintBase + k) (dc.decodedBase + k) (hint k) m1 layout
        (fun i ib => by
          have := chain.outAbove i ib; have := chain.outBelow i ib
          rw [gathered i ib, untouched _ (by omega) (Or.inr (by omega))]
          exact residues i ib k kb)
        (fun i ib => residuesSmall i ib k kb)
        (by
          rw [frame1.ram _ fun ⟨j, jb, same⟩ => by
              dsimp only at jb same
              have := word_inj (by omega) (by omega) same
              omega,
            untouched _ (by omega) (Or.inl (by omega))]
          exact hints k kb)
        valueFits boundFits
      refine ⟨m2, by rw [decodeOne, Prog.exec_seq_some _ _ _ _ run1, run2], fun e eb => ?_, ?_⟩
      · rcases Nat.lt_or_ge e k with lt | ge
        · rw [frame2.ram _ ?_, frame1.ram _ ?_]
          · exact done e lt
          · rintro ⟨j, jb, same⟩
            dsimp only at jb same
            have := word_inj (by omega) (by omega) same
            omega
          · rintro ((⟨j, jb, same⟩ | ⟨j, jb, same⟩) | same)
            · dsimp only at jb same
              have := word_inj (by omega) (by omega) same
              omega
            · dsimp only at jb same
              have := word_inj (by omega) (by omega) same
              omega
            · have := word_inj (by omega) (by omega) same
              omega
        · have : e = k := by omega
          subst this
          exact out2
      · refine ((frame.trans frame1).trans frame2).mono ?_ ?_
        · rintro address (((inside | ⟨j, jb, same⟩) | ⟨j, jb, same⟩) | ((⟨j, jb, same⟩ | ⟨j, jb, same⟩) | same))
          · exact Or.inl inside
          · dsimp only at jb same
            exact Or.inr ⟨j, by show j < k + 1; omega, same⟩
          · dsimp only at jb same
            exact Or.inl ⟨dc.gbase + j, by omega, by omega, same⟩
          · dsimp only at jb same
            exact Or.inl ⟨dc.vaddr + j, by omega, by omega, same⟩
          · dsimp only at jb same
            exact Or.inl ⟨dc.zbase + j, by omega, by omega, same⟩
          · exact Or.inr ⟨k, by show k < k + 1; omega, by rw [same]⟩
        · rintro register ((inside | inside) | inside)
          · exact inside
          · simp only [Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false] at inside
            simp only [reconstructClobbers, Clobbers.ofList, List.mem_cons, List.not_mem_nil, or_false]
            rcases inside with h | h <;> simp [h]
          · exact inside)
    memory ⟨fun e eb => absurd eb (Nat.not_lt_zero _), Frame.refl _ _ _⟩
  exact ⟨after, run, done, frame⟩

end Kriterion.CRT.SimMachine
