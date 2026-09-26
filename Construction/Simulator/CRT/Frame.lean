/-
**The frame-condition schema of the CRT machine's blocks** (the machine half of the interface).

Why a schema. In the switch-system machine's skeleton a frozen post (`ChunkPost`) promised every `OffChunk` cell
unchanged, and a new block wrote cells outside the regions `OffChunk` excluded; the fix had to be
propagated to every consumer. The CRT machine has only new blocks, so
the frame of every block is fixed here, before the bodies, in one shape:

1. **Every block exports two predicates next to its signature**: `writes : Writes` (the RAM cells it
   may change, a union of `Region`s and single cells) and `clobbers : Clobbers` (the registers it may
   change). They are definitions in this interface, not conjuncts inside a proof.
2. **Every block lemma's post is `Spec ∧ Frame writes clobbers start after`**, where `start` is the
   memory at the block's entry (for an `Agree` lemma: `fun value after => Spec value after ∧
   Frame writes clobbers start after`). `Frame` says: RAM equal outside `writes`, registers equal
   outside `clobbers`, stacks equal. No replay block touches a stack.
3. **Composition is by `Frame.trans` and `Frame.mono`, never by re-proof**: a sequence of blocks has
   the frame of the union of its parts; a consumer that needs a cell unchanged proves `¬ writes cell`
   from region disjointness (`Region.not_holds_of_before`, `Region.not_holds_of_after`), which is
   arithmetic on the layout's bases.
4. **Registers.** Scratch registers are always clobbered; the oracle operands `R12 … R15` are
   clobbered by every block that queries, and by the arithmetic blocks (which hold their constants
   there). A value that must survive a block lives in RAM, not in a register, unless the block's
   `clobbers` excludes that register.
5. **A block that grows** (a new cell written) changes its `writes` predicate in this file, an
   interface change; consumers that only use `Frame.mono` and region disjointness do not
   change.
-/

import Construction.Simulator.Layout

namespace Kriterion.CRT.SimMachine

open Cryptography.BoundedMachine Kriterion.ArgoMAC.PlanB.SimMachine

/-! ### Regions -/

/-- A RAM region: `count` consecutive cells from `base`. -/
structure Region where
  base : Nat
  count : Nat

/-- The address is one of the region's cells. -/
def Region.Holds (region : Region) (address : Word) : Prop :=
  ∃ k, k < region.count ∧ address = word (region.base + k)

/-- The region fits the address space. -/
def Region.Fits (region : Region) : Prop := region.base + region.count ≤ 2 ^ 256

/-! ### Write and clobber sets -/

/-- The RAM cells a block may write. -/
abbrev Writes := Word → Prop

/-- The registers a block may change. -/
abbrev Clobbers := Register → Prop

/-- No cell. -/
def Writes.none : Writes := fun _ => False

/-- One cell. -/
def Writes.cell (address : Nat) : Writes := fun other => other = word address

/-- One region. -/
def Writes.region (region : Region) : Writes := region.Holds

/-- The union of two write sets. -/
def Writes.union (first second : Writes) : Writes := fun address => first address ∨ second address

/-- The union of a family of write sets (a loop body's writes over its iterations). -/
def Writes.iUnion (count : Nat) (each : Nat → Writes) : Writes :=
  fun address => ∃ index, index < count ∧ each index address

/-- No register. -/
def Clobbers.none : Clobbers := fun _ => False

/-- A list of registers. -/
def Clobbers.ofList (registers : List Register) : Clobbers := fun register => register ∈ registers

/-- The union of two clobber sets. -/
def Clobbers.union (first second : Clobbers) : Clobbers :=
  fun register => first register ∨ second register

/-! ### The frame -/

/-- **The frame of a block**: RAM equal outside `writes`, registers equal outside `clobbers`, and
the stacks equal. -/
structure Frame (writes : Writes) (clobbers : Clobbers) (start after : Memory) : Prop where
  ram : ∀ address, ¬ writes address → after.ram address = start.ram address
  bits : after.bits = start.bits
  registers : ∀ register, ¬ clobbers register → after.registers register = start.registers register

namespace Frame

theorem refl (writes : Writes) (clobbers : Clobbers) (memory : Memory) :
    Frame writes clobbers memory memory :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩

/-- **Composition**: two blocks in sequence have the frame of the union. -/
theorem trans {writes writes' : Writes} {clobbers clobbers' : Clobbers} {first middle last : Memory}
    (one : Frame writes clobbers first middle) (two : Frame writes' clobbers' middle last) :
    Frame (writes.union writes') (clobbers.union clobbers') first last where
  ram address outside := by
    rw [two.ram address (fun inside => outside (Or.inr inside)),
      one.ram address (fun inside => outside (Or.inl inside))]
  bits := by rw [two.bits, one.bits]
  registers register outside := by
    rw [two.registers register (fun inside => outside (Or.inr inside)),
      one.registers register (fun inside => outside (Or.inl inside))]

/-- **Weakening** to larger write and clobber sets. -/
theorem mono {writes writes' : Writes} {clobbers clobbers' : Clobbers} {start after : Memory}
    (holds : Frame writes clobbers start after)
    (moreWrites : ∀ address, writes address → writes' address)
    (moreClobbers : ∀ register, clobbers register → clobbers' register) :
    Frame writes' clobbers' start after where
  ram address outside := holds.ram address fun inside => outside (moreWrites address inside)
  bits := holds.bits
  registers register outside :=
    holds.registers register fun inside => outside (moreClobbers register inside)

/-- A loop: iteration `index` has the frame of `each index`; the loop has their union. -/
theorem iUnion_step {count : Nat} {each : Nat → Writes} {clobbers : Clobbers} {start middle last : Memory}
    (before : Frame (Writes.iUnion count each) clobbers start middle)
    (step : Frame (each count) clobbers middle last) :
    Frame (Writes.iUnion (count + 1) each) clobbers start last :=
  (before.trans step).mono
    (fun address inside => by
      rcases inside with ⟨index, bound, holds⟩ | holds
      · exact ⟨index, by omega, holds⟩
      · exact ⟨count, by omega, holds⟩)
    (fun register inside => by rcases inside with inside | inside <;> exact inside)

end Frame

/-! ### Disjointness of regions -/

/-- A cell below a region's base is outside it (every address in range). -/
theorem Region.not_holds_of_before (region : Region) (fits : region.Fits) {address : Nat}
    (small : address < 2 ^ 256) (below : address < region.base) :
    ¬ region.Holds (word address) := by
  rintro ⟨k, bound, same⟩
  have := congrArg BitVec.toNat same
  simp only [word, BitVec.toNat_ofNat] at this
  unfold Region.Fits at fits
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- A cell at or above a region's end is outside it. -/
theorem Region.not_holds_of_after (region : Region) (fits : region.Fits) {address : Nat}
    (small : address < 2 ^ 256) (above : region.base + region.count ≤ address) :
    ¬ region.Holds (word address) := by
  rintro ⟨k, bound, same⟩
  have := congrArg BitVec.toNat same
  simp only [word, BitVec.toNat_ofNat] at this
  unfold Region.Fits at fits
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- A cell of a region is in it. -/
theorem Region.holds_cell (region : Region) {k : Nat} (bound : k < region.count) :
    region.Holds (word (region.base + k)) :=
  ⟨k, bound, rfl⟩

end Kriterion.CRT.SimMachine
