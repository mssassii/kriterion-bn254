import Construction.CRT.BitPacking
import Proof.Simulator.Stage1Wire

namespace Kriterion.CRT.BitPacking

open Kriterion.ArgoMAC.PlanB.SimMachine

/-- A regular head prevents reduction of large public codec expressions. -/
def bitsOf (base : BitPacking α width) (value : α) : List Bool := (base.encode value).toList

theorem bits_map (base : BitPacking α width) (encode : β → α) (decode : α → β)
    (inverse : ∀ value, decode (encode value) = value) (value : β) :
    bitsOf (base.map encode decode inverse) value = bitsOf base (encode value) := rfl

theorem bits_pair (first : BitPacking α left) (second : BitPacking β right) (a : α) (b : β) :
    bitsOf (first.pair second) (a, b) = bitsOf first a ++ bitsOf second b := by
  simp [bitsOf, pair]

theorem vector_flatten_toList (values : Vector (Vector α width) count) :
    values.flatten.toList = (values.toList.map Vector.toList).flatten := by
  simp only [Vector.flatten, Vector.toList, Array.toList_flatten, Array.toList_map, List.map_map]
  rfl

theorem bits_vector (base : BitPacking α width) (count : Nat) (values : Vector α count) :
    bitsOf (base.vector count) values =
      (List.ofFn fun i : Fin count => bitsOf base values[i.val]).flatten := by
  simp only [bitsOf, vector, vector_flatten_toList, Vector.toList_map, List.map_map]
  have asList : values.toList = List.ofFn (fun i : Fin count => values[i.val]) := by
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [asList, List.map_ofFn]
  rfl

theorem bits_natural (width : Nat) (value : Fin (2 ^ width)) :
    bitsOf (natural width) value = lsbs width value.val := by
  simp only [bitsOf, natural, lsbs, Vector.toList_ofFn]

theorem padded_bits (bits : Vector Bool width) :
    (padded bits).toList = bits.toList ++ List.replicate (padding width) false := by
  apply List.ext_getElem
  · simp only [Vector.length_toList, List.length_append, List.length_replicate]
    exact (padded_width width).symm
  · intro i hi hj
    simp only [Vector.getElem_toList, padded, Vector.getElem_ofFn]
    by_cases h : i < width
    · rw [dif_pos h, List.getElem_append_left (by simpa using h), Vector.getElem_toList]
    · rw [dif_neg h, List.getElem_append_right (by simpa using Nat.le_of_not_gt h)]
      simp

theorem packBytes_bits (bits : Vector Bool width) :
    byteBits (packBytes bits).toList = (padded bits).toList := by
  have each (value : Fin 256) :
      Kriterion.GarbledCircuit.SimulatorProtocol.bits 8 value.val =
        ((natural 8).encode value).toList := by
    rw [bits_eq_lsbs]
    exact (bits_natural 8 value).symm
  have same : ((packBytes bits).map (natural 8).encode).flatten = padded bits := by
    ext i hi
    simp only [Vector.getElem_flatten, Vector.getElem_map]
    dsimp only [packBytes, Vector.getElem_ofFn]
    simp only [natural_encode_decode, Vector.getElem_ofFn]
    congr 1
    omega
  rw [← same]
  simp only [byteBits, each, vector_flatten_toList, Vector.toList_map, List.map_map,
    List.flatMap_def, Function.comp_def]
  rfl

theorem encoding_bits (base : BitPacking α width) (value : α) :
    byteBits (base.encoding.encode value) = bitsOf base value ++ List.replicate (padding width) false := by
  change byteBits (packBytes (base.encode value)).toList = _
  rw [packBytes_bits, padded_bits]
  rfl

end Kriterion.CRT.BitPacking
