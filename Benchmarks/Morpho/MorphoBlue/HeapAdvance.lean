import Reasoning.HeapMemory

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: track an exact cursor advance and the previously allocated memory.
structure HeapAdvance (before : ByteArray) (fp : UInt256) (after : ByteArray) (fp' : UInt256) (count : Nat) : Prop where
  preserves : MemoryPrefix before after fp.toNat
  cursor : fp'.toNat = fp.toNat + count

theorem HeapAdvance.refl (mem : ByteArray) (fp : UInt256) : HeapAdvance mem fp mem fp 0 :=
  ⟨MemoryPrefix.refl _ _, by omega⟩

theorem HeapAdvance.trans {m1 m2 m3 f1 f2 f3 n1 n2}
    (h1 : HeapAdvance m1 f1 m2 f2 n1) (h2 : HeapAdvance m2 f2 m3 f3 n2) :
    HeapAdvance m1 f1 m3 f3 (n1 + n2) := by
  refine ⟨h1.preserves.trans (h2.preserves.mono (by have hh := h1.cursor; omega)), ?_⟩
  rw [h2.cursor, h1.cursor, Nat.add_assoc]

end Benchmarks.Morpho.MorphoBlue
