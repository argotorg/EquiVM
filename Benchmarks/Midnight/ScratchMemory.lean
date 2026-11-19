import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.WordArray

/-! Memory invariants preserved by repeated mapping hashes in administrative setters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure EntryScratch (mem : ByteArray) : Prop where
  size : 832 ≤ mem.size
  zero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩
  freePtr : memLoad (UInt256.ofNat 64) mem = ⟨832⟩

theorem midnightEntryScratch : EntryScratch midnightEntryMemory :=
  ⟨by rw [midnightEntryMemory_size], midnightEntryMemory_zero, midnightEntryMemory_freePtr⟩

theorem EntryScratch.hash {mem : ByteArray} (h : EntryScratch mem) (key slot : UInt256) :
    EntryScratch (twoWordHashMem key slot mem) := by
  have hm : 64 ≤ mem.size := by have := h.size; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [twoWordHashMem_size_of_ge_64 key slot hm]
    exact h.size
  · rw [memLoad_twoWordHashMem (mem := mem) key slot (UInt256.ofNat 800) (by decide) h.size, h.zero]
  · rw [memLoad_twoWordHashMem (mem := mem) key slot (UInt256.ofNat 64) (by decide)
      (by have := h.size; change 96 ≤ mem.size; omega), h.freePtr]

theorem EntryScratch.hashValue {mem : ByteArray} (h : EntryScratch mem) (key slot : UInt256) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key slot mem) = solcMappingSlot slot key :=
  twoWordHashMem_mapSlot_of_ge64 key slot (by have := h.size; omega)

theorem EntryScratch.writeZero {mem : ByteArray} (h : EntryScratch mem) (value : UInt256) :
    memLoad (UInt256.ofNat 800) (writeWord mem 832 value) = ⟨0⟩ := by
  rw [memLoad_writeWord_preserved mem 832 (UInt256.ofNat 800) value h.size (Or.inl (by decide)), h.zero]

end Benchmarks.Midnight
