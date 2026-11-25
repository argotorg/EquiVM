import Benchmarks.Midnight.Storage

/-! Scratch-memory facts for mapping getters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: mapping scratch writes preserve any later complete MLOAD.
theorem memLoad_twoWordHashMem {mem : ByteArray} (key slot off : UInt256)
    (hlo : 64 ≤ off.toNat) (hhi : off.toNat + 32 ≤ mem.size) :
    memLoad off (twoWordHashMem key slot mem) = memLoad off mem := by
  unfold memLoad
  rw [twoWordHashMem_size_of_ge_64 key slot (by omega)]
  rw [if_neg (by omega), if_neg (by omega)]
  rw [twoWordHashMem_read32_above64 key slot hlo hhi]

def mappingMemory (key slot : UInt256) : ByteArray :=
  twoWordHashMem key slot midnightEntryMemory

theorem mappingMemory_size (key slot : UInt256) : (mappingMemory key slot).size = 832 := by
  rw [mappingMemory, twoWordHashMem_size_of_ge_64 key slot
    (by rw [midnightEntryMemory_size]; decide), midnightEntryMemory_size]

theorem mappingMemory_zero (key slot : UInt256) :
    memLoad (UInt256.ofNat 800) (mappingMemory key slot) = ⟨0⟩ := by
  rw [mappingMemory, memLoad_twoWordHashMem key slot _ (by decide)
    (by rw [midnightEntryMemory_size]; decide), midnightEntryMemory_zero]

theorem mappingMemory_freePtr (key slot : UInt256) :
    memLoad (UInt256.ofNat 64) (mappingMemory key slot) = ⟨832⟩ := by
  rw [mappingMemory, memLoad_twoWordHashMem key slot _ (by decide)
    (by rw [midnightEntryMemory_size]; decide)]
  exact midnightEntryMemory_freePtr

theorem mappingMemory_hash (key slot : UInt256) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (mappingMemory key slot) = solcMappingSlot slot key := by
  exact twoWordHashMem_mapSlot_of_ge64 key slot (by rw [midnightEntryMemory_size]; decide)

theorem mappingMemory_return (key slot word : UInt256) :
    (writeWord (mappingMemory key slot) 832 word).readWithPadding 832 32 = word.toByteArray := by
  apply writeWord_read_back
  rw [mappingMemory_size]
  exact USize.size_pos

theorem midnightWordAt0_zero (key : UInt256) :
    memLoad (UInt256.ofNat 800) (wordAt0Mem key midnightEntryMemory) = ⟨0⟩ := by
  have hsize := wordAt0Mem_size_of_ge64 key
    (by rw [midnightEntryMemory_size]; decide)
  rw [show memLoad (UInt256.ofNat 800) (wordAt0Mem key midnightEntryMemory) =
      memLoad (UInt256.ofNat 800) midnightEntryMemory by
    unfold memLoad
    rw [hsize, midnightEntryMemory_size]
    simp only [show (UInt256.ofNat 800).toNat = 800 from rfl]
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 800 (by rw [toByteArray_size])
      (by rw [midnightEntryMemory_size]; decide) (by decide)
      (by rw [midnightEntryMemory_size])]]
  exact midnightEntryMemory_zero

def nestedMappingMemory (key0 key1 slot : UInt256) : ByteArray :=
  twoWordHashMem key1 (solcMappingSlot slot key0) (mappingMemory key0 slot)

theorem nestedMappingMemory_size (key0 key1 slot : UInt256) :
    (nestedMappingMemory key0 key1 slot).size = 832 := by
  rw [nestedMappingMemory, twoWordHashMem_size_of_ge_64 _ _
    (by rw [mappingMemory_size]; decide), mappingMemory_size]

theorem nestedMappingMemory_freePtr (key0 key1 slot : UInt256) :
    memLoad (UInt256.ofNat 64) (nestedMappingMemory key0 key1 slot) = ⟨832⟩ := by
  rw [nestedMappingMemory, memLoad_twoWordHashMem _ _ _ (by decide)
    (by rw [mappingMemory_size]; decide), mappingMemory_freePtr]

theorem nestedMappingMemory_zero (key0 key1 slot : UInt256) :
    memLoad (UInt256.ofNat 800) (nestedMappingMemory key0 key1 slot) = ⟨0⟩ := by
  rw [nestedMappingMemory, memLoad_twoWordHashMem _ _ _ (by decide)
    (by rw [mappingMemory_size]; decide), mappingMemory_zero]

theorem nestedMappingMemory_hash (key0 key1 slot : UInt256) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (nestedMappingMemory key0 key1 slot) =
      solcMappingSlot (solcMappingSlot slot key0) key1 := by
  exact twoWordHashMem_mapSlot_of_ge64 _ _ (by rw [mappingMemory_size]; decide)

theorem nestedMappingMemory_return (key0 key1 slot word : UInt256) :
    (writeWord (nestedMappingMemory key0 key1 slot) 832 word).readWithPadding 832 32 =
      word.toByteArray := by
  apply writeWord_read_back
  rw [nestedMappingMemory_size]
  exact USize.size_pos

theorem wordAt0_fold (word : UInt256) (mem : ByteArray) :
    word.toByteArray.write 0 mem 0 32 = wordAt0Mem word mem := rfl

theorem twoWordHash_fold (key slot : UInt256) (mem : ByteArray) :
    slot.toByteArray.write 0 (wordAt0Mem key mem) 32 32 = twoWordHashMem key slot mem := rfl

theorem mappingMemory_fold (key slot : UInt256) :
    twoWordHashMem key slot midnightEntryMemory = mappingMemory key slot := rfl

theorem nestedMappingMemory_fold (key0 key1 slot : UInt256) :
    twoWordHashMem key1 (solcMappingSlot slot key0) (mappingMemory key0 slot) =
      nestedMappingMemory key0 key1 slot := rfl

end Benchmarks.Midnight
