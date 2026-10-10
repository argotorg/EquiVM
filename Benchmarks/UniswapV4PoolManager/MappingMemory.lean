import Benchmarks.UniswapV4PoolManager.Storage
import Benchmarks.UniswapV4PoolManager.EntryTrace

/-! Scratch memory used by PoolManager mapping getters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

theorem entryMemory_size : entryMemory.size = 96 := by native_decide

theorem twoWordHashMem_load64 (key base : UInt256) :
    memLoad ⟨64⟩ (twoWordHashMem key base entryMemory) = ⟨160⟩ := by
  rw [memLoad, twoWordHashMem_size_96 key base entryMemory_size]
  change UInt256.ofNat (fromByteArrayBigEndian ((twoWordHashMem key base entryMemory).readWithPadding 64 32)) = ⟨160⟩
  rw [twoWordHashMem_read_above64 key base 64 (by decide) (by rw [entryMemory_size])]
  have h := entryMemory_load64
  rw [memLoad, entryMemory_size] at h
  exact h

theorem twoWordHashMem_returnWord (key base value : UInt256) :
    (value.toByteArray.write 0 (twoWordHashMem key base entryMemory)
      (memLoad ⟨64⟩ (twoWordHashMem key base entryMemory)).toNat 32).readWithPadding
      (memLoad ⟨64⟩ (twoWordHashMem key base entryMemory)).toNat 32 = value.toByteArray := by
  rw [twoWordHashMem_load64]
  exact writeWord_read_back _ 160 value (by rw [twoWordHashMem_size_96 key base entryMemory_size]; native_decide)

theorem twoWordHashMem_slot (key base : UInt256) :
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key base entryMemory) = mappingSlotWord key base := by
  change UInt256.ofNat (fromByteArrayBigEndian (KEC ((twoWordHashMem key base entryMemory).readWithPadding 0 64))) = _
  rw [twoWordHashMem_read0_64 key base entryMemory_size]
  exact keccakSlot_eq _

-- LIBRARY CANDIDATE: general word, mapping reference, or scratch-memory fact.
theorem mappingMemory_slot (key base : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key base mem) = mappingSlotWord key base := by
  change UInt256.ofNat (fromByteArrayBigEndian (KEC ((twoWordHashMem key base mem).readWithPadding 0 64))) = _
  rw [twoWordHashMem_read0_64 key base hmem]
  exact keccakSlot_eq _

-- LIBRARY CANDIDATE: general word, mapping reference, or scratch-memory fact.
theorem returnWordAt160 {mem : ByteArray} (hmem : mem.size = 96) (value : UInt256) :
    (value.toByteArray.write 0 mem 160 32).readWithPadding 160 32 = value.toByteArray :=
  writeWord_read_back mem 160 value (by rw [hmem]; native_decide)

-- LIBRARY CANDIDATE: general word, mapping reference, or scratch-memory fact.
theorem mappingMemory_load64 (key base : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    memLoad ⟨64⟩ (twoWordHashMem key base mem) = memLoad ⟨64⟩ mem := by
  rw [memLoad, twoWordHashMem_size_96 key base hmem, memLoad, hmem]
  change UInt256.ofNat (fromByteArrayBigEndian ((twoWordHashMem key base mem).readWithPadding 64 32)) =
    UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))
  rw [twoWordHashMem_read_above64 key base 64 (by decide) (by rw [hmem])]

-- LIBRARY CANDIDATE: a word store preserves a disjoint earlier word load.
theorem memLoad_writeWord_below (mem : ByteArray) (read : UInt256) (off : Nat) (value : UInt256)
    (hread : read.toNat + 32 ≤ mem.size) (hbefore : read.toNat + 32 ≤ off)
    (hgap : off - mem.size < USize.size) :
    memLoad read (Reasoning.Theory.writeWord mem off value) = memLoad read mem := by
  have hs := writeWord_size mem off value hgap
  rw [memLoad, memLoad, if_neg (by omega : ¬read.toNat ≥ (Reasoning.Theory.writeWord mem off value).size),
    if_neg (by omega : ¬read.toNat ≥ mem.size)]
  rw [Reasoning.Theory.writeWord, toByteArray_write_read_below_of_gap value mem off read.toNat hread hbefore hgap]

-- LIBRARY CANDIDATE: an event word followed by a scalar ABI return at the free pointer.
theorem eventWordThenReturn {mem : ByteArray} {ptr : UInt256}
    (hp : memLoad ⟨64⟩ mem = ptr) (hmem : 96 ≤ mem.size) (hoff : 96 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (eventWord resultWord : UInt256) :
    let written := eventWord.toByteArray.write 0 mem (memLoad ⟨64⟩ mem).toNat 32
    (resultWord.toByteArray.write 0 written (memLoad ⟨64⟩ written).toNat 32).readWithPadding
      (memLoad ⟨64⟩ written).toNat 32 = resultWord.toByteArray := by
  dsimp only
  rw [hp]
  let written := eventWord.toByteArray.write 0 mem ptr.toNat 32
  have hs : ptr.toNat + 32 ≤ written.size := toByteArray_write_size_ge_off_add32 _ _ _ hgap
  have hp' : memLoad ⟨64⟩ written = ptr :=
    (memLoad_writeWord_below mem ⟨64⟩ ptr.toNat eventWord hmem hoff hgap).trans hp
  change (resultWord.toByteArray.write 0 written (memLoad ⟨64⟩ written).toNat 32).readWithPadding
    (memLoad ⟨64⟩ written).toNat 32 = _
  rw [hp']
  exact writeWord_read_back _ _ _ (by rw [Nat.sub_eq_zero_of_le (by omega : ptr.toNat ≤ written.size)]; native_decide)

def nestedMappingMemory (key0 key1 base : UInt256) (mem : ByteArray) : ByteArray :=
  let first := twoWordHashMem key0 base mem
  twoWordHashMem key1 (keccakWord ⟨0⟩ ⟨64⟩ first) first

theorem nestedMappingMemory_size {mem : ByteArray} (key0 key1 base : UInt256)
    (hmem : mem.size = 96) : (nestedMappingMemory key0 key1 base mem).size = 96 :=
  twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ hmem)

theorem nestedMappingMemory_slot {mem : ByteArray} (key0 key1 base : UInt256)
    (hmem : mem.size = 96) :
    keccakWord ⟨0⟩ ⟨64⟩ (nestedMappingMemory key0 key1 base mem) =
      mappingSlotWord key1 (mappingSlotWord key0 base) := by
  rw [nestedMappingMemory, mappingMemory_slot _ _ (twoWordHashMem_size_96 _ _ hmem),
    mappingMemory_slot _ _ hmem]

theorem nestedMappingMemory_load64 {mem : ByteArray} (key0 key1 base : UInt256)
    (hmem : mem.size = 96) :
    memLoad ⟨64⟩ (nestedMappingMemory key0 key1 base mem) = memLoad ⟨64⟩ mem := by
  rw [nestedMappingMemory, mappingMemory_load64 _ _ (twoWordHashMem_size_96 _ _ hmem),
    mappingMemory_load64 _ _ hmem]

-- LIBRARY CANDIDATE: two event words followed by a scalar return at the free pointer.
theorem eventTwoWordsThenReturn {mem : ByteArray} {ptr : UInt256}
    (hp : memLoad ⟨64⟩ mem = ptr) (hmem : 96 ≤ mem.size) (hoff : 96 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (hbound : ptr.toNat + 32 < UInt256.size)
    (first second result : UInt256) :
    let events := Reasoning.Theory.writeWord
      (Reasoning.Theory.writeWord mem (memLoad ⟨64⟩ mem).toNat first)
      (memLoad ⟨64⟩ mem + ⟨32⟩).toNat second
    (result.toByteArray.write 0 events (memLoad ⟨64⟩ events).toNat 32).readWithPadding
      (memLoad ⟨64⟩ events).toNat 32 = result.toByteArray := by
  dsimp only
  rw [hp]
  have hadd : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt hbound
  rw [hadd]
  let m1 := Reasoning.Theory.writeWord mem ptr.toNat first
  let m2 := Reasoning.Theory.writeWord m1 (ptr.toNat + 32) second
  have hs1 : m1.size = max mem.size (ptr.toNat + 32) := writeWord_size _ _ _ hgap
  have hgap2 : ptr.toNat + 32 - m1.size < USize.size := by
    rw [hs1, Nat.sub_eq_zero_of_le (Nat.le_max_right _ _)]; native_decide
  have hs2 : m2.size = max m1.size (ptr.toNat + 32 + 32) := writeWord_size _ _ _ hgap2
  have hp1 : memLoad ⟨64⟩ m1 = ptr :=
    (memLoad_writeWord_below mem ⟨64⟩ ptr.toNat first hmem hoff hgap).trans hp
  have hp2 : memLoad ⟨64⟩ m2 = ptr :=
    (memLoad_writeWord_below m1 ⟨64⟩ (ptr.toNat + 32) second (by change 96 ≤ m1.size; omega)
      (by change 96 ≤ ptr.toNat + 32; omega) hgap2).trans hp1
  change (result.toByteArray.write 0 m2 (memLoad ⟨64⟩ m2).toNat 32).readWithPadding
    (memLoad ⟨64⟩ m2).toNat 32 = _
  rw [hp2]
  exact writeWord_read_back _ _ _
    (by rw [Nat.sub_eq_zero_of_le (by omega : ptr.toNat ≤ m2.size)]; native_decide)

def tripleMappingMemory (key0 key1 key2 base : UInt256) (mem : ByteArray) : ByteArray :=
  let first := nestedMappingMemory key0 key1 base mem
  twoWordHashMem key2 (keccakWord ⟨0⟩ ⟨64⟩ first) first

theorem tripleMappingMemory_size {mem : ByteArray} (key0 key1 key2 base : UInt256)
    (hmem : mem.size = 96) : (tripleMappingMemory key0 key1 key2 base mem).size = 96 :=
  twoWordHashMem_size_96 _ _ (nestedMappingMemory_size _ _ _ hmem)

theorem tripleMappingMemory_slot {mem : ByteArray} (key0 key1 key2 base : UInt256)
    (hmem : mem.size = 96) :
    keccakWord ⟨0⟩ ⟨64⟩ (tripleMappingMemory key0 key1 key2 base mem) =
      mappingSlotWord key2 (mappingSlotWord key1 (mappingSlotWord key0 base)) := by
  rw [tripleMappingMemory, mappingMemory_slot _ _ (nestedMappingMemory_size _ _ _ hmem),
    nestedMappingMemory_slot _ _ _ hmem]

theorem tripleMappingMemory_load64 {mem : ByteArray} (key0 key1 key2 base : UInt256)
    (hmem : mem.size = 96) :
    memLoad ⟨64⟩ (tripleMappingMemory key0 key1 key2 base mem) = memLoad ⟨64⟩ mem := by
  rw [tripleMappingMemory, mappingMemory_load64 _ _ (nestedMappingMemory_size _ _ _ hmem),
    nestedMappingMemory_load64 _ _ _ hmem]

end Benchmarks.UniswapV4PoolManager
