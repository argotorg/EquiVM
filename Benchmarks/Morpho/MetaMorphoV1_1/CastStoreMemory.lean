import Benchmarks.Morpho.MetaMorphoV1_1.Uint128AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory

/-! Memory effects of a successful allocating cast followed by a market-field store. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem nextCursor64_toNat {ptr : UInt256} (hfit : allocationFits ptr ⟨64⟩) :
    (nextCursor ptr ⟨64⟩).toNat = ptr.toNat + 64 := by
  have h := (allocationFits_aligned ptr ⟨64⟩ (by decide +kernel)).mp hfit
  exact uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)

theorem uint128CastMemory_load {mem : ByteArray} {ptr read : UInt256}
    (hlo : 96 ≤ read.toNat) (hptr : read.toNat + 32 ≤ ptr.toNat)
    (hin : read.toNat + 32 ≤ mem.size) :
    memLoad read (uint128CastMemory mem ptr) = memLoad read mem := by
  have he := (uint128CastMemory_prefix mem ptr).load_preserved hlo hptr hin read.val.isLt
  simpa only [u256_ofNat_toNat] using he

def castStoreMemory (mem : ByteArray) (ptr field value : UInt256) : ByteArray :=
  writeWord (uint128CastMemory mem ptr) field.toNat value

theorem castStoreMemory_size (mem : ByteArray) (ptr field value : UInt256)
    (hlo : 96 ≤ ptr.toNat) (hfield : field.toNat + 32 ≤ ptr.toNat) :
    (castStoreMemory mem ptr field value).size = max mem.size (ptr.toNat + 64) := by
  rw [castStoreMemory, writeWord_sparse_size, uint128CastMemory_size mem ptr hlo]
  omega

theorem castStoreMemory_free (mem : ByteArray) (ptr field value : UInt256)
    (hlo : 96 ≤ field.toNat) (hfield : field.toNat + 32 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (castStoreMemory mem ptr field value) = nextCursor ptr ⟨64⟩ := by
  have hptr : 96 ≤ ptr.toNat := by omega
  rw [castStoreMemory, memLoad_write_above _ _ _ _
    (by rw [uint128CastMemory_size mem ptr hptr]; change 64 + 32 ≤ _; omega) hlo]
  exact uint128CastMemory_free mem ptr hptr

theorem castStoreMemory_prefix (mem : ByteArray) (ptr field value : UInt256)
    (hfield : field.toNat ≤ ptr.toNat) :
    MemoryPrefix mem (castStoreMemory mem ptr field value) field.toNat :=
  ((uint128CastMemory_prefix mem ptr).mono hfield).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _)))

theorem castStoreMemory_field (mem : ByteArray) (ptr field value : UInt256) :
    memLoad field (castStoreMemory mem ptr field value) = value := by
  apply loadedWord_of_read
  · rw [castStoreMemory, writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ _ _

theorem castStoreMemory_preserves {mem : ByteArray} {ptr field value read : UInt256}
    (hlo : 96 ≤ read.toNat) (hptr : read.toNat + 32 ≤ ptr.toNat)
    (hin : read.toNat + 32 ≤ mem.size)
    (hsep : read.toNat + 32 ≤ field.toNat ∨ field.toNat + 32 ≤ read.toNat) :
    memLoad read (castStoreMemory mem ptr field value) = memLoad read mem := by
  have hw : memLoad read (castStoreMemory mem ptr field value) =
      memLoad read (uint128CastMemory mem ptr) :=
    memLoad_write_disjoint _ _ _ _
      (by have hs := (uint128CastMemory_prefix mem ptr).size; omega) hsep
  rw [hw]
  have he := (uint128CastMemory_prefix mem ptr).load_preserved hlo hptr hin read.val.isLt
  simpa only [u256_ofNat_toNat] using he

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
