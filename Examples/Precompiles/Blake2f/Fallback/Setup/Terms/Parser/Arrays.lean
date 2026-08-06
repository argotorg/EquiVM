import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Parser.Core

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem hArrayAllocMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayAllocMem I).size = 405 := by
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
    rw [hlen]
    decide
  unfold hArrayAllocMem
  apply toByteArray_write32_size_of_le
  · rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
      (by decide) hsrc (by native_decide)]
  · rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
      (by decide) hsrc (by native_decide)]
    decide
  · native_decide

theorem hArrayAllocMem_read64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayAllocMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 640) := by
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
    rw [hlen]
    decide
  unfold hArrayAllocMem
  rw [toByteArray_write32_read_back]
  rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
    (by decide) hsrc (by native_decide)]
  decide

theorem hArrayZeroMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayZeroMem I).size = 405 := by
  have hsize : (hArrayAllocMem I).size = 405 := hArrayAllocMem_size I hlen
  unfold hArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  show ((ffi.ByteArray.zeroes 21).copySlice 0 (hArrayAllocMem I) 384 21).size = 405
  rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  rw [show (ffi.ByteArray.zeroes 21).data.size = (ffi.ByteArray.zeroes 21).size from rfl,
    ByteArray_zeroes_size]
  rw [show (hArrayAllocMem I).data.size = (hArrayAllocMem I).size from rfl, hsize]
  omega

theorem hArrayZeroMem_read64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayZeroMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 640) := by
  have hsize : (hArrayAllocMem I).size = 405 := hArrayAllocMem_size I hlen
  unfold hArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 21).copySlice 0 (hArrayAllocMem I) 384 21).readWithPadding
    64 32 = UInt256.toByteArray (UInt256.ofNat 640)
  rw [copySlice_read_below_gen]
  exact hArrayAllocMem_read64 I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem mArrayAllocMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayAllocMem I).size = 405 := by
  unfold mArrayAllocMem
  apply toByteArray_write32_size_of_le
  · exact hArrayZeroMem_size I hlen
  · rw [hArrayZeroMem_size I hlen]
    decide
  · native_decide

theorem mArrayAllocMem_read64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayAllocMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1152) := by
  unfold mArrayAllocMem
  rw [toByteArray_write32_read_back]
  rw [hArrayZeroMem_size I hlen]
  decide

theorem mArrayZeroMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayZeroMem I).size = 405 := by
  have hsize : (mArrayAllocMem I).size = 405 := mArrayAllocMem_size I hlen
  unfold mArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 512 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  show ((ffi.ByteArray.zeroes 0).copySlice 0 (mArrayAllocMem I) 405 0).size = 405
  rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  rw [show (ffi.ByteArray.zeroes 0).data.size = (ffi.ByteArray.zeroes 0).size from rfl,
    ByteArray_zeroes_size]
  rw [show (mArrayAllocMem I).data.size = (mArrayAllocMem I).size from rfl, hsize]
  omega

theorem mArrayZeroMem_read64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayZeroMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1152) := by
  have hsize : (mArrayAllocMem I).size = 405 := mArrayAllocMem_size I hlen
  unfold mArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 512 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (mArrayAllocMem I) 405 0).readWithPadding
    64 32 = UInt256.toByteArray (UInt256.ofNat 1152)
  rw [copySlice_read_below_gen]
  exact mArrayAllocMem_read64 I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem tArrayAllocMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayAllocMem I).size = 405 := by
  unfold tArrayAllocMem
  apply toByteArray_write32_size_of_le
  · exact mArrayZeroMem_size I hlen
  · rw [mArrayZeroMem_size I hlen]
    decide
  · native_decide

theorem tArrayZeroMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayZeroMem I).size = 405 := by
  have hsize : (tArrayAllocMem I).size = 405 := tArrayAllocMem_size I hlen
  unfold tArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 64 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  show ((ffi.ByteArray.zeroes 0).copySlice 0 (tArrayAllocMem I) 405 0).size = 405
  rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  rw [show (ffi.ByteArray.zeroes 0).data.size = (ffi.ByteArray.zeroes 0).size from rfl,
    ByteArray_zeroes_size]
  rw [show (tArrayAllocMem I).data.size = (tArrayAllocMem I).size from rfl, hsize]
  omega

theorem tArrayAllocMem_read64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayAllocMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1216) := by
  unfold tArrayAllocMem
  rw [toByteArray_write32_read_back]
  rw [mArrayZeroMem_size I hlen]
  decide

theorem tArrayZeroMem_read64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayZeroMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1216) := by
  have hsize : (tArrayAllocMem I).size = 405 := tArrayAllocMem_size I hlen
  unfold tArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 64 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (tArrayAllocMem I) 405 0).readWithPadding
    64 32 = UInt256.toByteArray (UInt256.ofNat 1216)
  rw [copySlice_read_below_gen]
  exact tArrayAllocMem_read64 I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide


end Blake2f
