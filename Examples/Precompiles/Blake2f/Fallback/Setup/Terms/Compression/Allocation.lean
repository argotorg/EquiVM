import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Compression.Base

/-!
# BLAKE2F compression memory lemmas: scratch/vector allocation
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem compressionScratchAllocMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (compressionScratchAllocMem I).size = 1216 := by
  unfold compressionScratchAllocMem
  apply toByteArray_write32_size_of_le
  · exact t1StoredMem_size I hlen
  · rw [t1StoredMem_size I hlen]
    decide
  · native_decide

theorem compressionScratchAllocMem_read64
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (compressionScratchAllocMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1472) := by
  unfold compressionScratchAllocMem
  rw [toByteArray_write32_read_back]
  rw [t1StoredMem_size I hlen]
  decide

theorem compressionScratchZeroMem_read64
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (compressionScratchZeroMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1472) := by
  have hsize : (compressionScratchAllocMem I).size = 1216 :=
    compressionScratchAllocMem_size I hlen
  unfold compressionScratchZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (compressionScratchAllocMem I) 1216 0).readWithPadding
      64 32 = UInt256.toByteArray (UInt256.ofNat 1472)
  rw [copySlice_read_below_gen]
  exact compressionScratchAllocMem_read64 I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem compressionScratchZeroMem_size
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (compressionScratchZeroMem I).size = 1216 := by
  have hsize : (compressionScratchAllocMem I).size = 1216 :=
    compressionScratchAllocMem_size I hlen
  unfold compressionScratchZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (compressionScratchAllocMem I) 1216 0).size =
    1216
  rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  rw [show (ffi.ByteArray.zeroes 0).data.size = (ffi.ByteArray.zeroes 0).size from rfl,
    ByteArray_zeroes_size]
  rw [show (compressionScratchAllocMem I).data.size =
    (compressionScratchAllocMem I).size from rfl, hsize]
  omega

theorem compressionVAllocMem_read64
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (compressionVAllocMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold compressionVAllocMem
  rw [toByteArray_write32_read_back]
  rw [compressionScratchZeroMem_size I hlen]
  decide

theorem compressionVAllocMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (compressionVAllocMem I).size = 1216 := by
  unfold compressionVAllocMem
  apply toByteArray_write32_size_of_le
  · exact compressionScratchZeroMem_size I hlen
  · rw [compressionScratchZeroMem_size I hlen]
    decide
  · native_decide

end Blake2f
