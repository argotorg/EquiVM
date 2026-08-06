import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Compression.Read64

/-!
# BLAKE2F compression memory lemmas: return-buffer sizes
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem returnAllocMem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (returnAllocMem mem).size = 1984 := by
  unfold returnAllocMem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem returnLengthMem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (returnLengthMem mem).size = 2016 := by
  unfold returnLengthMem
  apply toByteArray_write32_size_of_ge
  · exact returnAllocMem_size hmem
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem returnZeroPadMem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnZeroPadMem I mem).size = 2016 := by
  unfold returnZeroPadMem ByteArray.write
  simp [hlen, returnLengthMem_size hmem]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (returnLengthMem mem) 2016 0).size = 2016
  rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  rw [show (ffi.ByteArray.zeroes 0).data.size = (ffi.ByteArray.zeroes 0).size from rfl,
    ByteArray_zeroes_size]
  rw [show (returnLengthMem mem).data.size = (returnLengthMem mem).size from rfl,
    returnLengthMem_size hmem]
  omega

theorem returnLoopWord0Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord0Mem I mem).size = 2048 := by
  unfold returnLoopWord0Mem
  apply toByteArray_write32_size_of_ge
  · exact returnZeroPadMem_size I hlen hmem
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem returnLoopWord1Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord1Mem I mem).size = 2056 := by
  unfold returnLoopWord1Mem
  apply toByteArray_write32_size_of_le
  · exact returnLoopWord0Mem_size I hlen hmem
  · rw [returnLoopWord0Mem_size I hlen hmem]
    decide
  · native_decide

theorem returnLoopWord2Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord2Mem I mem).size = 2064 := by
  unfold returnLoopWord2Mem
  apply toByteArray_write32_size_of_le
  · exact returnLoopWord1Mem_size I hlen hmem
  · rw [returnLoopWord1Mem_size I hlen hmem]
    decide
  · native_decide

theorem returnLoopWord3Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord3Mem I mem).size = 2072 := by
  unfold returnLoopWord3Mem
  apply toByteArray_write32_size_of_le
  · exact returnLoopWord2Mem_size I hlen hmem
  · rw [returnLoopWord2Mem_size I hlen hmem]
    decide
  · native_decide

theorem returnLoopWord4Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord4Mem I mem).size = 2080 := by
  unfold returnLoopWord4Mem
  apply toByteArray_write32_size_of_le
  · exact returnLoopWord3Mem_size I hlen hmem
  · rw [returnLoopWord3Mem_size I hlen hmem]
    decide
  · native_decide

theorem returnLoopWord5Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord5Mem I mem).size = 2088 := by
  unfold returnLoopWord5Mem
  apply toByteArray_write32_size_of_le
  · exact returnLoopWord4Mem_size I hlen hmem
  · rw [returnLoopWord4Mem_size I hlen hmem]
    decide
  · native_decide

theorem returnLoopWord6Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord6Mem I mem).size = 2096 := by
  unfold returnLoopWord6Mem
  apply toByteArray_write32_size_of_le
  · exact returnLoopWord5Mem_size I hlen hmem
  · rw [returnLoopWord5Mem_size I hlen hmem]
    decide
  · native_decide

theorem returnLoopWord7Mem_size
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord7Mem I mem).size = 2104 := by
  unfold returnLoopWord7Mem
  apply toByteArray_write32_size_of_le
  · exact returnLoopWord6Mem_size I hlen hmem
  · rw [returnLoopWord6Mem_size I hlen hmem]
    decide
  · native_decide

end Blake2f
