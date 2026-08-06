import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Compression.VSizes

/-!
# BLAKE2F compression memory lemmas: mixed/output sizes
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem v12MixedMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v12MixedMem I).size = 1984 := by
  unfold v12MixedMem
  apply toByteArray_write32_size_of_le
  · exact v15InitMem_size I hlen
  · rw [v15InitMem_size I hlen]
    decide
  · native_decide

theorem v13MixedMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).size = 1984 := by
  unfold v13MixedMem
  apply toByteArray_write32_size_of_le
  · exact v12MixedMem_size I hlen
  · rw [v12MixedMem_size I hlen]
    decide
  · native_decide

theorem v14FinalFlagMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).size = 1984 := by
  unfold v14FinalFlagMem
  apply toByteArray_write32_size_of_le
  · exact v13MixedMem_size I hlen
  · rw [v13MixedMem_size I hlen]
    decide
  · native_decide

theorem outputWord0Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord0Mem mem).size = 1984 := by
  unfold outputWord0Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem outputWord1Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord1Mem mem).size = 1984 := by
  unfold outputWord1Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem outputWord2Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord2Mem mem).size = 1984 := by
  unfold outputWord2Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem outputWord3Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord3Mem mem).size = 1984 := by
  unfold outputWord3Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem outputWord4Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord4Mem mem).size = 1984 := by
  unfold outputWord4Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem outputWord5Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord5Mem mem).size = 1984 := by
  unfold outputWord5Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem outputWord6Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord6Mem mem).size = 1984 := by
  unfold outputWord6Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem outputWord7Mem_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (outputWord7Mem mem).size = 1984 := by
  unfold outputWord7Mem
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

end Blake2f
