import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Compression.Allocation

/-!
# BLAKE2F compression memory lemmas: vector initialization sizes
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem v0InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v0InitMem I).size = 1504 := by
  unfold v0InitMem
  rw [toByteArray_write_eq _ _ _ (by
      rw [compressionVAllocMem_size I hlen]
      decide)
    (by
      rw [compressionVAllocMem_size I hlen]
      exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, compressionVAllocMem_size I hlen,
    ByteArray_zeroes_size, toByteArray_size]

theorem v1InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v1InitMem I).size = 1536 := by
  unfold v1InitMem
  apply toByteArray_write32_size_of_ge
  · exact v0InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v2InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v2InitMem I).size = 1568 := by
  unfold v2InitMem
  apply toByteArray_write32_size_of_ge
  · exact v1InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v3InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v3InitMem I).size = 1600 := by
  unfold v3InitMem
  apply toByteArray_write32_size_of_ge
  · exact v2InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v4InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v4InitMem I).size = 1632 := by
  unfold v4InitMem
  apply toByteArray_write32_size_of_ge
  · exact v3InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v5InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v5InitMem I).size = 1664 := by
  unfold v5InitMem
  apply toByteArray_write32_size_of_ge
  · exact v4InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v6InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v6InitMem I).size = 1696 := by
  unfold v6InitMem
  apply toByteArray_write32_size_of_ge
  · exact v5InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v7InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v7InitMem I).size = 1728 := by
  unfold v7InitMem
  apply toByteArray_write32_size_of_ge
  · exact v6InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v8InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v8InitMem I).size = 1760 := by
  unfold v8InitMem
  apply toByteArray_write32_size_of_ge
  · exact v7InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v9InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v9InitMem I).size = 1792 := by
  unfold v9InitMem
  apply toByteArray_write32_size_of_ge
  · exact v8InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v10InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v10InitMem I).size = 1824 := by
  unfold v10InitMem
  apply toByteArray_write32_size_of_ge
  · exact v9InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v11InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v11InitMem I).size = 1856 := by
  unfold v11InitMem
  apply toByteArray_write32_size_of_ge
  · exact v10InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v12InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v12InitMem I).size = 1888 := by
  unfold v12InitMem
  apply toByteArray_write32_size_of_ge
  · exact v11InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v13InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13InitMem I).size = 1920 := by
  unfold v13InitMem
  apply toByteArray_write32_size_of_ge
  · exact v12InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v14InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14InitMem I).size = 1952 := by
  unfold v14InitMem
  apply toByteArray_write32_size_of_ge
  · exact v13InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

theorem v15InitMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v15InitMem I).size = 1984 := by
  unfold v15InitMem
  apply toByteArray_write32_size_of_ge
  · exact v14InitMem_size I hlen
  · decide
  · change 0 < USize.size
    exact lt_usize 0 (by norm_num)
  · decide

end Blake2f
