import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Parser.Arrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem h0StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h0StoredMem I).size = 416 := by
  unfold h0StoredMem
  apply toByteArray_write32_size_of_le
  · exact tArrayZeroMem_size I hlen
  · rw [tArrayZeroMem_size I hlen]
    decide
  · native_decide

theorem h1StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h1StoredMem I).size = 448 := by
  unfold h1StoredMem
  apply toByteArray_write32_size_of_le
  · exact h0StoredMem_size I hlen
  · rw [h0StoredMem_size I hlen]
  · native_decide

theorem h2StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h2StoredMem I).size = 480 := by
  unfold h2StoredMem
  apply toByteArray_write32_size_of_le
  · exact h1StoredMem_size I hlen
  · rw [h1StoredMem_size I hlen]
  · native_decide

theorem h3StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h3StoredMem I).size = 512 := by
  unfold h3StoredMem
  apply toByteArray_write32_size_of_le
  · exact h2StoredMem_size I hlen
  · rw [h2StoredMem_size I hlen]
  · native_decide

theorem h4StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h4StoredMem I).size = 544 := by
  unfold h4StoredMem
  apply toByteArray_write32_size_of_le
  · exact h3StoredMem_size I hlen
  · rw [h3StoredMem_size I hlen]
  · native_decide

theorem h5StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h5StoredMem I).size = 576 := by
  unfold h5StoredMem
  apply toByteArray_write32_size_of_le
  · exact h4StoredMem_size I hlen
  · rw [h4StoredMem_size I hlen]
  · native_decide

theorem h6StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h6StoredMem I).size = 608 := by
  unfold h6StoredMem
  apply toByteArray_write32_size_of_le
  · exact h5StoredMem_size I hlen
  · rw [h5StoredMem_size I hlen]
  · native_decide

theorem h7StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (h7StoredMem I).size = 640 := by
  unfold h7StoredMem
  apply toByteArray_write32_size_of_le
  · exact h6StoredMem_size I hlen
  · rw [h6StoredMem_size I hlen]
  · native_decide


end Blake2f
