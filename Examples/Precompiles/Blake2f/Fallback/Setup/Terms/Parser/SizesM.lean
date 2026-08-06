import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Parser.SizesH

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem m0StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m0StoredMem I).size = 672 := by
  unfold m0StoredMem
  apply toByteArray_write32_size_of_le
  · exact h7StoredMem_size I hlen
  · rw [h7StoredMem_size I hlen]
  · native_decide

theorem m1StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m1StoredMem I).size = 704 := by
  unfold m1StoredMem
  apply toByteArray_write32_size_of_le
  · exact m0StoredMem_size I hlen
  · rw [m0StoredMem_size I hlen]
  · native_decide

theorem m2StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m2StoredMem I).size = 736 := by
  unfold m2StoredMem
  apply toByteArray_write32_size_of_le
  · exact m1StoredMem_size I hlen
  · rw [m1StoredMem_size I hlen]
  · native_decide

theorem m3StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m3StoredMem I).size = 768 := by
  unfold m3StoredMem
  apply toByteArray_write32_size_of_le
  · exact m2StoredMem_size I hlen
  · rw [m2StoredMem_size I hlen]
  · native_decide

theorem m4StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m4StoredMem I).size = 800 := by
  unfold m4StoredMem
  apply toByteArray_write32_size_of_le
  · exact m3StoredMem_size I hlen
  · rw [m3StoredMem_size I hlen]
  · native_decide

theorem m5StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m5StoredMem I).size = 832 := by
  unfold m5StoredMem
  apply toByteArray_write32_size_of_le
  · exact m4StoredMem_size I hlen
  · rw [m4StoredMem_size I hlen]
  · native_decide

theorem m6StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m6StoredMem I).size = 864 := by
  unfold m6StoredMem
  apply toByteArray_write32_size_of_le
  · exact m5StoredMem_size I hlen
  · rw [m5StoredMem_size I hlen]
  · native_decide

theorem m7StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m7StoredMem I).size = 896 := by
  unfold m7StoredMem
  apply toByteArray_write32_size_of_le
  · exact m6StoredMem_size I hlen
  · rw [m6StoredMem_size I hlen]
  · native_decide

theorem m8StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m8StoredMem I).size = 928 := by
  unfold m8StoredMem
  apply toByteArray_write32_size_of_le
  · exact m7StoredMem_size I hlen
  · rw [m7StoredMem_size I hlen]
  · native_decide

theorem m9StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m9StoredMem I).size = 960 := by
  unfold m9StoredMem
  apply toByteArray_write32_size_of_le
  · exact m8StoredMem_size I hlen
  · rw [m8StoredMem_size I hlen]
  · native_decide

theorem m10StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m10StoredMem I).size = 992 := by
  unfold m10StoredMem
  apply toByteArray_write32_size_of_le
  · exact m9StoredMem_size I hlen
  · rw [m9StoredMem_size I hlen]
  · native_decide

theorem m11StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m11StoredMem I).size = 1024 := by
  unfold m11StoredMem
  apply toByteArray_write32_size_of_le
  · exact m10StoredMem_size I hlen
  · rw [m10StoredMem_size I hlen]
  · native_decide

theorem m12StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m12StoredMem I).size = 1056 := by
  unfold m12StoredMem
  apply toByteArray_write32_size_of_le
  · exact m11StoredMem_size I hlen
  · rw [m11StoredMem_size I hlen]
  · native_decide

theorem m13StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m13StoredMem I).size = 1088 := by
  unfold m13StoredMem
  apply toByteArray_write32_size_of_le
  · exact m12StoredMem_size I hlen
  · rw [m12StoredMem_size I hlen]
  · native_decide

theorem m14StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m14StoredMem I).size = 1120 := by
  unfold m14StoredMem
  apply toByteArray_write32_size_of_le
  · exact m13StoredMem_size I hlen
  · rw [m13StoredMem_size I hlen]
  · native_decide

theorem m15StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m15StoredMem I).size = 1152 := by
  unfold m15StoredMem
  apply toByteArray_write32_size_of_le
  · exact m14StoredMem_size I hlen
  · rw [m14StoredMem_size I hlen]
  · native_decide


end Blake2f
