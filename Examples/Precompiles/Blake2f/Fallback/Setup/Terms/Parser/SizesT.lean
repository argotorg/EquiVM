import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Parser.SizesM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem t0StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t0StoredMem I).size = 1184 := by
  unfold t0StoredMem
  apply toByteArray_write32_size_of_le
  · exact m15StoredMem_size I hlen
  · rw [m15StoredMem_size I hlen]
  · native_decide

theorem t1StoredMem_size (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).size = 1216 := by
  unfold t1StoredMem
  apply toByteArray_write32_size_of_le
  · exact t0StoredMem_size I hlen
  · rw [t0StoredMem_size I hlen]
  · native_decide

end Blake2f
