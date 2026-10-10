import Benchmarks.UniswapV4PoolManager.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a fixed-size allocation fits both the word and a chosen capacity.
theorem fixedAllocationGuard (ptr limit : UInt256) (size : Nat)
    (hf : ptr.toNat+size ≤ limit.toNat) :
    UInt256.lor (UInt256.gt (ptr+UInt256.ofNat size) limit)
      (UInt256.lt (ptr+UInt256.ofNat size) ptr) = ⟨0⟩ := by
  have hn := uadd_word_ofNat_toNat ptr size (lt_of_le_of_lt hf limit.val.isLt)
  rw [ugt_zero (by rw [hn]; exact hf), ult_zero (by rw [hn]; omega)]
  rfl

end Benchmarks.UniswapV4PoolManager
