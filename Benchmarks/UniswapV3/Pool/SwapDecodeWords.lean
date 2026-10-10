import Benchmarks.UniswapV3.Pool.SwapCalldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapDecodedZeroWord (cd : ByteArray) :
    UInt256.isZero (UInt256.isZero (calldataWord cd 36)) =
    (swapDecodedArgs cd).zeroForOne.toUInt256 := by
  by_cases hz : calldataWord cd 36 = (⟨0⟩ : UInt256)
  · simp only [swapDecodedArgs, hz, ne_self_iff_false, decide_false]
    rfl
  · rw [isZero_eq_zero_of_ne hz]
    simp only [swapDecodedArgs, ne_eq, hz, not_false_eq_true, decide_true]
    rfl

end Benchmarks.UniswapV3.Pool
