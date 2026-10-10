import Benchmarks.UniswapV4PoolManager.SignedArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: SGT compares the mathematical signed interpretations.
theorem sgt_signed (a b : UInt256) :
    UInt256.sgt a b = UInt256.fromBool (decide (EVM.signed b < EVM.signed a)) := by
  have hswap : UInt256.sgt a b = UInt256.slt b a := by
    unfold UInt256.sgt UInt256.sgtBool UInt256.slt UInt256.sltBool
    split_ifs <;> rfl
  rw [hswap, slt_signed]

end Benchmarks.UniswapV4PoolManager
