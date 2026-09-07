import Examples.UniswapV2Pair.SwapRecipientRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapRuntimeCallbackBranchCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw token1 token0 scratch1 scratch0 reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨1904⟩ (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hov : R.length + 18 ≤ 1024) :
    (dataLen = ⟨0⟩ ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2091⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C') ∨
    (dataLen ≠ ⟨0⟩ ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1911⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem aw rdata acc k' C') := by
  have rdGuard := evm_run rd with [jumpdest, dup7, iszero, push2 ⟨2091⟩]
  by_cases hz : dataLen = ⟨0⟩
  · rw [hz] at rdGuard
    have rdRet := evm_run rdGuard with [jumpiT (by decide) (by jump_dest)]
    exact Or.inl ⟨hz, _, _, by simpa only [hz] using rdRet⟩
  · rw [isZero_eq_zero_of_ne hz] at rdGuard
    have rdEntry := evm_run rdGuard with [jumpiNT (by decide)]
    exact Or.inr ⟨hz, _, _, rdEntry⟩


end UniswapV2Pair
