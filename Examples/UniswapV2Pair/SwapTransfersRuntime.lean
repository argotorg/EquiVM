import Examples.UniswapV2Pair.SwapRecipientRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapRuntimeFirstTransferCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw token1 token0 scratch1 scratch0 reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨1870⟩ (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hov : R.length + 18 ≤ 1024) :
    (amount0Out = ⟨0⟩ ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1887⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C') ∨
    (amount0Out ≠ ⟨0⟩ ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6370⟩
      (amount0Out :: toWord :: token0 :: ⟨1887⟩ :: token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem aw rdata acc k' C') := by
  have rdGuard := evm_run rd with [jumpdest, dup11, iszero, push2 ⟨1887⟩]
  by_cases hz : amount0Out = ⟨0⟩
  · rw [hz] at rdGuard
    have rdRet := evm_run rdGuard with [jumpiT (by decide) (by jump_dest)]
    exact Or.inl ⟨hz, _, _, by simpa only [hz] using rdRet⟩
  · rw [isZero_eq_zero_of_ne hz] at rdGuard
    have rdEntry := evm_run rdGuard with [jumpiNT (by decide), push2 ⟨1887⟩,
      dup3, dup11, dup14, push2 ⟨6370⟩, jump (by jump_dest)]
    exact Or.inr ⟨hz, _, _, rdEntry⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSwapRuntimeSecondTransferCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw token1 token0 scratch1 scratch0 reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨1887⟩ (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hov : R.length + 18 ≤ 1024) :
    (amount1Out = ⟨0⟩ ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1904⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C') ∨
    (amount1Out ≠ ⟨0⟩ ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6370⟩
      (amount1Out :: toWord :: token1 :: ⟨1904⟩ :: token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem aw rdata acc k' C') := by
  have rdGuard := evm_run rd with [jumpdest, dup10, iszero, push2 ⟨1904⟩]
  by_cases hz : amount1Out = ⟨0⟩
  · rw [hz] at rdGuard
    have rdRet := evm_run rdGuard with [jumpiT (by decide) (by jump_dest)]
    exact Or.inl ⟨hz, _, _, by simpa only [hz] using rdRet⟩
  · rw [isZero_eq_zero_of_ne hz] at rdGuard
    have rdEntry := evm_run rdGuard with [jumpiNT (by decide), push2 ⟨1904⟩,
      dup2, dup11, dup13, push2 ⟨6370⟩, jump (by jump_dest)]
    exact Or.inr ⟨hz, _, _, rdEntry⟩

end UniswapV2Pair
