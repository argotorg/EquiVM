import Examples.UniswapV2Pair.BurnBeforeTransfersSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeFirstSafeTransferEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw totalSupply feeOn liquidity balance0 balance1
      token0 token1 reserve0 reserve1 amount0 amount1 toWord : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4617 : RD uniswapV2PairBytecode I g s0 ⟨4617⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: toWord :: R) mem aw rdata acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6370⟩
      (amount0 :: toWord :: token0 :: ⟨4628⟩ ::
        totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: toWord :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd4617 with [jumpdest, push2 ⟨4628⟩, dup8, dup14, dup14,
    push2 ⟨6370⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeSecondSafeTransferEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw totalSupply feeOn liquidity balance0 balance1
      token0 token1 reserve0 reserve1 amount0 amount1 toWord : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4628 : RD uniswapV2PairBytecode I g s0 ⟨4628⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: toWord :: R) mem aw rdata acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6370⟩
      (amount1 :: toWord :: token1 :: ⟨4639⟩ ::
        totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: toWord :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd4628 with [jumpdest, push2 ⟨4639⟩, dup7, dup14, dup13,
    push2 ⟨6370⟩, jump (by jump_dest)]⟩

end UniswapV2Pair
