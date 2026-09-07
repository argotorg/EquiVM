import Examples.UniswapV2Pair.SwapInvariantRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapUpdateEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw amount1In amount0In balance1 balance0 reserve1 reserve0 : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd2701 : RD uniswapV2PairBytecode I g s0 ⟨2701⟩
      (amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: R) mem aw rdata acc k C)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: ⟨2712⟩ ::
        amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd2701 with [push2 ⟨2712⟩, dup5, dup5, dup9, dup9, push2 ⟨6959⟩, jump (by jump_dest)]⟩

end UniswapV2Pair
