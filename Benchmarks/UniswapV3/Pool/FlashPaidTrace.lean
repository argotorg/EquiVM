import Benchmarks.UniswapV3.Pool.FlashGrowthTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashPaidX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw after1 after0 before1 before0 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7139⟩ (after1 :: after0 :: before1 :: before0 :: R)
      mem aw rdata σ k C) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0
      (if UInt256.sub after0 before0 = ⟨0⟩ then flashUpdateExit false else flashProtocolEntry false)
      (UInt256.sub after1 before1 :: UInt256.sub after0 before0 ::
        after1 :: after0 :: before1 :: before0 :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.sub after0 before0 = ⟨0⟩
  · rw [if_pos hz]
    exact ⟨_, _, uniswapV3Pool_block_7139_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hz]; decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
  · rw [if_neg hz]
    exact ⟨_, _, uniswapV3Pool_block_7139_fallthrough (immWords := wordsOf (immStore v)) hov
      (isZero_eq_zero_of_ne hz) rd⟩

theorem flashSecondGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw paid1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7282⟩ (paid1 :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0
      (if paid1 = ⟨0⟩ then flashUpdateExit true else flashProtocolEntry true)
      (paid1 :: R) mem aw rdata σ k' C' := by
  by_cases hz : paid1 = ⟨0⟩
  · rw [if_pos hz]
    exact ⟨_, _, uniswapV3Pool_block_7282_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hz]; decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
  · rw [if_neg hz]
    exact ⟨_, _, uniswapV3Pool_block_7282_fallthrough (immWords := wordsOf (immStore v)) hov
      (isZero_eq_zero_of_ne hz) rd⟩

end Benchmarks.UniswapV3.Pool
