import Benchmarks.UniswapV3.Pool.FlashTransferSource
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashTransferEntry (second : Bool) : UInt256 := if second then ⟨6778⟩ else ⟨6727⟩
def flashTransferExit (second : Bool) : UInt256 := if second then ⟨6827⟩ else ⟨6778⟩

def flashTransferRest (bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 : UInt256)
    (recipient : AccountAddress) (R : List UInt256) : List UInt256 :=
  bal1 :: bal0 :: fee1 :: fee0 :: liquidity :: len :: start :: amount1 :: amount0 ::
    EVM.word recipient.val :: R

def flashTransferInput (second : Bool) (junk bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 : UInt256)
    (recipient : AccountAddress) (R : List UInt256) : List UInt256 :=
  if second then flashTransferRest bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 recipient R
  else bal1 :: junk :: bal0 :: fee1 :: fee0 :: liquidity :: len :: start :: amount1 :: amount0 ::
    EVM.word recipient.val :: R

theorem flashTransferBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw junk bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 (flashTransferEntry second)
      (flashTransferInput second junk bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 recipient R)
      mem aw rdata σ k C) (hov : R.length + 15 ≤ 1024) :
    ((if second then amount1 else amount0) = ⟨0⟩ ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 (flashTransferExit second)
        (flashTransferRest bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 recipient R)
        mem aw rdata σ k' C') ∨
    ((if second then amount1 else amount0) ≠ ⟨0⟩ ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨15238⟩
        ((if second then amount1 else amount0) :: EVM.word recipient.val ::
          EVM.word (poolToken v second).val :: flashTransferExit second ::
          flashTransferRest bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 recipient R)
        mem aw rdata σ k' C') := by
  cases second
  · by_cases hz : amount0 = ⟨0⟩
    · have rdSkip := uniswapV3Pool_block_6727_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hz]; decide +kernel)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact Or.inl ⟨hz, _, _, rdSkip⟩
    · have rdGuard := uniswapV3Pool_block_6727_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by exact isZero_eq_zero_of_ne hz) rd
      have rdCall := uniswapV3Pool_block_6736 (immWords := wordsOf (immStore v)) hov
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdGuard
      simp only [uniswapV3Pool_block_6736_stack, wordsOf_immStore_token0] at rdCall
      exact Or.inr ⟨hz, _, _, rdCall⟩
  · by_cases hz : amount1 = ⟨0⟩
    · have rdSkip := uniswapV3Pool_block_6778_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hz]; decide +kernel)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact Or.inl ⟨hz, _, _, rdSkip⟩
    · have rdGuard := uniswapV3Pool_block_6778_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by exact isZero_eq_zero_of_ne hz) rd
      have rdCall := uniswapV3Pool_block_6785 (immWords := wordsOf (immStore v)) hov
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdGuard
      simp only [uniswapV3Pool_block_6785_stack, wordsOf_immStore_token1] at rdCall
      exact Or.inr ⟨hz, _, _, rdCall⟩

end Benchmarks.UniswapV3.Pool
