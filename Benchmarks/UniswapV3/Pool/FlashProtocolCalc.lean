import Benchmarks.UniswapV3.Pool.FlashProtocolWords
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_024
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_025

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashProtocolEntry (second : Bool) : UInt256 := if second then ⟨7289⟩ else ⟨7152⟩
def flashProtocolStoreEntry (second : Bool) : UInt256 := if second then ⟨7333⟩ else ⟨7193⟩
def flashGrowthEntry (second : Bool) : UInt256 := if second then ⟨7383⟩ else ⟨7244⟩

theorem flashProtocolCalcX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw paid0 paid1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (flashProtocolEntry second) (paid1 :: paid0 :: R)
      mem aw rdata σ k C) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (flashProtocolStoreEntry second)
      (poolProtocolFees (if second then paid1 else paid0) (poolProtocolDivisor second σ ee) ::
        ⟨0⟩ :: poolProtocolDivisor second σ ee :: paid1 :: paid0 :: R) mem aw rdata σ k' C' := by
  cases second
  · by_cases hz : poolProtocolDivisor false σ ee = ⟨0⟩
    · obtain ⟨_, _, rdZero⟩ := uniswapV3Pool_block_7152_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by change UInt256.isZero (poolProtocolDivisor false σ ee) ≠ _; rw [hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_7152_taken_stack] at rdZero
      have rdNext := uniswapV3Pool_block_7190 (immWords := wordsOf (immStore v)) (by evm_ov) rdZero
      simpa only [poolProtocolFees, hz, ↓reduceIte] using
        (show ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7193⟩
          (⟨0⟩ :: ⟨0⟩ :: poolProtocolDivisor false σ ee :: paid1 :: paid0 :: R)
          mem aw rdata σ k' C' from ⟨_, _, rdNext⟩)
    · obtain ⟨_, _, rdNonzero⟩ := uniswapV3Pool_block_7152_fallthrough
        (immWords := wordsOf (immStore v)) (by evm_ov) (isZero_eq_zero_of_ne hz) rd
      change RD _ _ _ _ _ (⟨0⟩ :: poolProtocolDivisor false σ ee :: paid1 :: paid0 :: R)
        _ _ _ _ _ _ at rdNonzero
      have rdDiv := uniswapV3Pool_block_7173_taken (immWords := wordsOf (immStore v)) hov
        (by rw [poolProtocolDivisor_clean]; exact hz)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdNonzero
      simp only [uniswapV3Pool_block_7173_taken_stack, poolProtocolDivisor_clean] at rdDiv
      have rdNext := uniswapV3Pool_block_7184 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDiv
      exact ⟨_, _, by simpa only [flashProtocolStoreEntry, poolProtocolFees, if_neg hz,
        ↓reduceIte] using rdNext⟩
  · by_cases hz : poolProtocolDivisor true σ ee = ⟨0⟩
    · obtain ⟨_, _, rdZero⟩ := uniswapV3Pool_block_7289_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by change UInt256.isZero (poolProtocolDivisor true σ ee) ≠ _; rw [hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_7289_taken_stack] at rdZero
      have rdNext := uniswapV3Pool_block_7330 (immWords := wordsOf (immStore v)) (by evm_ov) rdZero
      simpa only [poolProtocolFees, hz, ↓reduceIte] using
        (show ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7333⟩
          (⟨0⟩ :: ⟨0⟩ :: poolProtocolDivisor true σ ee :: paid1 :: paid0 :: R)
          mem aw rdata σ k' C' from ⟨_, _, rdNext⟩)
    · obtain ⟨_, _, rdNonzero⟩ := uniswapV3Pool_block_7289_fallthrough
        (immWords := wordsOf (immStore v)) (by evm_ov) (isZero_eq_zero_of_ne hz) rd
      change RD _ _ _ _ _ (⟨0⟩ :: poolProtocolDivisor true σ ee :: paid1 :: paid0 :: R)
        _ _ _ _ _ _ at rdNonzero
      have rdDiv := uniswapV3Pool_block_7313_taken (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [poolProtocolDivisor_clean]; exact hz)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdNonzero
      simp only [uniswapV3Pool_block_7313_taken_stack, poolProtocolDivisor_clean] at rdDiv
      have rdNext := uniswapV3Pool_block_7324 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDiv
      exact ⟨_, _, by simpa only [flashProtocolStoreEntry, poolProtocolFees, if_neg hz,
        ↓reduceIte] using rdNext⟩

end Benchmarks.UniswapV3.Pool
