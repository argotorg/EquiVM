import Benchmarks.UniswapV3.Pool.SwapStepRecalcTraceModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_041
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_042

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepInputGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (zero maxFlag inputFlag : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapStepRecalcEntry zero)
      (maxFlag.toUInt256 :: inputFlag.toUInt256 :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (swapStepRecalcGuardPC zero true)
      ((maxFlag && inputFlag).toUInt256 :: maxFlag.toUInt256 :: inputFlag.toUInt256 :: R)
      mem aw rdata σ k' C' := by
  cases maxFlag
  · cases zero
    · have rr := uniswapV3Pool_block_12753_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨_, _, rr⟩
    · have rr := uniswapV3Pool_block_12676_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨_, _, rr⟩
  · cases zero
    · have r1 := uniswapV3Pool_block_12753_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) rfl rd
      have r2 := uniswapV3Pool_block_12761 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      simpa only [Bool.true_and] using RD.pack r2
    · have r1 := uniswapV3Pool_block_12676_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) rfl rd
      have r2 := uniswapV3Pool_block_12683 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      simpa only [Bool.true_and] using RD.pack r2

theorem swapStepOutputGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw newIn oldIn oldOut zeroWord feeWord : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zero maxFlag inputFlag : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapStepRecalcJoinPC zero true)
      (newIn :: maxFlag.toUInt256 :: inputFlag.toUInt256 :: zeroWord :: feeWord ::
        oldOut :: oldIn :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (swapStepRecalcGuardPC zero false)
      ((maxFlag && !inputFlag).toUInt256 :: maxFlag.toUInt256 :: inputFlag.toUInt256 ::
        zeroWord :: feeWord :: oldOut :: newIn :: R) mem aw rdata σ k' C' := by
  have hn : UInt256.isZero inputFlag.toUInt256 = (!inputFlag).toUInt256 := by
    cases inputFlag <;> rfl
  cases maxFlag
  · cases zero
    · have rr := uniswapV3Pool_block_12787_taken (immWords := wordsOf (immStore v))
        hov (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨_, _, rr⟩
    · have rr := uniswapV3Pool_block_12709_taken (immWords := wordsOf (immStore v))
        hov (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨_, _, rr⟩
  · cases zero
    · have r1 := uniswapV3Pool_block_12787_fallthrough (immWords := wordsOf (immStore v))
        hov rfl rd
      have r2 := uniswapV3Pool_block_12797 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      simpa only [Bool.true_and, uniswapV3Pool_block_12797_stack, hn] using RD.pack r2
    · have r1 := uniswapV3Pool_block_12709_fallthrough (immWords := wordsOf (immStore v))
        hov rfl rd
      have r2 := uniswapV3Pool_block_12719 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      simpa only [Bool.true_and, uniswapV3Pool_block_12719_stack, hn] using RD.pack r2

end Benchmarks.UniswapV3.Pool
