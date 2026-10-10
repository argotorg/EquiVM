import Benchmarks.UniswapV3.Pool.TickLogBoundsTrace
import Benchmarks.UniswapV3.Pool.TickSqrtTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_048

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickLogChooseX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw log price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14758⟩
      (tickSqrtRaw (tickLogHigh log) :: price :: tickLogHighRaw log :: tickLogLowRaw log :: R)
      mem aw rdata σ k C)
    (he : tickLogLow log ≠ tickLogHigh log) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14788⟩
      (tickLogChoiceRaw log price :: tickLogHighRaw log :: tickLogLowRaw log :: R)
      mem aw rdata σ k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by decide
  have hsqrt : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (tickSqrtRaw (tickLogHigh log)) =
      tickSqrtValue (tickLogHigh log) := by
    rw [u256_land_comm]
    rfl
  by_cases h : (tickSqrtValue (tickLogHigh log)).toNat ≤ price.toNat
  · have hgt : UInt256.gt (tickSqrtValue (tickLogHigh log)) price = ⟨0⟩ := ugt_zero h
    have rcmp := uniswapV3Pool_block_14758_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hmask, hsqrt, hgt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have rchoose := uniswapV3Pool_block_14779 (immWords := wordsOf (immStore v))
      (by evm_ov) rcmp
    have out := uniswapV3Pool_block_14781 (immWords := wordsOf (immStore v))
      (by simp only [uniswapV3Pool_block_14779_stack,
        uniswapV3Pool_block_14758_taken_stack, List.length_cons]; omega) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rchoose
    refine ⟨k + 11 + 2 + 3, C + 38 + 4 + 12, ?_⟩
    simpa only [tickLogChoiceRaw, if_neg he, if_pos h, uniswapV3Pool_block_14779_stack,
      uniswapV3Pool_block_14758_taken_stack] using out
  · have hgt : UInt256.gt (tickSqrtValue (tickLogHigh log)) price = ⟨1⟩ :=
      ugt_one (Nat.lt_of_not_ge h)
    have rcmp := uniswapV3Pool_block_14758_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hmask, hsqrt, hgt]; rfl) rd
    have rchoose := uniswapV3Pool_block_14774 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rcmp
    have out := uniswapV3Pool_block_14781 (immWords := wordsOf (immStore v))
      (by simp only [uniswapV3Pool_block_14774_stack,
        uniswapV3Pool_block_14758_fallthrough_stack, List.length_cons]; omega) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rchoose
    refine ⟨k + 11 + 3 + 3, C + 38 + 14 + 12, ?_⟩
    simpa only [tickLogChoiceRaw, if_neg he, if_neg h, uniswapV3Pool_block_14774_stack,
      uniswapV3Pool_block_14758_fallthrough_stack] using out

end Benchmarks.UniswapV3.Pool
