import Benchmarks.UniswapV3.Pool.BitLsbModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_034
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_058
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_059

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitLsbFirstX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw junk : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (x : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨17782⟩ (junk :: x :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨17817⟩
      (UInt256.ofNat (bitLsbStep (255, x) 128).1 :: (bitLsbStep (255, x) 128).2 :: R)
        mem aw rdata σ k' C' := by
  by_cases h : 0 < (bitLsbLow x 128).toNat
  · have hc : UInt256.isZero (bitLsbLow x 128) = ⟨0⟩ := by
      apply isZero_eq_zero_of_ne
      intro hz
      rw [hz] at h
      exact Nat.not_lt_zero _ h
    have r1 := uniswapV3Pool_block_17782_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128]; exact hc) rd
    have r2 := uniswapV3Pool_block_17801 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simpa only [bitLsbStep, if_pos h, uniswapV3Pool_block_17801_stack,
      uniswapV3Pool_block_17782_fallthrough_stack,
      wordLnot_add_nat (n := 255) (bits := 128) (by decide) (by decide) (by decide)] using RD.pack r2
  · have hz : bitLsbLow x 128 = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
    have hc : UInt256.isZero (bitLsbLow x 128) ≠ ⟨0⟩ := by rw [hz]; decide
    have r1 := uniswapV3Pool_block_17782_taken (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128]; exact hc)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_17809 (immWords := wordsOf (immStore v)) (by evm_ov) r1
    simpa only [bitLsbStep, if_neg h, uniswapV3Pool_block_17809_stack,
      uniswapV3Pool_block_17782_taken_stack] using RD.pack r2

theorem bitLsbLastX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (state : Nat × UInt256)
    (hb : state.1 < 256) (hle : 1 ≤ state.1)
    (rd : RD (deployedRuntime v) ee g s0 ⟨17984⟩
      (UInt256.ofNat state.1 :: state.2 :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (bitLsbStep state 1).1 :: R) mem aw rdata σ k' C' := by
  by_cases h : 0 < (bitLsbLow state.2 1).toNat
  · have hc : UInt256.isZero (bitLsbLow state.2 1) = ⟨0⟩ := by
      apply isZero_eq_zero_of_ne
      intro hz
      rw [hz] at h
      exact Nat.not_lt_zero _ h
    have r1 := uniswapV3Pool_block_17984_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hc rd
    have r2 := uniswapV3Pool_block_17994 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r1
    simpa only [bitLsbStep, if_pos h, uniswapV3Pool_block_17994_stack,
      wordLnot_add_nat (by decide) hle (lt_trans hb (by decide))] using RD.pack r2
  · have hz : bitLsbLow state.2 1 = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
    have hc : UInt256.isZero (bitLsbLow state.2 1) ≠ ⟨0⟩ := by rw [hz]; decide
    have r1 := uniswapV3Pool_block_17984_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_11243 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r1
    simpa only [bitLsbStep, if_neg h] using RD.pack r2

end Benchmarks.UniswapV3.Pool
