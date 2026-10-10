import Benchmarks.UniswapV3.Pool.TickSqrtStartTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_039

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickSqrtInvertX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ratio absTick junk tick : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12379⟩
      (ratio :: absTick :: junk :: tick :: R) mem aw rdata σ k C)
    (hn : ratio ≠ ⟨0⟩) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12406⟩
      (tickSqrtInvert (tickSqrtTick tick) ratio :: absTick :: junk :: tick :: R)
      mem aw rdata σ k' C' := by
  have ht : -(2 ^ 23 : Int) ≤ tickSqrtTick tick ∧ tickSqrtTick tick < 2 ^ 23 :=
    normalizeSint_bounds _ _
  have hgt : UInt256.sgt (UInt256.signextend (UInt256.ofNat 2) tick) (UInt256.ofNat 0) =
      if 0 < tickSqrtTick tick then ⟨1⟩ else ⟨0⟩ := by
    rw [sgt_eq_slt_swap,
      signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide),
      show UInt256.ofNat 0 = EVM.wordOfInt 0 from rfl]
    exact slt_wordOfInt 0 (tickSqrtTick tick) (by decide) (by decide) (by omega) (by omega)
  by_cases hp : 0 < tickSqrtTick tick
  · have r1 := uniswapV3Pool_block_12379_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hgt, if_pos hp]; rfl) rd
    have r2 := uniswapV3Pool_block_12392_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hn (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_12392_taken_stack] at r2
    have out := uniswapV3Pool_block_12402 (immWords := wordsOf (immStore v)) (by evm_ov) r2
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12402_stack, tickSqrtInvert, if_pos hp] using out⟩
  · have out := uniswapV3Pool_block_12379_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hgt, if_neg hp]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtInvert, if_neg hp] using out⟩

theorem tickSqrtRoundX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ratio junk0 junk1 junk2 ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12406⟩
      (ratio :: junk0 :: junk1 :: junk2 :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (tickSqrtRound ratio :: R) mem aw rdata σ k' C' := by
  let bit : UInt256 := if UInt256.mod ratio (UInt256.ofNat (2 ^ 32)) = ⟨0⟩ then ⟨0⟩ else ⟨1⟩
  have hb : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12429⟩
      (bit :: ratio :: junk0 :: junk1 :: junk2 :: ret :: R) mem aw rdata σ k' C' := by
    by_cases hz : UInt256.mod ratio (UInt256.ofNat (2 ^ 32)) = ⟨0⟩
    · have r1 := uniswapV3Pool_block_12406_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by
          change UInt256.isZero (UInt256.mod ratio (UInt256.ofNat (2 ^ 32))) ≠ ⟨0⟩
          rw [hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have out := uniswapV3Pool_block_12426 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      exact ⟨_, _, by simpa only [uniswapV3Pool_block_12426_stack, bit, if_pos hz] using out⟩
    · have r1 := uniswapV3Pool_block_12406_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (isZero_eq_zero_of_ne hz) rd
      have out := uniswapV3Pool_block_12420 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨_, _, by simpa only [uniswapV3Pool_block_12420_stack, bit, if_neg hz] using out⟩
  obtain ⟨k', C', rbit⟩ := hb
  have hclean : UInt256.land (UInt256.ofNat 255) bit = bit := by unfold bit; split <;> decide
  have out := uniswapV3Pool_block_12429 (immWords := wordsOf (immStore v)) hov hret rbit
  exact ⟨_, _, by simpa only [uniswapV3Pool_block_12429_stack, hclean, tickSqrtRound, bit] using out⟩

end Benchmarks.UniswapV3.Pool
