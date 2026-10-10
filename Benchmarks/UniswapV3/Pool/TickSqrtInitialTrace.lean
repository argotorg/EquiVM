import Benchmarks.UniswapV3.Pool.TickSqrtModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickSqrtInitialX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11722⟩ (absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11812⟩
      (tickSqrtStep absTick (tickSqrtInitial absTick)
        (2, 340248342086729790484326174814286782778) :: absTick :: R) mem aw rdata σ k' C' := by
  have hinit : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11760⟩
      (tickSqrtInitial absTick :: ⟨0⟩ :: absTick :: R) mem aw rdata σ k' C' := by
    by_cases hz : UInt256.land absTick ⟨1⟩ = ⟨0⟩
    · have r1 := uniswapV3Pool_block_11722_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) hz rd
      have r2 := uniswapV3Pool_block_11733 (immWords := wordsOf (immStore v))
        (by simp only [uniswapV3Pool_block_11722_fallthrough_stack, List.length_cons]; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      have hshift : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) =
          UInt256.ofNat (2 ^ 128) := by decide
      exact ⟨_, _, by simpa only [uniswapV3Pool_block_11733_stack,
        uniswapV3Pool_block_11722_fallthrough_stack, tickSqrtInitial, if_pos hz,
        hshift] using r2⟩
    · have r1 := uniswapV3Pool_block_11722_taken (immWords := wordsOf (immStore v))
        (by evm_ov) hz (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_11742 (immWords := wordsOf (immStore v))
        (by simp only [uniswapV3Pool_block_11722_taken_stack, List.length_cons]; omega) r1
      exact ⟨_, _, by simpa only [uniswapV3Pool_block_11742_stack,
        uniswapV3Pool_block_11722_taken_stack, tickSqrtInitial, if_neg hz] using r2⟩
  obtain ⟨k', C', rinit⟩ := hinit
  have hclean : UInt256.land (UInt256.ofNat 87112285931760246646623899502532662132735)
      (tickSqrtInitial absTick) = tickSqrtInitial absTick := by
    unfold tickSqrtInitial
    split <;> decide
  by_cases hz : UInt256.land absTick (UInt256.ofNat 2) = ⟨0⟩
  · have out := uniswapV3Pool_block_11760_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rinit
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11760_taken_stack,
      hclean, tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11760_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (isZero_eq_zero_of_ne hz) rinit
    simp only [uniswapV3Pool_block_11760_fallthrough_stack, hclean] at rdCalc
    have out := uniswapV3Pool_block_11791 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11791_stack,
      tickSqrtStep, if_neg hz] using out⟩

end Benchmarks.UniswapV3.Pool
