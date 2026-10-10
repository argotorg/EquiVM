import Benchmarks.UniswapV3.Pool.BurnOwedSource
import Benchmarks.UniswapV3.Pool.PositionUpdateGrowthTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem burnAmountsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw key : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a0 a1 : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9737⟩
      (EVM.wordOfInt a1 :: EVM.wordOfInt a0 :: key ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9770⟩
      ((burnHasAmounts a0 a1).toUInt256 :: EVM.wordOfInt a1 :: EVM.wordOfInt a0 :: key ::
        burnAmount a1 :: burnAmount a0 :: R) mem aw rdata σ k' C' := by
  have hflag : UInt256.gt (UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a0)) (UInt256.ofNat 0) =
      (decide (0 < (burnAmount a0).toNat)).toUInt256 := gtZero_wordPositive (burnAmount a0)
  by_cases hp : 0 < (burnAmount a0).toNat
  · have hhas : burnHasAmounts a0 a1 = true := by
      simp only [burnHasAmounts, decide_eq_true hp, Bool.true_or]
    have r1 := uniswapV3Pool_block_9737_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hflag, decide_eq_true hp]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_9737_taken_stack, hflag, decide_eq_true hp] at r1
    exact ⟨_, _, by simpa only [hhas, burnAmount] using r1⟩
  · have r1 := uniswapV3Pool_block_9737_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hflag, decide_eq_false hp]; rfl) rd
    simp only [uniswapV3Pool_block_9737_fallthrough_stack] at r1
    have r2 := uniswapV3Pool_block_9765 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 6 ≤ 1024; omega) r1
    have hhas : burnHasAmounts a0 a1 = decide (0 < (burnAmount a1).toNat) := by
      simp only [burnHasAmounts, decide_eq_false hp, Bool.false_or]
    simpa only [uniswapV3Pool_block_9765_stack, gtZero_wordPositive, hhas, burnAmount] using
      (show ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9770⟩
        (uniswapV3Pool_block_9765_stack (x1 := EVM.wordOfInt a1) (x2 := EVM.wordOfInt a0)
          (x3 := key) (x4 := burnAmount a1) (R := burnAmount a0 :: R))
        mem aw rdata σ k' C' from ⟨_, _, r2⟩)

end Benchmarks.UniswapV3.Pool
