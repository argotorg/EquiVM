import Benchmarks.UniswapV3.Pool.SafeCast256Source
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem safeCast256X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (y : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12945⟩ (y :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ safeCast256Valid y) ∨
      (safeCast256Valid y ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (y :: R) mem aw rdata σ k' C') := by
  classical
  have hb : (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)).toNat = 2 ^ 255 :=
    by native_decide
  by_cases hy : safeCast256Valid y
  · have hc : UInt256.lt y (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) =
        UInt256.ofNat 1 := ult_one (by rw [hb]; exact hy)
    have rr := uniswapV3Pool_block_12945_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hc]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have rout := uniswapV3Pool_block_12963 (immWords := wordsOf (immStore v))
      (by evm_ov) hret rr
    exact Or.inr ⟨hy, _, _, rout⟩
  · have hc : UInt256.lt y (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) =
        UInt256.ofNat 0 := ult_zero (by rw [hb]; exact Nat.le_of_not_gt hy)
    have rr := uniswapV3Pool_block_12945_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hc rd
    simp only [uniswapV3Pool_block_12945_fallthrough_stack] at rr
    exact Or.inl ⟨uniswapV3Pool_block_12959 (immWords := wordsOf (immStore v)) (by evm_ov) rr, hy⟩

end Benchmarks.UniswapV3.Pool
