import Benchmarks.UniswapV4PoolManager.BalanceDeltaSubTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_040

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterLiquidityFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw delta hookDelta ret : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+11 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14631⟩
      (hookDelta :: UInt256.ofNat 14638 :: delta :: ret :: R) mem aw rdata evm.accountMap k C) :
    if balanceDeltaCombineFits true delta hookDelta then
      ∃ k' C', RD (deployedRuntime v) I g s0 ret
        (hookDelta :: balanceDeltaCombineWord true delta hookDelta :: R) mem aw rdata evm.accountMap k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := poolManager_block_14631 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := balanceDeltaSubTrace (R := hookDelta :: ret :: R) f v
    (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  by_cases hfit : balanceDeltaCombineFits true delta hookDelta
  · rw [balanceDeltaCombineResult, if_pos hfit] at hr
    rw [if_pos hfit]
    obtain ⟨_, _, k2, C2, rd2⟩ := hr
    have rd3 := poolManager_block_14638 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := poolManager_block_14489 (by simp only [List.length_cons]; omega) hret rd3
    exact ⟨_, _, rd4⟩
  · rw [balanceDeltaCombineResult, if_neg hfit] at hr
    rw [if_neg hfit]
    exact hr

end Benchmarks.UniswapV4PoolManager
