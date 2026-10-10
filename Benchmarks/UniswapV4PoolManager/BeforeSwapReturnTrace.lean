import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeSwapReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw junk ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15499⟩ (junk :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C' := by
  have hdup := poolManager_block_15499 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := poolManager_block_15223 (by omega) hret hdup
  exact ⟨_, _, by omega, hr⟩

end Benchmarks.UniswapV4PoolManager
