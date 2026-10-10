import Benchmarks.UniswapV4PoolManager.Common
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem hookFailureTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr hook ret input : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+10 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨16323⟩
      (ptr :: hook :: ret :: input :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hguard : (⟨0⟩ : UInt256).toNat+(UInt256.ofNat out.size).toNat ≤ out.size := by
    change 0+out.size % UInt256.size ≤ out.size
    simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size
  by_cases hc : UInt256.lt (memLoad ptr mem) (UInt256.ofNat 4) = UInt256.ofNat 0
  · have rd1 := poolManagerBlocks.poolManager_block_16323_fallthrough (by omega) hc h
    have rd2 := poolManagerBlocks.poolManager_block_16371 (by simp only [List.length_cons]; omega) hguard rd1
    exact poolManagerBlocks.poolManager_block_16597 (by simp only [List.length_cons]; omega) rd2
  · have rd1 := poolManagerBlocks.poolManager_block_16323_taken (by omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_16599 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have rd3 := poolManagerBlocks.poolManager_block_16371 (by simp only [List.length_cons]; omega) hguard rd2
    exact poolManagerBlocks.poolManager_block_16597 (by simp only [List.length_cons]; omega) rd3

end Benchmarks.UniswapV4PoolManager
