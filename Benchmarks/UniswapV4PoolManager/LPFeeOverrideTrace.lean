import Benchmarks.UniswapV4PoolManager.LPFeeOverrideSource
import Benchmarks.UniswapV4PoolManager.LPFeeTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem lpFeeOverrideValidateTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18928⟩ (fee :: R) mem aw rdata σ k C) :
    if (lpFeeRemoveOverride fee).toNat ≤ 1000000 then
      ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18941⟩ (lpFeeRemoveOverride fee :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd := poolManagerBlocks.poolManager_block_18928 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_18928_stack,
    u256_land_comm (UInt256.ofNat 12582911) fee] at rd
  exact lpFeeValidateTrace v (by simp only [List.length_cons]; omega) (lpFeeRemoveOverride_bound fee)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd

end Benchmarks.UniswapV4PoolManager
