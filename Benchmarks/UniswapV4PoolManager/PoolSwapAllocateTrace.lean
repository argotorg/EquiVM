import Benchmarks.UniswapV4PoolManager.Allocate96Trace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapAllocateAW (aw : UInt256) : UInt256 :=
  M (M aw (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩

theorem poolSwapAllocateTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw pool params ret ptr : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hp : memLoad (UInt256.ofNat 64) mem = ptr) (hf : ptr.toNat+96 ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨18777⟩ (pool :: params :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ C+Cₘ (poolSwapAllocateAW aw) ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨18793⟩
      ([⟨0⟩, params, ret, pool, ptr]++R) (writeWord mem 64 (ptr+⟨96⟩))
      (poolSwapAllocateAW aw) rdata σ k' C' := by
  have rd1 := poolManagerBlocks.poolManager_block_18777 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_18777_stack, hp] at rd1
  have rd2 := allocate96CostTrace v (by change R.length+5+5 ≤ 1024; omega) hf
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  refine ⟨_, _, by omega, ?_, rd2⟩
  dsimp only [poolSwapAllocateAW, memExpansionCost]
  omega

end Benchmarks.UniswapV4PoolManager
