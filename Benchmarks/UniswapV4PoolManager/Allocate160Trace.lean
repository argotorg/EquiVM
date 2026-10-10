import Benchmarks.UniswapV4PoolManager.FixedAllocationGuard
import Benchmarks.UniswapV4PoolManager.AllocationTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem allocate160CostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hf : ptr.toNat+160 ≤ solcMaxU64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11794⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 ret R (writeWord mem 64 (ptr+⟨160⟩))
      (M aw (UInt256.ofNat 64) ⟨32⟩) rdata σ (k+16) (C+58+memExpansionCost aw (UInt256.ofNat 64) ⟨32⟩) := by
  have rd1 := poolManagerBlocks.poolManager_block_11794_fallthrough (by change R.length+1+4 ≤ 1024; omega)
    (fixedAllocationGuard ptr (UInt256.ofNat solcMaxU64) 160 hf) h
  have rd2 := poolManagerBlocks.poolManager_block_11818 (by omega) hret rd1
  exact RD.normalizeCounters rd2 (by omega) (by omega)

end Benchmarks.UniswapV4PoolManager
