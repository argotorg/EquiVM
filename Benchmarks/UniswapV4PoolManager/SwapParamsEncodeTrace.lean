import Benchmarks.UniswapV4PoolManager.SwapParamsEncodeMemory
import Benchmarks.UniswapV4PoolManager.NatSubBounds
import Benchmarks.UniswapV4PoolManager.EntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem swapParamsEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr dest ret x2 x3 x4 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hv : MemorySlice mem ptr.toNat (wordBytes (swapParamsWordList p)))
    (hl : p.priceLimit.toNat < 2^160) (hb : ptr.toNat+96 ≤ dest.toNat+228)
    (hp : ptr.toNat+96 < UInt256.size) (hf : dest.toNat+324 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15382⟩ (ptr :: ret :: x2 :: x3 :: x4 :: dest :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+84+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret
      (x2 :: x3 :: x4 :: dest :: R) (wordSequenceMemory mem (dest.toNat+228) (swapParamsWordList p))
        aw' rdata σ k' C' := by
  have hm := swapParamsEncodeMemory hv hl hb hp hf
  have hr := poolManager_block_15382 hstack hret h
  simp only [poolManager_block_15382_stack, hm] at hr
  refine ⟨_, _, _, ?_, hr⟩
  dsimp only [memExpansionCost]
  nat_sub_bounds
  omega -splitNatSub

end Benchmarks.UniswapV4PoolManager
