import Benchmarks.UniswapV4PoolManager.AfterSwapKeyEncodeMemory
import Benchmarks.UniswapV4PoolManager.NatSubBounds
import Benchmarks.UniswapV4PoolManager.EntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterSwapKeyEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len hook unspecified : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hstack : R.length+22 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨15936⟩
      (paramsPtr :: len :: src :: keyPtr :: hook :: unspecified :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+244+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨15382⟩
      (paramsPtr :: UInt256.ofNat 16097 :: len :: src :: UInt256.ofNat 14575 :: free ::
        UInt256.ofNat 16124 :: free :: hook :: UInt256.ofNat 6381 :: UInt256.ofNat 16136 :: unspecified ::
        UInt256.ofNat 16142 :: R)
      (wordCallMemory mem (free.toNat+32) afterSwapSelectorWord (accountWord I.source :: poolKeyWordList key))
      aw' rdata σ k' C' := by
  have rd1 := poolManager_block_15936 hstack h
  simp only [poolManager_block_15936_stack, hfree] at rd1
  have rd2 := poolManager_block_16079 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  rw [poolManager_block_16079_stack, afterSwapKeyEncodeMemory hk hc hb hf hfree] at rd2
  refine ⟨_, _, _, ?_, rd2⟩
  dsimp only [memExpansionCost]
  nat_sub_bounds
  omega -splitNatSub

end Benchmarks.UniswapV4PoolManager
