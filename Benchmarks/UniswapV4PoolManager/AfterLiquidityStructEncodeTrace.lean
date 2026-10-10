import Benchmarks.UniswapV4PoolManager.LiquidityStructEncodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterLiquidityKeyEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta fees src len selector : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {sender : AccountAddress} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨14227⟩
      ((free+UInt256.ofNat 36) :: accountWord sender :: keyPtr :: paramsPtr :: delta :: fees :: src :: len :: R)
      (writeWord mem (free+UInt256.ofNat 32).toNat selector) aw rdata σ k C) :
    ∃ aw' k' C', C+200+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨14354⟩
        (paramsPtr :: UInt256.ofNat 14401 :: delta :: fees :: (free+UInt256.ofNat 36) :: UInt256.ofNat 416 ::
          len :: src :: UInt256.ofNat 13903 :: R)
        (wordCallMemory mem (free.toNat+32) selector (accountWord sender :: poolKeyWordList key))
        aw' rdata σ k' C' := by
  have hm := liquidityKeyEncodeMemory hk hc (solcAddrMask_clean (accountWord_canonical sender)) hb hf
    (selector := selector)
  have rd1 := poolManager_block_14227 hstack h
  simp only [poolManager_block_14227_stack] at rd1
  have rd2 := poolManager_block_14351 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  change RD _ _ _ _ _ _ (poolManager_block_14027_memory
    (mem := writeWord mem (free+UInt256.ofNat 32).toNat selector)
    (x0 := free+UInt256.ofNat 36) (x1 := accountWord sender) (x2 := keyPtr)) _ _ _ _ _ at rd2
  rw [hm] at rd2
  refine ⟨_, _, _, ?_, rd2⟩
  dsimp only [memExpansionCost]
  nat_sub_bounds
  omega -splitNatSub

theorem afterLiquidityParamsEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr dest ret delta fees : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {p : ModifyLiquidityWords}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hv : MemorySlice mem ptr.toNat (wordBytes (modifyLiquidityWords p)))
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hb : ptr.toNat+128 ≤ dest.toNat+192)
    (hp : ptr.toNat+128 < UInt256.size) (hf : dest.toNat+320 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14354⟩ (ptr :: ret :: delta :: fees :: dest :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', C+118+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ret (delta :: fees :: dest :: R)
        (wordSequenceMemory mem (dest.toNat+192) (modifyLiquidityWords p)) aw' rdata σ k' C' := by
  have hm : poolManager_block_14354_memory (mem := mem) (x0 := ptr) (x4 := dest) =
      wordSequenceMemory mem (dest.toNat+192) (modifyLiquidityWords p) :=
    modifyLiquidityEncodeMemory hv hl hu hb hp hf
  have hr := poolManager_block_14354 hstack hret h
  simp only [poolManager_block_14354_stack, hm] at hr
  refine ⟨_, _, _, ?_, hr⟩
  dsimp only [memExpansionCost]
  nat_sub_bounds
  omega -splitNatSub

end Benchmarks.UniswapV4PoolManager
