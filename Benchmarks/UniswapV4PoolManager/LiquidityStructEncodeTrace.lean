import Benchmarks.UniswapV4PoolManager.LiquidityEncodeMemory
import Benchmarks.UniswapV4PoolManager.NatSubBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeLiquidityKeyEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len selector : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {sender : AccountAddress} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨14027⟩
      ((free+UInt256.ofNat 36) :: accountWord sender :: keyPtr :: paramsPtr :: src :: len :: R)
      (writeWord mem (free+UInt256.ofNat 32).toNat selector) aw rdata σ k C) :
    ∃ aw' k' C', C+200+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨14152⟩
        (paramsPtr :: UInt256.ofNat 14199 :: (free+UInt256.ofNat 36) :: UInt256.ofNat 352 ::
          len :: src :: UInt256.ofNat 13903 :: R)
        (wordCallMemory mem (free.toNat+32) selector (accountWord sender :: poolKeyWordList key))
        aw' rdata σ k' C' := by
  have hm := liquidityKeyEncodeMemory hk hc (solcAddrMask_clean (accountWord_canonical sender)) hb hf
    (selector := selector)
  have rd1 := poolManager_block_14027 hstack h
  simp only [poolManager_block_14027_stack, hm] at rd1
  have rd2 := poolManager_block_14151 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  refine ⟨_, _, _, ?_, rd2⟩
  dsimp only [memExpansionCost]
  nat_sub_bounds
  omega -splitNatSub

theorem modifyLiquidityParamsEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr dest ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    {p : ModifyLiquidityWords} (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024)
    (hv : MemorySlice mem ptr.toNat (wordBytes (modifyLiquidityWords p)))
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hb : ptr.toNat+128 ≤ dest.toNat+192)
    (hp : ptr.toNat+128 < UInt256.size) (hf : dest.toNat+320 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14152⟩ (ptr :: ret :: dest :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+118+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ret (dest :: R)
        (wordSequenceMemory mem (dest.toNat+192) (modifyLiquidityWords p)) aw' rdata σ k' C' := by
  have hm := modifyLiquidityEncodeMemory hv hl hu hb hp hf
  have hr := poolManager_block_14152 hstack hret h
  simp only [poolManager_block_14152_stack, hm] at hr
  refine ⟨_, _, _, ?_, hr⟩
  dsimp only [memExpansionCost]
  nat_sub_bounds
  omega -splitNatSub

end Benchmarks.UniswapV4PoolManager
