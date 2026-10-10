import Benchmarks.UniswapV4PoolManager.AfterSwapKeyEncodeTrace
import Benchmarks.UniswapV4PoolManager.SwapParamsEncodeTrace
import Benchmarks.UniswapV4PoolManager.BytesValueTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterSwapEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len hook unspecified specified delta ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+26 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hf : free.toNat+len.toNat+452 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨15936⟩
      (paramsPtr :: len :: src :: keyPtr :: hook :: unspecified :: specified :: delta :: ret :: paramsPtr :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', (free.toNat+len.toNat+483)/32 ≤ aw'.toNat ∧
      C+468+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨14575⟩
        (UInt256.ofNat (free.toNat+420+paddedSize len.toNat) :: free :: UInt256.ofNat 16124 :: free ::
          hook :: UInt256.ofNat 6381 :: UInt256.ofNat 16136 :: unspecified :: UInt256.ofNat 16142 ::
          specified :: delta :: ret :: paramsPtr :: R)
        (wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) afterSwapSelectorWord
          (swapHookHeadWords true I.source key p delta) len) aw' rdata σ k' C' := by
  have h388 := uadd_word_ofNat_toNat free 388 (by omega : free.toNat+388 < UInt256.size)
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := afterSwapKeyEncodeTrace v
    (by simp only [List.length_cons]; omega) hk hc hkb (by omega) hfree h
  have hp1 : MemorySlice (wordCallMemory mem (free.toNat+32) afterSwapSelectorWord
      (accountWord I.source :: poolKeyWordList key)) paramsPtr.toNat (wordBytes (swapParamsWordList p)) := by
    apply (hp.writeWord (free.toNat+32) afterSwapSelectorWord (.inl ?_)).wordSequence (free.toNat+36) _ ?_
    all_goals simp only [wordBytes_size, swapParamsWordList, List.length_cons, List.length_nil]; omega
  obtain ⟨aw2, k2, C2, hc2, rd2⟩ := swapParamsEncodeTrace
    (dest := free) (ret := UInt256.ofNat 16097) v
    (by simp only [List.length_cons]; omega) hp1 hl (by omega) (by omega) (by omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  have hm3 : poolManager_block_16097_memory
      (mem := wordSequenceMemory (wordCallMemory mem (free.toNat+32) afterSwapSelectorWord
        (accountWord I.source :: poolKeyWordList key)) (free.toNat+228) (swapParamsWordList p))
      (x3 := free) (x12 := delta) =
      wordCallMemory mem (free.toNat+32) afterSwapSelectorWord (swapHookHeadWords true I.source key p delta) := by
    change writeWord (writeWord _ (free+UInt256.ofNat 324).toNat delta)
      (free+UInt256.ofNat 356).toNat (UInt256.ofNat 352) = _
    rw [uadd_word_ofNat_toNat _ 324 (by omega), uadd_word_ofNat_toNat _ 356 (by omega)]
    simp only [swapHookHeadWords, if_true, poolKeyWordList, swapParamsWordList,
      List.cons_append, List.nil_append, wordCallMemory, wordSequenceMemory, Nat.add_assoc]
  have rd3 := poolManager_block_16097 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
  simp only [poolManager_block_16097_stack, hm3] at rd3
  obtain ⟨aw4, k4, C4, hspan, hcost, rd4⟩ := encodeBytesValueTrace v
    (by simp only [List.length_cons]; omega) (by rw [h388]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd3
  have hhead : (swapHookHeadWords true I.source key p delta).length = 11 := rfl
  have hm4 : bytesValueMemory I.calldata
      (wordCallMemory mem (free.toNat+32) afterSwapSelectorWord (swapHookHeadWords true I.source key p delta))
      src.toNat (free+UInt256.ofNat 388).toNat len =
      wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) afterSwapSelectorWord
        (swapHookHeadWords true I.source key p delta) len := by
    rw [wordBytesCallMemory, hhead, h388]
  rw [hm4, h388] at rd4
  refine ⟨aw4, k4, C4, ?_, ?_, ?_⟩
  · rw [h388] at hspan
    convert hspan using 1 <;> congr 1 <;> omega
  · dsimp only [memExpansionCost] at hcost
    omega
  · simpa only [show free.toNat+388+32 = free.toNat+420 by omega] using rd4

end Benchmarks.UniswapV4PoolManager
