import Benchmarks.UniswapV4PoolManager.AfterLiquidityStructEncodeTrace
import Benchmarks.UniswapV4PoolManager.LiquidityHookABI
import Benchmarks.UniswapV4PoolManager.WordBytesCallMemory
import Benchmarks.UniswapV4PoolManager.BytesValueTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterLiquidityEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta fees src len ret selector : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {sender : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (v : PoolManagerImmutables) (hstack : R.length+19 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hf : free.toNat+len.toNat+516 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14227⟩
      ((free+UInt256.ofNat 36) :: accountWord sender :: keyPtr :: paramsPtr :: delta :: fees :: src :: len :: ret :: R)
      (writeWord mem (free+UInt256.ofNat 32).toNat selector) aw rdata σ k C) :
    ∃ aw' k' C', (free.toNat+len.toNat+547)/32 ≤ aw'.toNat ∧
      C+449+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ret
        (UInt256.ofNat (free.toNat+484+paddedSize len.toNat) :: R)
        (wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) selector
          (liquidityHookHeadWords true sender key p delta fees) len) aw' rdata σ k' C' := by
  have h36 := uadd_word_ofNat_toNat free 36 (by omega : free.toNat+36 < UInt256.size)
  have h452 : ((free+UInt256.ofNat 36)+UInt256.ofNat 416).toNat = free.toNat+452 := by
    rw [uadd_word_ofNat_toNat _ 416 (by rw [h36]; omega), h36]
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := afterLiquidityKeyEncodeTrace v
    (by simp only [List.length_cons]; omega) hk hc hkb (by omega) h
  have hp1 : MemorySlice (wordCallMemory mem (free.toNat+32) selector
      (accountWord sender :: poolKeyWordList key)) paramsPtr.toNat (wordBytes (modifyLiquidityWords p)) := by
    apply (hp.writeWord (free.toNat+32) selector (.inl ?_)).wordSequence (free.toNat+36) _ ?_
    all_goals simp only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil]; omega
  obtain ⟨aw3, k3, C3, hc3, rd3⟩ := afterLiquidityParamsEncodeTrace
    (dest := free+UInt256.ofNat 36) (ret := UInt256.ofNat 14401)
    v (by simp only [List.length_cons]; omega) hp1 hl hu
    (by rw [h36]; omega) (by omega) (by rw [h36]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  rw [h36] at rd3
  have hm4 : poolManager_block_14401_memory
      (mem := wordSequenceMemory (wordCallMemory mem (free.toNat+32) selector
        (accountWord sender :: poolKeyWordList key)) (free.toNat+36+192) (modifyLiquidityWords p))
      (x0 := delta) (x1 := fees) (x2 := free+UInt256.ofNat 36) (x3 := UInt256.ofNat 416) =
      wordCallMemory mem (free.toNat+32) selector (liquidityHookHeadWords true sender key p delta fees) := by
    change writeWord (writeWord (writeWord _ ((free+UInt256.ofNat 36)+UInt256.ofNat 320).toNat delta)
      ((free+UInt256.ofNat 36)+UInt256.ofNat 352).toNat fees)
      ((free+UInt256.ofNat 36)+UInt256.ofNat 384).toNat (UInt256.ofNat 416) = _
    rw [uadd_word_ofNat_toNat _ 320 (by rw [h36]; omega),
      uadd_word_ofNat_toNat _ 352 (by rw [h36]; omega),
      uadd_word_ofNat_toNat _ 384 (by rw [h36]; omega), h36]
    simp only [liquidityHookHeadWords, if_true,
      poolKeyWordList, modifyLiquidityWords, List.cons_append, List.nil_append,
      wordCallMemory, wordSequenceMemory, Nat.add_assoc]
  have rd4 := poolManager_block_14401 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
  simp only [poolManager_block_14401_stack, hm4] at rd4
  obtain ⟨aw5, k5, C5, hspan, hcost, rd5⟩ := encodeBytesValueTrace v
    (by simp only [List.length_cons]; omega) (by rw [h452]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd4
  have hhead : (liquidityHookHeadWords true sender key p delta fees).length = 13 := rfl
  have hm5 : bytesValueMemory I.calldata
      (wordCallMemory mem (free.toNat+32) selector (liquidityHookHeadWords true sender key p delta fees))
      src.toNat ((free+UInt256.ofNat 36)+UInt256.ofNat 416).toNat len =
      wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) selector
        (liquidityHookHeadWords true sender key p delta fees) len := by
    rw [wordBytesCallMemory, hhead, h452]
  rw [hm5, h452] at rd5
  have rd6 := poolManager_block_13903 (R := R) (by omega) hret rd5
  refine ⟨_, _, _, ?_, ?_, rd6⟩
  · rw [h452] at hspan
    convert hspan using 1 <;> congr 1 <;> omega
  · dsimp only [memExpansionCost] at hcost ⊢
    omega

end Benchmarks.UniswapV4PoolManager
