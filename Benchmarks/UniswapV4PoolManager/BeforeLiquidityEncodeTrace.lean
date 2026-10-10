import Benchmarks.UniswapV4PoolManager.LiquidityStructEncodeTrace
import Benchmarks.UniswapV4PoolManager.LiquidityHookABI
import Benchmarks.UniswapV4PoolManager.WordBytesCallMemory
import Benchmarks.UniswapV4PoolManager.BytesValueTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeLiquidityEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len ret selector : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {sender : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hf : free.toNat+len.toNat+452 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14027⟩
      ((free+UInt256.ofNat 36) :: accountWord sender :: keyPtr :: paramsPtr :: src :: len :: ret :: R)
      (writeWord mem (free+UInt256.ofNat 32).toNat selector) aw rdata σ k C) :
    ∃ aw' k' C', (free.toNat+len.toNat+483)/32 ≤ aw'.toNat ∧
      C+449+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ret
        (UInt256.ofNat (free.toNat+420+paddedSize len.toNat) :: R)
        (wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) selector
          (liquidityHookHeadWords false sender key p ⟨0⟩ ⟨0⟩) len) aw' rdata σ k' C' := by
  have h36 := uadd_word_ofNat_toNat free 36 (by omega : free.toNat+36 < UInt256.size)
  have h388 : ((free+UInt256.ofNat 36)+UInt256.ofNat 352).toNat = free.toNat+388 := by
    rw [uadd_word_ofNat_toNat _ 352 (by rw [h36]; omega), h36]
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := beforeLiquidityKeyEncodeTrace v
    (by simp only [List.length_cons]; omega) hk hc hkb (by omega) h
  have hp1 : MemorySlice (wordCallMemory mem (free.toNat+32) selector
      (accountWord sender :: poolKeyWordList key)) paramsPtr.toNat (wordBytes (modifyLiquidityWords p)) := by
    apply (hp.writeWord (free.toNat+32) selector (.inl ?_)).wordSequence (free.toNat+36) _ ?_
    all_goals simp only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil]; omega
  obtain ⟨aw3, k3, C3, hc3, rd3⟩ := modifyLiquidityParamsEncodeTrace
    (dest := free+UInt256.ofNat 36) (ret := UInt256.ofNat 14199)
    v (by simp only [List.length_cons]; omega) hp1 hl hu
    (by rw [h36]; omega) (by omega) (by rw [h36]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  rw [h36] at rd3
  have hm4 : poolManager_block_14199_memory
      (mem := wordSequenceMemory (wordCallMemory mem (free.toNat+32) selector
        (accountWord sender :: poolKeyWordList key)) (free.toNat+36+192) (modifyLiquidityWords p))
      (x0 := free+UInt256.ofNat 36) (x1 := UInt256.ofNat 352) =
      wordCallMemory mem (free.toNat+32) selector (liquidityHookHeadWords false sender key p ⟨0⟩ ⟨0⟩) := by
    change writeWord _ ((free+UInt256.ofNat 36)+UInt256.ofNat 320).toNat (UInt256.ofNat 352) = _
    rw [uadd_word_ofNat_toNat _ 320 (by rw [h36]; omega), h36]
    simp only [liquidityHookHeadWords, Bool.false_eq_true, if_false, List.append_nil,
      poolKeyWordList, modifyLiquidityWords, List.cons_append, List.nil_append,
      wordCallMemory, wordSequenceMemory, Nat.add_assoc]
  have rd4 := poolManager_block_14199 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
  simp only [poolManager_block_14199_stack, hm4] at rd4
  obtain ⟨aw5, k5, C5, hspan, hcost, rd5⟩ := encodeBytesValueTrace v
    (by simp only [List.length_cons]; omega) (by rw [h388]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd4
  have hhead : (liquidityHookHeadWords false sender key p ⟨0⟩ ⟨0⟩).length = 11 := rfl
  have hm5 : bytesValueMemory I.calldata
      (wordCallMemory mem (free.toNat+32) selector (liquidityHookHeadWords false sender key p ⟨0⟩ ⟨0⟩))
      src.toNat ((free+UInt256.ofNat 36)+UInt256.ofNat 352).toNat len =
      wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) selector
        (liquidityHookHeadWords false sender key p ⟨0⟩ ⟨0⟩) len := by
    rw [wordBytesCallMemory, hhead, h388]
  rw [hm5, h388] at rd5
  have rd6 := poolManager_block_13903 (R := R) (by omega) hret rd5
  refine ⟨_, _, _, ?_, ?_, rd6⟩
  · rw [h388] at hspan
    convert hspan using 1 <;> congr 1 <;> omega
  · dsimp only [memExpansionCost] at hcost ⊢
    omega

end Benchmarks.UniswapV4PoolManager
