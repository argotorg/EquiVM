import Benchmarks.UniswapV4PoolManager.LiquidityEncodeMemory
import Benchmarks.UniswapV4PoolManager.DonateHookABI
import Benchmarks.UniswapV4PoolManager.WordBytesCallMemory
import Benchmarks.UniswapV4PoolManager.BytesValueTrace
import Benchmarks.UniswapV4PoolManager.NatSubBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem donateHookKeyEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr amount0 amount1 src len selector : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {sender : AccountAddress} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨13756⟩
      ((free+UInt256.ofNat 36) :: accountWord sender :: keyPtr :: amount0 :: amount1 :: src :: len :: R)
      (writeWord mem (free+UInt256.ofNat 32).toNat selector) aw rdata σ k C) :
    ∃ aw' k' C', C+200+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨13879⟩
        (amount0 :: amount1 :: (free+UInt256.ofNat 36) :: UInt256.ofNat 288 :: len :: src :: UInt256.ofNat 13903 :: R)
        (wordCallMemory mem (free.toNat+32) selector (accountWord sender :: poolKeyWordList key))
        aw' rdata σ k' C' := by
  have hm : poolManager_block_13756_memory
      (mem := writeWord mem (free+UInt256.ofNat 32).toNat selector)
      (x0 := free+UInt256.ofNat 36) (x1 := accountWord sender) (x2 := keyPtr) =
      wordCallMemory mem (free.toNat+32) selector (accountWord sender :: poolKeyWordList key) :=
    liquidityKeyEncodeMemory hk hc (solcAddrMask_clean (accountWord_canonical sender)) hb hf
  have rd1 := poolManager_block_13756 hstack h
  simp only [poolManager_block_13756_stack, hm] at rd1
  have rd2 := poolManager_block_13878 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  refine ⟨_, _, _, ?_, rd2⟩
  dsimp only [memExpansionCost]
  nat_sub_bounds
  omega -splitNatSub

theorem donateHookEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr amount0 amount1 src len ret selector : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {sender : AccountAddress} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+len.toNat+388 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13756⟩
      ((free+UInt256.ofNat 36) :: accountWord sender :: keyPtr :: amount0 :: amount1 :: src :: len :: ret :: R)
      (writeWord mem (free+UInt256.ofNat 32).toNat selector) aw rdata σ k C) :
    ∃ aw' k' C', (free.toNat+len.toNat+419)/32 ≤ aw'.toNat ∧
      C+355+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ret (UInt256.ofNat (free.toNat+356+paddedSize len.toNat) :: R)
        (wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) selector
          (donateHookHeadWords sender key amount0 amount1) len) aw' rdata σ k' C' := by
  have h36 := uadd_word_ofNat_toNat free 36 (by omega : free.toNat+36 < UInt256.size)
  have h324 : ((free+UInt256.ofNat 36)+UInt256.ofNat 288).toNat = free.toNat+324 := by
    rw [uadd_word_ofNat_toNat _ 288 (by rw [h36]; omega), h36]
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := donateHookKeyEncodeTrace v
    (by simp only [List.length_cons]; omega) hk hc hb (by omega) h
  have hm2 : poolManager_block_13879_memory
      (mem := wordCallMemory mem (free.toNat+32) selector (accountWord sender :: poolKeyWordList key))
      (x0 := amount0) (x1 := amount1) (x2 := free+UInt256.ofNat 36) (x3 := UInt256.ofNat 288) =
      wordCallMemory mem (free.toNat+32) selector (donateHookHeadWords sender key amount0 amount1) := by
    change writeWord (writeWord (writeWord _ ((free+UInt256.ofNat 36)+UInt256.ofNat 192).toNat amount0)
      ((free+UInt256.ofNat 36)+UInt256.ofNat 224).toNat amount1)
      ((free+UInt256.ofNat 36)+UInt256.ofNat 256).toNat (UInt256.ofNat 288) = _
    rw [uadd_word_ofNat_toNat _ 192 (by rw [h36]; omega),
      uadd_word_ofNat_toNat _ 224 (by rw [h36]; omega),
      uadd_word_ofNat_toNat _ 256 (by rw [h36]; omega), h36]
    simp only [donateHookHeadWords, poolKeyWordList, List.cons_append, List.nil_append,
      wordCallMemory, wordSequenceMemory, Nat.add_assoc]
  have rd2 := poolManager_block_13879 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  simp only [poolManager_block_13879_stack, hm2] at rd2
  obtain ⟨aw3, k3, C3, hspan, hc3, rd3⟩ := encodeBytesValueTrace v
    (by simp only [List.length_cons]; omega) (by rw [h324]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
  have hhead : (donateHookHeadWords sender key amount0 amount1).length = 9 := rfl
  have hm3 : bytesValueMemory I.calldata
      (wordCallMemory mem (free.toNat+32) selector (donateHookHeadWords sender key amount0 amount1))
      src.toNat ((free+UInt256.ofNat 36)+UInt256.ofNat 288).toNat len =
      wordBytesCallMemory I.calldata mem src.toNat (free.toNat+32) selector
        (donateHookHeadWords sender key amount0 amount1) len := by
    rw [wordBytesCallMemory, hhead, h324]
  rw [hm3, h324] at rd3
  have rd4 := poolManager_block_13903 (R := R) (by omega) hret rd3
  refine ⟨_, _, _, ?_, ?_, rd4⟩
  · rw [h324] at hspan
    convert hspan using 1 <;> congr 1 <;> omega
  · dsimp only [memExpansionCost] at hc3 ⊢
    omega

end Benchmarks.UniswapV4PoolManager
