import Benchmarks.UniswapV4PoolManager.InitializeHookMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

set_option maxHeartbeats 1000000 in
theorem afterInitializeEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr hook price tick : UInt256}
    {key : PoolKeyWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+292 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4611⟩
      (hook :: keyPtr :: price :: tick :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11822⟩
      (free :: UInt256.ofNat 292 :: ⟨4778⟩ :: hook :: free :: ⟨4783⟩ :: tick :: ⟨32⟩ :: R)
      (wordCallObjectMemory mem free afterInitializeSelectorWord
        (accountWord I.source :: poolKeyWordList key ++ [price, tick])) aw' rdata σ k' C' := by
  have hm : poolManagerBlocks.poolManager_block_4611_memory (ee := I) (mem := mem)
      (x1 := keyPtr) (x4 := ⟨32⟩) =
      poolKeyPrefixMemory mem free keyPtr afterInitializeSelectorWord (accountWord I.source) := by
    simp only [poolManagerBlocks.poolManager_block_4611_memory, hfree]
    rfl
  have hst : poolManagerBlocks.poolManager_block_4611_stack (ee := I) (mem := mem)
      (x0 := hook) (x1 := keyPtr) (x2 := price) (x3 := tick) (x4 := ⟨32⟩) (R := R) =
      (key.hooks :: ⟨128⟩ :: (free+⟨68⟩) :: ⟨4749⟩ :: price :: hook :: free :: ⟨4783⟩ :: tick :: ⟨32⟩ :: R) := by
    change (UInt256.land (memLoad (keyPtr+UInt256.ofNat 128)
      (poolKeyPrefixMemory mem (memLoad (UInt256.ofNat 64) mem) keyPtr afterInitializeSelectorWord
        (accountWord I.source))) solcAddrMask :: ⟨128⟩ ::
        (memLoad (UInt256.ofNat 64) mem+⟨68⟩) :: ⟨4749⟩ :: price :: hook ::
        memLoad (UInt256.ofNat 64) mem :: ⟨4783⟩ :: tick :: ⟨32⟩ :: R) = _
    rw [hfree, poolKeyPrefixMemory_hook hv hc hb (by omega)]
  obtain ⟨aw1, k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_4611_packed hstack h
  rw [hst, hm] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_4745_packed
    (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := poolManagerBlocks.poolManager_block_4749_packed
    (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
  have h68 := uadd_word_ofNat_toNat free 68 (by omega : free.toNat+68 < UInt256.size)
  have h196 : ((free+⟨68⟩)+⟨128⟩).toNat = free.toNat+196 := by
    change ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat = _
    rw [uadd_word_ofNat_toNat _ 128 (by rw [h68]; omega), h68]
  have h228 := uadd_word_ofNat_toNat free 228 (by omega : free.toNat+228 < UInt256.size)
  have h260 := uadd_word_ofNat_toNat free 260 (by omega : free.toNat+260 < UInt256.size)
  have hobj : poolManagerBlocks.poolManager_block_4749_memory
      (mem := poolManagerBlocks.poolManager_block_4745_memory
        (mem := poolKeyPrefixMemory mem free keyPtr afterInitializeSelectorWord (accountWord I.source))
        (x0 := key.hooks) (x1 := ⟨128⟩) (x2 := free+⟨68⟩)) (x0 := price) (x2 := free) (x4 := tick) =
      wordCallObjectMemory mem free afterInitializeSelectorWord
        (accountWord I.source :: poolKeyWordList key ++ [price, tick]) := by
    simp only [poolManagerBlocks.poolManager_block_4749_memory,
      poolManagerBlocks.poolManager_block_4745_memory, h196, h228, h260,
      poolKeyPrefixMemory_eq hv hc hb (by omega), wordCallObjectMemory, wordCallMemory,
      poolKeyPrefixWords, poolKeyWordList, wordSequenceMemory, List.cons_append, List.nil_append, Nat.add_assoc]
    rfl
  simp only [poolManagerBlocks.poolManager_block_4749_stack, hobj] at rd3
  exact ⟨aw3, k3, C3, rd3⟩

end Benchmarks.UniswapV4PoolManager
