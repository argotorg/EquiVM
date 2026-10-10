import Benchmarks.UniswapV4PoolManager.InitializeHookMemory
import Benchmarks.UniswapV4PoolManager.AllocationTrace
import Benchmarks.UniswapV4PoolManager.PoolKeyEncodeGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

set_option maxHeartbeats 1000000 in
theorem beforeInitializeEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr hook a b c d price : UInt256}
    {key : PoolKeyWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+291 ≤ solcMaxU64)
    (haw : aw.toNat ≤ 2048) (hs : free.toNat ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4847⟩
      (hook :: a :: b :: c :: d :: keyPtr :: price :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', aw'.toNat ≤ 2048 ∧ RD (deployedRuntime v) I g s0 ⟨16165⟩
      (hook :: free :: ⟨5008⟩ :: a :: b :: c :: d :: keyPtr :: price :: R)
      (beforeInitializeMemory mem free I.source key price) aw' rdata σ k' C' := by
  have hfit : free.toNat+291 < UInt256.size := lt_of_le_of_lt hf (by decide)
  have hm : poolManagerBlocks.poolManager_block_4847_memory (ee := I) (mem := mem) (x5 := keyPtr) =
      poolKeyPrefixMemory mem free keyPtr beforeInitializeSelectorWord (accountWord I.source) := by
    simp only [poolManagerBlocks.poolManager_block_4847_memory, hfree]
    rfl
  have hst : poolManagerBlocks.poolManager_block_4847_stack (ee := I) (mem := mem)
      (x0 := hook) (x1 := a) (x2 := b) (x3 := c) (x4 := d) (x5 := keyPtr) (R := price :: R) =
      (key.hooks :: ⟨128⟩ :: (free+⟨68⟩) :: ⟨4986⟩ :: hook :: free :: ⟨5008⟩ ::
        a :: b :: c :: d :: keyPtr :: price :: R) := by
    change (UInt256.land (memLoad (keyPtr+UInt256.ofNat 128)
      (poolKeyPrefixMemory mem (memLoad (UInt256.ofNat 64) mem) keyPtr beforeInitializeSelectorWord
        (accountWord I.source))) solcAddrMask :: ⟨128⟩ ::
        (memLoad (UInt256.ofNat 64) mem+⟨68⟩) :: ⟨4986⟩ :: hook ::
        memLoad (UInt256.ofNat 64) mem :: ⟨5008⟩ :: a :: b :: c :: d :: keyPtr :: price :: R) = _
    rw [hfree, poolKeyPrefixMemory_hook hv hc hb (by omega)]
  obtain ⟨k1, C1, rd1⟩ := RD.pack (poolManagerBlocks.poolManager_block_4847
    (by simp only [List.length_cons]; omega) h)
  rw [hst, hm, hfree] at rd1
  have haw1 := poolKeyPrefixActiveWords_le haw hs (by omega : keyPtr.toNat ≤ 1024)
  obtain ⟨k2, C2, rd2⟩ := RD.pack (poolManagerBlocks.poolManager_block_4982
    (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1)
  obtain ⟨k3, C3, rd3⟩ := RD.pack (poolManagerBlocks.poolManager_block_4986
    (by omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2)
  have h68 := uadd_word_ofNat_toNat free 68 (by omega : free.toNat+68 < UInt256.size)
  have h196 : ((free+⟨68⟩)+⟨128⟩).toNat = free.toNat+196 := by
    change ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat = _
    rw [uadd_word_ofNat_toNat _ 128 (by rw [h68]; omega), h68]
  have h228 := uadd_word_ofNat_toNat free 228 (by omega : free.toNat+228 < UInt256.size)
  have hobj : poolManagerBlocks.poolManager_block_4986_memory
      (mem := poolManagerBlocks.poolManager_block_4982_memory
        (mem := poolKeyPrefixMemory mem free keyPtr beforeInitializeSelectorWord (accountWord I.source))
        (x0 := key.hooks) (x1 := ⟨128⟩) (x2 := free+⟨68⟩)) (x1 := free) (x8 := price) =
      wordCallObjectMemory mem free beforeInitializeSelectorWord
        (accountWord I.source :: poolKeyWordList key ++ [price]) := by
    simp only [poolManagerBlocks.poolManager_block_4986_memory,
      poolManagerBlocks.poolManager_block_4982_memory, h196, h228,
      poolKeyPrefixMemory_eq hv hc hb (by omega), wordCallObjectMemory, wordCallMemory,
      poolKeyPrefixWords, poolKeyWordList, wordSequenceMemory, List.cons_append, List.nil_append, Nat.add_assoc]
    rfl
  simp only [poolManagerBlocks.poolManager_block_4986_stack, hobj] at rd3
  obtain ⟨k4, C4, rd4⟩ := allocateTraceWords v (by simp only [List.length_cons]; omega) hf
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd3
  have hend : allocationEnd free (UInt256.ofNat 260) = free+⟨288⟩ := by
    unfold allocationEnd
    congr 1
  rw [hend] at rd4
  have rd5 := poolManagerBlocks.poolManager_block_4778 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
  refine ⟨_, _, _, ?_, rd5⟩
  clear * - haw1 hs
  iterate 4 apply memoryWords_le
  · exact haw1
  all_goals
    simp only [uadd_toNat, UInt256.size,
      show (⟨32⟩ : UInt256).toNat = 32 from rfl,
      show (UInt256.ofNat 64).toNat = 64 from rfl,
      show (⟨68⟩ : UInt256).toNat = 68 from rfl,
      show (⟨128⟩ : UInt256).toNat = 128 from rfl,
      show (UInt256.ofNat 228).toNat = 228 from rfl] <;> omega

end Benchmarks.UniswapV4PoolManager
