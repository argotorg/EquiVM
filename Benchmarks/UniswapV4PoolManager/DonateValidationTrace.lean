import Benchmarks.UniswapV4PoolManager.DonateValidationSource
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation
import Benchmarks.UniswapV4PoolManager.PoolCheckTrace
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_028

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def donateValidationTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 evm : State) (mem rdata : ByteArray) (key : PoolKeyWords)
    (keyPtr amount0 amount1 src len junk : UInt256) (R : List UInt256) : Prop :=
  if transientWord evm lockSlot = ⟨0⟩ then RDrev (deployedRuntime v) g s0
  else if I.codeOwner = v.original then
    if poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩ then RDrev (deployedRuntime v) g s0
    else ∃ aw k C, aw.toNat ≤ 10 ∧ RD (deployedRuntime v) I g s0 ⟨10153⟩
      ([keyPtr, src, amount1, amount0, len, poolSlot (poolKeyId key), poolKeyId key, junk] ++ R)
      (twoWordHashMem (poolKeyId key) ⟨6⟩ mem) aw rdata evm.accountMap k C
  else RDrev (deployedRuntime v) g s0

theorem donateValidationTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw keyPtr amount0 amount1 src len junk : UInt256} {k C : Nat}
    {key : PoolKeyWords} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+11 ≤ 1024) (hI : evm.executionEnv = I)
    (hk : PoolKeyView mem keyPtr key)
    (hb : keyPtr.toNat+160 ≤ 320) (haw : aw.toNat ≤ 10)
    (h : RD (deployedRuntime v) I g s0 ⟨10076⟩
      ([len, src, amount0, keyPtr, amount1, junk] ++ R)
      mem aw rdata evm.accountMap k C) :
    donateValidationTraceResult v I g s0 evm mem rdata key keyPtr amount0 amount1 src len junk R := by
  rw [donateValidationTraceResult]
  have hlock : codeOwnerTransientWord I evm.accountMap lockSlot = transientWord evm lockSlot :=
    (transientWord_accountMap hI lockSlot).symm
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    have hr := poolManagerBlocks.poolManager_block_10076_taken (by change R.length+8 ≤ 1024; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩
          rw [hlock, hl]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_1239 (by change R.length+8 ≤ 1024; omega) hr
  rw [if_neg hl]
  have rd1 := poolManagerBlocks.poolManager_block_10076_fallthrough (by change R.length+8 ≤ 1024; omega)
    (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩
        rw [hlock]; exact isZero_eq_zero_of_ne hl) h
  have rd2 := poolManagerBlocks.poolManager_block_10119 (by change R.length+8 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hdelegate := noDelegateCallTrace v (by change R.length+9 ≤ 1024; omega)
    (by rw [deployedRuntime_jumps]; jump_dest) rd2
  by_cases hd : I.codeOwner = v.original
  swap
  · rw [if_neg hd] at hdelegate ⊢
    exact hdelegate
  rw [if_pos hd] at hdelegate ⊢
  obtain ⟨k3, C3, rd3⟩ := hdelegate
  have hh : keccakWord keyPtr (UInt256.ofNat 160) mem = poolKeyId key := hk.hash
  have hm : poolManagerBlocks.poolManager_block_10126_memory (mem := mem) (x3 := keyPtr) =
      twoWordHashMem (poolKeyId key) ⟨6⟩ mem := by
    unfold poolManagerBlocks.poolManager_block_10126_memory
    rw [hh]
    rfl
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 6).toByteArray.write 0 ((poolKeyId key).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32) = poolSlot (poolKeyId key) := mappingMemory_slot_any _ _ _
  obtain ⟨k5, C5, rd5⟩ := RD.pack (poolManagerBlocks.poolManager_block_10126
    (by change R.length+11 ≤ 1024; exact hstack)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3)
  simp only [poolManagerBlocks.poolManager_block_10126_stack, hm, hh, hslot] at rd5
  have haw5 : (M (M (M (M aw keyPtr (UInt256.ofNat 160)) ⟨0⟩ ⟨32⟩)
      (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)).toNat ≤ 10 := by
    iterate 4 apply memoryWords_le
    · exact haw
    · exact hb
    all_goals decide
  have hword : slot0SqrtPriceWord (solcSlotWordAt (poolSlot (poolKeyId key)) evm.accountMap I) =
      poolSqrtPriceWord evm (poolKeyId key) := by
    unfold poolSqrtPriceWord poolSlot0Word
    rw [storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])]
  have hcheck := poolCheckTrace v (by change R.length+11 ≤ 1024; exact hstack)
    (by rw [deployedRuntime_jumps]; jump_dest) rd5
  rw [hword] at hcheck
  rcases hcheck with ⟨hinit, hr⟩ | ⟨hinit, k6, C6, rd6⟩
  · rw [if_pos hinit]; exact hr
  · rw [if_neg hinit]
    exact ⟨_, k6, C6, haw5, rd6⟩

end Benchmarks.UniswapV4PoolManager
