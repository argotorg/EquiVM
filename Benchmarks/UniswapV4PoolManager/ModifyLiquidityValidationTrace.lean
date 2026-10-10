import Benchmarks.UniswapV4PoolManager.ModifyLiquidityValidationSource
import Benchmarks.UniswapV4PoolManager.PoolLookupMemory
import Benchmarks.UniswapV4PoolManager.PoolCheckTrace
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_016
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityValidationTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 evm : State) (mem rdata : ByteArray) (key : PoolKeyWords)
    (keyPtr paramsPtr src len junk : UInt256) (R : List UInt256) : Prop :=
  if transientWord evm lockSlot = ⟨0⟩ then RDrev (deployedRuntime v) g s0
  else if I.codeOwner = v.original then
    if poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩ then RDrev (deployedRuntime v) g s0
    else ∃ aw k C, aw.toNat ≤ 14 ∧ RD (deployedRuntime v) I g s0 ⟨5474⟩
      ([src, paramsPtr, len, keyPtr, poolKeyId key, junk] ++ R)
      (poolLookupMemory mem (poolKeyId key)) aw rdata evm.accountMap k C
  else RDrev (deployedRuntime v) g s0

theorem modifyLiquidityValidationTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw keyPtr paramsPtr src len junk : UInt256} {k C : Nat}
    {key : PoolKeyWords} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hk : PoolKeyView mem keyPtr key) (hb : keyPtr.toNat+160 ≤ 448) (haw : aw.toNat ≤ 14)
    (h : RD (deployedRuntime v) I g s0 ⟨5394⟩
      ([len, src, keyPtr, paramsPtr, junk] ++ R) mem aw rdata evm.accountMap k C) :
    modifyLiquidityValidationTraceResult v I g s0 evm mem rdata key keyPtr paramsPtr src len junk R := by
  rw [modifyLiquidityValidationTraceResult]
  have hlock : codeOwnerTransientWord I evm.accountMap lockSlot = transientWord evm lockSlot :=
    (transientWord_accountMap hI lockSlot).symm
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    have hr := poolManagerBlocks.poolManager_block_5394_taken (by change R.length+7 ≤ 1024; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩
          rw [hlock, hl]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_1239 (by change R.length+7 ≤ 1024; omega) hr
  rw [if_neg hl]
  have rd1 := poolManagerBlocks.poolManager_block_5394_fallthrough
    (by change R.length+7 ≤ 1024; omega)
    (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩
        rw [hlock]; exact isZero_eq_zero_of_ne hl) h
  have rd2 := poolManagerBlocks.poolManager_block_5436 (by change R.length+7 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hdelegate := noDelegateCallTrace v (by change R.length+8 ≤ 1024; omega)
    (by rw [deployedRuntime_jumps]; jump_dest) rd2
  by_cases hd : I.codeOwner = v.original
  swap
  · rw [if_neg hd] at hdelegate ⊢
    exact hdelegate
  rw [if_pos hd] at hdelegate ⊢
  obtain ⟨k3, C3, rd3⟩ := hdelegate
  change RD _ _ _ _ ⟨5443⟩ (paramsPtr :: len :: keyPtr :: src :: junk :: R) _ _ _ _ _ _ at rd3
  have hh : keccakWord keyPtr (UInt256.ofNat 160) mem = poolKeyId key := hk.hash
  have hm : poolManagerBlocks.poolManager_block_5443_memory (mem := mem) (x2 := keyPtr) =
      poolLookupMemory mem (poolKeyId key) := by
    unfold poolManagerBlocks.poolManager_block_5443_memory
    rw [hh]
    change writeWord (twoWordHashMem (poolKeyId key) ⟨6⟩ mem) 128
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (poolKeyId key) ⟨6⟩ mem)) = _
    rw [mappingMemory_slot_any]
    rfl
  have hs : poolManagerBlocks.poolManager_block_5443_stack (mem := mem)
      (x0 := paramsPtr) (x1 := len) (x2 := keyPtr) (x3 := src) (R := junk :: R) =
      [poolSlot (poolKeyId key), ⟨5474⟩, src, paramsPtr, len, keyPtr, poolKeyId key, junk] ++ R := by
    change memLoad (UInt256.ofNat 128)
        (poolManagerBlocks.poolManager_block_5443_memory (mem := mem) (x2 := keyPtr)) ::
      UInt256.ofNat 5474 :: src :: paramsPtr :: len :: keyPtr :: keccakWord keyPtr (UInt256.ofNat 160) mem :: junk :: R = _
    rw [hm, hh, poolLookupMemory_slot]
    rfl
  obtain ⟨k4, C4, rd4⟩ := RD.pack (poolManagerBlocks.poolManager_block_5443
    (by change R.length+9 ≤ 1024; exact hstack)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3)
  rw [hs, hm] at rd4
  have haw4 : (M (M (M (M (M (M aw keyPtr (UInt256.ofNat 160)) ⟨0⟩ ⟨32⟩)
      (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)) (UInt256.ofNat 128) ⟨32⟩)
      (UInt256.ofNat 128) ⟨32⟩).toNat ≤ 14 := by
    iterate 6 apply memoryWords_le
    · exact haw
    · exact hb
    all_goals decide
  have hword : slot0SqrtPriceWord (solcSlotWordAt (poolSlot (poolKeyId key)) evm.accountMap I) =
      poolSqrtPriceWord evm (poolKeyId key) := by
    unfold poolSqrtPriceWord poolSlot0Word
    rw [storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])]
  have hcheck := poolCheckTrace v (by change R.length+9 ≤ 1024; exact hstack)
    (by rw [deployedRuntime_jumps]; jump_dest) rd4
  rw [hword] at hcheck
  rcases hcheck with ⟨hp, hr⟩ | ⟨hp, k5, C5, rd5⟩
  · rw [if_pos hp]; exact hr
  · rw [if_neg hp]
    exact ⟨_, k5, C5, haw4, rd5⟩

end Benchmarks.UniswapV4PoolManager
