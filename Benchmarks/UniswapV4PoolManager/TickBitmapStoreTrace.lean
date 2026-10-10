import Benchmarks.UniswapV4PoolManager.TickBitmapSource
import Benchmarks.UniswapV4PoolManager.TickBitmapStoreStatic
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory
import Benchmarks.UniswapV4PoolManager.TransientTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickBitmapActiveWords (aw : UInt256) : UInt256 :=
  M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)

theorem tickBitmapStoreExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing ret : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : (EVM.signed tick).natAbs ≤ 887272) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16670⟩ (tick :: spacing :: (poolSlot id+⟨5⟩) :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ k' C',
      RD (deployedRuntime v) I g s0 ret R
        (twoWordHashMem (EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
          (poolSlot id+⟨5⟩) mem) (tickBitmapActiveWords aw) rdata
        (tickBitmapPost evm id (EVM.signed tick) (EVM.signed spacing)).accountMap k' C' := by
  by_cases hp : I.perm = false
  · rw [if_pos hp]
    exact tickBitmapStoreStatic hstack hp h
  · rw [if_neg hp]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_16670 hstack
      (Bool.eq_true_of_not_eq_false hp) hret h
    have hkey := tickBitmapPosition_word tick spacing ht
    have hhash : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((poolSlot id+⟨5⟩).toByteArray.write 0
          ((UInt256.sar (UInt256.ofNat 8) (UInt256.sdiv tick spacing)).toByteArray.write 0 mem
            (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        tickBitmapSlot id (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)) := by
      change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.sar (UInt256.ofNat 8) (UInt256.sdiv tick spacing))
        (poolSlot id+⟨5⟩) mem) = _
      rw [mappingMemory_slot_any, ← hkey]
      rfl
    have hmask : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.land (UInt256.sdiv tick spacing) (UInt256.ofNat 255)) =
        tickBitmapMask (tickBitmapCompressed (EVM.signed tick) (EVM.signed spacing)) := by
      rw [sdiv_signed]
      rfl
    rw [hhash, hmask] at rd1
    have hload : solcSlotWordAt (tickBitmapSlot id (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
        evm.accountMap I = tickBitmapWord evm id (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)) :=
      (storageLoad_codeOwner_eq_solcSlotWordAt _ I _ (by rw [hI])).symm
    dsimp only [solcSlotWordAt, solcSlotWord] at hload
    rw [hload] at rd1
    have hσ : (tickBitmapPost evm id (EVM.signed tick) (EVM.signed spacing)).accountMap =
        sstoreAccountMap I.codeOwner evm.accountMap
          (tickBitmapSlot id (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
          (UInt256.xor (tickBitmapWord evm id (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
            (tickBitmapMask (tickBitmapCompressed (EVM.signed tick) (EVM.signed spacing)))) := by
      rw [tickBitmapPost, storageStore_accountMap, hI]
    rw [← hσ] at rd1
    simp only [poolManagerBlocks.poolManager_block_16670_stack,
      poolManagerBlocks.poolManager_block_16670_memory, ← hkey] at rd1
    exact ⟨k1, C1, rd1⟩

theorem tickBitmapStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing ret : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : (EVM.signed tick).natAbs ≤ 887272) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16670⟩ (tick :: spacing :: (poolSlot id+⟨5⟩) :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret R
        (twoWordHashMem (EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
          (poolSlot id+⟨5⟩) mem) aw' rdata
        (tickBitmapPost evm id (EVM.signed tick) (EVM.signed spacing)).accountMap k' C' := by
  have hr := tickBitmapStoreExactTrace v hstack hI ht hret h
  split_ifs at hr ⊢
  · exact hr
  · obtain ⟨k', C', rd⟩ := hr
    exact ⟨_, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
