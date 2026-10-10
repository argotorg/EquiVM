import Benchmarks.UniswapV4PoolManager.TickScanWords
import Benchmarks.UniswapV4PoolManager.TransientTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickScanMemory (mem : ByteArray) (id compressed : UInt256) : ByteArray :=
  twoWordHashMem (tickPositionWord compressed) (poolSlot id + UInt256.ofNat 5) mem

theorem tickScanMemory_hash (mem : ByteArray) (id compressed : UInt256) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (tickScanMemory mem id compressed) =
      tickBitmapSlot id (EVM.signed (tickPositionWord compressed)) := by
  change keccakWord ⟨0⟩ ⟨64⟩
    (twoWordHashMem (tickPositionWord compressed) (poolSlot id + UInt256.ofNat 5) mem) = _
  rw [mappingMemory_slot_any, tickBitmapSlot, wordOfInt_signed]
  rfl

theorem tickScanStorageLoad {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I)
    (mem : ByteArray) (id compressed : UInt256) :
    solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64) (tickScanMemory mem id compressed)) evm.accountMap I =
      tickBitmapWord evm id (EVM.signed (tickPositionWord compressed)) := by
  rw [tickScanMemory_hash]
  exact (storageLoad_codeOwner_eq_solcSlotWordAt _ I _ (by rw [hI])).symm

theorem tickScanStorageLoad_compiled {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I)
    (mem : ByteArray) (id compressed : UInt256) :
    (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD
      (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((poolSlot id + UInt256.ofNat 5).toByteArray.write 0
          ((UInt256.signextend (UInt256.ofNat 1) (UInt256.sar (UInt256.ofNat 8)
            (UInt256.signextend (UInt256.ofNat 2) compressed))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32)) ⟨0⟩)) =
      tickBitmapWord evm id (EVM.signed (tickPositionWord compressed)) :=
  tickScanStorageLoad hI mem id compressed

end Benchmarks.UniswapV4PoolManager
