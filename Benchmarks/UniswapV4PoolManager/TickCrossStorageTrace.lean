import Benchmarks.UniswapV4PoolManager.TickCrossWords
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.WordNarrowCast

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickCrossMemory (mem : ByteArray) (id tick : UInt256) : ByteArray :=
  twoWordHashMem (UInt256.signextend (UInt256.ofNat 2) tick) (poolSlot id + UInt256.ofNat 4) mem

theorem tickCrossMemory_hash (mem : ByteArray) (id tick : UInt256) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (tickCrossMemory mem id tick) =
      tickSlot id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) := by
  change keccakWord ⟨0⟩ ⟨64⟩
    (twoWordHashMem (UInt256.signextend (UInt256.ofNat 2) tick) (poolSlot id + UInt256.ofNat 4) mem) = _
  rw [mappingMemory_slot_any, tickSlot, wordOfInt_signed]
  rfl

theorem tickCrossMemory_hash_compiled (mem : ByteArray) (id tick : UInt256) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((poolSlot id + UInt256.ofNat 4).toByteArray.write 0
        ((UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) tick)).toByteArray.write
          0 mem (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32) =
      tickSlot id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) := by
  rw [signextend24_idempotent]
  exact tickCrossMemory_hash mem id tick

theorem tickCrossField_load {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I)
    (id : UInt256) (tick : Int) (field : TickField) :
    tickFieldWord evm id tick field = solcSlotWordAt (field.slot (tickSlot id tick)) evm.accountMap I :=
  storageLoad_codeOwner_eq_solcSlotWordAt _ I _ (by rw [hI])

def tickCrossAccounts (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (tick : Int)
    (growth0 growth1 : UInt256) : AccountMap :=
  let a0 := sstoreAccountMap I.codeOwner σ (tickSlot id tick + ⟨1⟩)
    (UInt256.sub growth0 (solcSlotWordAt (tickSlot id tick + ⟨1⟩) σ I))
  sstoreAccountMap I.codeOwner a0 (tickSlot id tick + ⟨2⟩)
    (UInt256.sub growth1 (solcSlotWordAt (tickSlot id tick + ⟨2⟩) a0 I))

theorem tickCrossPost_accounts {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I)
    (id : UInt256) (tick : Int) (growth0 growth1 : UInt256) :
    (tickCrossPost evm id tick growth0 growth1).accountMap =
      tickCrossAccounts evm.accountMap I id tick growth0 growth1 := by
  have h0 := tickCrossField_load hI id tick .feeGrowthOutside0
  have hI1 : (tickCrossWrite0 evm id tick growth0).executionEnv = I := by
    rw [tickCrossWrite0, storageStore_executionEnv, hI]
  have hs1 : (tickCrossWrite0 evm id tick growth0).accountMap =
      sstoreAccountMap I.codeOwner evm.accountMap (tickSlot id tick + ⟨1⟩)
        (UInt256.sub growth0 (solcSlotWordAt (tickSlot id tick + ⟨1⟩) evm.accountMap I)) := by
    rw [tickCrossWrite0, storageStore_accountMap, hI, h0]
    rfl
  have h1 := tickCrossField_load hI1 id tick .feeGrowthOutside1
  rw [tickCrossPost, storageStore_accountMap, hI1, h1, hs1]
  rfl

theorem tickCrossNet_compiled {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I)
    (id : UInt256) (tick : Int) (growth0 growth1 : UInt256) :
    UInt256.sar (UInt256.ofNat 128)
      (solcSlotWordAt (tickSlot id tick) (tickCrossAccounts evm.accountMap I id tick growth0 growth1) I) =
      tickCrossNet evm id tick growth0 growth1 := by
  rw [← tickCrossPost_accounts hI]
  exact congrArg (UInt256.sar (UInt256.ofNat 128))
    (tickCrossField_load ((tickCrossPost_executionEnv ..).trans hI) id tick .liquidityPacked).symm

end Benchmarks.UniswapV4PoolManager
