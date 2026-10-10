import Benchmarks.UniswapV4PoolManager.PoolUpdateTickFees

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickFeeWrites_accounts {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I)
    (id : UInt256) (tick : Int) :
    (tickFeeWrites evm id tick).accountMap =
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner evm.accountMap (tickSlot id tick+⟨1⟩)
          (solcSlotWordAt (poolSlot id+⟨1⟩) evm.accountMap I))
        (tickSlot id tick+⟨2⟩)
        (solcSlotWordAt (poolSlot id+⟨2⟩)
          (sstoreAccountMap I.codeOwner evm.accountMap (tickSlot id tick+⟨1⟩)
            (solcSlotWordAt (poolSlot id+⟨1⟩) evm.accountMap I)) I) := by
  have h0 : poolFeeGrowthWord evm id false = solcSlotWordAt (poolSlot id+⟨1⟩) evm.accountMap I :=
    storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])
  have hI1 : (tickFeeWrite0 evm id tick).executionEnv = I := by
    rw [tickFeeWrite0, storageStore_executionEnv, hI]
  have hs1 : (tickFeeWrite0 evm id tick).accountMap =
      sstoreAccountMap I.codeOwner evm.accountMap (tickSlot id tick+⟨1⟩)
        (solcSlotWordAt (poolSlot id+⟨1⟩) evm.accountMap I) := by
    rw [tickFeeWrite0, storageStore_accountMap, hI, h0]
  have h1 : poolFeeGrowthWord (tickFeeWrite0 evm id tick) id true =
      solcSlotWordAt (poolSlot id+⟨2⟩) (tickFeeWrite0 evm id tick).accountMap I :=
    storageLoad_codeOwner_eq_solcSlotWordAt _ I _ (by rw [hI1])
  rw [tickFeeWrites, storageStore_accountMap, hI1, h1, hs1]

end Benchmarks.UniswapV4PoolManager
