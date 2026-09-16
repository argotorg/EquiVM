import Examples.UniswapV2Pair.ConstructorSource
import Examples.UniswapV2Pair.ConstructorStoreRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

theorem constructorStoredAccountMap_equiv {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (he : evm.executionEnv = I) (ha : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (constructorStoredAccountMap σ I
      (constructorDomainHashWord (UInt256.ofNat I.codeOwner.val)))
      (constructorFactoryState (constructorDomainState evm)).accountMap := by
  let σD := sstoreAccountMap I.codeOwner σ ⟨3⟩
    (constructorDomainHashWord (UInt256.ofNat I.codeOwner.val))
  have haD : accountMapEquiv σD (constructorDomainState evm).accountMap := by
    simpa only [constructorDomainState, storageStore_accountMap, he] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩
        (constructorDomainHashWord (UInt256.ofNat I.codeOwner.val)) ha
  have heD : (constructorDomainState evm).executionEnv = I := by
    simp only [constructorDomainState, storageStore_executionEnv, he]
  have hslot : uniswapSlotWord ⟨5⟩ σD I =
      Solm.EVM.storageLoad (constructorDomainState evm) I.codeOwner ⟨5⟩ := by
    simpa only [uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using
      accountMapEquiv_storage_findD haD I.codeOwner ⟨5⟩ ⟨0⟩
  unfold constructorStoredAccountMap constructorFactoryState
  rw [storageStore_accountMap, heD]
  change accountMapEquiv (sstoreAccountMap I.codeOwner σD ⟨5⟩ _)
    (sstoreAccountMap I.codeOwner (constructorDomainState evm).accountMap ⟨5⟩ _)
  rw [← hslot]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ _ haD

end UniswapV2Pair
