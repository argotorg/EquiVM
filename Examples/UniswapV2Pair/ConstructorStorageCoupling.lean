import Examples.UniswapV2Pair.ConstructorSource
import Examples.UniswapV2Pair.ConstructorStoreRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

theorem constructorStoredAccountMap_eq {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (he : evm.executionEnv = I) (ha : Eq σ evm.accountMap) :
    Eq (constructorStoredAccountMap σ I
      (constructorDomainHashWord (UInt256.ofNat I.codeOwner.val)))
      (constructorFactoryState (constructorDomainState evm)).accountMap := by
  let σD := sstoreAccountMap I.codeOwner σ ⟨3⟩
    (constructorDomainHashWord (UInt256.ofNat I.codeOwner.val))
  have haD : Eq σD (constructorDomainState evm).accountMap := by
    simpa only [constructorDomainState, storageStore_accountMap, he] using
      congrArg (fun accounts => sstoreAccountMap I.codeOwner accounts ⟨3⟩
        (constructorDomainHashWord (UInt256.ofNat I.codeOwner.val))) ha
  have heD : (constructorDomainState evm).executionEnv = I := by
    simp only [constructorDomainState, storageStore_executionEnv, he]
  have hslot : solcSlotWordAt ⟨5⟩ σD I =
      Solm.EVM.storageLoad (constructorDomainState evm) I.codeOwner ⟨5⟩ := by
    simpa only [solcSlotWordAt, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage]
      using congrArg (fun accounts => solcSlotWordAt ⟨5⟩ accounts I) haD
  unfold constructorStoredAccountMap constructorFactoryState
  rw [storageStore_accountMap, heD]
  change Eq (sstoreAccountMap I.codeOwner σD ⟨5⟩ _)
    (sstoreAccountMap I.codeOwner (constructorDomainState evm).accountMap ⟨5⟩ _)
  rw [← hslot]
  rw [← haD]

end UniswapV2Pair
