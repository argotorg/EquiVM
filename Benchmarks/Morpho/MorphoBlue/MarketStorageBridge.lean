import Benchmarks.Morpho.MorphoBlue.MarketParamsStorage
import Benchmarks.Morpho.MorphoBlue.MarketStorageCommon
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def storeAddressAccounts (σ : AccountMap) (I : ExecutionEnv) (slot value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ slot (setAddressOffset0Word (solcSlotWordAt slot σ I) value)

theorem storeAddressWord_accounts (evm : EVM.State) (slot value : UInt256) :
    (storeAddressWord evm slot value).accountMap =
      storeAddressAccounts evm.accountMap evm.executionEnv slot value := by
  simp only [storeAddressWord, storageStore_accountMap, storeAddressAccounts,
    storageLoad_eq_solcSlotWord, solcSlotWordAt]

def storeMarketParamsAccounts (σ : AccountMap) (I : ExecutionEnv) (id : UInt256)
    (p : MarketParamsWords) : AccountMap :=
  let s1 := storeAddressAccounts σ I (marketParamsFieldSlot id 0) p.loanToken
  let s2 := storeAddressAccounts s1 I (marketParamsFieldSlot id 1) p.collateralToken
  let s3 := storeAddressAccounts s2 I (marketParamsFieldSlot id 2) p.oracle
  let s4 := storeAddressAccounts s3 I (marketParamsFieldSlot id 3) p.irm
  sstoreAccountMap I.codeOwner s4 (marketParamsFieldSlot id 4) p.lltv

theorem storeMarketParams_accounts (evm : EVM.State) (id : UInt256) (p : MarketParamsWords) :
    (storeMarketParams evm id p).accountMap =
      storeMarketParamsAccounts evm.accountMap evm.executionEnv id p := by
  have henv (e : EVM.State) (s w : UInt256) :
      (storeAddressWord e s w).executionEnv = e.executionEnv := storageStore_executionEnv _ _ _ _
  simp only [storeMarketParams, storageStore_accountMap, storeAddressWord_accounts,
    henv, storeMarketParamsAccounts]

theorem storeMarketLastUpdate_accounts (evm : EVM.State) (id value : UInt256) :
    (storeMarketLastUpdate evm id value).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap (marketFieldSlot id 4)
        (setUint128LowWord (solcSlotWordAt (marketFieldSlot id 4) evm.accountMap evm.executionEnv) value) := by
  simp only [storeMarketLastUpdate, storageStore_accountMap, storageLoad_eq_solcSlotWord, solcSlotWordAt]

theorem storeMarketParams_world (evm : EVM.State) (id : UInt256) (p : MarketParamsWords) :
    (storeMarketParams evm id p).σ₀ = evm.σ₀ := by
  simp only [storeMarketParams, storeAddressWord, storageStore_σ₀]

end Benchmarks.Morpho.MorphoBlue
