import Benchmarks.CompoundIII.Comet.ScalarWrites
import Benchmarks.CompoundIII.Comet.InitializeWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def initializeSourceState (evm : EVM.State) : EVM.State :=
  storeTotalsIndex (storeTotalsIndex
    (storeLastAccrual evm (timestampWord evm.executionEnv)) false ⟨1000000000000000⟩)
    true ⟨1000000000000000⟩

def initializeTimeAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨1⟩
    (initializeTimeWord (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I))

def initializeAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let τ := initializeTimeAccounts σ I
  sstoreAccountMap I.codeOwner τ ⟨0⟩ (initializeIndicesWord (solcSlotWordAt ⟨0⟩ τ I))

-- LIBRARY CANDIDATE: combine successive writes to the two low uint64 fields.
theorem storeInitialIndices_accountMap (evm : EVM.State) :
    (storeTotalsIndex (storeTotalsIndex evm false ⟨1000000000000000⟩)
      true ⟨1000000000000000⟩).accountMap =
    sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
      (initializeIndicesWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  unfold storeTotalsIndex
  simp only [totalsIndexOffset, Bool.false_eq_true, if_false, if_true, storageStore_executionEnv]
  cases he : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
      rw [storageStore_absent evm _ he, storageStore_absent evm _ he,
        sstoreAccountMap_absent_same he]
  | some acc =>
      rw [storageLoad_storageStore_same_present evm _ he,
        storageStore_accountMap, storageStore_accountMap]
      simp only [show (0 : Fin 32).val = 0 from rfl, show (8 : Fin 32).val = 8 from rfl]
      rw [initializeIndicesWord_packed, ← sstoreAccountMap_self_update]

theorem initializeSourceState_accountMap {σ σ₀ A I} {g : Sat256} :
    (initializeSourceState (initState σ σ₀ g A I)).accountMap = initializeAccounts σ I := by
  unfold initializeSourceState
  rw [storeInitialIndices_accountMap]
  simp only [storeLastAccrual, storageStore_executionEnv, storageStore_accountMap,
    initializeTimeWord_packed, storageLoad_initState_solcSlotWord]
  change sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨1⟩
      (initializeTimeWord (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I))) ⟨0⟩
    (initializeIndicesWord (Solm.EVM.storageLoad
      (Solm.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner ⟨1⟩
        (initializeTimeWord (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I))) I.codeOwner ⟨0⟩)) = _
  rw [storageLoad_after_initState_store]
  rfl

end Benchmarks.CompoundIII.Comet
