import Benchmarks.Dss.Clipper.RedoSuccessEVM
import Benchmarks.Dss.Clipper.RedoSuccessSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Clipper

theorem clipperRedoTopSlotWord_eq (I : ExecutionEnv) :
    clipperRedoTopSlotWord (clipperRedoIdWord I) = clipperRedoSalesTopSlot I := by
  simp [clipperRedoTopSlotWord, clipperRedoSalesTopSlot,
    clipperRedoSalesBaseSlot_eq]

theorem clipperRedoTopState_accounts_eq
    {σ τ : AccountMap} (evm : EVM.State) (I : ExecutionEnv) (topNew : UInt256)
    (hevmAccount : evm.accountMap = τ)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : σ = τ) :
    sstoreAccountMap I.codeOwner σ
        (clipperRedoTopSlotWord (clipperRedoIdWord I)) topNew =
      (clipperRedoTopState evm I topNew).accountMap := by
  have hMaps : σ = evm.accountMap := hAccounts.trans hevmAccount.symm
  simpa [clipperRedoTopState, storageStore_accountMap, hevmEnv,
    clipperRedoTopSlotWord_eq] using
    congrArg (fun m => sstoreAccountMap I.codeOwner m
      (clipperRedoSalesTopSlot I) topNew) hMaps

theorem clipperRedoTipWord_eq_of_accounts_eq
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : σ = evm.accountMap) :
    clipperRedoTipWord σ I = clipperRedoTipSolmWord evm := by
  rw [hAccounts]
  simp [clipperRedoTipWord, clipperRedoTipSolmWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, solcSlotWord, hevmEnv]

theorem clipperRedoChipWord_eq_of_accounts_eq
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : σ = evm.accountMap) :
    clipperRedoChipWord σ I = clipperRedoChipSolmWord evm := by
  have hslot := congrArg
    (fun m : AccountMap =>
      (m.get? I.codeOwner).option (⟨0⟩ : UInt256)
        (fun acc => acc.storage.getD ⟨8⟩ ⟨0⟩)) hAccounts
  rw [clipperRedoChipWord, clipperRedoChipSolmWord, hevmEnv]
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord] using congrArg
      (fun w => UInt256.land w (UInt256.ofNat (2 ^ 64 - 1))) hslot

end Benchmarks.Dss.Clipper
