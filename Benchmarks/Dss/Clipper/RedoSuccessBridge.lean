import Benchmarks.Dss.Clipper.RedoSuccessEVM
import Benchmarks.Dss.Clipper.RedoSuccessSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Clipper

theorem clipperRedoTopSlotWord_eq (I : ExecutionEnv) :
    clipperRedoTopSlotWord (clipperRedoIdWord I) = clipperRedoSalesTopSlot I := by
  simp [clipperRedoTopSlotWord, clipperRedoSalesTopSlot,
    clipperRedoSalesBaseSlot_eq]

theorem clipperRedoTopState_accountMapEquiv
    {σ τ : AccountMap} (evm : EVM.State) (I : ExecutionEnv) (topNew : UInt256)
    (hevmAccount : evm.accountMap = τ)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ
        (clipperRedoTopSlotWord (clipperRedoIdWord I)) topNew)
      (clipperRedoTopState evm I topNew).accountMap := by
  subst τ
  simpa [clipperRedoTopState, storageStore_accountMap, hevmEnv,
    clipperRedoTopSlotWord_eq] using
    (accountMapEquiv_sstoreAccountMap I.codeOwner
      (clipperRedoSalesTopSlot I) topNew hAccounts)

theorem clipperRedoTipWord_eq_of_accountMapEquiv
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    clipperRedoTipWord σ I = clipperRedoTipSolmWord evm := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  rw [clipperRedoTipWord, clipperRedoTipSolmWord, hevmEnv]
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord] using congrArg
      (fun w => UInt256.land
        (UInt256.div w (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)) hslot

theorem clipperRedoChipWord_eq_of_accountMapEquiv
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (hevmEnv : evm.executionEnv = I)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    clipperRedoChipWord σ I = clipperRedoChipSolmWord evm := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  rw [clipperRedoChipWord, clipperRedoChipSolmWord, hevmEnv]
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord] using congrArg
      (fun w => UInt256.land w (UInt256.ofNat (2 ^ 64 - 1))) hslot

end Benchmarks.Dss.Clipper
