import Examples.OpenZeppelinBench.Pausable.Bytecode
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-!
# Pausable storage helpers

The benchmark has one packed `bool` in slot `0`, byte offset `0`.  Most low-byte storage facts are
reused from `Reasoning.Storage` / packed scalar storage.
-/

def pausedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def pausedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (pausedRawWord σ I) ⟨255⟩

def pausedSetTrueWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩

def pausedSetFalseWord (w : UInt256) : UInt256 :=
  UInt256.land w (UInt256.lnot ⟨255⟩)

def pausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetTrueWord (pausedRawWord σ I))

def unpausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetFalseWord (pausedRawWord σ I))

def pausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

def unpausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

theorem pausableStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem pausableStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool false := by
  simpa [boolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0_false evm slot hzero

theorem pausableStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool true := by
  simpa [boolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0_true evm slot hnz

theorem pausableStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  simpa [boolLoc, boolOffset0Loc, pausedSetTrueWord] using
    storageLocStore_bool_true_offset0 evm slot

theorem pausableStorageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  simpa [boolLoc, boolOffset0Loc, pausedSetFalseWord] using
    storageLocStore_bool_false_offset0 evm slot

theorem pausableStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  exact storageStore_accountMap evm a slot val

theorem pausableStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  exact storageStore_createdAccounts evm a slot val

theorem pausableAccountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) :=
  accountMapEquiv_sstoreAccountMap a slot val hστ

theorem pausableEVMStateEquiv_storageStore_codeOwner {evm₁ evm₂ : EVM.State}
    (h : EVMStateEquiv evm₁ evm₂) (slot : UInt256) {val₁ val₂ : UInt256}
    (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) :=
  EVMStateEquiv.storageStore_codeOwner h slot hval

theorem pausePostState_accountMap (evm : EVM.State) :
    (pausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [pausePostState, pausableStorageStore_accountMap]

theorem unpausePostState_accountMap (evm : EVM.State) :
    (unpausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [unpausePostState, pausableStorageStore_accountMap]

theorem pausePostState_createdAccounts (evm : EVM.State) :
    (pausePostState evm).createdAccounts = evm.createdAccounts := by
  simp [pausePostState, pausableStorageStore_createdAccounts]

theorem unpausePostState_createdAccounts (evm : EVM.State) :
    (unpausePostState evm).createdAccounts = evm.createdAccounts := by
  simp [unpausePostState, pausableStorageStore_createdAccounts]

end OpenZeppelinBench.Pausable
