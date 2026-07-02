import Examples.OpenZeppelinBench.AccessControl.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl benchmark storage helpers

Helpers for the `_roles` nested mapping layout and full-slot/low-byte storage load-store facts.
-/

theorem accessControlStorageLocLoad_bytes32_raw (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 32, hbound := by decide,
          type := .bytes ⟨31, by decide⟩ }
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [Reasoning.Theory.bytes32Loc] using storageLocLoad_bytes32 evm slot

theorem accessControlStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot)
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [bytes32Loc] using accessControlStorageLocLoad_bytes32_raw evm slot

theorem accessControlStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem accessControlStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool false := by
  simpa [boolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0_false evm slot hzero

theorem accessControlStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool true := by
  simpa [boolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0_true evm slot hnz

theorem accessControlAccountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256) (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) :=
  accountMapEquiv_sstoreAccountMap a slot val hστ

theorem accessControlEVMStateEquiv_storageStore_codeOwner {evm₁ evm₂ : EVM.State}
    (h : EVMStateEquiv evm₁ evm₂) (slot : UInt256) {val₁ val₂ : UInt256}
    (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) :=
  EVMStateEquiv.storageStore_codeOwner h slot hval

end OpenZeppelinBench.AccessControl
