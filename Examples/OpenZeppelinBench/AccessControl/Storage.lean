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

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem accessControlAccountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256) (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) := by
  by_cases hval : (val == (default : UInt256)) = false
  · exact accountMapEquiv_sstoreAccountMap_insert a slot val hστ hval
  have hzero : (val == (default : UInt256)) = true := by
    cases h : (val == (default : UInt256)) <;> simp [h] at hval ⊢
  intro addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    specialize hστ a
    cases hσ : σ.find? a with
    | none =>
        cases hτ : τ.find? a with
        | none =>
            simp [hσ, hτ, Option.option]
        | some accτ =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
    | some accσ =>
        cases hτ : τ.find? a with
        | none =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
        | some accτ =>
            have hacc : accountEquiv accσ accτ := by simpa [hσ, hτ] using hστ
            simpa [hσ, hτ, Option.option, hzero, accountMap_find_insert_self] using
              accountEquiv_erase_storage_of_equiv slot hacc
  · unfold sstoreAccountMap
    specialize hστ addr
    cases hσa : σ.find? a <;> cases hτa : τ.find? a <;> simp only [Option.option]
    · exact hστ
    · rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
theorem accessControlEVMStateEquiv_storageStore_codeOwner {evm₁ evm₂ : EVM.State}
    (h : EVMStateEquiv evm₁ evm₂) (slot : UInt256) {val₁ val₂ : UInt256}
    (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) := by
  subst val₂
  refine ⟨?_, ?_, ?_⟩
  · rw [storageStore_executionEnv, storageStore_executionEnv]
    exact h.executionEnv
  · rw [storageStore_createdAccounts, storageStore_createdAccounts]
    exact h.createdAccounts
  · rw [storageStore_accountMap, storageStore_accountMap, h.executionEnv]
    exact accessControlAccountMapEquiv_sstoreAccountMap evm₂.executionEnv.codeOwner slot val₁
      h.accountMap

end OpenZeppelinBench.AccessControl
