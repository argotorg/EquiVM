import Examples.BytesStoreLite.FullPacketTag

/-!
# BytesStoreLite — packet storage readback helpers

Small readback facts for the `setPacket(bytes,uint256)` storage sequence.  These sit outside the
large packet-tag runtime proof so local packet storage refactors do not force that file to change.
-/

namespace BytesStoreLite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

theorem bytesStoreLitePacketLengthHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreLitePacketLengthHeaderWord σ_evm I =
      bytesStoreLitePacketLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩

theorem bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨2⟩ =
      bytesStoreLitePacketLengthHeaderWord σ_evm I := by
  simpa [bytesStoreLitePacketLengthHeaderWord] using
    bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) ⟨2⟩ hAccounts

theorem bytesStoreLitePacketDataWordAfterDataSstore_zero
    (σ : AccountMap) (I : ExecutionEnv) :
    ((sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      ⟨0⟩ := by
  rw [bytesStoreLiteStorageWordAfterSstore_eq_if]
  cases hacc : σ.find? I.codeOwner with
  | none => rfl
  | some acc => rfl

theorem bytesStoreLitePacketDataWordAfterDataSstore_of_find_some
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account} {word : UInt256}
    (hacc : σ.find? I.codeOwner = some acc)
    (hword : (word == (default : UInt256)) = false) :
    ((sstoreAccountMap I.codeOwner σ ⟨2⟩ word).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      word := by
  exact sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc ⟨2⟩ word hacc hword

theorem bytesStoreLitePacketDataWordAfterDataTagSstore_zero
    (σ : AccountMap) (I : ExecutionEnv) (tag : UInt256) :
    ((sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩)
        ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      ⟨0⟩ := by
  exact bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩) (I := I) (tag := tag)
    (bytesStoreLitePacketDataWordAfterDataSstore_zero σ I)

theorem bytesStoreLitePacketDataWordAfterDataTagSstore_of_find_some
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account} {word tag : UInt256}
    (hacc : σ.find? I.codeOwner = some acc)
    (hword : (word == (default : UInt256)) = false) :
    ((sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨2⟩ word)
        ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      word := by
  exact bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩ word) (I := I) (tag := tag)
    (bytesStoreLitePacketDataWordAfterDataSstore_of_find_some hacc hword)

end BytesStoreLite
