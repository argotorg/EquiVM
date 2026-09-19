import Solm.Benchmarks.Auction.SettleStorage
import Solm.Benchmarks.Auction.InitializeState

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def clearSettledWord (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 160 + 2 ^ 168 * (old.toNat / 2 ^ 168))

def clearAuctionPackedWord (old : UInt256) : UInt256 :=
  UInt256.land old (UInt256.lnot ⟨2 ^ 168 - 1⟩)

set_option maxRecDepth 2048 in
theorem clearAuctionPackedWord_toNat (old : UInt256) :
    (clearAuctionPackedWord old).toNat = old.toNat / 2 ^ 168 * 2 ^ 168 := by
  rw [clearAuctionPackedWord, u256_land_comm]
  exact u256_land_high_mask_toNat old 168 (by decide)

-- GENERALIZES the offset-zero bool write to the settled flag at byte 20.
set_option maxRecDepth 2048 in
theorem storageLocStore_settledFalse (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (auctionBoolLocAt slot 20) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord auctionBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20 ++
      (EVM.Word.toBytesLEWithSizeProof false.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 21) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof false.toUInt256).2]
  change _ % 2 ^ 160 + 2 ^ 160 * 0 + 2 ^ 168 * (_ / 2 ^ 168) =
    (_ % 2 ^ 160 + 2 ^ 168 * (_ / 2 ^ 168)) % UInt256.size
  rw [Nat.mul_zero, Nat.add_zero]
  apply (Nat.mod_eq_of_lt _).symm
  have hb : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256 :=
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
  have hlo := Nat.mod_lt
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat (by decide : 0 < 2 ^ 160)
  change _ < 2 ^ 256
  omega

theorem clearBidderThenSettled (old : UInt256) :
    clearSettledWord (setAddressOffset0Word old ⟨0⟩) = clearAuctionPackedWord old := by
  apply u256_inj
  change ((setAddressOffset0Word old ⟨0⟩).toNat % 2 ^ 160 +
    2 ^ 168 * ((setAddressOffset0Word old ⟨0⟩).toNat / 2 ^ 168)) % UInt256.size = _
  rw [setAddressOffset0Word_toNat old ⟨0⟩ (by decide),
    clearAuctionPackedWord_toNat]
  change ((0 + old.toNat / 2 ^ 160 * 2 ^ 160) % 2 ^ 160 +
    2 ^ 168 * ((0 + old.toNat / 2 ^ 160 * 2 ^ 160) / 2 ^ 168)) % (2 ^ 256) = _
  have hb := old.val.isLt
  change old.toNat < 2 ^ 256 at hb
  omega

theorem auctionFieldWrite (evm evm' : EVM.State) (locals : Store) (name : Ident)
    (ty : StorageType) (loc : StorageLoc) (value : Value)
    (hbase : locals.get? "auction" = none)
    (hty : storageTypeAt? auctionContract.storage
      { base := "auction", steps := [.field name] } = some ty)
    (hloc : auctionConfig.storage.layout
      { base := "auction", steps := [.field name] } = fun _ ↦ some loc)
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True)
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm
      .storage (aField name) value =
        .ok ({ contract := auctionContract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value hbase _ hty hloc hscalar hstore
  simp [aField, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, pure,
    bind]

def clearBidderState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ⟨0⟩)

def clearSettledState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
    (clearSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))

def clearAuctionPackedState (evm : EVM.State) : EVM.State :=
  clearSettledState (clearBidderState evm)

theorem clearAuctionPackedState_accounts (evm : EVM.State) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨211⟩
        (clearAuctionPackedWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)))
      (clearAuctionPackedState evm).accountMap := by
  unfold clearAuctionPackedState clearSettledState clearBidderState
  rw [storageStore_executionEnv]
  cases ha : evm.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
    rw [storageStore_absent evm _ ha, storageStore_absent evm _ ha,
      sstoreAccountMap_absent_same ha]
    exact accountMapEquiv.refl _
  | some acc =>
    rw [storageLoad_storageStore_same_present evm _ ha, clearBidderThenSettled,
      storageStore_accountMap, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap_self_update _ _ _ _ _

theorem SourceState.clearAuctionPacked {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm) :
    SourceState s0 I cA
      (sstoreAccountMap I.codeOwner σ ⟨211⟩ (clearAuctionPackedWord (storedWord σ I ⟨211⟩)))
      (clearAuctionPackedState evm) := by
  have hs1 := hs.storageWrite ⟨211⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm I.codeOwner ⟨211⟩) ⟨0⟩)
  have hs2 := hs1.storageWrite ⟨211⟩
    (clearSettledWord (Solm.EVM.storageLoad (clearBidderState evm) I.codeOwner ⟨211⟩))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [clearAuctionPackedState, clearSettledState, clearBidderState,
      storageStore_executionEnv, hs.env] using hs2.world
  · simp only [clearAuctionPackedState, clearSettledState, clearBidderState,
      storageStore_executionEnv, hs.env]
  · simp only [clearAuctionPackedState, clearSettledState, clearBidderState,
      storageStore_createdAccounts, hs.created]
  · have he := clearAuctionPackedState_accounts evm
    rw [storedWord_equiv hs.accounts, ← hs.env]
    exact (accountMapEquiv_sstoreAccountMap _ _ _ hs.accounts).trans he

end Auction
