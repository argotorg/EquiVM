import Examples.SimpleAuction.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace SimpleAuction

/-!
# SimpleAuction storage helpers

Shared storage-map and mapping-slot helpers for the per-function proofs live here.  Phase-1
workers should keep this file read-only; local helpers that need promotion should be tagged in the
owning function file and reconciled after the parallel body pass.
-/

/-- Storing a full-slot SimpleAuction `uint256` writes exactly the EVM word in the same slot. -/
theorem simpleAuctionStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (simpleAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [simpleAuctionUint256Loc, uint256Loc] using storageLocStore_uint256 evm slot val

def simpleAuctionSetAddressWord (old addr : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask)) (UInt256.land addr solcAddrMask)

theorem simpleAuctionSourceWord_canonical (I : ExecutionEnv) :
    (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt (by decide : AccountAddress.size ≤ UInt256.size))]
  have hsrc : I.source.val < AccountAddress.size := I.source.isLt
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hsrc

theorem simpleAuctionStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (simpleAuctionBoolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [simpleAuctionBoolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem simpleAuctionStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (simpleAuctionBoolLoc slot) = .bool false := by
  simpa [simpleAuctionBoolLoc, boolOffset0Loc] using
    storageLocLoad_bool_offset0_false evm slot hzero

theorem simpleAuctionStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (simpleAuctionBoolLoc slot) = .bool true := by
  simpa [simpleAuctionBoolLoc, boolOffset0Loc] using
    storageLocLoad_bool_offset0_true evm slot hnz

theorem simpleAuctionHigh160Mask_toNat (old : UInt256) :
    (UInt256.land old (UInt256.lnot solcAddrMask)).toNat =
      (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  exact addressOffset0High160Mask_toNat old

theorem simpleAuctionSetAddressNat_lt_size (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 < UInt256.size := by
  exact setAddressOffset0Nat_lt_size old addr hcanon

theorem simpleAuctionSetAddressWord_eq (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    simpleAuctionSetAddressWord old addr =
      UInt256.ofNat (addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160) := by
  simpa [simpleAuctionSetAddressWord, setAddressOffset0Word] using
    setAddressOffset0Word_eq old addr hcanon

theorem simpleAuctionSetAddressWord_toNat (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    (simpleAuctionSetAddressWord old addr).toNat =
      addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  simpa [simpleAuctionSetAddressWord, setAddressOffset0Word] using
    setAddressOffset0Word_toNat old addr hcanon

theorem simpleAuctionStorageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (simpleAuctionAddrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (simpleAuctionSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  simpa [simpleAuctionAddrLoc, addressOffset0Loc, simpleAuctionSetAddressWord,
    setAddressOffset0Word] using storageLocStore_address_offset0 evm slot addr hcanon

theorem simpleAuctionStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (simpleAuctionBoolLoc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  simpa [simpleAuctionBoolLoc, boolOffset0Loc] using storageLocStore_bool_true_offset0 evm slot

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem simpleAuctionStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  exact storageStore_accountMap evm a slot val

/-- `EVM.storageStore` does not create accounts. -/
theorem simpleAuctionStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  exact storageStore_createdAccounts evm a slot val

/-! ## Storage-map preservation re-exports -/

theorem simpleAuctionUInt256_compare_eq_val_compare (a b : UInt256) :
    compare a b = compare a.val b.val := uInt256_compare_eq_val_compare a b

theorem simpleAuctionStorage_findD_insert_ne
    (storage : Storage) (readSlot writeSlot val default : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).findD readSlot default = storage.findD readSlot default :=
  storage_findD_insert_ne storage readSlot writeSlot val default hne

theorem simpleAuctionStorage_findD_erase_ne
    (storage : Storage) (readSlot writeSlot default : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).findD readSlot default = storage.findD readSlot default :=
  storage_findD_erase_ne storage readSlot writeSlot default hne

theorem simpleAuctionStorage_findD_update_ne
    (storage : Storage) (readSlot writeSlot val default : UInt256) (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).findD
        readSlot default) = storage.findD readSlot default :=
  storage_findD_update_ne storage readSlot writeSlot val default hne

theorem simpleAuctionStorage_find?_insert_ne
    (storage : Storage) (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).find? readSlot = storage.find? readSlot :=
  storage_find?_insert_ne storage readSlot writeSlot val hne

theorem simpleAuctionStorage_find?_erase_ne
    (storage : Storage) (readSlot writeSlot : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).find? readSlot = storage.find? readSlot :=
  storage_find?_erase_ne storage readSlot writeSlot hne

theorem simpleAuctionStorage_find?_update_ne
    (storage : Storage) (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    ((if val == (default : UInt256) then storage.erase writeSlot
      else storage.insert writeSlot val).find? readSlot) = storage.find? readSlot :=
  storage_find?_update_ne storage readSlot writeSlot val hne

theorem simpleAuctionAccountMap_find_insert_self
    (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.insert a acc).find? a = some acc :=
  accountMap_find_insert_self σ a acc

theorem simpleAuctionStorage_findD_insert_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 default : UInt256) :
    ((storage.insert writeSlot val1).insert writeSlot val2).findD readSlot default =
      (storage.insert writeSlot val2).findD readSlot default :=
  storage_findD_insert_insert_self storage writeSlot readSlot val1 val2 default

theorem simpleAuctionStorage_findD_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).findD readSlot
        (default : UInt256)) =
      (storage.insert writeSlot val2).findD readSlot (default : UInt256) :=
  storage_findD_update_insert_self storage writeSlot readSlot val1 val2

end SimpleAuction
