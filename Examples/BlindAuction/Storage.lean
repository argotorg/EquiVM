import Examples.BlindAuction.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace BlindAuction

/-!
# BlindAuction-local storage helpers

This file is the contract-local facade for storage-map and full-word storage facts used by the body
proofs.  It is intentionally additive and mostly re-exports generic `Reasoning.Storage` lemmas under
BlindAuction-local names so per-function files do not duplicate RBMap proofs.
-/

/-- Storing a full-slot BlindAuction `uint256` writes exactly the EVM word in the same slot. -/
theorem blindAuctionStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (blindAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [blindAuctionUint256Loc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem blindAuctionStorageLocStore_uint256_natCast (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (blindAuctionUint256Loc slot) (.int ↑val.toNat) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  change storageLocStore evm (blindAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) = _
  rw [blindAuctionStorageLocStore_uint256]

theorem blindAuctionStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionUint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [blindAuctionUint256Loc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem blindAuctionStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionBoolLoc slot) =
      wordToElem .bool
        (UInt256.land ⟨255⟩ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  rw [Reasoning.Theory.u256_land_comm ⟨255⟩
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)]
  simpa [blindAuctionBoolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem blindAuctionStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  exact storageStore_accountMap evm a slot val

/-- `EVM.storageStore` does not create accounts. -/
theorem blindAuctionStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  exact storageStore_createdAccounts evm a slot val

/-! ## Storage-map preservation re-exports -/

theorem blindAuctionUInt256_compare_eq_val_compare (a b : UInt256) :
    compare a b = compare a.val b.val := uInt256_compare_eq_val_compare a b

theorem blindAuctionStorage_findD_insert_ne
    (storage : Storage) (readSlot writeSlot val default : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).findD readSlot default = storage.findD readSlot default :=
  storage_findD_insert_ne storage readSlot writeSlot val default hne

theorem blindAuctionStorage_findD_erase_ne
    (storage : Storage) (readSlot writeSlot default : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).findD readSlot default = storage.findD readSlot default :=
  storage_findD_erase_ne storage readSlot writeSlot default hne

theorem blindAuctionStorage_findD_update_ne
    (storage : Storage) (readSlot writeSlot val default : UInt256) (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).findD
        readSlot default) = storage.findD readSlot default :=
  storage_findD_update_ne storage readSlot writeSlot val default hne

theorem blindAuctionStorage_find?_insert_ne
    (storage : Storage) (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).find? readSlot = storage.find? readSlot :=
  storage_find?_insert_ne storage readSlot writeSlot val hne

theorem blindAuctionStorage_find?_erase_ne
    (storage : Storage) (readSlot writeSlot : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).find? readSlot = storage.find? readSlot :=
  storage_find?_erase_ne storage readSlot writeSlot hne

theorem blindAuctionStorage_find?_update_ne
    (storage : Storage) (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    ((if val == (default : UInt256) then storage.erase writeSlot
      else storage.insert writeSlot val).find? readSlot) = storage.find? readSlot :=
  storage_find?_update_ne storage readSlot writeSlot val hne

theorem blindAuctionAccountMap_find_insert_self (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.insert a acc).find? a = some acc :=
  accountMap_find_insert_self σ a acc

theorem blindAuctionStorage_findD_insert_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 default : UInt256) :
    ((storage.insert writeSlot val1).insert writeSlot val2).findD readSlot default =
      (storage.insert writeSlot val2).findD readSlot default :=
  storage_findD_insert_insert_self storage writeSlot readSlot val1 val2 default

theorem blindAuctionStorage_findD_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).findD readSlot
        (default : UInt256)) =
      (storage.insert writeSlot val2).findD readSlot (default : UInt256) :=
  storage_findD_update_insert_self storage writeSlot readSlot val1 val2

end BlindAuction
