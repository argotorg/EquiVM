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

/-- `wordOfInt (Int.ofNat a.toNat) = a` for an EVM word. -/
theorem blindAuctionWordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

/-- Storing a full-slot BlindAuction `uint256` writes exactly the EVM word in the same slot. -/
theorem blindAuctionStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (blindAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore storageLocWriteWord blindAuctionUint256Loc
  simp only [valueToWord, blindAuctionWordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = val.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem blindAuctionStorageLocStore_uint256_natCast (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (blindAuctionUint256Loc slot) (.int ↑val.toNat) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  change storageLocStore evm (blindAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) = _
  rw [blindAuctionStorageLocStore_uint256]

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem blindAuctionStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

/-- `EVM.storageStore` does not create accounts. -/
theorem blindAuctionStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

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
