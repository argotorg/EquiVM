import Examples.ERC20.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ERC20-local storage-store and bool-return helpers -/

/-- `wordOfInt (Int.ofNat a.toNat) = a` for an EVM word. -/
theorem erc20WordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

/-- Storing a full-slot ERC20 `uint256` writes exactly the EVM word in the same slot. -/
theorem erc20StorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (erc20Uint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore storageLocWriteWord erc20Uint256Loc
  simp only [valueToWord, erc20WordOfInt_ofNat_toNat, bind, Option.bind, pure]
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
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytesLE_roundtrip]

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem erc20StorageStore_accountMap (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

/-- `EVM.storageStore` does not create accounts. -/
theorem erc20StorageStore_createdAccounts (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

/-! ## ERC20-local storage-map preservation helpers

Moved to the library: `storage_findD_insert_ne` / `_erase_ne` / `_update_ne`,
`rbmap_find?_erase_ne`, and `accountMap_find_insert_self` are in `Reasoning.Memory`; the `UInt256`
`compare` `Std.*Cmp` instances and `uInt256_compare_eq_val_compare` are in `Reasoning.EVMWord`.
Kept here as thin re-exports so ERC20's call sites are unchanged. -/

theorem erc20UInt256_compare_eq_val_compare (a b : UInt256) :
    compare a b = compare a.val b.val := uInt256_compare_eq_val_compare a b

theorem erc20Storage_findD_insert_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).findD readSlot default = storage.findD readSlot default :=
  storage_findD_insert_ne storage readSlot writeSlot val default hne

theorem erc20Storage_findD_erase_ne (storage : Storage) (readSlot writeSlot default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).findD readSlot default = storage.findD readSlot default :=
  storage_findD_erase_ne storage readSlot writeSlot default hne

theorem erc20Storage_findD_update_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).findD
        readSlot default) = storage.findD readSlot default :=
  storage_findD_update_ne storage readSlot writeSlot val default hne

theorem erc20AccountMap_find_insert_self (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.insert a acc).find? a = some acc :=
  accountMap_find_insert_self σ a acc

/-- ABI-encoding `true` is the one-word value `1`.  Re-export of
    `Reasoning.Theory.boolTrueReturnEncoding`. -/
theorem erc20BoolTrueReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some (UInt256.toByteArray ⟨1⟩) :=
  boolTrueReturnEncoding

end ERC20
