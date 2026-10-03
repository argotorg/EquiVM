import Examples.BlindAuction.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace BlindAuction

/-!
# BlindAuction-local storage helpers

This file contains BlindAuction's storage-location and word-encoding bridges for body proofs.
Generic storage-map facts are imported from `Reasoning.Storage`.
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

theorem blindAuctionStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionAddrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [blindAuctionAddrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

def blindAuctionSetAddressWord (old addr : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask)) (UInt256.land addr solcAddrMask)

theorem blindAuctionSetAddressNat_lt_size (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 < UInt256.size := by
  exact setAddressOffset0Nat_lt_size old addr hcanon

theorem blindAuctionSetAddressWord_eq (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    blindAuctionSetAddressWord old addr =
      UInt256.ofNat (addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160) := by
  simpa [blindAuctionSetAddressWord, setAddressOffset0Word] using
    setAddressOffset0Word_eq old addr hcanon

theorem blindAuctionSetAddressWord_toNat (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    (blindAuctionSetAddressWord old addr).toNat =
      addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  simpa [blindAuctionSetAddressWord, setAddressOffset0Word] using
    setAddressOffset0Word_toNat old addr hcanon

theorem blindAuctionStorageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (blindAuctionAddrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (blindAuctionSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  simpa [blindAuctionAddrLoc, addressOffset0Loc, blindAuctionSetAddressWord,
    setAddressOffset0Word] using storageLocStore_address_offset0 evm slot addr hcanon

theorem blindAuctionStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionBoolLoc slot) =
      wordToElem .bool
        (UInt256.land ⟨255⟩ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  rw [Reasoning.Theory.u256_land_comm ⟨255⟩
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)]
  simpa [blindAuctionBoolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

end BlindAuction
