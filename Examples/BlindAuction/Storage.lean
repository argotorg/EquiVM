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


theorem blindAuctionStorageLocStore_uint256_natCast (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (blindAuctionUint256Loc slot) (.int ↑val.toNat) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  change storageLocStore evm (blindAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) = _
  erw [storageLocStore_uint256]


def blindAuctionSetAddressWord (old addr : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask)) (UInt256.land addr solcAddrMask)


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


end BlindAuction
