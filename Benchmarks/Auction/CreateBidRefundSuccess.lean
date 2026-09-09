import Benchmarks.Auction.CreateBidExtension
import Benchmarks.Auction.CreateBidRefund

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionCreateBidPackedBidderAddress_ne_zero (packed : UInt256)
    (hbidder : auctionPackedBidderWord packed ≠ ⟨0⟩) :
    AccountAddress.ofNat (auctionPackedBidderWord packed).toNat ≠
      AccountAddress.ofNat 0 := by
  intro haddr
  apply hbidder
  apply u256_inj
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat, Fin.val_ofNat] at hval
  have hcanon :
      (auctionPackedBidderWord packed).toNat < EVM.addressModulus := by
    simpa [auctionPackedBidderWord, EVM.addressModulus, EVM.twoPow,
      AccountAddress.size] using solcAddrMask_result_canonical packed
  have hmod :
      (auctionPackedBidderWord packed).toNat % AccountAddress.size =
        (auctionPackedBidderWord packed).toNat := by
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  rw [hmod] at hval
  simpa using hval

theorem auctionCreateBid_afterRefund_bidderAccounts_state
    {σEvm σSolm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σEvm σSolm)
    (hmap : evmSolm.accountMap = σSolm)
    (howner : evmSolm.executionEnv.codeOwner = I.codeOwner)
    (hsource : evmSolm.executionEnv.source = I.source)
    (hwei : evmSolm.executionEnv.weiValue = I.weiValue) :
    accountMapEquiv
      (auctionCreateBidBidderMap (auctionCreateBidAmountMap σEvm I) I)
      (auctionCreateBidBidderState (auctionCreateBidAmountState evmSolm)).accountMap := by
  let σAmountEvm := auctionCreateBidAmountMap σEvm I
  let evmAmountSolm := auctionCreateBidAmountState evmSolm
  have hamount :
      accountMapEquiv σAmountEvm evmAmountSolm.accountMap := by
    simpa [σAmountEvm, evmAmountSolm, auctionCreateBidAmountMap,
      auctionCreateBidAmountState, hmap, howner, hwei, storageStore_accountMap,
      storageStore_executionEnv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨208⟩ I.weiValue hAccounts
  have hslot211 :
      auctionSlotWord ⟨211⟩ σAmountEvm I =
        auctionSlotWord ⟨211⟩ evmAmountSolm.accountMap I :=
    accountMapEquiv_storage_findD hamount I.codeOwner ⟨211⟩ ⟨0⟩
  have hbidderVal :
      setAddressOffset0Word (auctionSlotWord ⟨211⟩ σAmountEvm I) (auctionSourceWord I) =
        setAddressOffset0Word (auctionSlotWord ⟨211⟩ evmAmountSolm.accountMap I)
          (auctionSourceWord I) := by
    rw [hslot211]
  have hbidder :
      accountMapEquiv
        (auctionCreateBidBidderMap σAmountEvm I)
        (auctionCreateBidBidderMap evmAmountSolm.accountMap I) := by
    unfold auctionCreateBidBidderMap
    rw [hbidderVal]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (setAddressOffset0Word (auctionSlotWord ⟨211⟩ evmAmountSolm.accountMap I)
        (auctionSourceWord I)) hamount
  simpa [σAmountEvm, evmAmountSolm, auctionCreateBidAmountMap, auctionCreateBidBidderMap,
    auctionCreateBidAmountState, auctionCreateBidBidderState, auctionSourceWord, howner,
    hsource, hwei, auctionSlotWord, storageStore_accountMap, storageStore_executionEnv,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hbidder

theorem auctionCreateBid_noExtension_afterRefund_postAccounts_state
    {σEvm σSolm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σEvm σSolm)
    (hmap : evmSolm.accountMap = σSolm)
    (howner : evmSolm.executionEnv.codeOwner = I.codeOwner)
    (hsource : evmSolm.executionEnv.source = I.source)
    (hwei : evmSolm.executionEnv.weiValue = I.weiValue) :
    accountMapEquiv
      (auctionCreateBidUnlockedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σEvm I) I) I)
      (auctionCreateBidUnlockedState
        (auctionCreateBidBidderState (auctionCreateBidAmountState evmSolm))).accountMap := by
  let σAmountEvm := auctionCreateBidAmountMap σEvm I
  let σBidderEvm := auctionCreateBidBidderMap σAmountEvm I
  let evmAmountSolm := auctionCreateBidAmountState evmSolm
  let evmBidderSolm := auctionCreateBidBidderState evmAmountSolm
  have hbidder :
      accountMapEquiv σBidderEvm evmBidderSolm.accountMap := by
    simpa [σAmountEvm, σBidderEvm, evmAmountSolm, evmBidderSolm] using
      auctionCreateBid_afterRefund_bidderAccounts_state
        (σEvm := σEvm) (σSolm := σSolm) (evmSolm := evmSolm) (I := I)
        hAccounts hmap howner hsource hwei
  have hunlocked :
      accountMapEquiv
        (auctionCreateBidUnlockedMap σBidderEvm I)
        (auctionCreateBidUnlockedMap evmBidderSolm.accountMap I) := by
    simpa [auctionCreateBidUnlockedMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hbidder
  simpa [σAmountEvm, σBidderEvm, evmAmountSolm, evmBidderSolm,
    auctionCreateBidAmountMap, auctionCreateBidBidderMap, auctionCreateBidUnlockedMap,
    auctionCreateBidAmountState, auctionCreateBidBidderState, auctionCreateBidUnlockedState,
    howner, storageStore_accountMap, storageStore_executionEnv] using hunlocked

theorem auctionCreateBid_extension_afterRefund_postAccounts_state
    {σEvm σSolm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σEvm σSolm)
    (hmap : evmSolm.accountMap = σSolm)
    (howner : evmSolm.executionEnv.codeOwner = I.codeOwner)
    (hsource : evmSolm.executionEnv.source = I.source)
    (hwei : evmSolm.executionEnv.weiValue = I.weiValue)
    (htimestamp : evmSolm.executionEnv.header.timestamp = I.header.timestamp) :
    accountMapEquiv
      (auctionCreateBidUnlockedMap
        (auctionCreateBidExtendedMap
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σEvm I) I) I) I)
      (auctionCreateBidUnlockedState
        (auctionCreateBidExtendedState
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmSolm)))).accountMap := by
  let σAmountEvm := auctionCreateBidAmountMap σEvm I
  let σBidderEvm := auctionCreateBidBidderMap σAmountEvm I
  let evmAmountSolm := auctionCreateBidAmountState evmSolm
  let evmBidderSolm := auctionCreateBidBidderState evmAmountSolm
  have hbidder :
      accountMapEquiv σBidderEvm evmBidderSolm.accountMap := by
    simpa [σAmountEvm, σBidderEvm, evmAmountSolm, evmBidderSolm] using
      auctionCreateBid_afterRefund_bidderAccounts_state
        (σEvm := σEvm) (σSolm := σSolm) (evmSolm := evmSolm) (I := I)
        hAccounts hmap howner hsource hwei
  have htimeBuffer :
      auctionSlotWord ⟨203⟩ σBidderEvm I =
        auctionSlotWord ⟨203⟩ evmBidderSolm.accountMap I :=
    accountMapEquiv_storage_findD hbidder I.codeOwner ⟨203⟩ ⟨0⟩
  have hextended :
      accountMapEquiv
        (auctionCreateBidExtendedMap σBidderEvm I)
        (auctionCreateBidExtendedMap evmBidderSolm.accountMap I) := by
    unfold auctionCreateBidExtendedMap
    rw [htimeBuffer]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨210⟩
      (UInt256.add (UInt256.ofNat I.header.timestamp)
        (auctionSlotWord ⟨203⟩ evmBidderSolm.accountMap I)) hbidder
  have hunlocked :
      accountMapEquiv
        (auctionCreateBidUnlockedMap (auctionCreateBidExtendedMap σBidderEvm I) I)
        (auctionCreateBidUnlockedMap
          (auctionCreateBidExtendedMap evmBidderSolm.accountMap I) I) := by
    simpa [auctionCreateBidUnlockedMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hextended
  simpa [σAmountEvm, σBidderEvm, evmAmountSolm, evmBidderSolm,
    auctionCreateBidAmountMap, auctionCreateBidBidderMap, auctionCreateBidExtendedMap,
    auctionCreateBidUnlockedMap, auctionCreateBidAmountState, auctionCreateBidBidderState,
    auctionCreateBidExtendedState, auctionCreateBidUnlockedState, howner, htimestamp,
    auctionSlotWord, storageStore_accountMap, storageStore_executionEnv,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hunlocked

theorem auctionCreateBidRefundLoopMem_read64_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  unfold auctionCreateBidRefundLoopMem
  rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
    (auctionCreateBidRefundFreeMem noun amount start finish bidder settled) 352 64
    (by rw [auctionCreateBidRefundFreeMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundFreeMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundFreeMem
  exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
    (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled) 64
    (by rw [auctionCreateBidRefundZeroLenMem_size]; exact lt_usize _ (by norm_num))

theorem auctionCreateBidRefundLoopMem_read128_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled).readWithPadding
        128 32 =
      UInt256.toByteArray noun := by
  unfold auctionCreateBidRefundLoopMem
  rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
    (auctionCreateBidRefundFreeMem noun amount start finish bidder settled) 352 128
    (by rw [auctionCreateBidRefundFreeMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundFreeMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundFreeMem
  rw [write32_read_above (UInt256.toByteArray (⟨352⟩ : UInt256))
    (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled) 64 128
    (by rw [toByteArray_size])
    (by rw [auctionCreateBidRefundZeroLenMem_size]; omega)
    (by omega)
    (by rw [auctionCreateBidRefundZeroLenMem_size]; omega)]
  unfold auctionCreateBidRefundZeroLenMem
  rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 128
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read128_word noun amount start finish bidder settled

theorem auctionCreateBidRefundLoopMem_mload128
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundLoopMem noun amount start finish bidder settled).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      noun :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidRefundLoopMem_size]; decide)
    (by decide)
    (auctionCreateBidRefundLoopMem_read128_word noun amount start finish bidder settled)

theorem auctionCreateBidRefundLoopMem_read224_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled).readWithPadding
        224 32 =
      UInt256.toByteArray finish := by
  unfold auctionCreateBidRefundLoopMem
  rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
    (auctionCreateBidRefundFreeMem noun amount start finish bidder settled) 352 224
    (by rw [auctionCreateBidRefundFreeMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundFreeMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundFreeMem
  rw [write32_read_above (UInt256.toByteArray (⟨352⟩ : UInt256))
    (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled) 64 224
    (by rw [toByteArray_size])
    (by rw [auctionCreateBidRefundZeroLenMem_size]; omega)
    (by omega)
    (by rw [auctionCreateBidRefundZeroLenMem_size]; omega)]
  unfold auctionCreateBidRefundZeroLenMem
  rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 224
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read224_word noun amount start finish bidder settled

theorem auctionCreateBidRefundLoopMem_mload224
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundLoopMem noun amount start finish bidder settled).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      finish :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidRefundLoopMem_size]; decide)
    (by decide)
    (auctionCreateBidRefundLoopMem_read224_word noun amount start finish bidder settled)

noncomputable def auctionCreateBidRefundAuctionBidMem0
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (auctionSourceWord I)).write 0
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled) 352 32

noncomputable def auctionCreateBidRefundAuctionBidMem1
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray I.weiValue).write 0
    (auctionCreateBidRefundAuctionBidMem0 noun amount start finish bidder settled I) 384 32

noncomputable def auctionCreateBidRefundAuctionBidMem2
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray extended).write 0
    (auctionCreateBidRefundAuctionBidMem1 noun amount start finish bidder settled I) 416 32

theorem auctionCreateBidRefundAuctionBidMem0_size
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundAuctionBidMem0 noun amount start finish bidder settled I).size =
      384 := by
  unfold auctionCreateBidRefundAuctionBidMem0
  exact toByteArray_write32_size_of_le
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
    (auctionSourceWord I) 352 384 384
    (auctionCreateBidRefundLoopMem_size noun amount start finish bidder settled)
    (by rw [auctionCreateBidRefundLoopMem_size]; omega) (by decide)

theorem auctionCreateBidRefundAuctionBidMem1_size
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundAuctionBidMem1 noun amount start finish bidder settled I).size =
      416 := by
  unfold auctionCreateBidRefundAuctionBidMem1
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidRefundAuctionBidMem0 noun amount start finish bidder settled I)
    I.weiValue 384 384 416
    (auctionCreateBidRefundAuctionBidMem0_size noun amount start finish bidder settled I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidRefundAuctionBidMem2_size
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled extended I).size =
      448 := by
  unfold auctionCreateBidRefundAuctionBidMem2
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidRefundAuctionBidMem1 noun amount start finish bidder settled I)
    extended 416 416 448
    (auctionCreateBidRefundAuctionBidMem1_size noun amount start finish bidder settled I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidRefundAuctionBidMem2_read64
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled extended I
        |>.readWithPadding 64 32) =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  unfold auctionCreateBidRefundAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap extended _ 416 64
    (by rw [auctionCreateBidRefundAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 384 64
    (by rw [auctionCreateBidRefundAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I)
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled) 352 64
    (by rw [auctionCreateBidRefundLoopMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundLoopMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidRefundLoopMem_read64_word noun amount start finish bidder settled

theorem auctionCreateBidRefundAuctionBidMem2_mload64
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled extended I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled extended I)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidRefundAuctionBidMem2_size]; decide)
    (auctionCreateBidRefundAuctionBidMem2_read64 noun amount start finish bidder settled
      extended I)
    (by decide) (by decide)

noncomputable def auctionCreateBidRefundExtendedSnapshotMem
    (noun amount start finish bidder settled newEnd : UInt256) : ByteArray :=
  (UInt256.toByteArray newEnd).write 0
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled) 224 32

theorem auctionCreateBidRefundExtendedSnapshotMem_size
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd).size =
      384 := by
  unfold auctionCreateBidRefundExtendedSnapshotMem
  exact toByteArray_write32_size_of_le
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
    newEnd 224 384 384
    (auctionCreateBidRefundLoopMem_size noun amount start finish bidder settled)
    (by rw [auctionCreateBidRefundLoopMem_size]; omega) (by decide)

theorem auctionCreateBidRefundExtendedSnapshotMem_read64
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd
        |>.readWithPadding 64 32) =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  unfold auctionCreateBidRefundExtendedSnapshotMem
  rw [toByteArray_write_read_below_of_gap newEnd _ 224 64
    (by rw [auctionCreateBidRefundLoopMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundLoopMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidRefundLoopMem_read64_word noun amount start finish bidder settled

theorem auctionCreateBidRefundExtendedSnapshotMem_mload64
    (noun amount start finish bidder settled newEnd : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; decide)
    (auctionCreateBidRefundExtendedSnapshotMem_read64 noun amount start finish bidder settled newEnd)
    (by decide) (by decide)

theorem auctionCreateBidRefundExtendedSnapshotMem_read128_word
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd
        |>.readWithPadding 128 32) =
      UInt256.toByteArray noun := by
  unfold auctionCreateBidRefundExtendedSnapshotMem
  rw [toByteArray_write_read_below_of_gap newEnd _ 224 128
    (by rw [auctionCreateBidRefundLoopMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundLoopMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidRefundLoopMem_read128_word noun amount start finish bidder settled

theorem auctionCreateBidRefundExtendedSnapshotMem_mload128
    (noun amount start finish bidder settled newEnd : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd)
            |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      noun :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; decide)
    (by decide)
    (auctionCreateBidRefundExtendedSnapshotMem_read128_word noun amount start finish bidder settled
      newEnd)

theorem auctionCreateBidRefundExtendedSnapshotMem_read224_word
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd
        |>.readWithPadding 224 32) =
      UInt256.toByteArray newEnd := by
  unfold auctionCreateBidRefundExtendedSnapshotMem
  exact toByteArray_write_read_back_of_gap newEnd
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled) 224
    (by rw [auctionCreateBidRefundLoopMem_size]; exact lt_usize _ (by norm_num))

theorem auctionCreateBidRefundExtendedSnapshotMem_mload224
    (noun amount start finish bidder settled newEnd : UInt256) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd)
            |>.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      newEnd :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; decide)
    (by decide)
    (auctionCreateBidRefundExtendedSnapshotMem_read224_word noun amount start finish bidder settled
      newEnd)

noncomputable def auctionCreateBidRefundExtendedAuctionBidMem0
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (auctionSourceWord I)).write 0
    (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd)
    352 32

noncomputable def auctionCreateBidRefundExtendedAuctionBidMem1
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray I.weiValue).write 0
    (auctionCreateBidRefundExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I)
    384 32

noncomputable def auctionCreateBidRefundExtendedAuctionBidMem2
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (auctionCreateBidRefundExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I)
    416 32

theorem auctionCreateBidRefundExtendedAuctionBidMem0_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I).size =
      384 := by
  unfold auctionCreateBidRefundExtendedAuctionBidMem0
  exact toByteArray_write32_size_of_le
    (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd)
    (auctionSourceWord I) 352 384 384
    (auctionCreateBidRefundExtendedSnapshotMem_size noun amount start finish bidder settled newEnd)
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; omega) (by decide)

theorem auctionCreateBidRefundExtendedAuctionBidMem1_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I).size =
      416 := by
  unfold auctionCreateBidRefundExtendedAuctionBidMem1
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidRefundExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I)
    I.weiValue 384 384 416
    (auctionCreateBidRefundExtendedAuctionBidMem0_size noun amount start finish bidder settled newEnd I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidRefundExtendedAuctionBidMem2_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size =
      448 := by
  unfold auctionCreateBidRefundExtendedAuctionBidMem2
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidRefundExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I)
    (⟨1⟩ : UInt256) 416 416 448
    (auctionCreateBidRefundExtendedAuctionBidMem1_size noun amount start finish bidder settled newEnd I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidRefundExtendedAuctionBidMem2_read64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I
        |>.readWithPadding 64 32) =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  unfold auctionCreateBidRefundExtendedAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap (⟨1⟩ : UInt256) _ 416 64
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundExtendedAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 384 64
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundExtendedAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I) _ 352 64
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidRefundExtendedSnapshotMem_read64 noun amount start finish bidder settled
    newEnd

theorem auctionCreateBidRefundExtendedAuctionBidMem2_mload64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem2_size]; decide)
    (auctionCreateBidRefundExtendedAuctionBidMem2_read64 noun amount start finish bidder settled
      newEnd I)
    (by decide) (by decide)

theorem auctionCreateBidRefundExtendedAuctionBidMem2_read128_word
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I
        |>.readWithPadding 128 32) =
      UInt256.toByteArray noun := by
  unfold auctionCreateBidRefundExtendedAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap (⟨1⟩ : UInt256) _ 416 128
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundExtendedAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 384 128
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundExtendedAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I) _ 352 128
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidRefundExtendedSnapshotMem_read128_word noun amount start finish bidder settled
    newEnd

theorem auctionCreateBidRefundExtendedAuctionBidMem2_mload128
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      noun :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem2_size]; decide)
    (by decide)
    (auctionCreateBidRefundExtendedAuctionBidMem2_read128_word noun amount start finish bidder settled
      newEnd I)

theorem auctionCreateBidRefundExtendedAuctionBidMem2_read224_word
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I
        |>.readWithPadding 224 32) =
      UInt256.toByteArray newEnd := by
  unfold auctionCreateBidRefundExtendedAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap (⟨1⟩ : UInt256) _ 416 224
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundExtendedAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 384 224
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidRefundExtendedAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I) _ 352 224
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidRefundExtendedSnapshotMem_read224_word noun amount start finish bidder settled
    newEnd

theorem auctionCreateBidRefundExtendedAuctionBidMem2_mload224
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      newEnd :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem2_size]; decide)
    (by decide)
    (auctionCreateBidRefundExtendedAuctionBidMem2_read224_word noun amount start finish bidder settled
      newEnd I)

noncomputable def auctionCreateBidRefundAuctionExtendedMem0
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray newEnd).write 0
    (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
    352 32

theorem auctionCreateBidRefundAuctionExtendedMem0_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundAuctionExtendedMem0 noun amount start finish bidder settled newEnd I).size =
      448 := by
  unfold auctionCreateBidRefundAuctionExtendedMem0
  exact toByteArray_write32_size_of_le
    (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
    newEnd 352 448 448
    (auctionCreateBidRefundExtendedAuctionBidMem2_size noun amount start finish bidder settled newEnd I)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem2_size]; omega) (by decide)

theorem auctionCreateBidRefundAuctionExtendedMem0_read64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidRefundAuctionExtendedMem0 noun amount start finish bidder settled newEnd I
        |>.readWithPadding 64 32) =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  unfold auctionCreateBidRefundAuctionExtendedMem0
  rw [toByteArray_write_read_below_of_gap newEnd _ 352 64
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem2_size]; omega) (by omega)
    (by rw [auctionCreateBidRefundExtendedAuctionBidMem2_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidRefundExtendedAuctionBidMem2_read64 noun amount start finish bidder settled
    newEnd I

theorem auctionCreateBidRefundAuctionExtendedMem0_mload64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundAuctionExtendedMem0 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidRefundAuctionExtendedMem0_size]; decide)
    (auctionCreateBidRefundAuctionExtendedMem0_read64 noun amount start finish bidder settled
      newEnd I)
    (by decide) (by decide)

theorem auctionCreateBidX_toExtensionCheck_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let packedAfterAmount := auctionSlotWord ⟨211⟩ σAmount I
  obtain ⟨_, _, rd1715'⟩ := rd1715
  have rd1719 := evm_run rd1715' with [jumpdest, callvalue, push1 ⟨208⟩]
  obtain ⟨_, _, rd1720₀⟩ := rd1719.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1720⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1720⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σAmount) k C := by
    exact ⟨_, _, by simpa [σAmount, auctionCreateBidAmountMap] using rd1720₀⟩
  have rd1723₀ := evm_run rd1720 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd1723₁⟩ := rd1723₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1724⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1724⟩
      [packedAfterAmount, ⟨211⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σAmount) k C := by
    exact ⟨_, _, by simpa [packedAfterAmount, auctionSlotWord] using rd1723₁⟩
  have hsourceClean : UInt256.land (auctionSourceWord I) solcAddrMask = auctionSourceWord I :=
    solcAddrMask_clean (auctionSourceWord_canonical I)
  have hpostWord :
      UInt256.lor (UInt256.ofNat I.source.val)
          (UInt256.land
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
            packedAfterAmount) =
        setAddressOffset0Word packedAfterAmount (auctionSourceWord I) := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide]
    rw [u256_land_comm (UInt256.lnot solcAddrMask) packedAfterAmount]
    change UInt256.lor (auctionSourceWord I)
        (UInt256.land packedAfterAmount (UInt256.lnot solcAddrMask)) =
      setAddressOffset0Word packedAfterAmount (auctionSourceWord I)
    unfold setAddressOffset0Word
    rw [hsourceClean, u256_lor_comm]
  have rd1737₀ := evm_run rd1724 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and, caller, lor, swap1]
  have rd1737 := rd1737₀
  rw [hpostWord] at rd1737
  obtain ⟨_, _, rd1738₀⟩ := rd1737.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [auctionCreateBidBidderMap, packedAfterAmount, σAmount] using rd1738₀⟩

theorem auctionCreateBidX_toExtensionDecision_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [UInt256.sub finish (UInt256.ofNat I.header.timestamp),
        auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  obtain ⟨_, _, rd1738⟩ := auctionCreateBidX_toExtensionCheck_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm rd1715
  obtain ⟨_, _, rd1738'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder] using rd1738⟩
  obtain ⟨_, _, rd1740₀⟩ := (evm_run rd1738' with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1741⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1741⟩
      [timeBuffer, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1740₀⟩
  have rd1745₀ := evm_run rd1741 with [push1 ⟨96⟩, dup4, add]
  have rd1745 := rd1745₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1745
  have rd1746 := evm_run rd1745 with [
    raw mload 0 finish (UInt256.ofNat 12) (by native_decide)
      mem_cost
      (auctionCreateBidRefundLoopMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd5723 := evm_run rd1746 with [
    push0, swap2, swap1, push2 ⟨1759⟩, swap1, timestamp, swap1, push2 ⟨5723⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidCheckedSubOk
    (a := finish) (b := UInt256.ofNat I.header.timestamp) (ret := ⟨1759⟩)
    (R := [timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
      auctionSelWord I])
    rd5723 (Nat.le_of_lt htime) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer] using rd1759⟩

theorem auctionCreateBidX_toAuctionBid_noExtension_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat ≤
        (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime rd1715
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨0⟩ := by
    apply ult_zero
    simpa [timeLeft, timeBuffer, σBidder, σAmount] using hnotExtended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1764
  have rd1792 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1792⟩

theorem auctionCreateBidX_toAuctionBidLog_noExtension_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat ≤
        (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨352⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 14) rdata
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  obtain ⟨_, _, rd1792⟩ := auctionCreateBidX_toAuctionBid_noExtension_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hnotExtended rd1715
  obtain ⟨_, _, rd1792'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder] using rd1792⟩
  have rd1794 := evm_run rd1792' with [
    jumpdest, dup3,
    raw mload 0 noun (UInt256.ofNat 12) (by native_decide)
      mem_cost
      (auctionCreateBidRefundLoopMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost
      (auctionCreateBidRefundLoopMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    caller, dup2]
  have rd1801 := evm_run rd1794 with [
    raw mstore 0 (auctionCreateBidRefundAuctionBidMem0 noun amount start finish bidder settled I)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1807₀ := evm_run rd1801 with [callvalue, push1 ⟨32⟩, dup3, add]
  have rd1807 := rd1807₀
  rw [show (⟨352⟩ : UInt256) + ⟨32⟩ = ⟨384⟩ by decide] at rd1807
  have rd1808 := evm_run rd1807 with [
    raw mstore 3 (auctionCreateBidRefundAuctionBidMem1 noun amount start finish bidder settled I)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1814₀ := evm_run rd1808 with [dup4, iszero, iszero, dup2, dup4, add]
  have rd1814 := rd1814₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1814
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1814
  rw [show (⟨64⟩ : UInt256) + ⟨352⟩ = ⟨416⟩ by decide] at rd1814
  have rd1815 := evm_run rd1814 with [
    raw mstore 3
      (auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 14) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1816 := evm_run rd1815 with [swap1]
  have rd1817₀ := evm_run rd1816 with [
    raw mload 0 ⟨352⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost
      (auctionCreateBidRefundAuctionBidMem2_mload64 noun amount start finish bidder settled
        ⟨0⟩ I)
      (by decide) (by evm_ov)]
  have rd1850 := rd1817₀.pushConst auctionCreateBidAuctionBidTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1858₀ := evm_run rd1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  have rd1858 := rd1858₀
  rw [show UInt256.sub (⟨352⟩ : UInt256) ⟨352⟩ = ⟨0⟩ by decide] at rd1858
  rw [show (⟨96⟩ : UInt256) + ⟨0⟩ = ⟨96⟩ by decide] at rd1858
  exact ⟨_, _, by simpa [σAmount, σBidder] using rd1858⟩

theorem auctionCreateBidX_success_noExtension_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat ≤
        (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionCreateBidUnlockedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I)
      ByteArray.empty := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  obtain ⟨_, _, rd1858⟩ := auctionCreateBidX_toAuctionBidLog_noExtension_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hnotExtended rd1715
  obtain ⟨_, _, rd1858'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨352⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 14) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder] using rd1858⟩
  have rd1859 := Auction.RD.log2 0 (UInt256.ofNat 14) rd1858'
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1864₀ := evm_run rd1859 with [dup1, iszero]
  have rd1864 := rd1864₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1864
  have rd1923 := evm_run rd1864 with [
    push2 ⟨1923⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1930 := evm_run rd1923 with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1931₀⟩ := rd1930.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1931⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1931⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 14) rdata
      (cA', auctionCreateBidUnlockedMap σBidder I) k C := by
    exact ⟨_, _, by simpa [auctionCreateBidUnlockedMap] using rd1931₀⟩
  have rd413 := evm_run rd1931 with [pop, pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionCreateBidX_toAuctionBid_extension_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat <
        UInt256.size)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled
        (UInt256.add (UInt256.ofNat I.header.timestamp)
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I)))
      (UInt256.ofNat 12) rdata
      (cA', auctionCreateBidExtendedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  let nowWord := UInt256.ofNat I.header.timestamp
  let newEnd := UInt256.add nowWord timeBuffer
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime rd1715
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨1⟩ := by
    apply ult_one
    simpa [timeLeft, timeBuffer, σBidder, σAmount] using hextended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1764
  have rd1768 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiNT (by decide)]
  obtain ⟨_, _, rd1771₀⟩ := (evm_run rd1768 with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1771⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1772⟩
      [timeBuffer, ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1771₀⟩
  have rd5704 := evm_run rd1771 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1781₀⟩ := auctionCreateAuctionCheckedAddOk
    (a := nowWord) (b := timeBuffer) (ret := ⟨1781⟩)
    (R := [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 (by simpa [nowWord, timeBuffer, σBidder, σAmount] using haddExtFit)
    (by jump_dest) (by simp)
  have rd1781 := rd1781₀
  rw [show timeBuffer + nowWord = newEnd by
    dsimp [newEnd, nowWord]
    exact u256_add_comm timeBuffer (UInt256.ofNat I.header.timestamp)] at rd1781
  have rd1785₀ := evm_run rd1781 with [jumpdest, push1 ⟨96⟩, dup5, add]
  have rd1785 := rd1785₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1785
  have rd1788 := evm_run rd1785 with [
    dup2, swap1,
    raw mstore 0
      (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1792₀⟩ := (evm_run rd1788 with [push1 ⟨210⟩]).sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [σAmount, σBidder, timeBuffer, timeLeft, nowWord, newEnd,
      auctionCreateBidExtendedMap] using rd1792₀⟩

theorem auctionCreateBidX_toAuctionBidLog_extension_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat <
        UInt256.size)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨352⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled
        (UInt256.add (UInt256.ofNat I.header.timestamp)
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I))
        I)
      (UInt256.ofNat 14) rdata
      (cA', auctionCreateBidExtendedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let newEnd := UInt256.add (UInt256.ofNat I.header.timestamp) timeBuffer
  let σExtended := auctionCreateBidExtendedMap σBidder I
  obtain ⟨_, _, rd1792⟩ := auctionCreateBidX_toAuctionBid_extension_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hextended haddExtFit rd1715
  obtain ⟨_, _, rd1792'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundExtendedSnapshotMem noun amount start finish bidder settled newEnd)
      (UInt256.ofNat 12) rdata (cA', σExtended) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, newEnd, σExtended] using rd1792⟩
  have rd1794 := evm_run rd1792' with [
    jumpdest, dup3,
    raw mload 0 noun (UInt256.ofNat 12) (by native_decide)
      mem_cost
      (auctionCreateBidRefundExtendedSnapshotMem_mload128 noun amount start finish bidder settled
        newEnd)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost
      (auctionCreateBidRefundExtendedSnapshotMem_mload64 noun amount start finish bidder settled
        newEnd)
      (by decide) (by evm_ov),
    caller, dup2]
  have rd1801 := evm_run rd1794 with [
    raw mstore 0
      (auctionCreateBidRefundExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1807₀ := evm_run rd1801 with [callvalue, push1 ⟨32⟩, dup3, add]
  have rd1807 := rd1807₀
  rw [show (⟨352⟩ : UInt256) + ⟨32⟩ = ⟨384⟩ by decide] at rd1807
  have rd1808 := evm_run rd1807 with [
    raw mstore 3
      (auctionCreateBidRefundExtendedAuctionBidMem1 noun amount start finish bidder settled
        newEnd I)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1814₀ := evm_run rd1808 with [dup4, iszero, iszero, dup2, dup4, add]
  have rd1814 := rd1814₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1814
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1814
  rw [show (⟨64⟩ : UInt256) + ⟨352⟩ = ⟨416⟩ by decide] at rd1814
  have rd1815 := evm_run rd1814 with [
    raw mstore 3
      (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled
        newEnd I)
      (UInt256.ofNat 14) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1816 := evm_run rd1815 with [swap1]
  have rd1817₀ := evm_run rd1816 with [
    raw mload 0 ⟨352⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost
      (auctionCreateBidRefundExtendedAuctionBidMem2_mload64 noun amount start finish bidder
        settled newEnd I)
      (by decide) (by evm_ov)]
  have rd1850 := rd1817₀.pushConst auctionCreateBidAuctionBidTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1858₀ := evm_run rd1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  have rd1858 := rd1858₀
  rw [show UInt256.sub (⟨352⟩ : UInt256) ⟨352⟩ = ⟨0⟩ by decide] at rd1858
  rw [show (⟨96⟩ : UInt256) + ⟨0⟩ = ⟨96⟩ by decide] at rd1858
  exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, newEnd, σExtended] using rd1858⟩

theorem auctionCreateBidX_success_extension_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat <
        UInt256.size)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionCreateBidUnlockedMap
        (auctionCreateBidExtendedMap
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) I)
      ByteArray.empty := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let newEnd := UInt256.add (UInt256.ofNat I.header.timestamp) timeBuffer
  let σExtended := auctionCreateBidExtendedMap σBidder I
  obtain ⟨_, _, rd1858⟩ := auctionCreateBidX_toAuctionBidLog_extension_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hextended haddExtFit rd1715
  obtain ⟨_, _, rd1858'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨352⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundExtendedAuctionBidMem2 noun amount start finish bidder settled
        newEnd I)
      (UInt256.ofNat 14) rdata (cA', σExtended) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, newEnd, σExtended] using rd1858⟩
  have rd1859 := Auction.RD.log2 0 (UInt256.ofNat 14) rd1858'
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1864₀ := evm_run rd1859 with [dup1, iszero]
  have rd1864 := rd1864₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1864
  have rd1865 := evm_run rd1864 with [push2 ⟨1923⟩, jumpiNT (by decide)]
  have rd1870₀ := evm_run rd1865 with [
    dup3,
    raw mload 0 noun (UInt256.ofNat 14) (by native_decide)
      mem_cost
      (auctionCreateBidRefundExtendedAuctionBidMem2_mload128 noun amount start finish bidder
        settled newEnd I)
      (by decide) (by evm_ov),
    push1 ⟨96⟩, dup5, add]
  have rd1870 := rd1870₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1870
  have rd1874 := evm_run rd1870 with [
    raw mload 0 newEnd (UInt256.ofNat 14) (by native_decide)
      mem_cost
      (auctionCreateBidRefundExtendedAuctionBidMem2_mload224 noun amount start finish bidder
        settled newEnd I)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost
      (auctionCreateBidRefundExtendedAuctionBidMem2_mload64 noun amount start finish bidder
        settled newEnd I)
      (by decide) (by evm_ov)]
  have rd1877 := evm_run rd1874 with [
    swap1, dup2,
    raw mstore 0
      (auctionCreateBidRefundAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 14) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1911 := rd1877.pushConst auctionCreateBidAuctionExtendedTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1914₀ := evm_run rd1911 with [swap1, push1 ⟨32⟩, add]
  have rd1914 := rd1914₀
  rw [show (⟨32⟩ : UInt256) + ⟨352⟩ = ⟨384⟩ by decide] at rd1914
  have rd1921₀ := evm_run rd1914 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost
      (auctionCreateBidRefundAuctionExtendedMem0_mload64 noun amount start finish bidder
        settled newEnd I)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1921 := rd1921₀
  rw [show UInt256.sub (⟨384⟩ : UInt256) ⟨352⟩ = ⟨32⟩ by decide] at rd1921
  have rd1923 := Auction.RD.log2 0 (UInt256.ofNat 14) rd1921
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1930 := evm_run rd1923 with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1931₀⟩ := rd1930.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1931⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1931⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 14) rdata
      (cA', auctionCreateBidUnlockedMap σExtended I) k C := by
    exact ⟨_, _, by simpa [auctionCreateBidUnlockedMap] using rd1931₀⟩
  have rd413 := evm_run rd1931 with [pop, pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidPanicOverflowRevert_aw12 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5630⟩ R mem (UInt256.ofNat 12) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hsel : UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
      ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ := by
    decide
  have rd5639₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd5639 := rd5639₀
  rw [hsel] at rd5639
  have rd5643 := evm_run rd5639 with [
    raw mstore 0
      ((UInt256.toByteArray
        (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
          UInt256)).write 0 mem 0 32)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩]
  have rd5648 := evm_run rd5643 with [
    raw mstore 0
      ((UInt256.toByteArray (⟨17⟩ : UInt256)).write 0
        ((UInt256.toByteArray
          (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
            UInt256)).write 0 mem 0 32) 4 32)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, push0]
  exact rd5648.rev 0 (by native_decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidCheckedAddOverflow_aw12 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5704⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 12)
      rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hgt : UInt256.gt a (b + a) = ⟨1⟩ :=
    auctionCreateAuctionCheckedAddOverflowGt a b hover
  have rd5711₀ := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd5711 := rd5711₀
  rw [hgt] at rd5711
  have rd5712₀ := evm_run rd5711 with [iszero]
  have rd5712 := rd5712₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5712
  have rd5630 := evm_run rd5712 with [
    push2 ⟨4886⟩, jumpiNT (by decide), push2 ⟨4886⟩, push2 ⟨5630⟩,
    jump (by jump_dest)]
  exact auctionCreateBidPanicOverflowRevert_aw12 rd5630 (by evm_ov)

theorem auctionCreateBidX_revert_extensionOverflow_afterRefundLoopJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256} {rdata : ByteArray}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat +
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σCall) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  let nowWord := UInt256.ofNat I.header.timestamp
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_afterRefundLoopJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime rd1715
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨1⟩ := by
    apply ult_one
    simpa [timeLeft, timeBuffer, σBidder, σAmount] using hextended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1764
  have rd1768 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiNT (by decide)]
  obtain ⟨_, _, rd1771₀⟩ := (evm_run rd1768 with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1771⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1772⟩
      [timeBuffer, ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1771₀⟩
  have rd5704 := evm_run rd1771 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  have hoverEVM : UInt256.size ≤ nowWord.toNat + timeBuffer.toNat := by
    simpa [nowWord, timeBuffer, σBidder, σAmount] using hover
  exact auctionCreateBidCheckedAddOverflow_aw12
    (a := nowWord) (b := timeBuffer) (ret := ⟨1781⟩)
    (R := [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 hoverEVM (by simp)

theorem auctionCreateBidX_toAuctionBid_noExtension_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat ≤
        (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime rd1715
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨0⟩ := by
    apply ult_zero
    simpa [timeLeft, timeBuffer, σBidder, σAmount] using hnotExtended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1764
  have rd1792 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1792⟩

theorem auctionCreateBidX_toAuctionBidLog_noExtension_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat ≤
        (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 13) ByteArray.empty
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  obtain ⟨_, _, rd1792⟩ := auctionCreateBidX_toAuctionBid_noExtension_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hnotExtended rd1715
  obtain ⟨_, _, rd1792'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder] using rd1792⟩
  have rd1794 := evm_run rd1792' with [
    jumpdest, dup3,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    caller, dup2]
  have rd1801 := evm_run rd1794 with [
    raw mstore 3 (auctionCreateBidAuctionBidMem0 noun amount start finish bidder settled I)
      (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1807₀ := evm_run rd1801 with [callvalue, push1 ⟨32⟩, dup3, add]
  have rd1807 := rd1807₀
  rw [show (⟨320⟩ : UInt256) + ⟨32⟩ = ⟨352⟩ by decide] at rd1807
  have rd1808 := evm_run rd1807 with [
    raw mstore 3 (auctionCreateBidAuctionBidMem1 noun amount start finish bidder settled I)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1814₀ := evm_run rd1808 with [dup4, iszero, iszero, dup2, dup4, add]
  have rd1814 := rd1814₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1814
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1814
  rw [show (⟨64⟩ : UInt256) + ⟨320⟩ = ⟨384⟩ by decide] at rd1814
  have rd1815 := evm_run rd1814 with [
    raw mstore 3 (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1816 := evm_run rd1815 with [swap1]
  have rd1817₀ := evm_run rd1816 with [
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidAuctionBidMem2_mload64 noun amount start finish bidder settled ⟨0⟩ I)
      (by decide) (by evm_ov)]
  have rd1850 := rd1817₀.pushConst auctionCreateBidAuctionBidTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1858₀ := evm_run rd1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  have rd1858 := rd1858₀
  rw [show UInt256.sub (⟨320⟩ : UInt256) ⟨320⟩ = ⟨0⟩ by decide] at rd1858
  rw [show (⟨96⟩ : UInt256) + ⟨0⟩ = ⟨96⟩ by decide] at rd1858
  exact ⟨_, _, by simpa [σAmount, σBidder] using rd1858⟩

theorem auctionCreateBidX_success_noExtension_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat ≤
        (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionCreateBidUnlockedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I)
      ByteArray.empty := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  obtain ⟨_, _, rd1858⟩ := auctionCreateBidX_toAuctionBidLog_noExtension_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hnotExtended rd1715
  obtain ⟨_, _, rd1858'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 13) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder] using rd1858⟩
  have rd1859 := Auction.RD.log2 0 (UInt256.ofNat 13) rd1858'
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1864₀ := evm_run rd1859 with [dup1, iszero]
  have rd1864 := rd1864₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1864
  have rd1923 := evm_run rd1864 with [
    push2 ⟨1923⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1930 := evm_run rd1923 with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1931₀⟩ := rd1930.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1931⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1931⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 13) ByteArray.empty
      (cA', auctionCreateBidUnlockedMap σBidder I) k C := by
    exact ⟨_, _, by simpa [auctionCreateBidUnlockedMap] using rd1931₀⟩
  have rd413 := evm_run rd1931 with [pop, pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionCreateBidX_toAuctionBid_extension_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat <
        UInt256.size)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled
        (UInt256.add (UInt256.ofNat I.header.timestamp)
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA', auctionCreateBidExtendedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  let nowWord := UInt256.ofNat I.header.timestamp
  let newEnd := UInt256.add nowWord timeBuffer
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime rd1715
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨1⟩ := by
    apply ult_one
    simpa [timeLeft, timeBuffer, σBidder, σAmount] using hextended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1764
  have rd1768 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiNT (by decide)]
  obtain ⟨_, _, rd1771₀⟩ := (evm_run rd1768 with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1771⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1772⟩
      [timeBuffer, ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1771₀⟩
  have rd5704 := evm_run rd1771 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1781₀⟩ := auctionCreateAuctionCheckedAddOk
    (a := nowWord) (b := timeBuffer) (ret := ⟨1781⟩)
    (R := [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 (by simpa [nowWord, timeBuffer, σBidder, σAmount] using haddExtFit)
    (by jump_dest) (by simp)
  have rd1781 := rd1781₀
  rw [show timeBuffer + nowWord = newEnd by
    dsimp [newEnd, nowWord]
    exact u256_add_comm timeBuffer (UInt256.ofNat I.header.timestamp)] at rd1781
  have rd1785₀ := evm_run rd1781 with [jumpdest, push1 ⟨96⟩, dup5, add]
  have rd1785 := rd1785₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1785
  have rd1788 := evm_run rd1785 with [
    dup2, swap1,
    raw mstore 0
      (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd)
      (UInt256.ofNat 10) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1792₀⟩ := (evm_run rd1788 with [push1 ⟨210⟩]).sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [σAmount, σBidder, timeBuffer, timeLeft, nowWord, newEnd,
      auctionCreateBidExtendedMap] using rd1792₀⟩

theorem auctionCreateBidX_toAuctionBidLog_extension_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat <
        UInt256.size)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled
        (UInt256.add (UInt256.ofNat I.header.timestamp)
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I))
        I)
      (UInt256.ofNat 13) ByteArray.empty
      (cA', auctionCreateBidExtendedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let newEnd := UInt256.add (UInt256.ofNat I.header.timestamp) timeBuffer
  let σExtended := auctionCreateBidExtendedMap σBidder I
  obtain ⟨_, _, rd1792⟩ := auctionCreateBidX_toAuctionBid_extension_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hextended haddExtFit rd1715
  obtain ⟨_, _, rd1792'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd)
      (UInt256.ofNat 10) ByteArray.empty (cA', σExtended) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, newEnd, σExtended] using rd1792⟩
  have rd1794 := evm_run rd1792' with [
    jumpdest, dup3,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedSnapshotMem_mload128 noun amount start finish bidder settled newEnd)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedSnapshotMem_mload64 noun amount start finish bidder settled newEnd)
      (by decide) (by evm_ov),
    caller, dup2]
  have rd1801 := evm_run rd1794 with [
    raw mstore 3
      (auctionCreateBidExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1807₀ := evm_run rd1801 with [callvalue, push1 ⟨32⟩, dup3, add]
  have rd1807 := rd1807₀
  rw [show (⟨320⟩ : UInt256) + ⟨32⟩ = ⟨352⟩ by decide] at rd1807
  have rd1808 := evm_run rd1807 with [
    raw mstore 3
      (auctionCreateBidExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1814₀ := evm_run rd1808 with [dup4, iszero, iszero, dup2, dup4, add]
  have rd1814 := rd1814₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1814
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1814
  rw [show (⟨64⟩ : UInt256) + ⟨320⟩ = ⟨384⟩ by decide] at rd1814
  have rd1815 := evm_run rd1814 with [
    raw mstore 3
      (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1816 := evm_run rd1815 with [swap1]
  have rd1817₀ := evm_run rd1816 with [
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload64 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov)]
  have rd1850 := rd1817₀.pushConst auctionCreateBidAuctionBidTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1858₀ := evm_run rd1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  have rd1858 := rd1858₀
  rw [show UInt256.sub (⟨320⟩ : UInt256) ⟨320⟩ = ⟨0⟩ by decide] at rd1858
  rw [show (⟨96⟩ : UInt256) + ⟨0⟩ = ⟨96⟩ by decide] at rd1858
  exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, newEnd, σExtended] using rd1858⟩

theorem auctionCreateBidX_success_extension_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat <
        UInt256.size)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionCreateBidUnlockedMap
        (auctionCreateBidExtendedMap
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) I)
      ByteArray.empty := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let newEnd := UInt256.add (UInt256.ofNat I.header.timestamp) timeBuffer
  let σExtended := auctionCreateBidExtendedMap σBidder I
  obtain ⟨_, _, rd1858⟩ := auctionCreateBidX_toAuctionBidLog_extension_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime hextended haddExtFit rd1715
  obtain ⟨_, _, rd1858'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) ByteArray.empty (cA', σExtended) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, newEnd, σExtended] using rd1858⟩
  have rd1859 := Auction.RD.log2 0 (UInt256.ofNat 13) rd1858'
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1864₀ := evm_run rd1859 with [dup1, iszero]
  have rd1864 := rd1864₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1864
  have rd1865 := evm_run rd1864 with [push2 ⟨1923⟩, jumpiNT (by decide)]
  have rd1870₀ := evm_run rd1865 with [
    dup3,
    raw mload 0 noun (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload128 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov),
    push1 ⟨96⟩, dup5, add]
  have rd1870 := rd1870₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1870
  have rd1874 := evm_run rd1870 with [
    raw mload 0 newEnd (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload224 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload64 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov)]
  have rd1877 := evm_run rd1874 with [
    swap1, dup2,
    raw mstore 0
      (auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1911 := rd1877.pushConst auctionCreateBidAuctionExtendedTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1914₀ := evm_run rd1911 with [swap1, push1 ⟨32⟩, add]
  have rd1914 := rd1914₀
  rw [show (⟨32⟩ : UInt256) + ⟨320⟩ = ⟨352⟩ by decide] at rd1914
  have rd1921₀ := evm_run rd1914 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidAuctionExtendedMem0_mload64 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1921 := rd1921₀
  rw [show UInt256.sub (⟨352⟩ : UInt256) ⟨320⟩ = ⟨32⟩ by decide] at rd1921
  have rd1923 := Auction.RD.log2 0 (UInt256.ofNat 13) rd1921
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1930 := evm_run rd1923 with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1931₀⟩ := rd1930.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1931⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1931⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) ByteArray.empty
      (cA', auctionCreateBidUnlockedMap σExtended I) k C := by
    exact ⟨_, _, by simpa [auctionCreateBidUnlockedMap] using rd1931₀⟩
  have rd413 := evm_run rd1931 with [pop, pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

end Auction
