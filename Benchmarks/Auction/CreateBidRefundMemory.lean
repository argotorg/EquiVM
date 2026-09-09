import Benchmarks.Auction.CreateBidRefundReturn
import Benchmarks.Auction.SettleAuctionDynamicWeth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionCreateBidRefundLoopMem_eq_payout
    (noun amount start finish bidder settled : UInt256) :
    auctionCreateBidRefundLoopMem noun amount start finish bidder settled =
      auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled := by
  let snap := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  have hsnap : snap.size = 320 := auctionSettleAuctionSnapshotMem_size ..
  unfold auctionCreateBidRefundLoopMem auctionCreateBidRefundFreeMem
    auctionCreateBidRefundZeroLenMem auctionSettleAuctionPayoutLoopMem
    auctionSettleAuctionPayoutFreeMem auctionSettleAuctionPayoutZeroLenMem
    auctionSettleAuctionBurnCallMem auctionSettleAuctionBurnSelectorMem
  change (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
      ((UInt256.toByteArray (⟨352⟩ : UInt256)).write 0
        ((UInt256.toByteArray (⟨0⟩ : UInt256)).write 0 snap 320 32) 64 32) 352 32 = _
  simp only [show
    auctionSettleAuctionSnapshotMem noun amount start finish bidder settled = snap from rfl]
  simp (disch := simp_all only [toByteArray_size, hsnap,
    ByteArray.size_append, ByteArray.size_extract]; omega) [write32_eq, toByteArray_size, hsnap,
    ByteArray.extract_append, ByteArray.extract_extract, Nat.min_def]
  have hempty (a : ByteArray) (i j : Nat) (h : j ≤ i) : a.extract i j = ByteArray.empty :=
    ByteArray.extract_eq_empty_iff.mpr (Nat.le_trans (Nat.min_le_left _ _) h)
  simp (disch := omega) only [hempty, ByteArray.append_empty]

theorem auctionRefundReturnedMem_eq_payout
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hsize : o.size < UInt256.size) :
    auctionRefundReturnedMem
        (auctionCreateBidRefundLoopMem noun amount start finish bidder settled) o =
      auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o := by
  simp only [auctionRefundReturnedMem, auctionRefundReturnedFree,
    auctionSettleAuctionPayoutNonemptyMemCopy, auctionSettleAuctionPayoutNonemptyMemLen,
    auctionSettleAuctionPayoutNonemptyMemFree, auctionSettleAuctionPayoutNonemptyNewFree,
    auctionSettleAuctionPayoutNonemptyRounded, auctionSettleAuctionPayoutNonemptyOszWord,
    auctionCreateBidRefundLoopMem_eq_payout, UInt256.toNat_ofNat_of_lt hsize]

end Auction
