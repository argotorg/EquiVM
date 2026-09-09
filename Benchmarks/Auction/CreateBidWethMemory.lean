import Benchmarks.Auction.CreateBidRefundMemory
import Benchmarks.Auction.SafeTransferWethSavedMemory
import Benchmarks.Auction.SettleAuctionBurnBranchPayoutNonemptyTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidWethMemory_nonempty
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (hclean : UInt256.land solcAddrMask owner = owner) :
    AuctionWethMemory
      (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
      (auctionSettleAuctionPayoutNonemptyAwCopy o) amount owner finish := by
  let mem := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let aw := auctionSettleAuctionPayoutNonemptyAwCopy o
  let free := auctionSettleAuctionDynMload64 mem aw
  have haw : auctionWethTransferCallAw mem aw =
      UInt256.ofNat (MachineState.M
        (auctionSettleAuctionDynTransferAw (auctionSettleAuctionDynDepositCallAw mem aw)
          free).toNat free.toNat 32) :=
    auctionSettleAuctionPayoutNonemptyTransferReturnAwAfterCall_eq
      noun amount start finish bidder settled owner hosmall hne
  have hfree : free = auctionSettleAuctionPayoutNonemptyNewFree o :=
    auctionSettleAuctionPayoutNonemptyMemCopy_mload64
      noun amount start finish bidder settled hosmall hne
  have hbounds : 3 ≤ (auctionWethTransferCallAw mem aw).toNat ∧
      (auctionWethTransferCallAw mem aw).toNat * 32 < UInt256.size ∧
      free.toNat + 32 ≤ 32 * (auctionWethTransferCallAw mem aw).toNat := by
    rw [haw]
    exact auctionSettleAuctionPayoutNonemptyTransferCallAw_bounds
      noun amount start finish bidder settled owner hosmall hne
  refine {
    depositFree := auctionSettleAuctionPayoutNonemptyDepositFreeStable
      noun amount start finish bidder settled hosmall hne
    depositLen := auctionSettleAuctionPayoutNonemptyDepositLen
      noun amount start finish bidder settled hosmall hne
    depositEncode := auctionSettleAuctionPayoutNonemptyDepositEncode_eq
      noun amount start finish bidder settled hosmall hne
    depositCallFree := auctionSettleAuctionPayoutNonemptyDepositCallFreeStable
      noun amount start finish bidder settled hosmall hne
    transferFree := auctionSettleAuctionPayoutNonemptyTransferFreeStable
      noun amount start finish bidder settled owner hosmall hne
    transferLen := auctionSettleAuctionPayoutNonemptyTransferLen
      noun amount start finish bidder settled hosmall hne
    transferEncode := ?_
    returnFree := ?_
    returnWord := ?_
    returnBase := ?_
    returnFinish := ?_ }
  · have henc := auctionSettleAuctionPayoutNonemptyTransferEncode_eq
      noun amount start finish bidder settled owner hosmall hne (by
        rw [u256_land_comm]
        exact solcAddrMask_result_canonical owner)
    simpa only [hclean] using henc
  · intro out hsize
    change auctionLoadWord (auctionWethTransferReturnMem mem aw amount owner out)
      (auctionWethTransferCallAw mem aw) ⟨64⟩ = free
    rw [haw]
    exact auctionSettleAuctionPayoutNonemptyTransferReturnMload64_any
      noun amount start finish bidder settled owner hosmall hne hsize
  · intro out hsize hlen
    change auctionLoadWord (auctionSafeTransferDecodedMem free
      (auctionWethTransferReturnMem mem aw amount owner out) out)
      (auctionGrowWords (auctionGrowWords (auctionWethTransferCallAw mem aw) ⟨64⟩ 32) ⟨64⟩ 32)
      free = _
    rw [haw, readWithPadding_eq_extract out 0 hlen]
    exact auctionSettleAuctionPayoutNonemptyTransferReturnMloadFree
      noun amount start finish bidder settled owner hosmall hne hlen hsize
  · intro out hsize
    exact auctionSettleAuctionPayoutNonemptyTransferReturn_baseAddHi
      noun amount start finish bidder settled hosmall hne hsize
  · intro out hsize hlen
    have hmem : 256 ≤ mem.size := by
      rw [auctionSettleAuctionPayoutNonemptyMemCopy_size
        noun amount start finish bidder settled hosmall hne]
      omega
    have hge : 256 ≤ free.toNat := by
      rw [hfree, auctionSettleAuctionPayoutNonemptyNewFree_toNat hosmall]
      omega
    have hptr : free.toNat + 99 < UInt256.size := by
      rw [hfree]
      exact auctionSettleAuctionPayoutNonemptyNewFree_add99_lt hosmall
    have hgap : free.toNat - mem.size < USize.size := by
      rw [hfree]
      exact auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne
    have hread : mem.readWithPadding 224 32 = finish.toByteArray := by
      dsimp only [mem]
      rw [← auctionRefundReturnedMem_eq_payout noun amount start finish bidder settled
        (Nat.lt_trans hosmall (by native_decide))]
      rw [auctionRefundReturnedMem_read224
        (auctionCreateBidRefundLoopMem_size noun amount start finish bidder settled) hne]
      exact auctionCreateBidRefundLoopMem_read224_word noun amount start finish bidder settled
    exact auctionWethDecodedMemory_load224 hmem hge hptr hgap hlen hsize hread
      hbounds.1 hbounds.2.1 hbounds.2.2

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidWethMemory_empty
    (noun amount start finish bidder settled owner : UInt256)
    (hclean : UInt256.land solcAddrMask owner = owner) :
    AuctionWethMemory (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) amount owner finish := by
  let mem := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled
  have hload : auctionSettleAuctionDynMload64 mem (UInt256.ofNat 12) = ⟨352⟩ :=
    auctionSettleAuctionPayoutLoopMem_mload64 noun amount start finish bidder settled
  have hdep : auctionSettleAuctionDynDepositMem mem (UInt256.ofNat 12) =
      auctionSettleAuctionWethDepositMem noun amount start finish bidder settled := by
    unfold auctionSettleAuctionDynDepositMem
    rw [hload]
    rfl
  have hdaw : auctionSettleAuctionDynDepositAw mem (UInt256.ofNat 12) = UInt256.ofNat 12 := by
    unfold auctionSettleAuctionDynDepositAw
    rw [hload]
    native_decide
  have hdcaw : auctionSettleAuctionDynDepositCallAw mem (UInt256.ofNat 12) =
      UInt256.ofNat 12 := by
    unfold auctionSettleAuctionDynDepositCallAw auctionSettleAuctionDynDepositAwAfterMload64
    rw [hload, hdaw]
    native_decide
  have hxfer : auctionWethTransferMem mem (UInt256.ofNat 12) amount owner =
      auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner := by
    unfold auctionWethTransferMem
    rw [hdep, hload]
    rfl
  have haw : auctionWethTransferCallAw mem (UInt256.ofNat 12) = UInt256.ofNat 14 := by
    unfold auctionWethTransferCallAw
    rw [hload, hdcaw]
    native_decide
  have hreturn (out : ByteArray) :
      auctionWethTransferReturnMem mem (UInt256.ofNat 12) amount owner out =
        out.write 0 (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
          352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat := by
    unfold auctionWethTransferReturnMem
    rw [hxfer, hload]
    rfl
  change AuctionWethMemory mem (UInt256.ofNat 12) amount owner finish
  constructor
  · rw [hdep, hdaw, hload]
    exact auctionSettleAuctionWethDepositMem_mload64 noun amount start finish bidder settled
  · rw [hload]; native_decide
  · rw [hdep, hload]
    exact auctionSettleAuctionWethDepositEncode_eq noun amount start finish bidder settled
  · rw [hdep, hdcaw, hload]
    exact auctionSettleAuctionWethDepositMem_mload64 noun amount start finish bidder settled
  · rw [hxfer, hdcaw, hload]
    exact auctionSettleAuctionWethTransferMem_mload64 noun amount start finish bidder settled owner
  · rw [hload]; native_decide
  · rw [hxfer, hload]
    have henc := auctionSettleAuctionWethTransferEncode_eq
      noun amount start finish bidder settled owner (by
        rw [u256_land_comm]
        exact solcAddrMask_result_canonical owner)
    simpa only [hclean] using henc
  · intro out hsize
    rw [hreturn, haw, hload]
    exact auctionSettleAuctionTransferReturnMload64_any
      noun amount start finish bidder settled owner hsize
  · intro out hsize hlen
    rw [hreturn, haw, hload, readWithPadding_eq_extract out 0 hlen]
    exact auctionSettleAuctionTransferReturnMload352
      noun amount start finish bidder settled owner hlen hsize
  · intro out hsize
    rw [hload]
    change 352 + out.size < UInt256.size
    have hbound : 352 + 2 ^ 255 ≤ UInt256.size := by native_decide
    omega
  · intro out hsize hlen
    have hmem : mem.size = 384 := auctionSettleAuctionPayoutLoopMem_size ..
    have hread : mem.readWithPadding 224 32 = finish.toByteArray := by
      dsimp only [mem]
      rw [← auctionCreateBidRefundLoopMem_eq_payout]
      exact auctionCreateBidRefundLoopMem_read224_word noun amount start finish bidder settled
    exact auctionWethDecodedMemory_load224 (by rw [hmem]; omega)
      (by rw [hload]; native_decide) (by rw [hload]; native_decide)
      (by rw [hload, hmem]; native_decide) hlen hsize hread
      (by rw [haw]; native_decide) (by rw [haw]; native_decide)
      (by rw [hload, haw]; native_decide)

end Auction
