import Benchmarks.Auction.Bytecode
import Solm.Dispatch

open Solm Ethereum Ethereum.EVM

namespace Auction

/-!
# Auction trusted selector facts

The selector facts are trusted because `ffi.KEC` is opaque to Lean. The jump-destination tables are
proved by `native_decide` in `Bytecode.lean`.
-/

/-- `keccak("initialize(address,address,uint256,uint256,uint8,uint256)")[0:4]`. -/
axiom initializeSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr initializeTransition))).extract 0 4 =
      ⟨#[0x87, 0xf4, 0x9f, 0x54]⟩

/-- `keccak("createBid(uint256)")[0:4]`. -/
axiom createBidSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr createBidTransition))).extract 0 4 =
      ⟨#[0x65, 0x9d, 0xd2, 0xb4]⟩

/-- `keccak("settleCurrentAndCreateNewAuction()")[0:4]`. -/
axiom settleAndCreateSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr settleAndCreateTransition))).extract 0 4 =
      ⟨#[0xf2, 0x5e, 0xff, 0xfc]⟩

/-- `keccak("settleAuction()")[0:4]`. -/
axiom settleAuctionSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr settleAuctionTransition))).extract 0 4 =
      ⟨#[0xa4, 0xd0, 0xa1, 0x7e]⟩

/-- `keccak("pause()")[0:4]`. -/
axiom pauseSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr pauseTransition))).extract 0 4 =
      ⟨#[0x84, 0x56, 0xcb, 0x59]⟩

/-- `keccak("unpause()")[0:4]`. -/
axiom unpauseSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr unpauseTransition))).extract 0 4 =
      ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩

/-- `keccak("setTimeBuffer(uint256)")[0:4]`. -/
axiom setTimeBufferSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr setTimeBufferTransition))).extract 0 4 =
      ⟨#[0x71, 0x20, 0x33, 0x4b]⟩

/-- `keccak("setReservePrice(uint256)")[0:4]`. -/
axiom setReservePriceSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr setReservePriceTransition))).extract 0 4 =
      ⟨#[0xce, 0x9c, 0x7c, 0x0d]⟩

/-- `keccak("setMinBidIncrementPercentage(uint8)")[0:4]`. -/
axiom setMinBidIncSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr setMinBidIncTransition))).extract 0 4 =
      ⟨#[0x36, 0xeb, 0xdb, 0x38]⟩

/-- `keccak("transferOwnership(address)")[0:4]`. -/
axiom transferOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr transferOwnershipTransition))).extract 0 4 =
      ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩

/-- `keccak("renounceOwnership()")[0:4]`. -/
axiom renounceOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr renounceOwnershipTransition))).extract 0 4 =
      ⟨#[0x71, 0x50, 0x18, 0xa6]⟩

/-- `keccak("owner()")[0:4]`. -/
axiom ownerSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr ownerGetter))).extract 0 4 =
      ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩

/-- `keccak("paused()")[0:4]`. -/
axiom pausedSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr pausedGetter))).extract 0 4 =
      ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩

/-- `keccak("nouns()")[0:4]`. -/
axiom nounsSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr nounsGetter))).extract 0 4 =
      ⟨#[0x2d, 0xe4, 0x5f, 0x18]⟩

/-- `keccak("weth()")[0:4]`. -/
axiom wethSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr wethGetter))).extract 0 4 =
      ⟨#[0x3f, 0xc8, 0xce, 0xf3]⟩

/-- `keccak("timeBuffer()")[0:4]`. -/
axiom timeBufferSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr timeBufferGetter))).extract 0 4 =
      ⟨#[0xec, 0x91, 0xf2, 0xa4]⟩

/-- `keccak("reservePrice()")[0:4]`. -/
axiom reservePriceSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr reservePriceGetter))).extract 0 4 =
      ⟨#[0xdb, 0x2e, 0x1e, 0xed]⟩

/-- `keccak("minBidIncrementPercentage()")[0:4]`. -/
axiom minBidIncSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr minBidIncGetter))).extract 0 4 =
      ⟨#[0xb2, 0x96, 0x02, 0x4d]⟩

/-- `keccak("duration()")[0:4]`. -/
axiom durationSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr durationGetter))).extract 0 4 =
      ⟨#[0x0f, 0xb5, 0xa6, 0xb4]⟩

/-- `keccak("auction()")[0:4]`. -/
axiom auctionGetterSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr auctionGetter))).extract 0 4 =
      ⟨#[0x7d, 0x9f, 0x6d, 0xb5]⟩

end Auction
