import Benchmarks.Auction.Bytecode
import Benchmarks.Auction.Spec

open Solm Ethereum Ethereum.EVM

namespace Auction

/-! ABI selector facts: the trusted boundary for the opaque `ffi.KEC` function. -/

axiom durationSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr durationGetter))).extract 0 4 =
      ⟨#[0x0f, 0xb5, 0xa6, 0xb4]⟩

axiom nounsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr nounsGetter))).extract 0 4 =
      ⟨#[0x2d, 0xe4, 0x5f, 0x18]⟩

axiom setMinBidIncrementPercentageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setMinBidIncTransition))).extract 0 4 =
      ⟨#[0x36, 0xeb, 0xdb, 0x38]⟩

axiom unpauseSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr unpauseTransition))).extract 0 4 =
      ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩

axiom wethSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wethGetter))).extract 0 4 =
      ⟨#[0x3f, 0xc8, 0xce, 0xf3]⟩

axiom pausedSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr pausedGetter))).extract 0 4 =
      ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩

axiom createBidSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr createBidTransition))).extract 0 4 =
      ⟨#[0x65, 0x9d, 0xd2, 0xb4]⟩

axiom setTimeBufferSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setTimeBufferTransition))).extract 0 4 =
      ⟨#[0x71, 0x20, 0x33, 0x4b]⟩

axiom renounceOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr renounceOwnershipTransition))).extract 0 4 =
      ⟨#[0x71, 0x50, 0x18, 0xa6]⟩

axiom auctionSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr auctionGetter))).extract 0 4 =
      ⟨#[0x7d, 0x9f, 0x6d, 0xb5]⟩

axiom pauseSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr pauseTransition))).extract 0 4 =
      ⟨#[0x84, 0x56, 0xcb, 0x59]⟩

axiom initializeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr initializeTransition))).extract 0 4 =
      ⟨#[0x87, 0xf4, 0x9f, 0x54]⟩

axiom ownerSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ownerGetter))).extract 0 4 =
      ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩

axiom settleAuctionSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr settleAuctionTransition))).extract 0 4 =
      ⟨#[0xa4, 0xd0, 0xa1, 0x7e]⟩

axiom minBidIncrementPercentageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr minBidIncGetter))).extract 0 4 =
      ⟨#[0xb2, 0x96, 0x02, 0x4d]⟩

axiom setReservePriceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setReservePriceTransition))).extract 0 4 =
      ⟨#[0xce, 0x9c, 0x7c, 0x0d]⟩

axiom reservePriceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr reservePriceGetter))).extract 0 4 =
      ⟨#[0xdb, 0x2e, 0x1e, 0xed]⟩

axiom timeBufferSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr timeBufferGetter))).extract 0 4 =
      ⟨#[0xec, 0x91, 0xf2, 0xa4]⟩

axiom settleCurrentAndCreateNewAuctionSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr settleAndCreateTransition))).extract 0 4 =
      ⟨#[0xf2, 0x5e, 0xff, 0xfc]⟩

axiom transferOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferOwnershipTransition))).extract 0 4 =
      ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩

end Auction

