import Benchmarks.Auction.Bytecode
import Benchmarks.Auction.Spec

open Solm ABI Ethereum Ethereum.EVM

namespace Auction

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem durationSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr durationGetter))).extract 0 4 =
      ⟨#[0x0f, 0xb5, 0xa6, 0xb4]⟩ := by decide +kernel

theorem nounsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr nounsGetter))).extract 0 4 =
      ⟨#[0x2d, 0xe4, 0x5f, 0x18]⟩ := by decide +kernel

theorem setMinBidIncrementPercentageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr setMinBidIncTransition))).extract 0 4 =
      ⟨#[0x36, 0xeb, 0xdb, 0x38]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, setMinBidIncTransition, uint8]; decide +kernel

theorem unpauseSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr unpauseTransition))).extract 0 4 =
      ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩ := by decide +kernel

theorem wethSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wethGetter))).extract 0 4 =
      ⟨#[0x3f, 0xc8, 0xce, 0xf3]⟩ := by decide +kernel

theorem pausedSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr pausedGetter))).extract 0 4 =
      ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩ := by decide +kernel

theorem createBidSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr createBidTransition))).extract 0 4 =
      ⟨#[0x65, 0x9d, 0xd2, 0xb4]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, createBidTransition, uint256]; decide +kernel

theorem setTimeBufferSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr setTimeBufferTransition))).extract 0 4 =
      ⟨#[0x71, 0x20, 0x33, 0x4b]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, setTimeBufferTransition, uint256]; decide +kernel

theorem renounceOwnershipSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr renounceOwnershipTransition))).extract 0 4 =
      ⟨#[0x71, 0x50, 0x18, 0xa6]⟩ := by decide +kernel

theorem auctionSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr auctionGetter))).extract 0 4 =
      ⟨#[0x7d, 0x9f, 0x6d, 0xb5]⟩ := by decide +kernel

theorem pauseSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr pauseTransition))).extract 0 4 =
      ⟨#[0x84, 0x56, 0xcb, 0x59]⟩ := by decide +kernel

theorem initializeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr initializeTransition))).extract 0 4 =
      ⟨#[0x87, 0xf4, 0x9f, 0x54]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, initializeTransition, addr, uint256, uint8]; decide +kernel

theorem ownerSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ownerGetter))).extract 0 4 =
      ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩ := by decide +kernel

theorem settleAuctionSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr settleAuctionTransition))).extract 0 4 =
      ⟨#[0xa4, 0xd0, 0xa1, 0x7e]⟩ := by decide +kernel

theorem minBidIncrementPercentageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr minBidIncGetter))).extract 0 4 =
      ⟨#[0xb2, 0x96, 0x02, 0x4d]⟩ := by decide +kernel

theorem setReservePriceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr setReservePriceTransition))).extract 0 4 =
      ⟨#[0xce, 0x9c, 0x7c, 0x0d]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, setReservePriceTransition, uint256]; decide +kernel

theorem reservePriceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr reservePriceGetter))).extract 0 4 =
      ⟨#[0xdb, 0x2e, 0x1e, 0xed]⟩ := by decide +kernel

theorem timeBufferSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr timeBufferGetter))).extract 0 4 =
      ⟨#[0xec, 0x91, 0xf2, 0xa4]⟩ := by decide +kernel

theorem settleCurrentAndCreateNewAuctionSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr settleAndCreateTransition))).extract 0 4 =
      ⟨#[0xf2, 0x5e, 0xff, 0xfc]⟩ := by decide +kernel

theorem transferOwnershipSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr transferOwnershipTransition))).extract 0 4 =
      ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, transferOwnershipTransition, addr]; decide +kernel

end Auction
