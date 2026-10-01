import Examples.SimpleAuction.Bytecode

open Solm Ethereum Ethereum.EVM

namespace SimpleAuction

/-!
# SimpleAuction selector facts

The selector facts are kernel proofs of the deployed function selectors.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("bid()")[0:4] = 0x1998aeef`. -/
theorem simpleAuctionBidSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr bidTransition))).extract 0 4 =
      ⟨#[0x19, 0x98, 0xae, 0xef]⟩ := by decide +kernel

/-- `keccak("withdraw()")[0:4] = 0x3ccfd60b`. -/
theorem simpleAuctionWithdrawSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr withdrawTransition))).extract 0 4 =
      ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ := by decide +kernel

/-- `keccak("auctionEnd()")[0:4] = 0x2a24f46c`. -/
theorem simpleAuctionAuctionEndSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr auctionEndTransition))).extract 0 4 =
      ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ := by decide +kernel

/-- `keccak("beneficiary()")[0:4] = 0x38af3eed`. -/
theorem simpleAuctionBeneficiarySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr beneficiaryGetter))).extract 0 4 =
      ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ := by decide +kernel

/-- `keccak("auctionEndTime()")[0:4] = 0x4b449cba`. -/
theorem simpleAuctionAuctionEndTimeSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr auctionEndTimeGetter))).extract 0 4 =
      ⟨#[0x4b, 0x44, 0x9c, 0xba]⟩ := by decide +kernel

/-- `keccak("highestBidder()")[0:4] = 0x91f90157`. -/
theorem simpleAuctionHighestBidderSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr highestBidderGetter))).extract 0 4 =
      ⟨#[0x91, 0xf9, 0x01, 0x57]⟩ := by decide +kernel

/-- `keccak("highestBid()")[0:4] = 0xd57bde79`. -/
theorem simpleAuctionHighestBidSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr highestBidGetter))).extract 0 4 =
      ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ := by decide +kernel

end SimpleAuction
