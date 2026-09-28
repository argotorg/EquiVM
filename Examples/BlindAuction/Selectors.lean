import Examples.BlindAuction.Bytecode

open Solm Ethereum Ethereum.EVM

namespace BlindAuction

/-!
# BlindAuction selector facts

Selector facts are proved by kernel reduction.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("bid(bytes32)")[0:4] = 0x957bb1e0`. -/
theorem blindAuctionBidSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr bidTransition))).extract 0 4 =
      ⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩ := by
  have hsig : Solm.transitionSigStr bidTransition = "bid(bytes32)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature,
      bidTransition, bytes32, ABI.abiToSigStr, ABI.elemToSigStr,
      show Nat.repr 32 = "32" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("reveal(uint256[],bool[],bytes32[])")[0:4] = 0x900f080a`. -/
theorem blindAuctionRevealSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr revealTransition))).extract 0 4 =
      ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩ := by
  have hsig : Solm.transitionSigStr revealTransition =
      "reveal(uint256[],bool[],bytes32[])" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature,
      revealTransition, uint256, uint256Int, boolTy, bytes32,
      ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      show Nat.repr 256 = "256" by decide +kernel,
      show Nat.repr 32 = "32" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("withdraw()")[0:4] = 0x3ccfd60b`. -/
theorem blindAuctionWithdrawSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr withdrawTransition))).extract 0 4 =
      ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ := by decide +kernel

/-- `keccak("auctionEnd()")[0:4] = 0x2a24f46c`. -/
theorem blindAuctionAuctionEndSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr auctionEndTransition))).extract 0 4 =
      ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ := by decide +kernel

/-- `keccak("beneficiary()")[0:4] = 0x38af3eed`. -/
theorem blindAuctionBeneficiarySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr beneficiaryGetter))).extract 0 4 =
      ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ := by decide +kernel

/-- `keccak("biddingEnd()")[0:4] = 0x423b217f`. -/
theorem blindAuctionBiddingEndSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr biddingEndGetter))).extract 0 4 =
      ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩ := by decide +kernel

/-- `keccak("revealEnd()")[0:4] = 0xa6e66477`. -/
theorem blindAuctionRevealEndSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr revealEndGetter))).extract 0 4 =
      ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩ := by decide +kernel

/-- `keccak("ended()")[0:4] = 0x12fa6feb`. -/
theorem blindAuctionEndedSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr endedGetter))).extract 0 4 =
      ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩ := by decide +kernel

/-- `keccak("highestBidder()")[0:4] = 0x91f90157`. -/
theorem blindAuctionHighestBidderSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr highestBidderGetter))).extract 0 4 =
      ⟨#[0x91, 0xf9, 0x01, 0x57]⟩ := by decide +kernel

/-- `keccak("highestBid()")[0:4] = 0xd57bde79`. -/
theorem blindAuctionHighestBidSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr highestBidGetter))).extract 0 4 =
      ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ := by decide +kernel

/-- `keccak("bids(address,uint256)")[0:4] = 0x01495c1c`. -/
theorem blindAuctionBidsSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr bidsGetter))).extract 0 4 =
      ⟨#[0x01, 0x49, 0x5c, 0x1c]⟩ := by
  have hsig : Solm.transitionSigStr bidsGetter = "bids(address,uint256)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature,
      bidsGetter, addr, uint256, uint256Int,
      ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

end BlindAuction
