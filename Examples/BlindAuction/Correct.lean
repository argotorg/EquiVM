import Examples.BlindAuction.Bid
import Examples.BlindAuction.Reveal
import Examples.BlindAuction.Withdraw
import Examples.BlindAuction.AuctionEnd
import Examples.BlindAuction.Bids
import Examples.BlindAuction.Ended
import Examples.BlindAuction.Beneficiary
import Examples.BlindAuction.BiddingEnd
import Examples.BlindAuction.RevealEnd
import Examples.BlindAuction.HighestBidder
import Examples.BlindAuction.HighestBid
import Reasoning.Refinement

/-!
# BlindAuction — top-level correctness proof

This file is the Phase 0 dispatcher assembly for
`blindAuctionCorrect : runtimeEquivalence!?! …`.  It follows the optimizer-on binary-search
dispatcher shape shared with Ballot/SimpleAuction, but with BlindAuction's payable top-level
dispatcher: calldata size and selector routing happen before any callvalue check, and non-payable
guards are proved inside the individual body files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-- The deployed BlindAuction runtime bytecode refines the Solm specification. -/
theorem blindAuctionCorrect :
    runtimeEquivalence!?! blindAuctionConfig blindAuctionBytecode blindAuctionContract := by
  refine ⟨fun cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm g A I hcode hsize hperm
      hAccounts hOriginalAccounts => ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases h0 : selIs I ⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩
    · exact blindAuctionBidBodyCore hcode hsize hperm h0
        (blindAuctionReachHighBody 3 (by omega) ⟨449⟩ hcode hsz hsize
          (blindAuctionPivotNotTaken 3 (by omega) hsz
            (by simpa [selIs, blindAuctionHighSelBytes] using h0))
          (blindAuctionHighMatches 3 (by omega) hsz
            (by simpa [selIs, blindAuctionHighSelBytes] using h0)).1
          (blindAuctionHighMatches 3 (by omega) hsz
            (by simpa [selIs, blindAuctionHighSelBytes] using h0)).2
          (by jump_dest) (by decide)) hAccounts hOriginalAccounts
    · by_cases h1 : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩
      · exact blindAuctionRevealBodyCore hcode hsize hperm h1
          (blindAuctionReachHighBody 1 (by omega) ⟨387⟩ hcode hsz hsize
            (blindAuctionPivotNotTaken 1 (by omega) hsz
              (by simpa [selIs, blindAuctionHighSelBytes] using h1))
            (blindAuctionHighMatches 1 (by omega) hsz
              (by simpa [selIs, blindAuctionHighSelBytes] using h1)).1
            (blindAuctionHighMatches 1 (by omega) hsz
              (by simpa [selIs, blindAuctionHighSelBytes] using h1)).2
            (by jump_dest) (by decide)) hAccounts hOriginalAccounts
      · by_cases h2 : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩
        · exact blindAuctionWithdrawBodyCore hcode hsize hperm h2
            (blindAuctionReachLowBody 4 (by omega) ⟨332⟩ hcode hsz hsize
              (blindAuctionPivotTaken 4 (by omega) hsz
                (by simpa [selIs, blindAuctionLowSelBytes] using h2))
              (blindAuctionLowMatches 4 (by omega) hsz
                (by simpa [selIs, blindAuctionLowSelBytes] using h2)).1
              (blindAuctionLowMatches 4 (by omega) hsz
                (by simpa [selIs, blindAuctionLowSelBytes] using h2)).2
              (by jump_dest) (by decide)) hAccounts hOriginalAccounts
        · by_cases h3 : selIs I ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩
          · exact blindAuctionAuctionEndBodyCore hcode hsize hperm h3
              (blindAuctionReachLowBody 2 (by omega) ⟨256⟩ hcode hsz hsize
                (blindAuctionPivotTaken 2 (by omega) hsz
                  (by simpa [selIs, blindAuctionLowSelBytes] using h3))
                (blindAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, blindAuctionLowSelBytes] using h3)).1
                (blindAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, blindAuctionLowSelBytes] using h3)).2
                (by jump_dest) (by decide)) hAccounts hOriginalAccounts
          · by_cases h4 : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩
            · exact blindAuctionBeneficiaryBodyCore hcode hsize hperm h4
                (blindAuctionReachLowBody 3 (by omega) ⟨278⟩ hcode hsz hsize
                  (blindAuctionPivotTaken 3 (by omega) hsz
                    (by simpa [selIs, blindAuctionLowSelBytes] using h4))
                  (blindAuctionLowMatches 3 (by omega) hsz
                    (by simpa [selIs, blindAuctionLowSelBytes] using h4)).1
                  (blindAuctionLowMatches 3 (by omega) hsz
                    (by simpa [selIs, blindAuctionLowSelBytes] using h4)).2
                  (by jump_dest) (by decide)) hAccounts hOriginalAccounts
            · by_cases h5 : selIs I ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩
              · exact blindAuctionBiddingEndBodyCore hcode hsize hperm h5
                  (blindAuctionReachHighBody 0 (by omega) ⟨352⟩ hcode hsz hsize
                    (blindAuctionPivotNotTaken 0 (by omega) hsz
                      (by simpa [selIs, blindAuctionHighSelBytes] using h5))
                    (blindAuctionHighMatches 0 (by omega) hsz
                      (by simpa [selIs, blindAuctionHighSelBytes] using h5)).1
                    (blindAuctionHighMatches 0 (by omega) hsz
                      (by simpa [selIs, blindAuctionHighSelBytes] using h5)).2
                    (by jump_dest) (by decide)) hAccounts hOriginalAccounts
              · by_cases h6 : selIs I ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩
                · exact blindAuctionRevealEndBodyCore hcode hsize hperm h6
                    (blindAuctionReachHighBody 4 (by omega) ⟨468⟩ hcode hsz hsize
                      (blindAuctionPivotNotTaken 4 (by omega) hsz
                        (by simpa [selIs, blindAuctionHighSelBytes] using h6))
                      (blindAuctionHighMatches 4 (by omega) hsz
                        (by simpa [selIs, blindAuctionHighSelBytes] using h6)).1
                      (blindAuctionHighMatches 4 (by omega) hsz
                        (by simpa [selIs, blindAuctionHighSelBytes] using h6)).2
                      (by jump_dest) (by decide)) hAccounts hOriginalAccounts
                · by_cases h7 : selIs I ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩
                  · exact blindAuctionEndedBodyCore hcode hsize hperm h7
                      (blindAuctionReachLowBody 1 (by omega) ⟨215⟩ hcode hsz hsize
                        (blindAuctionPivotTaken 1 (by omega) hsz
                          (by simpa [selIs, blindAuctionLowSelBytes] using h7))
                        (blindAuctionLowMatches 1 (by omega) hsz
                          (by simpa [selIs, blindAuctionLowSelBytes] using h7)).1
                        (blindAuctionLowMatches 1 (by omega) hsz
                          (by simpa [selIs, blindAuctionLowSelBytes] using h7)).2
                        (by jump_dest) (by decide)) hAccounts hOriginalAccounts
                  · by_cases h8 : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩
                    · exact blindAuctionHighestBidderBodyCore hcode hsize hperm h8
                        (blindAuctionReachHighBody 2 (by omega) ⟨418⟩ hcode hsz hsize
                          (blindAuctionPivotNotTaken 2 (by omega) hsz
                            (by simpa [selIs, blindAuctionHighSelBytes] using h8))
                          (blindAuctionHighMatches 2 (by omega) hsz
                            (by simpa [selIs, blindAuctionHighSelBytes] using h8)).1
                          (blindAuctionHighMatches 2 (by omega) hsz
                            (by simpa [selIs, blindAuctionHighSelBytes] using h8)).2
                          (by jump_dest) (by decide)) hAccounts hOriginalAccounts
                    · by_cases h9 : selIs I ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩
                      · exact blindAuctionHighestBidBodyCore hcode hsize hperm h9
                          (blindAuctionReachHighBody 5 (by omega) ⟨489⟩ hcode hsz hsize
                            (blindAuctionPivotNotTaken 5 (by omega) hsz
                              (by simpa [selIs, blindAuctionHighSelBytes] using h9))
                            (blindAuctionHighMatches 5 (by omega) hsz
                              (by simpa [selIs, blindAuctionHighSelBytes] using h9)).1
                            (blindAuctionHighMatches 5 (by omega) hsz
                              (by simpa [selIs, blindAuctionHighSelBytes] using h9)).2
                            (by jump_dest) (by decide)) hAccounts hOriginalAccounts
                      · by_cases h10 : selIs I ⟨#[0x01, 0x49, 0x5c, 0x1c]⟩
                        · exact blindAuctionBidsBodyCore hcode hsize hperm h10
                            (blindAuctionReachLowBody 0 (by omega) ⟨158⟩ hcode hsz hsize
                              (blindAuctionPivotTaken 0 (by omega) hsz
                                (by simpa [selIs, blindAuctionLowSelBytes] using h10))
                              (blindAuctionLowMatches 0 (by omega) hsz
                                (by simpa [selIs, blindAuctionLowSelBytes] using h10)).1
                              (blindAuctionLowMatches 0 (by omega) hsz
                                (by simpa [selIs, blindAuctionLowSelBytes] using h10)).2
                              (by jump_dest) (by decide)) hAccounts hOriginalAccounts
                        · refine blindAuctionNoDispatch hcode hsize hperm ?_
                          intro i hi
                          interval_cases i
                          · simpa [selIs, blindAuctionSelBytes] using h0
                          · simpa [selIs, blindAuctionSelBytes] using h1
                          · simpa [selIs, blindAuctionSelBytes] using h2
                          · simpa [selIs, blindAuctionSelBytes] using h3
                          · simpa [selIs, blindAuctionSelBytes] using h4
                          · simpa [selIs, blindAuctionSelBytes] using h5
                          · simpa [selIs, blindAuctionSelBytes] using h6
                          · simpa [selIs, blindAuctionSelBytes] using h7
                          · simpa [selIs, blindAuctionSelBytes] using h8
                          · simpa [selIs, blindAuctionSelBytes] using h9
                          · simpa [selIs, blindAuctionSelBytes] using h10
  · exact blindAuctionShortRevert hcode hsize hperm (by omega)

end BlindAuction
