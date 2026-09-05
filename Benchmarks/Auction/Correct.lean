import Benchmarks.Auction.AuctionGetter
import Benchmarks.Auction.Constructor
import Benchmarks.Auction.CreateBid
import Benchmarks.Auction.Duration
import Benchmarks.Auction.Initialize
import Benchmarks.Auction.MinBidIncrementPercentage
import Benchmarks.Auction.Nouns
import Benchmarks.Auction.Owner
import Benchmarks.Auction.Pause
import Benchmarks.Auction.Paused
import Benchmarks.Auction.RenounceOwnership
import Benchmarks.Auction.ReservePrice
import Benchmarks.Auction.SetMinBidIncrementPercentage
import Benchmarks.Auction.SetReservePrice
import Benchmarks.Auction.SetTimeBuffer
import Benchmarks.Auction.SettleAuction
import Benchmarks.Auction.SettleAuctionBody
import Benchmarks.Auction.SettleCurrentAndCreateNewAuction
import Benchmarks.Auction.TimeBuffer
import Benchmarks.Auction.TransferOwnership
import Benchmarks.Auction.Unpause
import Benchmarks.Auction.Weth
import Solm.Equiv

/-!
# Auction benchmark correctness stub

The upstream Solidity source closure, optimized runtime bytecode, creation bytecode, storage layout,
and external-call ABI model are present. The runtime-equivalence proof is intentionally left as the
benchmark target. This file also exposes the whole-contract wrapper that combines constructor and
runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Auction

theorem auctionCorrect :
    runtimeEquivalence!?! auctionConfig auctionBytecode Auction.auctionContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases h0 : selIs I (auctionSelBytes 0)
  · exact auctionDurationBodyCore hcode hsize hperm h0 hAccounts
  · by_cases h1 : selIs I (auctionSelBytes 1)
    · exact auctionNounsBodyCore hcode hsize hperm h1 hAccounts
    · by_cases h2 : selIs I (auctionSelBytes 2)
      · exact auctionSetMinBidIncrementPercentageBodyCore hcode hsize hperm h2 hAccounts
      · by_cases h3 : selIs I (auctionSelBytes 3)
        · exact auctionUnpauseBodyCore hcode hsize hperm h3 hAccounts
        · by_cases h4 : selIs I (auctionSelBytes 4)
          · exact auctionWethBodyCore hcode hsize hperm h4 hAccounts
          · by_cases h5 : selIs I (auctionSelBytes 5)
            · exact auctionPausedBodyCore hcode hsize hperm h5 hAccounts
            · by_cases h6 : selIs I (auctionSelBytes 6)
              · exact auctionCreateBidBodyCore hcode hsize hperm h6 hAccounts
              · by_cases h7 : selIs I (auctionSelBytes 7)
                · exact auctionSetTimeBufferBodyCore hcode hsize hperm h7 hAccounts
                · by_cases h8 : selIs I (auctionSelBytes 8)
                  · exact auctionRenounceOwnershipBodyCore hcode hsize hperm h8 hAccounts
                  · by_cases h9 : selIs I (auctionSelBytes 9)
                    · exact auctionAuctionBodyCore hcode hsize hperm h9 hAccounts
                    · by_cases h10 : selIs I (auctionSelBytes 10)
                      · exact auctionPauseBodyCore hcode hsize hperm h10 hAccounts
                      · by_cases h11 : selIs I (auctionSelBytes 11)
                        · exact auctionInitializeBodyCore hcode hsize hperm h11 hAccounts
                        · by_cases h12 : selIs I (auctionSelBytes 12)
                          · exact auctionOwnerBodyCore hcode hsize hperm h12 hAccounts
                          · by_cases h13 : selIs I (auctionSelBytes 13)
                            · exact auctionSettleAuctionBodyCore hcode hsize hperm h13 hAccounts
                            · by_cases h14 : selIs I (auctionSelBytes 14)
                              · exact auctionMinBidIncrementPercentageBodyCore hcode hsize hperm h14
                                  hAccounts
                              · by_cases h15 : selIs I (auctionSelBytes 15)
                                · exact auctionSetReservePriceBodyCore hcode hsize hperm h15 hAccounts
                                · by_cases h16 : selIs I (auctionSelBytes 16)
                                  · exact auctionReservePriceBodyCore hcode hsize hperm h16 hAccounts
                                  · by_cases h17 : selIs I (auctionSelBytes 17)
                                    · exact auctionTimeBufferBodyCore hcode hsize hperm h17 hAccounts
                                    · by_cases h18 : selIs I (auctionSelBytes 18)
                                      · exact auctionSettleCurrentAndCreateNewAuctionBodyCore hcode hsize
                                          hperm h18 hAccounts
                                      · by_cases h19 : selIs I (auctionSelBytes 19)
                                        · exact auctionTransferOwnershipBodyCore hcode hsize hperm h19
                                            hAccounts
                                        · refine auctionNoDispatch hcode hsize hperm ?_ hAccounts
                                          intro i hi
                                          interval_cases i
                                          · exact h0
                                          · exact h1
                                          · exact h2
                                          · exact h3
                                          · exact h4
                                          · exact h5
                                          · exact h6
                                          · exact h7
                                          · exact h8
                                          · exact h9
                                          · exact h10
                                          · exact h11
                                          · exact h12
                                          · exact h13
                                          · exact h14
                                          · exact h15
                                          · exact h16
                                          · exact h17
                                          · exact h18
                                          · exact h19

theorem auctionContractCorrect :
    contractEquivalence auctionConfig auctionCreationBytecode auctionBytecode Auction.auctionContract :=
  contractEquivalence.intro auctionConstructorCorrect auctionCorrect

end Auction
