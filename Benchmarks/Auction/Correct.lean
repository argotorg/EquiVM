import Benchmarks.Auction.Duration
import Benchmarks.Auction.Nouns
import Benchmarks.Auction.SetMinBidIncrementPercentage
import Benchmarks.Auction.Unpause
import Benchmarks.Auction.Weth
import Benchmarks.Auction.Paused
import Benchmarks.Auction.CreateBid
import Benchmarks.Auction.SetTimeBuffer
import Benchmarks.Auction.RenounceOwnership
import Benchmarks.Auction.Auction
import Benchmarks.Auction.Pause
import Benchmarks.Auction.Initialize
import Benchmarks.Auction.Owner
import Benchmarks.Auction.SettleAuction
import Benchmarks.Auction.MinBidIncrementPercentage
import Benchmarks.Auction.SetReservePrice
import Benchmarks.Auction.ReservePrice
import Benchmarks.Auction.TimeBuffer
import Benchmarks.Auction.SettleCurrentAndCreateNewAuction
import Benchmarks.Auction.TransferOwnership
import Benchmarks.Auction.Constructor
import Benchmarks.Auction.Dispatcher
import Solm.Refine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

/-! Selector routing for the deployed Auction runtime. -/

end Auction

open Auction

theorem auctionCorrect :
    runtimeRefinement auctionConfig auctionBytecode Auction.auctionContract := by
  refine ⟨fun σ σ₀ g A I hcode hsize ↦ ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact auctionShortRevert hcode (by omega)
  by_cases h0 : selIs I (entryBytes 0)
  · exact durationBodyCore hcode hsize h0
      (auctionReachEntry 0 hcode hsz hsize h0)
  by_cases h1 : selIs I (entryBytes 1)
  · exact nounsBodyCore hcode hsize h1
      (auctionReachEntry 1 hcode hsz hsize h1)
  by_cases h2 : selIs I (entryBytes 2)
  · exact setMinBidIncrementPercentageBodyCore hcode hsize h2
      (auctionReachEntry 2 hcode hsz hsize h2)
  by_cases h3 : selIs I (entryBytes 3)
  · exact unpauseBodyCore hcode hsize h3
      (auctionReachEntry 3 hcode hsz hsize h3)
  by_cases h4 : selIs I (entryBytes 4)
  · exact wethBodyCore hcode hsize h4
      (auctionReachEntry 4 hcode hsz hsize h4)
  by_cases h5 : selIs I (entryBytes 5)
  · exact pausedBodyCore hcode hsize h5
      (auctionReachEntry 5 hcode hsz hsize h5)
  by_cases h6 : selIs I (entryBytes 6)
  · exact createBidBodyCore hcode hsize h6
      (auctionReachEntry 6 hcode hsz hsize h6)
  by_cases h7 : selIs I (entryBytes 7)
  · exact setTimeBufferBodyCore hcode hsize h7
      (auctionReachEntry 7 hcode hsz hsize h7)
  by_cases h8 : selIs I (entryBytes 8)
  · exact renounceOwnershipBodyCore hcode hsize h8
      (auctionReachEntry 8 hcode hsz hsize h8)
  by_cases h9 : selIs I (entryBytes 9)
  · exact auctionBodyCore hcode hsize h9
      (auctionReachEntry 9 hcode hsz hsize h9)
  by_cases h10 : selIs I (entryBytes 10)
  · exact pauseBodyCore hcode hsize h10
      (auctionReachEntry 10 hcode hsz hsize h10)
  by_cases h11 : selIs I (entryBytes 11)
  · exact initializeBodyCore hcode hsize h11
      (auctionReachEntry 11 hcode hsz hsize h11)
  by_cases h12 : selIs I (entryBytes 12)
  · exact ownerBodyCore hcode hsize h12
      (auctionReachEntry 12 hcode hsz hsize h12)
  by_cases h13 : selIs I (entryBytes 13)
  · exact settleAuctionBodyCore hcode hsize h13
      (auctionReachEntry 13 hcode hsz hsize h13)
  by_cases h14 : selIs I (entryBytes 14)
  · exact minBidIncrementPercentageBodyCore hcode hsize h14
      (auctionReachEntry 14 hcode hsz hsize h14)
  by_cases h15 : selIs I (entryBytes 15)
  · exact setReservePriceBodyCore hcode hsize h15
      (auctionReachEntry 15 hcode hsz hsize h15)
  by_cases h16 : selIs I (entryBytes 16)
  · exact reservePriceBodyCore hcode hsize h16
      (auctionReachEntry 16 hcode hsz hsize h16)
  by_cases h17 : selIs I (entryBytes 17)
  · exact timeBufferBodyCore hcode hsize h17
      (auctionReachEntry 17 hcode hsz hsize h17)
  by_cases h18 : selIs I (entryBytes 18)
  · exact settleCurrentAndCreateNewAuctionBodyCore hcode hsize h18
      (auctionReachEntry 18 hcode hsz hsize h18)
  by_cases h19 : selIs I (entryBytes 19)
  · exact transferOwnershipBodyCore hcode hsize h19
      (auctionReachEntry 19 hcode hsz hsize h19)
  apply auctionNoDispatch hcode hsz hsize
  rintro ⟨i, hi⟩
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
    contractRefinement auctionConfig auctionCreationBytecode
      Auction.auctionContract :=
  contractRefinement.of_constant auctionConstructorCorrect auctionCorrect
