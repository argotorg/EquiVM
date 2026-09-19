import Solm.Benchmarks.Auction.Duration
import Solm.Benchmarks.Auction.Nouns
import Solm.Benchmarks.Auction.SetMinBidIncrementPercentage
import Solm.Benchmarks.Auction.Unpause
import Solm.Benchmarks.Auction.Weth
import Solm.Benchmarks.Auction.Paused
import Solm.Benchmarks.Auction.CreateBid
import Solm.Benchmarks.Auction.SetTimeBuffer
import Solm.Benchmarks.Auction.RenounceOwnership
import Solm.Benchmarks.Auction.Auction
import Solm.Benchmarks.Auction.Pause
import Solm.Benchmarks.Auction.Initialize
import Solm.Benchmarks.Auction.Owner
import Solm.Benchmarks.Auction.SettleAuction
import Solm.Benchmarks.Auction.MinBidIncrementPercentage
import Solm.Benchmarks.Auction.SetReservePrice
import Solm.Benchmarks.Auction.ReservePrice
import Solm.Benchmarks.Auction.TimeBuffer
import Solm.Benchmarks.Auction.SettleCurrentAndCreateNewAuction
import Solm.Benchmarks.Auction.TransferOwnership
import Solm.Benchmarks.Auction.Constructor
import Solm.Benchmarks.Auction.Dispatcher

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

/-! Selector routing for the deployed Auction runtime. -/

end Auction

open Auction

theorem auctionCorrect :
    runtimeEquivalence auctionConfig auctionBytecode Auction.auctionContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact auctionShortRevert hcode (by omega)
  by_cases h0 : selIs I (entryBytes 0)
  · exact durationBodyCore hcode hsize hperm h0
      (auctionReachEntry 0 hcode hsz hsize h0) hAccounts
  by_cases h1 : selIs I (entryBytes 1)
  · exact nounsBodyCore hcode hsize hperm h1
      (auctionReachEntry 1 hcode hsz hsize h1) hAccounts
  by_cases h2 : selIs I (entryBytes 2)
  · exact setMinBidIncrementPercentageBodyCore hcode hsize hperm h2
      (auctionReachEntry 2 hcode hsz hsize h2) hAccounts
  by_cases h3 : selIs I (entryBytes 3)
  · exact unpauseBodyCore hcode hsize hperm h3
      (auctionReachEntry 3 hcode hsz hsize h3) hAccounts
  by_cases h4 : selIs I (entryBytes 4)
  · exact wethBodyCore hcode hsize hperm h4
      (auctionReachEntry 4 hcode hsz hsize h4) hAccounts
  by_cases h5 : selIs I (entryBytes 5)
  · exact pausedBodyCore hcode hsize hperm h5
      (auctionReachEntry 5 hcode hsz hsize h5) hAccounts
  by_cases h6 : selIs I (entryBytes 6)
  · exact createBidBodyCore hcode hsize hperm h6
      (auctionReachEntry 6 hcode hsz hsize h6) hAccounts
  by_cases h7 : selIs I (entryBytes 7)
  · exact setTimeBufferBodyCore hcode hsize hperm h7
      (auctionReachEntry 7 hcode hsz hsize h7) hAccounts
  by_cases h8 : selIs I (entryBytes 8)
  · exact renounceOwnershipBodyCore hcode hsize hperm h8
      (auctionReachEntry 8 hcode hsz hsize h8) hAccounts
  by_cases h9 : selIs I (entryBytes 9)
  · exact auctionBodyCore hcode hsize hperm h9
      (auctionReachEntry 9 hcode hsz hsize h9) hAccounts
  by_cases h10 : selIs I (entryBytes 10)
  · exact pauseBodyCore hcode hsize hperm h10
      (auctionReachEntry 10 hcode hsz hsize h10) hAccounts
  by_cases h11 : selIs I (entryBytes 11)
  · exact initializeBodyCore hcode hsize hperm h11
      (auctionReachEntry 11 hcode hsz hsize h11) hAccounts
  by_cases h12 : selIs I (entryBytes 12)
  · exact ownerBodyCore hcode hsize hperm h12
      (auctionReachEntry 12 hcode hsz hsize h12) hAccounts
  by_cases h13 : selIs I (entryBytes 13)
  · exact settleAuctionBodyCore hcode hsize hperm h13
      (auctionReachEntry 13 hcode hsz hsize h13) hAccounts
  by_cases h14 : selIs I (entryBytes 14)
  · exact minBidIncrementPercentageBodyCore hcode hsize hperm h14
      (auctionReachEntry 14 hcode hsz hsize h14) hAccounts
  by_cases h15 : selIs I (entryBytes 15)
  · exact setReservePriceBodyCore hcode hsize hperm h15
      (auctionReachEntry 15 hcode hsz hsize h15) hAccounts
  by_cases h16 : selIs I (entryBytes 16)
  · exact reservePriceBodyCore hcode hsize hperm h16
      (auctionReachEntry 16 hcode hsz hsize h16) hAccounts
  by_cases h17 : selIs I (entryBytes 17)
  · exact timeBufferBodyCore hcode hsize hperm h17
      (auctionReachEntry 17 hcode hsz hsize h17) hAccounts
  by_cases h18 : selIs I (entryBytes 18)
  · exact settleCurrentAndCreateNewAuctionBodyCore hcode hsize hperm h18
      (auctionReachEntry 18 hcode hsz hsize h18) hAccounts
  by_cases h19 : selIs I (entryBytes 19)
  · exact transferOwnershipBodyCore hcode hsize hperm h19
      (auctionReachEntry 19 hcode hsz hsize h19) hAccounts
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
    contractEquivalence auctionConfig auctionCreationBytecode auctionBytecode
      Auction.auctionContract :=
  contractEquivalence.intro auctionConstructorCorrect auctionCorrect
