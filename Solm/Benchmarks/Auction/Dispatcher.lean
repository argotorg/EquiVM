import Solm.Benchmarks.Auction.DispatchReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem auctionShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (auctionXShort (g := Sat256.ofUInt256 g) hcode hsz)
    |>.reEquivNoDispatch hcode (dispatchShort hsz)

theorem auctionNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i : Entry, ¬ selIs I (entryBytes i)) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (auctionXNoMatch (g := Sat256.ofUInt256 g) hcode hsz hsize hnm)
    |>.reEquivNoDispatch hcode (dispatchNone (fun i => by
      simpa only [selIs, Bool.not_eq_true] using hnm i))

end Auction
