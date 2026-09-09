import Benchmarks.Auction.CreateAuctionWithMemoryFailure
import Benchmarks.Auction.CreateAuctionCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

theorem auctionCreateAuctionWithMemoryRuntime {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm : EVM.State} {mem rdata : ByteArray} {aw free ret : UInt256}
    {R : List UInt256} {k C : Nat}
    (hm : AuctionCreateMemoryValid mem aw free) (hfree : free.toNat < 2 ^ 68)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024) (hR : R.length ≤ 980)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (henv : evm.executionEnv = I) (ha : accountMapEquiv σ evm.accountMap)
    (horig : evm.σ₀ = σ₀) (hgen : evm.genesisBlockHeader = gh) (hblocks : evm.blocks = bl)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      (ret :: R) mem aw rdata (evm.createdAccounts, σ) k C) :
    AuctionCreateMemoryOutcome (initState cA gh bl σInit σ₀ g A I) I g evm free ret R := by
  obtain ⟨cA', σ', z, out, A', _, _, rd3067, hcallE, _⟩ :=
    auctionCreateAuctionWithMemoryPostMintCall hm hperm hdepth (by evm_ov) rd
  obtain ⟨σS', AS', hcall, hmap⟩ := auctionCreateAuctionMintCall_transport henv ha hdepth
    horig hgen hblocks hcallE
  have henvCall : ({ evm with accountMap := σS', substate := AS', createdAccounts := cA' } :
      EVM.State).executionEnv = I := henv
  cases z with
  | false =>
    exact auctionCreateAuctionWithMemoryFailure hm.selector hfree hR hperm hret
      hcall henvCall hmap rd3067
  | true =>
    cases hdec : ABI.decodeReturnValue? uint256 out with
    | none => exact auctionCreateAuctionWithMemoryDecodeFailure hm.selector hR hcall hdec rd3067
    | some decoded =>
      obtain ⟨nounId, hdec⟩ := auctionDecodeReturn_uint256_some_exists hdec
      exact auctionCreateAuctionWithMemorySuccess hm.selector hR hperm hret hcall
        henvCall hmap hdec rd3067

end Auction
