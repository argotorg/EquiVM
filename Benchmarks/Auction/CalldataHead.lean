import Reasoning.SolcRoutines
import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction


theorem oneResultReturn {I g s0 value unused off sz ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5350⟩ (value :: unused :: off :: sz :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (value :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, swap4, swap3, pop, pop, pop, jump hret]⟩

end Auction
