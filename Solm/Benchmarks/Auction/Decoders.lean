import Solm.Benchmarks.Auction.CalldataHead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option synthInstance.maxSize 1024 in
theorem uint256HeadWf : calldataHeadWf auctionBytecode ⟨5357⟩ ⟨5373⟩ ⟨32⟩ := by
  unfold calldataHeadWf
  native_decide

theorem decodeUint256Ok {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5357⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (calldataWord I.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5373⟩ := calldataHeadOk h uint256HeadWf
    (solcDecodeLenCheckOk_4_32 hlen hhi hsize) hov
  have rdRet := evm_run rd5373 with [
    jumpdest, pop, calldataload, swap2, swap1, pop, jump hret ]
  exact ⟨_, _, rdRet⟩

theorem decodeUint256Fail {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5357⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hbad : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 := by
  exact calldataHeadFail h uint256HeadWf hbad hov

end Auction
