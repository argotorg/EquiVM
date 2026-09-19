import Solm.Benchmarks.Auction.Returns

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem wordEventReturn {I g s0 val topic ret R rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1065⟩ (⟨160⟩ :: topic :: val :: ret :: R)
      (solcReturnMem val) (UInt256.ofNat 5) rdata acc k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (solcReturnMem val) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have rd1073 := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
      (solcReturnMem_mload64 val) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact ⟨_, _, evm_run rd1073 with [
    raw log1 0 (UInt256.ofNat 5) (by native_decide) hperm mem_cost
      (by decide) (by evm_ov),
    pop, jump hret ]⟩

theorem auctionStop {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨413⟩ R mem aw rdata acc k C)
    (hov : R.length ≤ 1024) : RDret auctionBytecode g s0 acc ByteArray.empty := by
  exact evm_run h with [jumpdest, raw stop (by native_decide) hov]

end Auction
