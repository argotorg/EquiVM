import Benchmarks.Auction.CheckedAdd

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem checkedDivOk {I g s0 a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5673⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hb : b ≠ ⟨0⟩) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (UInt256.div a b :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, push0, dup3, push2 ⟨5699⟩, jumpiT hb (by jump_dest),
    jumpdest, pop, div, swap1, jump hret]⟩

theorem checkedSubOk {I g s0 a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5723⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hno : b.toNat ≤ a.toNat)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (UInt256.sub a b :: R) mem aw rdata acc k' C' := by
  have hg : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ := ugt_zero (by rw [usub_toNat hno]; omega)
  have rd4886 := evm_run h with [jumpdest, dup2, dup2, sub, dup2, dup2, gt, iszero,
    push2 ⟨4886⟩, jumpiT (by rw [hg]; decide) (by jump_dest)]
  exact arithmeticReturn rd4886 hret (by evm_ov)

end Auction
