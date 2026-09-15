import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the shared signed length guard for a one-word solc argument decoder.
def calldataHeadWf (code : ByteArray) (pc target need : UInt256) : Prop :=
  let p0 := pc
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + UInt256.ofNat 3
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  decode code p0 = some (.JUMPDEST, .none) ∧
  decode code p1 = some (.Push .PUSH0, .none) ∧
  decode code p2 = some (.Push .PUSH1, some (need, 1)) ∧
  decode code p3 = some (.DUP3, .none) ∧
  decode code p4 = some (.DUP5, .none) ∧
  decode code p5 = some (.SUB, .none) ∧
  decode code p6 = some (.SLT, .none) ∧
  decode code p7 = some (.ISZERO, .none) ∧
  decode code p8 = some (.Push .PUSH2, some (target, 2)) ∧
  decode code p9 = some (.JUMPI, .none) ∧
  decode code p10 = some (.Push .PUSH0, .none) ∧
  decode code p11 = some (.DUP1, .none) ∧
  decode code p12 = some (.REVERT, .none) ∧
  (D_J code 0).contains target = true

theorem calldataHeadOk {code I g s0 pc target need off sz ret R mem aw rdata acc k C}
    (h : RD code I g s0 pc (off :: sz :: ret :: R) mem aw rdata acc k C)
    (hwf : calldataHeadWf code pc target need)
    (hcheck : UInt256.slt (UInt256.sub sz off) need = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code I g s0 target (⟨0⟩ :: off :: sz :: ret :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, _, _, hd⟩ := hwf
  exact ⟨_, _, evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push0 h1 (by evm_ov), raw push1 need h2 (by evm_ov),
    raw dup3 h3 (by evm_ov), raw dup5 h4 (by evm_ov), raw sub h5 (by evm_ov),
    raw slt h6 (by evm_ov), raw iszero h7 (by evm_ov), raw push2 target h8 (by evm_ov),
    raw jumpiT h9 (by rw [hcheck]; decide) hd (by evm_ov) ]⟩

theorem calldataHeadFail {code I g s0 pc target need off sz ret R mem aw rdata acc k C}
    (h : RD code I g s0 pc (off :: sz :: ret :: R) mem aw rdata acc k C)
    (hwf : calldataHeadWf code pc target need)
    (hcheck : UInt256.slt (UInt256.sub sz off) need = ⟨1⟩)
    (hov : R.length + 8 ≤ 1024) : RDrev code g s0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _⟩ := hwf
  have rdFail := evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push0 h1 (by evm_ov), raw push1 need h2 (by evm_ov),
    raw dup3 h3 (by evm_ov), raw dup5 h4 (by evm_ov), raw sub h5 (by evm_ov),
    raw slt h6 (by evm_ov), raw iszero h7 (by evm_ov), raw push2 target h8 (by evm_ov),
    raw jumpiNT h9 (by rw [hcheck]; decide) (by evm_ov) ]
  exact rdFail.auctionRevert0 h10 h11 h12 (by evm_ov)

theorem oneResultReturn {I g s0 value unused off sz ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5350⟩ (value :: unused :: off :: sz :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (value :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, swap4, swap3, pop, pop, pop, jump hret]⟩

end Auction
