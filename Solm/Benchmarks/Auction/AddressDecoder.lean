import Solm.Benchmarks.Auction.CalldataHead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem addressCleanOk {I g s0 value ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5380⟩ (value :: ret :: R) mem aw rdata acc k C)
    (hc : value.toNat < EVM.addressModulus)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata acc k' C' := by
  have rd2850 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq,
    push2 ⟨2850⟩, jumpiT (by
      change UInt256.eq value (UInt256.land value solcAddrMask) ≠ ⟨0⟩
      rw [solcAddrCanon_eq hc]
      decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd2850 with [jumpdest, pop, jump hret]⟩

theorem addressCleanFail {I g s0 value ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5380⟩ (value :: ret :: R) mem aw rdata acc k C)
    (hc : ¬ value.toNat < EVM.addressModulus)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have hne : value ≠ UInt256.land value solcAddrMask := by
    intro he
    exact hc (he ▸ solcAddrMask_result_canonical value)
  exact evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq,
    push2 ⟨2850⟩, jumpiNT (u256_eq_of_ne hne),
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov) ]

set_option synthInstance.maxSize 1024 in
theorem addressHeadWf : calldataHeadWf auctionBytecode ⟨5495⟩ ⟨5511⟩ ⟨32⟩ := by
  unfold calldataHeadWf
  native_decide

theorem decodeAddressToClean {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5495⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5380⟩
      (calldataWord I.calldata 4 :: ⟨5350⟩ :: calldataWord I.calldata 4 :: ⟨0⟩ ::
        ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5511⟩ := calldataHeadOk h addressHeadWf
    (solcDecodeLenCheckOk_4_32 hlen hhi hsize) hov
  exact ⟨_, _, evm_run rd5511 with [
    jumpdest, dup2, calldataload, push2 ⟨5350⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest) ]⟩

theorem decodeAddressOk {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5495⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (calldataWord I.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5380⟩ := decodeAddressToClean h hlen hhi hsize (by omega)
  obtain ⟨_, _, rd5350⟩ := addressCleanOk rd5380 hc (by jump_dest) (by evm_ov)
  exact oneResultReturn rd5350 hret (by evm_ov)

theorem decodeAddressFailNoncanonical {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5495⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 11 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd5380⟩ := decodeAddressToClean h hlen hhi hsize (by omega)
  exact addressCleanFail rd5380 hc (by evm_ov)

end Auction
