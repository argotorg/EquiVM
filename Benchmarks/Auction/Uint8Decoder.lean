import Benchmarks.Auction.CalldataHead
import Benchmarks.Auction.PackedByte

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem uint8WordOk {I g s0 offset ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5304⟩ (offset :: ret :: R) mem aw rdata acc k C)
    (hc : (calldataWord I.calldata offset.toNat).toNat < 256)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret
      (calldataWord I.calldata offset.toNat :: R) mem aw rdata acc k' C' := by
  have rd5320 := evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiT (by rw [lowByteClean hc, uInt256_eq_self]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5320 with [jumpdest, swap2, swap1, pop, jump hret]⟩

theorem uint8WordFail {I g s0 offset ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5304⟩ (offset :: ret :: R) mem aw rdata acc k C)
    (hc : ¬ (calldataWord I.calldata offset.toNat).toNat < 256)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have hne : calldataWord I.calldata offset.toNat ≠
      UInt256.land (calldataWord I.calldata offset.toNat) ⟨255⟩ := by
    exact fun he => hc ((lowByteClean_iff _).mp he.symm)
  exact evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiNT (u256_eq_of_ne hne),
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov) ]

set_option synthInstance.maxSize 1024 in
theorem uint8HeadWf : calldataHeadWf auctionBytecode ⟨5325⟩ ⟨5341⟩ ⟨32⟩ := by
  unfold calldataHeadWf
  native_decide

theorem decodeUint8ToWord {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5325⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5304⟩
      (⟨4⟩ :: ⟨5350⟩ :: ⟨0⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5341⟩ := calldataHeadOk h uint8HeadWf
    (solcDecodeLenCheckOk_4_32 hlen hhi hsize) hov
  exact ⟨_, _, evm_run rd5341 with [
    jumpdest, push2 ⟨5350⟩, dup3, push2 ⟨5304⟩, jump (by jump_dest) ]⟩

theorem decodeUint8Ok {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5325⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hc : (calldataWord I.calldata 4).toNat < 256)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (calldataWord I.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5304⟩ := decodeUint8ToWord h hlen hhi hsize (by omega)
  obtain ⟨_, _, rd5350⟩ := uint8WordOk rd5304 hc (by jump_dest) (by evm_ov)
  exact oneResultReturn rd5350 hret (by evm_ov)

theorem decodeUint8FailNoncanonical {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5325⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hc : ¬ (calldataWord I.calldata 4).toNat < 256)
    (hov : R.length + 10 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd5304⟩ := decodeUint8ToWord h hlen hhi hsize (by omega)
  exact uint8WordFail rd5304 hc (by evm_ov)

end Auction
