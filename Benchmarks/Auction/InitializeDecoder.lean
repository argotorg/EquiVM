import Benchmarks.Auction.InitializeArgs
import Benchmarks.Auction.AddressDecoder
import Benchmarks.Auction.Uint8Decoder

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem initializeDecodeFirst {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5400⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 196 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5380⟩
      (calldataWord I.calldata 4 :: ⟨5432⟩ :: calldataWord I.calldata 4 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k' C' := by
  have hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ = ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 6) hlen hhi hsize
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩, dup8, dup10, sub, slt,
    iszero, push2 ⟨5421⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5421 with [
    jumpdest, dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest) ]⟩

theorem initializeDecodeSecond {I g s0 noun ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5432⟩
      (noun :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5380⟩
      (calldataWord I.calldata 36 :: ⟨5448⟩ :: calldataWord I.calldata 36 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: noun ::
        ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, swap6, pop, push1 ⟨32⟩, dup8, add, calldataload,
    push2 ⟨5448⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest) ]⟩

theorem initializeDecodeUint8 {I g s0 noun weth ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5448⟩
      (weth :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: noun ::
        ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5304⟩
      (⟨132⟩ :: ⟨5476⟩ :: ⟨0⟩ :: ⟨0⟩ :: calldataWord I.calldata 100 ::
        calldataWord I.calldata 68 :: weth :: noun :: ⟨4⟩ ::
        UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k' C' := by
  have rd5465 := evm_run h with [
    jumpdest, swap5, pop, push1 ⟨64⟩, dup8, add, calldataload, swap4, pop,
    push1 ⟨96⟩, dup8, add, calldataload, swap3, pop ]
  exact ⟨_, _, evm_run rd5465 with [
    push2 ⟨5476⟩, push1 ⟨128⟩, dup9, add, push2 ⟨5304⟩, jump (by jump_dest) ]⟩

theorem initializeDecodeReturn {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5476⟩
      (calldataWord I.calldata 132 :: ⟨0⟩ :: ⟨0⟩ :: calldataWord I.calldata 100 ::
        calldataWord I.calldata 68 :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 ::
        ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret ((initializeArgs I.calldata).words.reverse ++ R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, swap2, pop, push1 ⟨160⟩, dup8, add, calldataload, swap1, pop,
    swap3, swap6, pop, swap3, swap6, pop, swap3, swap6, jump hret ]⟩

theorem initializeDecoderOk {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5400⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 196 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hc : (initializeArgs I.calldata).canonical)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret ((initializeArgs I.calldata).words.reverse ++ R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5380⟩ := initializeDecodeFirst h hlen hhi hsize hov
  obtain ⟨_, _, rd5432⟩ := addressCleanOk rd5380 hc.1 (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5380'⟩ := initializeDecodeSecond rd5432 (by omega)
  obtain ⟨_, _, rd5448⟩ := addressCleanOk rd5380' hc.2.1 (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5304⟩ := initializeDecodeUint8 rd5448 (by omega)
  obtain ⟨_, _, rd5476⟩ := uint8WordOk rd5304 hc.2.2 (by jump_dest) (by evm_ov)
  exact initializeDecodeReturn rd5476 hret (by omega)

theorem initializeDecoderNoncanonical {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5400⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hlen : 196 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hc : ¬ (initializeArgs I.calldata).canonical)
    (hov : R.length + 16 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd5380⟩ := initializeDecodeFirst h hlen hhi hsize hov
  by_cases hn : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  · obtain ⟨_, _, rd5432⟩ := addressCleanOk rd5380 hn (by jump_dest) (by evm_ov)
    obtain ⟨_, _, rd5380'⟩ := initializeDecodeSecond rd5432 (by omega)
    by_cases hw : (calldataWord I.calldata 36).toNat < EVM.addressModulus
    · obtain ⟨_, _, rd5448⟩ := addressCleanOk rd5380' hw (by jump_dest) (by evm_ov)
      obtain ⟨_, _, rd5304⟩ := initializeDecodeUint8 rd5448 (by omega)
      exact uint8WordFail rd5304 (fun h8 => hc ⟨hn, hw, h8⟩) (by evm_ov)
    · exact addressCleanFail rd5380' hw (by evm_ov)
  · exact addressCleanFail rd5380 hn (by evm_ov)

theorem initializeDecoderBadLength {I g s0 ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5400⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ = ⟨1⟩)
    (hov : R.length + 16 ≤ 1024) : RDrev auctionBytecode g s0 := by
  exact evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩, dup8, dup10, sub, slt,
    iszero, push2 ⟨5421⟩, jumpiNT (by rw [hcheck]; decide),
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov) ]

end Auction
