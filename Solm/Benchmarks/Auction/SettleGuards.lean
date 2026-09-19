import Solm.Benchmarks.Auction.SettleSnapshot
import Solm.Benchmarks.Auction.ShortError

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem settleStarted {I g s0 s ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4162⟩ (ptr :: Snapshot.startTime s :: ret :: R)
      mem aw rdata acc k C) (hstart : s.startTime ≠ ⟨0⟩) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4231⟩ (ptr :: ret :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [swap1, push0, sub, push2 ⟨4231⟩,
    jumpiT (u256_zero_sub_ne_zero hstart) (by jump_dest)]⟩

theorem settleUnsettled {I g s0 s ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4231⟩ (ptr :: ret :: R) mem aw rdata acc k C)
    (hm : SnapshotMemory s mem aw ptr) (hset : s.settledByte = ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4313⟩ (ptr :: ret :: R) mem aw rdata acc k' C' := by
  have hl : loadedWord mem aw (ptr + ⟨160⟩) = s.settledWord := by
    set_option maxRecDepth 2048 in exact hm.load ⟨5, by decide⟩
  have ha : expandedWords aw (ptr + ⟨160⟩) ⟨32⟩ = aw := hm.expand_eq ⟨5, by decide⟩
  have rd4237 := evm_run h with [jumpdest, dup1, push1 ⟨160⟩, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [u256_add_comm ⟨160⟩ ptr, hl, ha] at rd4237
  exact ⟨_, _, evm_run rd4237 with [iszero, push2 ⟨4313⟩,
    jumpiT (by rw [Snapshot.settledWord, hset]; decide) (by jump_dest)]⟩

theorem settleEnded {I g s0 s ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4313⟩ (ptr :: ret :: R) mem aw rdata acc k C)
    (hm : SnapshotMemory s mem aw ptr)
    (htime : s.endTime.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4397⟩ (ptr :: ret :: R) mem aw rdata acc k' C' := by
  have hl : loadedWord mem aw (ptr + ⟨96⟩) = s.endTime := hm.load ⟨3, by decide⟩
  have ha : expandedWords aw (ptr + ⟨96⟩) ⟨32⟩ = aw := hm.expand_eq ⟨3, by decide⟩
  have rd4319 := evm_run h with [jumpdest, dup1, push1 ⟨96⟩, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [u256_add_comm ⟨96⟩ ptr, hl, ha] at rd4319
  exact ⟨_, _, evm_run rd4319 with [timestamp, lt, iszero, push2 ⟨4397⟩,
    jumpiT (by rw [ult_zero htime]; decide) (by jump_dest)]⟩

theorem auctionErrorRevert {I g s0 finish R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨994⟩ (finish :: R) mem aw rdata acc k C)
    (hov : R.length + 4 ≤ 1024) : RDrev auctionBytecode g s0 := by
  exact evm_run h with [jumpdest, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov), dup1, swap2, sub, swap1,
    raw revertSymbolic (by native_decide) (by evm_ov)]

set_option synthInstance.maxSize 4096 in
theorem settleNotStartedError {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4169⟩ R mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, _, _, _, hr⟩ := shortError (ret := ⟨994⟩) (len := ⟨20⟩)
    (word := ⟨0x20bab1ba34b7b7103430b9b713ba103132b3bab7⟩) (shift := ⟨97⟩)
    (op := .PUSH20) (width := 20) h (by
      unfold shortErrorWf errorHeaderWf errorWordTailWf
      native_decide) (by decide) hov
  exact auctionErrorRevert hr (by omega)

theorem settleAlreadySettledError {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4242⟩ R mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd4245 := evm_run h with [push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov)]
  have rd4249 := rd4245.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd4268 := evm_run rd4249 with [push1 ⟨229⟩, shl, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨32⟩, push1 ⟨4⟩, dup3, add, dup2,
    swap1, raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨36⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd4301 := rd4268.pushConst
    ⟨0x41756374696f6e2068617320616c7265616479206265656e20736574746c6564⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd994 := evm_run rd4301 with [push1 ⟨68⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨100⟩, add,
    push2 ⟨994⟩, jump (by jump_dest)]
  exact auctionErrorRevert rd994 (by evm_ov)

set_option synthInstance.maxSize 4096 in
theorem settleNotEndedError {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4326⟩ R mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, _, _, _, hr⟩ := literalError (ret := ⟨994⟩) (len := ⟨24⟩)
    (word := ⟨0x41756374696f6e206861736e277420636f6d706c657465640000000000000000⟩) h (by
      unfold literalErrorWf errorHeaderWf errorWordTailWf
      native_decide) hov
  exact auctionErrorRevert hr (by omega)

theorem settleNotStarted {I g s0 s ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4162⟩ (ptr :: Snapshot.startTime s :: ret :: R)
      mem aw rdata acc k C) (hstart : s.startTime = ⟨0⟩) (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  rw [hstart] at h
  have rd4169 := evm_run h with [swap1, push0, sub, push2 ⟨4231⟩, jumpiNT (by decide)]
  exact settleNotStartedError rd4169 (by evm_ov)

theorem settleAlreadySettled {I g s0 s ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4231⟩ (ptr :: ret :: R) mem aw rdata acc k C)
    (hm : SnapshotMemory s mem aw ptr) (hset : s.settledByte ≠ ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have hl : loadedWord mem aw (ptr + ⟨160⟩) = s.settledWord := by
    set_option maxRecDepth 2048 in exact hm.load ⟨5, by decide⟩
  have ha : expandedWords aw (ptr + ⟨160⟩) ⟨32⟩ = aw := hm.expand_eq ⟨5, by decide⟩
  have rd4237 := evm_run h with [jumpdest, dup1, push1 ⟨160⟩, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [u256_add_comm ⟨160⟩ ptr, hl, ha] at rd4237
  have hz : UInt256.isZero s.settledByte = ⟨0⟩ := isZero_eq_zero_of_ne hset
  have rd4242 := evm_run rd4237 with [iszero, push2 ⟨4313⟩,
    jumpiNT (by rw [Snapshot.settledWord, hz]; decide)]
  exact settleAlreadySettledError rd4242 (by evm_ov)

theorem settleNotEnded {I g s0 s ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4313⟩ (ptr :: ret :: R) mem aw rdata acc k C)
    (hm : SnapshotMemory s mem aw ptr)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < s.endTime.toNat)
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have hl : loadedWord mem aw (ptr + ⟨96⟩) = s.endTime := hm.load ⟨3, by decide⟩
  have ha : expandedWords aw (ptr + ⟨96⟩) ⟨32⟩ = aw := hm.expand_eq ⟨3, by decide⟩
  have rd4319 := evm_run h with [jumpdest, dup1, push1 ⟨96⟩, add,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [u256_add_comm ⟨96⟩ ptr, hl, ha] at rd4319
  have rd4326 := evm_run rd4319 with [timestamp, lt, iszero, push2 ⟨4397⟩,
    jumpiNT (by rw [ult_one htime]; decide)]
  exact settleNotEndedError rd4326 (by evm_ov)

end Auction
