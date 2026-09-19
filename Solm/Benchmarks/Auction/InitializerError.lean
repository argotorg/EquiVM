import Solm.Benchmarks.Auction.InitializerGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem initializerErrorRevert {I g s0 ptr R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5742⟩ (ptr :: ⟨994⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd5754 := evm_run h with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov),
    push1 ⟨46⟩, swap1, dup3, add, raw mstoreSymbolic (by native_decide) (by evm_ov) ]
  have rd5787 := rd5754.pushConst
    ⟨0x496e697469616c697a61626c653a20636f6e747261637420697320616c726561⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd5792 := evm_run rd5787 with [
    push1 ⟨64⟩, dup3, add, raw mstoreSymbolic (by native_decide) (by evm_ov) ]
  have rd5807 := rd5792.pushConst ⟨0x191e481a5b9a5d1a585b1a5e9959⟩
    (width := 14) (op := .PUSH14) (by decide) (by native_decide) (by evm_ov)
  have rd994 := evm_run rd5807 with [
    push1 ⟨146⟩, shl, push1 ⟨96⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov),
    push1 ⟨128⟩, add, swap1, jump (by jump_dest) ]
  exact evm_run rd994 with [
    jumpdest, push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1, raw revertSymbolic (by native_decide) (by evm_ov) ]

theorem initializeGuardRevert {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2130⟩ R mem aw rdata (cA, σ) k C)
    (hi : initializingWord σ I = ⟨0⟩) (hz : initializedWord σ I ≠ ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd2132 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd2133⟩ := rd2132.sload (by native_decide) (by evm_ov)
  have rd2141 := evm_run rd2133 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and]
  change RD _ _ _ _ _
    (UInt256.land ⟨255⟩ (UInt256.div (storedWord σ I ⟨0⟩) ⟨256⟩) :: R)
    _ _ _ _ _ _ at rd2141
  rw [u256_land_comm ⟨255⟩] at rd2141
  have rd2148 := evm_run rd2141 with [dup1, push2 ⟨2153⟩, jumpiNT hi, pop, push0]
  obtain ⟨_, _, rd2149⟩ := rd2148.sload (by native_decide) (by evm_ov)
  have rd2153 := evm_run rd2149 with [push1 ⟨255⟩, and, iszero]
  change RD _ _ _ _ _ (UInt256.isZero (UInt256.land ⟨255⟩ (storedWord σ I ⟨0⟩)) :: R)
    _ _ _ _ _ _ at rd2153
  rw [u256_land_comm ⟨255⟩] at rd2153
  have rd2161 := evm_run rd2153 with [
    jumpdest, push2 ⟨2181⟩, jumpiNT (isZero_eq_zero_of_ne hz),
    push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov) ]
  have rd2165 := rd2161.pushConst ⟨4594637⟩ (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd5742 := evm_run rd2165 with [
    push1 ⟨229⟩, shl, dup2, raw mstoreSymbolic (by native_decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨994⟩, swap1, push2 ⟨5742⟩, jump (by jump_dest) ]
  exact initializerErrorRevert rd5742 hov

end Auction
