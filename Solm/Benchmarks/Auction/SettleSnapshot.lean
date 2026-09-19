import Solm.Benchmarks.Auction.SnapshotMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem settleSnapshotPrefix {I g s0 ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨4086⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 192 ≤ 2 ^ 200)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4162⟩
      (ptr :: (snapshotOf σ I).startTime :: ret :: R)
      ((snapshotOf σ I).mem mem ptr) (snapshotWords aw ptr) rdata (cA, σ) k' C' := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 :=
    addWord_toNat ptr ⟨64⟩ (by change ptr.toNat + 64 < 2 ^ 256; omega)
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    addWord_toNat ptr ⟨96⟩ (by change ptr.toNat + 96 < 2 ^ 256; omega)
  have h128 : (ptr + ⟨128⟩).toNat = ptr.toNat + 128 :=
    addWord_toNat ptr ⟨128⟩ (by change ptr.toNat + 128 < 2 ^ 256; omega)
  have h160 : (ptr + ⟨160⟩).toNat = ptr.toNat + 160 :=
    addWord_toNat ptr ⟨160⟩ (by change ptr.toNat + 160 < 2 ^ 256; omega)
  have rd4091 := evm_run h with [jumpdest, push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd4091
  have rd4099 := evm_run rd4091 with [push1 ⟨192⟩, dup2, add, dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨207⟩]
  rw [expandedWords64_eq hm.active] at rd4099
  obtain ⟨_, _, rd4100⟩ := rd4099.sload (by native_decide) (by evm_ov)
  have rd4104 := evm_run rd4100 with [dup2, raw mstoreSymbolic (by native_decide) (by evm_ov),
    push1 ⟨208⟩]
  obtain ⟨_, _, rd4105⟩ := rd4104.sload (by native_decide) (by evm_ov)
  have rd4112 := evm_run rd4105 with [push1 ⟨32⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨209⟩]
  rw [h32, expandedWords32_chain hm.active (by omega) (by omega)] at rd4112
  obtain ⟨_, _, rd4113⟩ := rd4112.sload (by native_decide) (by evm_ov)
  have rd4121 := evm_run rd4113 with [swap2, dup2, add, dup3, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨210⟩]
  rw [h64, expandedWords32_chain hm.active (by omega) (by omega)] at rd4121
  obtain ⟨_, _, rd4122⟩ := rd4121.sload (by native_decide) (by evm_ov)
  have rd4129 := evm_run rd4122 with [push1 ⟨96⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨211⟩]
  rw [h96, expandedWords32_chain hm.active (by omega) (by omega)] at rd4129
  obtain ⟨_, _, rd4130⟩ := rd4129.sload (by native_decide) (by evm_ov)
  have rd4145 := evm_run rd4130 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨128⟩, dup4, add, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask, h128, expandedWords32_chain hm.active (by omega) (by omega)] at rd4145
  have rd4162 := evm_run rd4145 with [push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div,
    push1 ⟨255⟩, and, iszero, iszero, push1 ⟨160⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hpow : UInt256.shiftLeft ⟨1⟩ ⟨160⟩ = ⟨2 ^ 160⟩ := by native_decide
  simp only [hpow, u256_land_comm ⟨255⟩, h160,
    expandedWords32_chain hm.active (show (ptr + ⟨128⟩).toNat ≤ (ptr + ⟨160⟩).toNat by omega)
      (by omega)] at rd4162
  exact ⟨_, _, rd4162⟩

end Auction
