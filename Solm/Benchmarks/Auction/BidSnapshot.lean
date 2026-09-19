import Solm.Benchmarks.Auction.SnapshotMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem bidSnapshotPrefix {I g s0 noun ret R mem aw ptr rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨1205⟩ (noun :: ret :: R) mem aw rdata (cA, σ) k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 192 ≤ 2 ^ 200)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨1282⟩
      (ptr :: (snapshotOf σ I).nounId :: noun :: ret :: R)
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
  have rd1209 := evm_run h with [push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd1209
  have rd1217 := evm_run rd1209 with [push1 ⟨192⟩, dup2, add, dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨207⟩]
  rw [expandedWords64_eq hm.active] at rd1217
  obtain ⟨_, _, rd1218⟩ := rd1217.sload (by native_decide) (by evm_ov)
  have rd1223 := evm_run rd1218 with [dup1, dup3, raw mstoreSymbolic (by native_decide) (by evm_ov),
    push1 ⟨208⟩]
  obtain ⟨_, _, rd1224⟩ := rd1223.sload (by native_decide) (by evm_ov)
  have rd1231 := evm_run rd1224 with [push1 ⟨32⟩, dup4, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨209⟩]
  rw [h32, expandedWords32_chain hm.active (by omega) (by omega)] at rd1231
  obtain ⟨_, _, rd1232⟩ := rd1231.sload (by native_decide) (by evm_ov)
  have rd1241 := evm_run rd1232 with [swap3, dup3, add, swap3, swap1, swap3,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨210⟩]
  rw [h64, expandedWords32_chain hm.active (by omega) (by omega)] at rd1241
  obtain ⟨_, _, rd1242⟩ := rd1241.sload (by native_decide) (by evm_ov)
  have rd1249 := evm_run rd1242 with [push1 ⟨96⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨211⟩]
  rw [h96, expandedWords32_chain hm.active (by omega) (by omega)] at rd1249
  obtain ⟨_, _, rd1250⟩ := rd1249.sload (by native_decide) (by evm_ov)
  have rd1265 := evm_run rd1250 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨128⟩, dup4, add, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask, h128, expandedWords32_chain hm.active (by omega) (by omega)] at rd1265
  have rd1282 := evm_run rd1265 with [push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div,
    push1 ⟨255⟩, and, iszero, iszero, push1 ⟨160⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hpow : UInt256.shiftLeft ⟨1⟩ ⟨160⟩ = ⟨2 ^ 160⟩ := by native_decide
  simp only [hpow, u256_land_comm ⟨255⟩, h160,
    expandedWords32_chain hm.active (show (ptr + ⟨128⟩).toNat ≤ (ptr + ⟨160⟩).toNat by omega)
      (by omega)] at rd1282
  exact ⟨_, _, rd1282⟩

end Auction
