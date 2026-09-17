import Benchmarks.Auction.SnapshotMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def createdSnapshot (noun start finish : UInt256) : Snapshot :=
  ⟨noun, ⟨0⟩, start, finish, ⟨0⟩⟩

set_option maxRecDepth 2048 in
theorem createSnapshotPrefix {I g s0 noun start finish ret R mem aw ptr rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨3189⟩ (finish :: ⟨0⟩ :: start :: noun :: ret :: R)
      mem aw rdata acc k C)
    (hm : MemoryCursor mem aw ptr) (hb : ptr.toNat + 192 ≤ 2 ^ 200)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3240⟩
      (⟨0⟩ :: ⟨32⟩ :: ⟨64⟩ :: finish :: ⟨0⟩ :: start :: noun :: ret :: R)
      ((createdSnapshot noun start finish).mem mem ptr) (snapshotWords aw ptr)
      rdata acc k' C' := by
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
  have rd3194 := evm_run h with [jumpdest, push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd3194
  have rd3203 := evm_run rd3194 with [push1 ⟨192⟩, dup2, add, dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov), dup6, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [expandedWords64_eq hm.active] at rd3203
  have rd3212 := evm_run rd3203 with [push0, push1 ⟨32⟩, dup1, dup4, add, dup3, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [h32, expandedWords32_chain hm.active (by omega) (by omega)] at rd3212
  have rd3218 := evm_run rd3212 with [dup3, dup5, add, dup8, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [u256_add_comm ⟨64⟩ ptr, h64,
    expandedWords32_chain hm.active (by omega) (by omega)] at rd3218
  have rd3225 := evm_run rd3218 with [push1 ⟨96⟩, dup4, add, dup6, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [h96, expandedWords32_chain hm.active (by omega) (by omega)] at rd3225
  have rd3232 := evm_run rd3225 with [push1 ⟨128⟩, dup4, add, dup3, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [h128, expandedWords32_chain hm.active (by omega) (by omega)] at rd3232
  have rd3240 := evm_run rd3232 with [push1 ⟨160⟩, swap1, swap3, add, dup2, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [h160, expandedWords32_chain hm.active (by omega) (by omega)] at rd3240
  exact ⟨_, _, rd3240⟩

end Auction
