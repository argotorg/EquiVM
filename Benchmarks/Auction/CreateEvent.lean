import Benchmarks.Auction.PairEventMemory
import Benchmarks.Auction.Log2
import Benchmarks.Auction.DepositPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem createEvent {I g s0 noun start finish ptr ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨3274⟩
      (⟨32⟩ :: ⟨64⟩ :: finish :: ⟨0⟩ :: start :: noun :: ret :: R)
      mem aw rdata acc k C)
    (hm : MemoryCursor mem aw ptr) (hb : ptr.toNat + 64 ≤ 2 ^ 200)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (pairEventMem mem ptr start finish)
      (pairEventWords aw ptr) rdata acc k' C' := by
  have rd3276 := evm_run h with [dup2, raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd3276
  have rd3279 := evm_run rd3276 with [dup6, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd3285 := evm_run rd3279 with [swap1, dup2, add, dup4, swap1,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  rw [hp] at rd3285
  have rd3290 := evm_run rd3285 with [swap2, swap3, pop, dup5, swap2]
  have rd3323 := rd3290.pushConst
    ⟨0xd6eddd1118d71820909c1197aa966dbc15ed6f508554252169cc3d5ccac756ca⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd3328 := evm_run rd3323 with [swap2, add, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have h1 := hm.writeAbove ptr start (le_refl _) (by omega)
  have h2 := h1.cursor.writeAbove (ptr + ⟨32⟩) finish (by omega) (by omega)
  rw [hp] at h2
  have hf := h2.load64
  simp only [Reasoning.Theory.writeWord] at hf
  rw [hf, expandedWords64_eq h2.active] at rd3328
  have rd3332 := evm_run rd3328 with [dup1, swap2, sub, swap1]
  rw [u256_add_comm ⟨64⟩ ptr, word_add_sub_left] at rd3332
  obtain ⟨_, _, rd3333⟩ := rd3332.log2Symbolic (by native_decide) hperm (by evm_ov)
  exact ⟨_, _, evm_run rd3333 with [pop, pop, pop, jump hret]⟩

end Auction
