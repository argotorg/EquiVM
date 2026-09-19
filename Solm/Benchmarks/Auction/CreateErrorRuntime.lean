import Solm.Benchmarks.Auction.ErrorDecodeRoutine
import Solm.Benchmarks.Auction.ErrorSelector

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option synthInstance.maxSize 1024 in
theorem createErrorDecodeRuntime {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨3116⟩ (ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (hin : ptr.toNat ≤ mem.size)
    (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200)
    (he : returnSelector out = ⟨0x08c379a0⟩) (hov : R.length + 19 ≤ 1024) :
    (ErrorDataValid out ∧ ErrorAllocAllowed ptr (errorAllocSize out) ∧
      ∃ value mem' aw' k' C', RD auctionBytecode I g s0 ⟨3655⟩
        (⟨2850⟩ :: value :: ret :: R) mem' aw' out acc k' C') ∨
    ((¬ ErrorDataValid out ∨ ¬ ErrorAllocAllowed ptr (errorAllocSize out)) ∧
      RDrev auctionBytecode g s0) := by
  have ho : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  obtain ⟨_, _, rd3123⟩ := createErrorSelectorPrefix h hm ho (by omega)
  have rd5925 := evm_run rd3123 with [jumpdest, dup1, push4 ⟨0x08c379a0⟩, sub, push2 ⟨3162⟩,
    jumpiNT (by rw [he]; decide), pop, push2 ⟨3143⟩, push2 ⟨5925⟩, jump (by jump_dest)]
  have hs := errorSelectorPrefix hm out
  rcases errorDecodeRoutine rd5925 (errorSelectorHeap hm out)
      (by have hsz := hs.size; omega) hb (by jump_dest) (by evm_ov) with
    ⟨hv, ha, ⟨_, _, rd3143⟩, _, hne⟩ | ⟨hv, mem', aw', _, _, rd3143⟩ | ⟨_, ha, hr⟩
  · exact Or.inl ⟨hv, ha, _, _, _, _, _, evm_run rd3143 with [jumpdest, dup1, push2 ⟨3154⟩,
      jumpiT hne (by jump_dest), jumpdest, push2 ⟨2850⟩, push2 ⟨3655⟩, jump (by jump_dest)]⟩
  · have rd3165 := evm_run rd3143 with [jumpdest, dup1, push2 ⟨3154⟩,
      jumpiNT (by decide), pop, push2 ⟨3164⟩, jump (by jump_dest), jumpdest]
    exact Or.inr ⟨Or.inl hv,
      rd3165.revertData (by unfold revertDataWf; native_decide) (by evm_ov)⟩
  · exact Or.inr ⟨Or.inr ha, hr⟩

end Auction
