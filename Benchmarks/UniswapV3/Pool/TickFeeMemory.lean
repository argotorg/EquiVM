import Benchmarks.UniswapV3.Pool.TickFeePrefixTrace
import Benchmarks.UniswapV3.Pool.TickUpdateMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a write to the first scratch word preserves the heap invariant.
theorem HeapMemory.wordAt0 {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (word : UInt256) : HeapMemory (wordAt0Mem word mem) aw p := by
  have hs := wordAt0Mem_size_of_ge_32 (mem := mem) word (by have h := hm.size; omega)
  refine ⟨?_, ?_, hm.lower, ?_, hm.active⟩
  · rw [hs]; exact hm.size
  · unfold wordAt0Mem
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by have h := hm.size; omega) (by decide) hm.size]
    exact hm.free
  · rw [hs]; exact hm.gap

theorem tickFeeMemory_heap {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (a : TickFeeArgs) : HeapMemory (tickFeeMemory mem a) aw p :=
  HeapMemory.wordAt0 (HeapMemory.twoWordHash hm (EVM.wordOfInt a.lower) ⟨5⟩) (EVM.wordOfInt a.upper)

theorem tickFeeMemoryWords_eq {aw : UInt256} (ha : ActiveWords aw) : tickFeeMemoryWords aw = aw := by
  change M (M (tickUpdateMemoryWords aw) ⟨0⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩ = aw
  rw [tickUpdateMemoryWords_eq ha]
  have h0 : M aw ⟨0⟩ ⟨32⟩ = aw :=
    UInt256_M_same_of_cover_len aw ⟨0⟩ 32 (by have h := ha.1; change 0 + 32 ≤ _; omega)
  rw [h0]
  exact UInt256_M_same_of_cover_len aw ⟨0⟩ 64 (by have h := ha.1; change 0 + 64 ≤ _; omega)

end Benchmarks.UniswapV3.Pool
