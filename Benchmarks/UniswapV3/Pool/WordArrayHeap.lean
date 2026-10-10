import Benchmarks.UniswapV3.Pool.WordArrayExtend

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a nonempty word array at the free pointer supplies the heap gap.
theorem wordArrayHeap {mem : ByteArray} {aw aw' p : UInt256}
    (hm : MemoryCursor mem aw p) (ws : List UInt256) (hn : ws ≠ [])
    (ha : ActiveWords aw') : HeapMemory (writeWordArray mem p.toNat ws) aw' p := by
  have hc := MemoryCursor.writeWordArray hm p.toNat ws (by have := hm.lower; omega)
  refine ⟨hc.size, hc.free, hc.lower, ?_, ha⟩
  rw [writeWordArray_size mem p.toNat ws hn]
  omega

end Benchmarks.UniswapV3.Pool
