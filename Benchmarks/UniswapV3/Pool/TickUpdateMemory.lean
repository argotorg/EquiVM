import Benchmarks.UniswapV3.Pool.TickUpdateLiquidityTrace
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: mapping scratch writes preserve the allocator invariant.
theorem HeapMemory.twoWordHash {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (key slot : UInt256) :
    HeapMemory (twoWordHashMem key slot mem) aw p := by
  have hs := twoWordHashMem_size_of_ge_64' (mem := mem) key slot (by have h := hm.size; omega)
  refine ⟨?_, ?_, hm.lower, ?_, hm.active⟩
  · rw [hs]; exact hm.size
  · rw [twoWordHashMem_read_above64 key slot 64 (by decide) hm.size]
    exact hm.free
  · rw [hs]; exact hm.gap

theorem tickUpdateMemoryWords_eq {aw : UInt256} (ha : ActiveWords aw) :
    tickUpdateMemoryWords aw = aw := by
  have h0 : M aw ⟨0⟩ ⟨32⟩ = aw :=
    UInt256_M_same_of_cover_len aw ⟨0⟩ 32 (by have h := ha.1; change 0 + 32 ≤ _; omega)
  have h1 : M aw ⟨32⟩ ⟨32⟩ = aw :=
    UInt256_M_same_of_cover_len aw ⟨32⟩ 32 (by have h := ha.1; change 32 + 32 ≤ _; omega)
  have h2 : M aw ⟨0⟩ ⟨64⟩ = aw :=
    UInt256_M_same_of_cover_len aw ⟨0⟩ 64 (by have h := ha.1; change 0 + 64 ≤ _; omega)
  rw [tickUpdateMemoryWords, h0, h1, h2]

end Benchmarks.UniswapV3.Pool
