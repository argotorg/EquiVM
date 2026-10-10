import Benchmarks.UniswapV3.Pool.WordArrayUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: updating an allocated array preserves the heap and earlier allocations.
theorem wordArrayWriteWithin {mem : ByteArray} {aw p free : UInt256} {ws : List UInt256}
    (hm : HeapMemory mem aw free) (hd : WordArrayMemory mem p ws)
    (hp : 96 ≤ p.toNat) (i : Nat) (hi : i < ws.length) (value : UInt256) :
    HeapMemory (writeWord mem (p.toNat + 32 * i) value) aw free ∧
      WordArrayMemory (writeWord mem (p.toNat + 32 * i) value) p (ws.set i value) ∧
      MemoryPrefix mem (writeWord mem (p.toNat + 32 * i) value) p.toNat := by
  refine ⟨HeapMemory.writeWithin hm _ value (by omega) ?_, WordArrayMemory.write hd i value,
    memoryPrefix_sparse_writeWord mem _ p.toNat value (Or.inl (by omega))⟩
  have hsize := hd.size
  omega

end Benchmarks.UniswapV3.Pool
