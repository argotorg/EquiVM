import Benchmarks.UniswapV3.Pool.WordArrayInPlace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: updating one allocated region preserves a later disjoint region.
theorem wordArrayWriteBefore {mem : ByteArray} {aw p q free : UInt256}
    {ws vs : List UInt256} (hm : HeapMemory mem aw free) (hp : WordArrayMemory mem p ws)
    (hq : WordArrayMemory mem q vs) (hl : 96 ≤ p.toNat)
    (hdisj : p.toNat + 32 * ws.length ≤ q.toNat) (i : Nat) (hi : i < ws.length)
    (value : UInt256) :
    HeapMemory (writeWord mem (p.toNat + 32 * i) value) aw free ∧
      WordArrayMemory (writeWord mem (p.toNat + 32 * i) value) p (ws.set i value) ∧
      WordArrayMemory (writeWord mem (p.toNat + 32 * i) value) q vs ∧
      MemoryPrefix mem (writeWord mem (p.toNat + 32 * i) value) p.toNat := by
  obtain ⟨hm', hp', hpre⟩ := wordArrayWriteWithin hm hp hl i hi value
  exact ⟨hm', hp', WordArrayMemory.write_disjoint hq _ value (Or.inl (by omega)), hpre⟩

end Benchmarks.UniswapV3.Pool
