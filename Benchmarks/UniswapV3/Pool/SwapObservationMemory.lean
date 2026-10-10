import Benchmarks.UniswapV3.Pool.SwapObservationSource
import Benchmarks.UniswapV3.Pool.WordArrayInPlace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def swapObservationStoreMem (mem : ByteArray) (cache : UInt256) (tick : Int)
    (seconds : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem (cache.toNat + 128) seconds)
    (cache.toNat + 96) (EVM.wordOfInt tick)) (cache.toNat + 160) ⟨1⟩

theorem swapObservationStoreMemory {mem : ByteArray} {aw cache p q free : UInt256}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData) (tick : Int) (seconds : UInt256)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (hcl : 96 ≤ cache.toNat) (hcachep : cache.toNat + 192 ≤ p.toNat)
    (hpq : p.toNat + 224 ≤ q.toNat) :
    let m := swapObservationStoreMem mem cache tick seconds
    HeapMemory m aw free ∧ SwapCacheMemory m cache (swapObservationCache c tick seconds) ∧
      SwapStateMemory m p s ∧ SwapIterationMemory m q d ∧ MemoryPrefix mem m cache.toNat := by
  dsimp only
  obtain ⟨hm1, hc1, hp1⟩ := wordArrayWriteWithin hm hc hcl 4 (by change 4 < 6; decide) seconds
  obtain ⟨hm2, hc2, hp2⟩ := wordArrayWriteWithin hm1 hc1 hcl 3
    (by change 3 < 6; decide) (EVM.wordOfInt tick)
  obtain ⟨hm3, hc3, hp3⟩ := wordArrayWriteWithin hm2 hc2 hcl 5 (by change 5 < 6; decide) ⟨1⟩
  have hs1 := WordArrayMemory.write_disjoint hs (cache.toNat + 128) seconds (Or.inl (by omega))
  have hs2 := WordArrayMemory.write_disjoint hs1 (cache.toNat + 96) (EVM.wordOfInt tick)
    (Or.inl (by omega))
  have hs3 := WordArrayMemory.write_disjoint hs2 (cache.toNat + 160) ⟨1⟩ (Or.inl (by omega))
  have hd1 := WordArrayMemory.write_disjoint hd (cache.toNat + 128) seconds (Or.inl (by omega))
  have hd2 := WordArrayMemory.write_disjoint hd1 (cache.toNat + 96) (EVM.wordOfInt tick)
    (Or.inl (by omega))
  have hd3 := WordArrayMemory.write_disjoint hd2 (cache.toNat + 160) ⟨1⟩ (Or.inl (by omega))
  exact ⟨hm3, hc3, hs3, hd3, hp1.trans (hp2.trans hp3)⟩

end Benchmarks.UniswapV3.Pool
