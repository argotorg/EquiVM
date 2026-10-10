import Benchmarks.UniswapV3.Pool.SwapIterationResultSource
import Benchmarks.UniswapV3.Pool.SwapMemoryModel
import Benchmarks.UniswapV3.Pool.WordArrayInPlace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def swapIterationResultMem (mem : ByteArray) (p q price amountIn amountOut fee : UInt256) :
    ByteArray :=
  writeWord
    (writeWord (writeWord (writeWord mem (q.toNat + 192) fee) (q.toNat + 160) amountOut)
      (q.toNat + 128) amountIn)
    (p.toNat + 64) price

theorem swapIterationResultMemory {mem : ByteArray} {aw p q free : UInt256}
    (s : SwapStateData) (d : SwapIterationData) (price amountIn amountOut fee : UInt256)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) :
    HeapMemory (swapIterationResultMem mem p q price amountIn amountOut fee) aw free ∧
      SwapStateMemory (swapIterationResultMem mem p q price amountIn amountOut fee) p
        {s with price := price} ∧
      SwapIterationMemory (swapIterationResultMem mem p q price amountIn amountOut fee) q
        (swapIterationResultData d amountIn amountOut fee) ∧
      MemoryPrefix mem (swapIterationResultMem mem p q price amountIn amountOut fee) p.toNat := by
  obtain ⟨hm1, hd1, hp1⟩ := wordArrayWriteWithin hm hd (by omega) 6
    (by change 6 < 7; decide) fee
  obtain ⟨hm2, hd2, hp2⟩ := wordArrayWriteWithin hm1 hd1 (by omega) 5
    (by change 5 < 7; decide) amountOut
  obtain ⟨hm3, hd3, hp3⟩ := wordArrayWriteWithin hm2 hd2 (by omega) 4
    (by change 4 < 7; decide) amountIn
  have hpq := (hp1.trans hp2).trans hp3
  have hs3 := MemoryPrefix.wordArray hpq hs hp hdisj
  obtain ⟨hm4, hs4, hp4⟩ := wordArrayWriteWithin hm3 hs3 hp 2
    (by change 2 < 7; decide) price
  refine ⟨hm4, hs4, ?_, (hpq.mono (by omega : p.toNat ≤ q.toNat)).trans hp4⟩
  exact WordArrayMemory.write_disjoint hd3 (p.toNat + 64) price (Or.inl (by omega))

end Benchmarks.UniswapV3.Pool
