import Benchmarks.UniswapV3.Pool.SwapProtocolSource
import Benchmarks.UniswapV3.Pool.WordArrayPairUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def swapProtocolUpdateMem (mem : ByteArray) (p q : UInt256) (c : SwapCacheData)
    (s : SwapStateData) (d : SwapIterationData) : ByteArray :=
  writeWord (writeWord mem (q.toNat + 192) (swapProtocolUpdatedData c d).feeAmount)
    (p.toNat + 160) (swapProtocolUpdatedState c s d).protocolFee

theorem swapProtocolUpdateMemory {mem : ByteArray} {aw p q free : UInt256}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) :
    HeapMemory (swapProtocolUpdateMem mem p q c s d) aw free ∧
      SwapStateMemory (swapProtocolUpdateMem mem p q c s d) p (swapProtocolUpdatedState c s d) ∧
      SwapIterationMemory (swapProtocolUpdateMem mem p q c s d) q (swapProtocolUpdatedData c d) ∧
      MemoryPrefix mem (swapProtocolUpdateMem mem p q c s d) p.toNat := by
  obtain ⟨hm1, hd1, hpre1⟩ := wordArrayWriteWithin hm hd (by omega) 6
    (by change 6 < 7; decide) (swapProtocolUpdatedData c d).feeAmount
  have hs1 := MemoryPrefix.wordArray hpre1 hs hp hdisj
  obtain ⟨hm2, hs2, hd2, hpre2⟩ := wordArrayWriteBefore hm1 hs1 hd1 hp hdisj 5
    (by change 5 < 7; decide) (swapProtocolUpdatedState c s d).protocolFee
  exact ⟨hm2, hs2, hd2, (hpre1.mono (by omega : p.toNat ≤ q.toNat)).trans hpre2⟩

theorem SwapCacheMemory.load_feeProtocol {mem : ByteArray} {p : UInt256} {c : SwapCacheData}
    (hm : SwapCacheMemory mem p c) (hb : p.toNat + 192 < UInt256.size) :
    memLoad p mem = c.feeProtocol := by
  have hh := WordArrayMemory.load hm 0 (by change 0 < 6; decide) hb
  have h0 : p + UInt256.ofNat 0 = p := u256_add_zero p
  simpa only [SwapCacheData.words, List.getElem_cons_zero, Nat.mul_zero, h0] using hh

theorem SwapStateMemory.load_protocolFee {mem : ByteArray} {p : UInt256} {s : SwapStateData}
    (hm : SwapStateMemory mem p s) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 160) mem = s.protocolFee :=
  WordArrayMemory.load hm 5 (by change 5 < 7; decide) hb

end Benchmarks.UniswapV3.Pool
