import Benchmarks.UniswapV3.Pool.SwapAccountingModel
import Benchmarks.UniswapV3.Pool.WordArrayPairUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem swapAccountingRemaining_word (exactInput : Bool) (s : SwapStateData)
    (d : SwapIterationData) :
    EVM.wordOfInt (swapAccountingRemaining exactInput s d) =
      if exactInput then UInt256.sub (EVM.wordOfInt s.remaining) (swapAccountingFirst exactInput d)
      else EVM.wordOfInt s.remaining + swapAccountingFirst exactInput d := by
  rw [swapAccountingRemaining, safeSignedMathResult_word, wordOfInt_ofNat_toNat]
  cases exactInput
  · exact u256_add_comm _ _
  · rfl

theorem SwapStateMemory.load_calculated {mem : ByteArray} {p : UInt256} {s : SwapStateData}
    (hm : SwapStateMemory mem p s) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 32) mem = EVM.wordOfInt s.calculated :=
  WordArrayMemory.load hm 1 (by change 1 < 7; decide) hb

theorem swapAccountingRemainingMemory {mem : ByteArray} {aw p q free : UInt256}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) :
    let m := writeWord mem p.toNat (EVM.wordOfInt (swapAccountingRemaining exactInput s d))
    HeapMemory m aw free ∧
      SwapStateMemory m p {s with remaining := swapAccountingRemaining exactInput s d} ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m p.toNat :=
  wordArrayWriteBefore hm hs hd hp hdisj 0 (by change 0 < 7; decide) _

theorem swapAccountingCalculatedMemory {mem : ByteArray} {aw p q free : UInt256}
    (s : SwapStateData) (d : SwapIterationData) (value : Int)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) :
    let m := writeWord mem (p.toNat + 32) (EVM.wordOfInt value)
    HeapMemory m aw free ∧ SwapStateMemory m p {s with calculated := value} ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m p.toNat :=
  wordArrayWriteBefore hm hs hd hp hdisj 1 (by change 1 < 7; decide) _

end Benchmarks.UniswapV3.Pool
