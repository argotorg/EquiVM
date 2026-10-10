import Benchmarks.UniswapV3.Pool.SwapIterationMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationTickWriteMemory {mem : ByteArray} {aw p free : UInt256}
    (d : SwapIterationData) (tick : Int)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem p d)
    (hp : 96 ≤ p.toNat) (hb : p.toNat + 224 < UInt256.size) :
    HeapMemory (writeWord mem (p + UInt256.ofNat 32).toNat (EVM.wordOfInt tick)) aw free ∧
      SwapIterationMemory (writeWord mem (p + UInt256.ofNat 32).toNat (EVM.wordOfInt tick)) p
        {d with tickNext := tick} ∧
      MemoryPrefix mem (writeWord mem (p + UInt256.ofNat 32).toNat (EVM.wordOfInt tick))
        p.toNat := by
  have hp32 := uadd_word_ofNat_toNat p 32 (show p.toNat + 32 < UInt256.size by omega)
  have hs : p.toNat + 224 ≤ mem.size := hd.1
  exact ⟨HeapMemory.writeWithin hm _ _ (by rw [hp32]; omega) (by rw [hp32]; omega),
    SwapIterationMemory.write_tick hd tick hb,
    memoryPrefix_sparse_writeWord mem _ p.toNat _ (Or.inl (by rw [hp32]; omega))⟩

end Benchmarks.UniswapV3.Pool
