import Benchmarks.UniswapV3.Pool.SwapIterationSource
import Benchmarks.UniswapV3.Pool.WordArrayUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem SwapIterationMemory.load_tick {mem : ByteArray} {p : UInt256} {d : SwapIterationData}
    (hm : SwapIterationMemory mem p d) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 32) mem = EVM.wordOfInt d.tickNext := by
  have h := WordArrayMemory.load hm 1 (by change 1 < 7; decide) hb
  exact h

theorem SwapIterationMemory.write_tick {mem : ByteArray} {p : UInt256} {d : SwapIterationData}
    (hm : SwapIterationMemory mem p d) (tick : Int) (hb : p.toNat + 224 < UInt256.size) :
    SwapIterationMemory (writeWord mem (p + UInt256.ofNat 32).toNat (EVM.wordOfInt tick)) p
      {d with tickNext := tick} := by
  rw [uadd_word_ofNat_toNat p 32 (by omega)]
  exact WordArrayMemory.write hm 1 (EVM.wordOfInt tick)

theorem SwapIterationMemory.write_initialized
    {mem : ByteArray} {p : UInt256} {d : SwapIterationData}
    (hm : SwapIterationMemory mem p d) (hit : Bool) (hb : p.toNat + 224 < UInt256.size) :
    SwapIterationMemory (writeWord mem (p + UInt256.ofNat 64).toNat hit.toUInt256) p
      {d with initialized := hit} := by
  rw [uadd_word_ofNat_toNat p 64 (by omega)]
  exact WordArrayMemory.write hm 2 hit.toUInt256

def swapIterationBitmapMem (mem : ByteArray) (p : UInt256) (tick : Int) (hit : Bool) : ByteArray :=
  writeWord (writeWord mem (p + UInt256.ofNat 64).toNat hit.toUInt256)
    (p + UInt256.ofNat 32).toNat (EVM.wordOfInt tick)

theorem swapIterationBitmapMemory {mem : ByteArray} {aw p free : UInt256}
    (d : SwapIterationData) (tick : Int) (hit : Bool)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem p d)
    (hp : 96 ≤ p.toNat) (hb : p.toNat + 224 < UInt256.size) :
    HeapMemory (swapIterationBitmapMem mem p tick hit) aw free ∧
      SwapIterationMemory (swapIterationBitmapMem mem p tick hit) p
        {d with tickNext := tick, initialized := hit} ∧
      MemoryPrefix mem (swapIterationBitmapMem mem p tick hit) p.toNat := by
  have hp32 := uadd_word_ofNat_toNat p 32 (show p.toNat + 32 < UInt256.size by omega)
  have hp64 := uadd_word_ofNat_toNat p 64 (show p.toNat + 64 < UInt256.size by omega)
  have hs : p.toNat + 224 ≤ mem.size := hd.1
  have hm1 := HeapMemory.writeWithin hm (p + UInt256.ofNat 64).toNat hit.toUInt256
    (by rw [hp64]; omega) (by rw [hp64]; omega)
  have hm2 := HeapMemory.writeWithin hm1 (p + UInt256.ofNat 32).toNat (EVM.wordOfInt tick)
    (by rw [hp32]; omega)
    (by rw [writeWord_sparse_size, hp32]; omega)
  refine ⟨hm2, SwapIterationMemory.write_tick (SwapIterationMemory.write_initialized hd hit hb)
    tick hb, ?_⟩
  exact (memoryPrefix_sparse_writeWord mem (p + UInt256.ofNat 64).toNat p.toNat hit.toUInt256
    (Or.inl (by rw [hp64]; omega))).trans
    (memoryPrefix_sparse_writeWord _ (p + UInt256.ofNat 32).toNat p.toNat (EVM.wordOfInt tick)
      (Or.inl (by rw [hp32]; omega)))

end Benchmarks.UniswapV3.Pool
