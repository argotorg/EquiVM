import Benchmarks.UniswapV4PoolManager.MemoryWindowEq
import Benchmarks.UniswapV4PoolManager.MemorySlice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: transport an allocated byte slice through a preserved window.
theorem MemoryWindowEq.slice {before after data : ByteArray} {low high base : Nat}
    (h : MemoryWindowEq before after low high) (hs : MemorySlice before base data)
    (hl : low ≤ base) (hh : base+data.size ≤ high) : MemorySlice after base data :=
  ⟨(h.read base data.size hl hh).trans hs.bytes, by rw [h.size]; exact hs.inBounds⟩

end Benchmarks.UniswapV4PoolManager
