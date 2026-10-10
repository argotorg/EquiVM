import Benchmarks.UniswapV4PoolManager.BytesObjectMemory
import Benchmarks.UniswapV4PoolManager.MemorySlice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: loading an arbitrary in-bounds word from a known memory slice.
theorem MemorySlice.loadWord {mem data : ByteArray} {base off : Nat} {read : UInt256}
    (h : MemorySlice mem base data) (hw : off+32 ≤ data.size) (hr : read.toNat = base+off) :
    memLoad read mem = calldataWord data off := by
  apply loadedWord_of_read
  · rw [hr]; have := h.inBounds; omega
  · rw [hr, h.read_window _ _ hw, calldataWord_bytes_at hw]

theorem BytesObjectView.loadWord {mem data : ByteArray} {ptr read : UInt256} {off : Nat}
    (h : BytesObjectView mem ptr data) (hw : off+32 ≤ data.size)
    (hr : read.toNat = ptr.toNat+32+off) : memLoad read mem = calldataWord data off :=
  (show MemorySlice mem (ptr.toNat+32) data from ⟨h.payload, h.inBounds⟩).loadWord hw hr

end Benchmarks.UniswapV4PoolManager
