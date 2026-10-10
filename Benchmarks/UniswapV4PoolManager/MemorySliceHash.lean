import Benchmarks.UniswapV4PoolManager.MemorySlice
import Benchmarks.UniswapV4PoolManager.ConditionalMappingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: mapping scratch words preserve every disjoint byte slice.
theorem MemorySlice.twoWordHash {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (a b : UInt256) (hb : 64 ≤ base) :
    MemorySlice (twoWordHashMem a b mem) base data :=
  (h.writeWord 0 a (.inr (by omega))).writeWord 32 b (.inr (by omega))

theorem MemorySlice.conditionalHash {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (a b : UInt256) (active : Bool) (hb : 64 ≤ base) :
    MemorySlice (conditionalHashMemory mem a b active) base data := by
  cases active with
  | false => exact h
  | true => exact h.twoWordHash a b hb

end Benchmarks.UniswapV4PoolManager
