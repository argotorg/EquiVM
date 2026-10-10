import Benchmarks.UniswapV3.Pool.Common
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: hashing scratch words preserves the allocated memory region.
theorem wordAt0Mem_prefix (mem : ByteArray) (key : UInt256) (limit : Nat) :
    MemoryPrefix mem (wordAt0Mem key mem) limit :=
  memoryPrefix_sparse_writeWord mem 0 limit key (Or.inr (by decide))

-- LIBRARY CANDIDATE: the two-word mapping preimage preserves the allocated memory region.
theorem twoWordHashMem_prefix (mem : ByteArray) (key slot : UInt256) (limit : Nat) :
    MemoryPrefix mem (twoWordHashMem key slot mem) limit :=
  (wordAt0Mem_prefix mem key limit).trans
    (memoryPrefix_sparse_writeWord _ 32 limit slot (Or.inr (by decide)))

end Benchmarks.UniswapV3.Pool
