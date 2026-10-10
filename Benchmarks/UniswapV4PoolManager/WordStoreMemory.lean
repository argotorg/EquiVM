import Benchmarks.UniswapV4PoolManager.SparseBytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a word load is preserved by every disjoint word store.
theorem writeWord_sparse_load_disjoint (mem : ByteArray) (off : Nat) (word read : UInt256)
    (hin : read.toNat+32 ≤ mem.size) (hd : read.toNat+32 ≤ off ∨ off+32 ≤ read.toNat) :
    memLoad read (writeWord mem off word) = memLoad read mem := by
  rw [memLoad, memLoad, if_neg (by rw [writeWord_sparse_size]; omega), if_neg (by omega),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin hd]

end Benchmarks.UniswapV4PoolManager
