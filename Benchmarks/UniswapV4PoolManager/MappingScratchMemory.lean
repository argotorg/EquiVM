import Benchmarks.UniswapV4PoolManager.MappingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES the free-pointer preservation rule to every word above mapping scratch space.
theorem twoWordHashMem_loadWord {mem : ByteArray} (key base read : UInt256)
    (hoff : 64 ≤ read.toNat) (hmem : read.toNat+32 ≤ mem.size) :
    memLoad read (twoWordHashMem key base mem) = memLoad read mem := by
  have hs := twoWordHashMem_size_of_ge_64' key base (mem := mem) (by omega)
  rw [memLoad, memLoad, if_neg (by rw [hs]; omega : ¬read.toNat ≥ (twoWordHashMem key base mem).size),
    if_neg (by omega : ¬read.toNat ≥ mem.size)]
  change UInt256.ofNat (fromByteArrayBigEndian ((twoWordHashMem key base mem).readWithPadding read.toNat 32)) = _
  rw [twoWordHashMem_read_above64 key base read.toNat hoff hmem]

end Benchmarks.UniswapV4PoolManager
