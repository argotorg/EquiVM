import Benchmarks.UniswapV4PoolManager.MappingScratchMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: memory after an optional two-word mapping hash.
def conditionalHashMemory (mem : ByteArray) (key base : UInt256) (active : Bool) : ByteArray :=
  if active then twoWordHashMem key base mem else mem

theorem conditionalHashMemory_size (mem : ByteArray) (key base : UInt256) (active : Bool)
    (hm : 64 ≤ mem.size) : (conditionalHashMemory mem key base active).size = mem.size := by
  cases active with
  | false => rfl
  | true => exact twoWordHashMem_size_of_ge_64' _ _ hm

theorem conditionalHashMemory_loadWord (mem : ByteArray) (key base read : UInt256) (active : Bool)
    (hoff : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size) :
    memLoad read (conditionalHashMemory mem key base active) = memLoad read mem := by
  cases active with
  | false => rfl
  | true => exact twoWordHashMem_loadWord _ _ _ hoff hin

end Benchmarks.UniswapV4PoolManager
