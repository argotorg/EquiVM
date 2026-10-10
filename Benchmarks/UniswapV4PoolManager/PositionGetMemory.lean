import Benchmarks.UniswapV4PoolManager.PositionKeyCompiled
import Benchmarks.UniswapV4PoolManager.PositionStorage
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory
import Benchmarks.UniswapV4PoolManager.TransientTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def positionGetMemory (mem : ByteArray) (free : UInt256) (id : UInt256) (owner : AccountAddress)
    (lower upper salt : UInt256) : ByteArray :=
  twoWordHashMem (positionKey owner lower upper salt) (poolSlot id+⟨6⟩)
    (positionKeyCleanMemory mem free.toNat owner lower upper salt)

theorem positionKeyScratch_load_pool {mem : ByteArray} {free id lower upper salt : UInt256}
    (owner : AccountAddress) (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hs : 160 ≤ mem.size) (hf : 160 ≤ free.toNat) :
    memLoad (UInt256.ofNat 128) ((positionKey owner lower upper salt).toByteArray.write 0
      (positionKeyCleanMemory mem free.toNat owner lower upper salt) (⟨0⟩ : UInt256).toNat 32) = poolSlot id := by
  change memLoad (UInt256.ofNat 128)
    (writeWord (positionKeyCleanMemory mem free.toNat owner lower upper salt) 0
      (positionKey owner lower upper salt)) = _
  rw [writeWord_sparse_load_disjoint _ _ _ _
      (by rw [positionKeyCleanMemory_size]; change 160 ≤ _; omega) (.inr (by decide)),
    positionKeyCleanMemory_load_before owner lower upper salt (UInt256.ofNat 128) hs hf, hm]

theorem positionGetMemory_size (mem : ByteArray) (free id : UInt256) (owner : AccountAddress)
    (lower upper salt : UInt256) :
    (positionGetMemory mem free id owner lower upper salt).size = max mem.size (free.toNat+96) := by
  rw [positionGetMemory, twoWordHashMem_size_of_ge_64' _ _
    (by rw [positionKeyCleanMemory_size]; omega), positionKeyCleanMemory_size]

theorem positionGetMemory_load_before {mem : ByteArray} {free id lower upper salt : UInt256}
    (owner : AccountAddress) (read : UInt256) (hin : read.toNat+32 ≤ mem.size)
    (hlo : 64 ≤ read.toNat) (hi : read.toNat+32 ≤ free.toNat) :
    memLoad read (positionGetMemory mem free id owner lower upper salt) = memLoad read mem := by
  have hp := twoWordHashMem_loadWord (mem := positionKeyCleanMemory mem free.toNat owner lower upper salt)
    (positionKey owner lower upper salt) (poolSlot id+⟨6⟩) read hlo
    (by rw [positionKeyCleanMemory_size]; omega)
  rw [positionGetMemory, hp, positionKeyCleanMemory_load_before owner lower upper salt read hin hi]

end Benchmarks.UniswapV4PoolManager
