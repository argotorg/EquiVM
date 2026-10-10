import Benchmarks.UniswapV4PoolManager.PoolFeeInsidePrelude
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory
import Benchmarks.UniswapV4PoolManager.TransientTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolFeeInsideMemory (mem : ByteArray) (id lower upper : UInt256) : ByteArray :=
  twoWordHashMem upper (poolSlot id+⟨4⟩) (twoWordHashMem lower (poolSlot id+⟨4⟩) mem)

theorem poolFeeInsideMemory_load {mem : ByteArray} (id lower upper read : UInt256)
    (hoff : 64 ≤ read.toNat) (hs : read.toNat+32 ≤ mem.size) :
    memLoad read (poolFeeInsideMemory mem id lower upper) = memLoad read mem := by
  have hi := twoWordHashMem_size_of_ge_64' lower (poolSlot id+⟨4⟩) (mem := mem) (by omega)
  have ho := twoWordHashMem_loadWord (mem := twoWordHashMem lower (poolSlot id+⟨4⟩) mem)
    upper (poolSlot id+⟨4⟩) read hoff (by rw [hi]; exact hs)
  rw [poolFeeInsideMemory, ho, twoWordHashMem_loadWord lower (poolSlot id+⟨4⟩) read hoff hs]

theorem poolFeeInsideMemory_size {mem : ByteArray} (id lower upper : UInt256) (hs : 64 ≤ mem.size) :
    (poolFeeInsideMemory mem id lower upper).size = mem.size := by
  have hi := twoWordHashMem_size_of_ge_64' lower (poolSlot id+⟨4⟩) (mem := mem) hs
  rw [poolFeeInsideMemory, twoWordHashMem_size_of_ge_64' upper (poolSlot id+⟨4⟩) (by rw [hi]; exact hs), hi]

theorem tickHashMem_slot (id tick : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) =
      tickSlot id (EVM.signed tick) := by
  change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) = _
  rw [mappingMemory_slot_any]
  simp only [tickSlot, wordOfInt_signed]

end Benchmarks.UniswapV4PoolManager
