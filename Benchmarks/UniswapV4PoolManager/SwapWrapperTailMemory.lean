import Benchmarks.UniswapV4PoolManager.SwapWrapperEventMemory
import Benchmarks.UniswapV4PoolManager.ProtocolFeesUpdateTrace
import Benchmarks.UniswapV4PoolManager.MemorySliceHash

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapWrapperFeeMemory (mem : ByteArray) (currency : AccountAddress) (amount : UInt256) : ByteArray :=
  if 0 < amount.toNat then protocolFeesUpdateMemory mem currency else mem

def swapWrapperTailMemory (mem : ByteArray) (free delta fee amount : UInt256) (currency : AccountAddress)
    (r : PoolSwapResultWords) : ByteArray :=
  swapWrapperEventMemory (swapWrapperFeeMemory mem currency amount) free delta fee r

theorem swapWrapperFeeMemory_size (mem : ByteArray) (currency : AccountAddress) (amount : UInt256)
    (hi : 64 ≤ mem.size) : (swapWrapperFeeMemory mem currency amount).size = mem.size := by
  unfold swapWrapperFeeMemory
  split
  · exact twoWordHashMem_size_of_ge_64' _ _ hi
  · rfl

theorem swapWrapperFeeMemory_free (mem : ByteArray) (currency : AccountAddress) (amount : UInt256)
    (hi : 96 ≤ mem.size) : memLoad (UInt256.ofNat 64) (swapWrapperFeeMemory mem currency amount) =
      memLoad (UInt256.ofNat 64) mem := by
  unfold swapWrapperFeeMemory
  split
  · exact twoWordHashMem_loadWord _ _ _ (by decide) hi
  · rfl

theorem swapWrapperFeeMemory_result {mem : ByteArray} {state : UInt256} {r : PoolSwapResultWords}
    (h : WordStructView mem state (poolSwapResultWordList r)) (currency : AccountAddress) (amount : UInt256)
    (hl : 64 ≤ state.toNat) :
    WordStructView (swapWrapperFeeMemory mem currency amount) state (poolSwapResultWordList r) := by
  unfold swapWrapperFeeMemory
  split
  · exact h.hash_scratch _ _ hl
  · exact h

theorem swapWrapperTailMemory_size (mem : ByteArray) (free delta fee amount : UInt256)
    (currency : AccountAddress) (r : PoolSwapResultWords) (hi : 64 ≤ mem.size) :
    (swapWrapperTailMemory mem free delta fee amount currency r).size = max mem.size (free.toNat+192) := by
  rw [swapWrapperTailMemory, swapWrapperEventMemory_size, swapWrapperFeeMemory_size _ _ _ hi]

theorem swapWrapperTailMemory_free (mem : ByteArray) (free delta fee amount : UInt256)
    (currency : AccountAddress) (r : PoolSwapResultWords) (hi : 96 ≤ mem.size) (hl : 96 ≤ free.toNat) :
    memLoad (UInt256.ofNat 64) (swapWrapperTailMemory mem free delta fee amount currency r) =
      memLoad (UInt256.ofNat 64) mem := by
  rw [swapWrapperTailMemory, swapWrapperEventMemory_free _ _ _ _ _
    (by rw [swapWrapperFeeMemory_size _ _ _ (by omega)]; exact hi) hl,
    swapWrapperFeeMemory_free _ _ _ hi]

theorem MemorySlice.swapWrapperTail {mem data : ByteArray} {base : Nat} (h : MemorySlice mem base data)
    (free delta fee amount : UInt256) (currency : AccountAddress) (r : PoolSwapResultWords)
    (hl : 64 ≤ base) (hb : base+data.size ≤ free.toNat) :
    MemorySlice (swapWrapperTailMemory mem free delta fee amount currency r) base data := by
  apply MemorySlice.swapWrapperEvent (hb := hb)
  unfold swapWrapperFeeMemory
  split
  · exact h.twoWordHash _ _ hl
  · exact h

end Benchmarks.UniswapV4PoolManager
