import Benchmarks.UniswapV4PoolManager.PoolKeyMemory
import Benchmarks.UniswapV4PoolManager.SparseBytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyStateMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  wordSequenceMemory mem ptr.toNat [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]

theorem poolModifyStateMemory_size (mem : ByteArray) (ptr : UInt256) :
    (poolModifyStateMemory mem ptr).size = max mem.size (ptr.toNat+128) := by
  simp only [poolModifyStateMemory, wordSequenceMemory, writeWord_sparse_size]
  omega

theorem poolModifyStateMemory_load_before (mem : ByteArray) (ptr read : UInt256)
    (hin : read.toNat+32 ≤ mem.size) (hbefore : read.toNat+32 ≤ ptr.toNat) :
    memLoad read (poolModifyStateMemory mem ptr) = memLoad read mem := by
  rw [memLoad, memLoad, if_neg (by rw [poolModifyStateMemory_size]; omega), if_neg (by omega)]
  rw [poolModifyStateMemory, wordSequenceMemory_read_below _ _ _ _ hin hbefore]

theorem poolModifyStateMemory_load (mem : ByteArray) (ptr : UInt256) {i : Nat}
    (hi : i < 4) (hfit : ptr.toNat+128 < UInt256.size) :
    memLoad (ptr+UInt256.ofNat (32*i)) (poolModifyStateMemory mem ptr) = ⟨0⟩ := by
  have hp := uadd_word_ofNat_toNat ptr (32*i) (by omega)
  apply loadedWord_of_read
  · rw [hp, poolModifyStateMemory_size]; omega
  · rw [hp]
    apply wordSequenceMemory_read_word
    interval_cases i <;> rfl

end Benchmarks.UniswapV4PoolManager
