import Benchmarks.UniswapV4PoolManager.PoolModifyStateMemory
import Benchmarks.UniswapV4PoolManager.WordStoreMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyAllocationMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  poolModifyStateMemory (writeWord mem 64 (ptr+UInt256.ofNat 128)) ptr

theorem poolModifyAllocationMemory_size (mem : ByteArray) (ptr : UInt256) :
    (poolModifyAllocationMemory mem ptr).size = max mem.size (ptr.toNat+128) := by
  rw [poolModifyAllocationMemory, poolModifyStateMemory_size, writeWord_sparse_size]
  omega

theorem poolModifyAllocationMemory_load_before (mem : ByteArray) (ptr read : UInt256)
    (hlo : 96 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size) (hbefore : read.toNat+32 ≤ ptr.toNat) :
    memLoad read (poolModifyAllocationMemory mem ptr) = memLoad read mem := by
  rw [poolModifyAllocationMemory, poolModifyStateMemory_load_before _ ptr read
      (by rw [writeWord_sparse_size]; omega) hbefore,
    writeWord_sparse_load_disjoint _ _ _ _ hin (Or.inr hlo)]

theorem poolModifyAllocationMemory_free (mem : ByteArray) (ptr : UInt256) (hp : 96 ≤ ptr.toNat) :
    memLoad (UInt256.ofNat 64) (poolModifyAllocationMemory mem ptr) = ptr+UInt256.ofNat 128 := by
  rw [poolModifyAllocationMemory, poolModifyStateMemory_load_before _ ptr (UInt256.ofNat 64)
      (by rw [writeWord_sparse_size]; change 96 ≤ _; omega) hp]
  exact writeWord_sparse_load_back _ (UInt256.ofNat 64) _

theorem poolModifyAllocationMemory_lowerZero (mem : ByteArray) (ptr : UInt256)
    (hf : ptr.toNat+128 < UInt256.size) : memLoad ptr (poolModifyAllocationMemory mem ptr) = ⟨0⟩ := by
  have h := poolModifyStateMemory_load (writeWord mem 64 (ptr+UInt256.ofNat 128)) ptr (i := 0) (by decide) hf
  have hz : UInt256.ofNat (32*0) = ⟨0⟩ := rfl
  simpa only [hz, uint256_add_zero_right] using h

theorem poolModifyAllocationMemory_upperZero (mem : ByteArray) (ptr : UInt256)
    (hf : ptr.toNat+128 < UInt256.size) :
    memLoad (ptr+UInt256.ofNat 64) (poolModifyAllocationMemory mem ptr) = ⟨0⟩ :=
  poolModifyStateMemory_load _ ptr (i := 2) (by decide) hf

end Benchmarks.UniswapV4PoolManager
