import Benchmarks.UniswapV4PoolManager.TickLowerStoreTrace
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory
import Benchmarks.UniswapV4PoolManager.SparseBytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickLowerResultMemory_size_ge (mem : ByteArray) (ptr gross flipped : UInt256) :
    mem.size ≤ (tickLowerResultMemory mem ptr gross flipped).size := by
  simp only [tickLowerResultMemory, writeWord_sparse_size]
  omega

theorem tickLowerResultMemory_load_before (mem : ByteArray) (ptr gross flipped read : UInt256)
    (hin : read.toNat+32 ≤ mem.size) (hbefore : read.toNat+32 ≤ ptr.toNat)
    (hfit : ptr.toNat+32 < UInt256.size) :
    memLoad read (tickLowerResultMemory mem ptr gross flipped) = memLoad read mem := by
  have h32 : (ptr+(⟨32⟩ : UInt256)).toNat = ptr.toNat+32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from rfl, Nat.mod_eq_of_lt hfit]
  rw [tickLowerResultMemory,
    writeWord_sparse_load_before _ _ _ read (by rw [writeWord_sparse_size]; omega) hbefore,
    writeWord_sparse_load_before _ _ _ read hin (by rw [h32]; omega)]

theorem tickLowerNextMemory_loadWord (mem : ByteArray) (lower upper base ptr gross flipped read : UInt256)
    (hoff : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size)
    (hbefore : read.toNat+32 ≤ ptr.toNat) (hfit : ptr.toNat+32 < UInt256.size) :
    memLoad read (twoWordHashMem upper base
      (tickLowerResultMemory (twoWordHashMem lower base mem) ptr gross flipped)) = memLoad read mem := by
  have hsize := twoWordHashMem_size_of_ge_64' lower base (mem := mem) (by omega)
  have hres := tickLowerResultMemory_size_ge (twoWordHashMem lower base mem) ptr gross flipped
  rw [twoWordHashMem_loadWord upper base read hoff (by omega),
    tickLowerResultMemory_load_before _ ptr gross flipped read (by omega) hbefore hfit,
    twoWordHashMem_loadWord lower base read hoff hin]

end Benchmarks.UniswapV4PoolManager
