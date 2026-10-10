import Benchmarks.UniswapV4PoolManager.PoolModifyFeesPreludeTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyClearsTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolModifyFeesMemory_size (mem : ByteArray) (free id : UInt256) (p : PoolModifyParams)
    (hm : 64 ≤ mem.size) :
    (poolModifyFeesMemory mem free id p).size = max mem.size (free.toNat+96) := by
  rw [poolModifyFeesMemory, positionGetMemory_size, poolFeeInsideMemory_size _ _ _ hm]

theorem poolModifyFeesMemory_load_before (mem : ByteArray) (free id : UInt256) (p : PoolModifyParams)
    (read : UInt256) (hlo : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size)
    (hbefore : read.toNat+32 ≤ free.toNat) :
    memLoad read (poolModifyFeesMemory mem free id p) = memLoad read mem := by
  rw [poolModifyFeesMemory, positionGetMemory_load_before p.owner read
      (by rw [poolFeeInsideMemory_size _ _ _ (by omega)]; exact hin) hlo hbefore,
    poolFeeInsideMemory_load id p.lower p.upper read hlo hin]

theorem poolModifyClearsMemory_size (mem : ByteArray) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool)
    (hm : 64 ≤ mem.size) : (poolModifyClearsMemory mem id p fl fu).size = mem.size := by
  unfold poolModifyClearsMemory poolModifyClearMemory
  split_ifs
  · rw [conditionalHashMemory_size _ _ _ _ (by rw [conditionalHashMemory_size _ _ _ _ hm]; exact hm),
      conditionalHashMemory_size _ _ _ _ hm]
  · rfl

theorem poolModifyClearsMemory_loadWord (mem : ByteArray) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool)
    (read : UInt256) (hlo : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size) :
    memLoad read (poolModifyClearsMemory mem id p fl fu) = memLoad read mem := by
  unfold poolModifyClearsMemory poolModifyClearMemory
  split_ifs
  · rw [conditionalHashMemory_loadWord _ _ _ _ _ hlo
      (by rw [conditionalHashMemory_size _ _ _ _ (by omega)]; exact hin),
      conditionalHashMemory_loadWord _ _ _ _ _ hlo hin]
  · rfl

def poolModifyAccountingMemory (mem : ByteArray) (free id : UInt256) (p : PoolModifyParams) (fl fu : Bool) : ByteArray :=
  poolModifyClearsMemory (poolModifyFeesMemory mem free id p) id p fl fu

end Benchmarks.UniswapV4PoolManager
