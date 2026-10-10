import Benchmarks.UniswapV4PoolManager.PoolModifyTickMemory
import Benchmarks.UniswapV4PoolManager.TickPairMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolModifyLowerMemory_span (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hp : 64 ≤ ptr.toNat) (hf : ptr.toNat+32 < UInt256.size) :
    ptr.toNat+64 ≤ (poolModifyLowerMemory mem ptr id p evm).size := by
  have hs := tickLowerResultMemory_span (twoWordHashMem p.lower (poolSlot id+⟨4⟩) mem) ptr
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
    (UInt256.fromBool (tickFlipped (poolModifyLowerPacked evm id p) p.delta)) hf
  rw [poolModifyLowerMemory, twoWordHashMem_size_of_ge_64' _ _ (by omega)]
  exact hs

theorem poolModifyLowerMemory_size_ge (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hm : 64 ≤ mem.size) : mem.size ≤ (poolModifyLowerMemory mem ptr id p evm).size := by
  have hs := twoWordHashMem_size_of_ge_64' p.lower (poolSlot id+⟨4⟩) hm
  have ht := tickLowerResultMemory_size_ge (twoWordHashMem p.lower (poolSlot id+⟨4⟩) mem) ptr
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
    (UInt256.fromBool (tickFlipped (poolModifyLowerPacked evm id p) p.delta))
  rw [poolModifyLowerMemory, twoWordHashMem_size_of_ge_64' _ _ (by omega)]
  omega

theorem poolModifyTwoTicksMemory_size_ge (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hm : 64 ≤ mem.size) : mem.size ≤ (poolModifyTwoTicksMemory mem ptr id p evm).size :=
  (poolModifyLowerMemory_size_ge mem ptr id p evm hm).trans (tickUpperResultMemory_size_ge _ _ _ _)

theorem poolModifyTwoTicksMemory_loadWord (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (read : UInt256) (hoff : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size)
    (hbefore : read.toNat+32 ≤ ptr.toNat) (hfit : ptr.toNat+128 < UInt256.size) :
    memLoad read (poolModifyTwoTicksMemory mem ptr id p evm) = memLoad read mem := by
  have hs := poolModifyLowerMemory_size_ge mem ptr id p evm (by omega)
  rw [poolModifyTwoTicksMemory, tickUpperResultMemory_load_before _ _ _ _ _
    (by omega) (by omega) (by omega)]
  exact poolModifyLowerMemory_loadWord mem ptr id p evm read hoff hin hbefore (by omega)

theorem poolModifyTwoTicksMemory_lowerFlipped (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hp : 64 ≤ ptr.toNat) (hf : ptr.toNat+128 < UInt256.size) :
    memLoad ptr (poolModifyTwoTicksMemory mem ptr id p evm) =
      UInt256.fromBool (tickFlipped (poolModifyLowerPacked evm id p) p.delta) := by
  have hs := poolModifyLowerMemory_span mem ptr id p evm hp (by omega)
  have ht := tickLowerResultMemory_span (twoWordHashMem p.lower (poolSlot id+⟨4⟩) mem) ptr
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
    (UInt256.fromBool (tickFlipped (poolModifyLowerPacked evm id p) p.delta)) (by omega)
  rw [poolModifyTwoTicksMemory, tickUpperResultMemory_load_before _ _ _ _ _ (by omega) (by omega) (by omega),
    poolModifyLowerMemory, twoWordHashMem_loadWord _ _ _ hp (by omega)]
  exact tickLowerResultMemory_flipped _ _ _ _

theorem poolModifyTwoTicksMemory_lowerGross (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hp : 64 ≤ ptr.toNat) (hf : ptr.toNat+128 < UInt256.size) :
    memLoad (ptr+UInt256.ofNat 32) (poolModifyTwoTicksMemory mem ptr id p evm) =
      EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta) := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hs := poolModifyLowerMemory_span mem ptr id p evm hp (by omega)
  have ht := tickLowerResultMemory_span (twoWordHashMem p.lower (poolSlot id+⟨4⟩) mem) ptr
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
    (UInt256.fromBool (tickFlipped (poolModifyLowerPacked evm id p) p.delta)) (by omega)
  rw [poolModifyTwoTicksMemory, tickUpperResultMemory_load_before _ _ _ _ _ (by omega) (by omega) (by omega),
    poolModifyLowerMemory, twoWordHashMem_loadWord _ _ _ (by omega) (by omega)]
  exact tickLowerResultMemory_gross _ _ _ _ (by omega)

theorem poolModifyTwoTicksMemory_upperFlipped (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State) :
    memLoad (ptr+UInt256.ofNat 64) (poolModifyTwoTicksMemory mem ptr id p evm) =
      UInt256.fromBool (tickFlipped (poolModifyUpperPacked evm id p) p.delta) :=
  tickUpperResultMemory_flipped _ _ _ _

theorem poolModifyTwoTicksMemory_upperGross (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hf : ptr.toNat+128 < UInt256.size) :
    memLoad (ptr+UInt256.ofNat 96) (poolModifyTwoTicksMemory mem ptr id p evm) =
      EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta) :=
  tickUpperResultMemory_gross _ _ _ _ (by omega)

end Benchmarks.UniswapV4PoolManager
