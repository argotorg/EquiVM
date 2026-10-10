import Benchmarks.UniswapV4PoolManager.PoolModifyTwoTicks
import Benchmarks.UniswapV4PoolManager.TickResultMemory
import Benchmarks.UniswapV4PoolManager.TickUpperStoreTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyLowerMemory (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State) : ByteArray :=
  twoWordHashMem p.upper (poolSlot id+⟨4⟩)
    (tickLowerResultMemory (twoWordHashMem p.lower (poolSlot id+⟨4⟩) mem) ptr
      (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
      (UInt256.fromBool (tickFlipped (poolModifyLowerPacked evm id p) p.delta)))

def poolModifyTwoTicksMemory (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State) : ByteArray :=
  tickUpperResultMemory (poolModifyLowerMemory mem ptr id p evm) ptr
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta))
    (UInt256.fromBool (tickFlipped (poolModifyUpperPacked evm id p) p.delta))

theorem poolModifyLowerMemory_loadWord (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (read : UInt256) (hoff : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size)
    (hbefore : read.toNat+32 ≤ ptr.toNat) (hfit : ptr.toNat+32 < UInt256.size) :
    memLoad read (poolModifyLowerMemory mem ptr id p evm) = memLoad read mem :=
  tickLowerNextMemory_loadWord mem _ _ _ ptr _ _ read hoff hin hbefore hfit

end Benchmarks.UniswapV4PoolManager
