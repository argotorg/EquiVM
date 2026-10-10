import Benchmarks.UniswapV4PoolManager.PoolSwapResultInitSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapResultZeroMem (mem : ByteArray) (state : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem state.toNat ⟨0⟩) (state+UInt256.ofNat 32).toNat ⟨0⟩)
    (state+UInt256.ofNat 64).toNat ⟨0⟩

def poolSwapResultInitMem (mem : ByteArray) (state packed liquidity : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem state.toNat (slot0SqrtPriceWord packed))
    (state+UInt256.ofNat 32).toNat (slot0TickWord packed)) (state+UInt256.ofNat 64).toNat liquidity

def poolSwapResultZeroAW (aw state params : UInt256) : UInt256 :=
  M (M (M (M aw state ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩)
    (state+UInt256.ofNat 64) ⟨32⟩) (params+UInt256.ofNat 64) ⟨32⟩

def poolSwapResultInitAW (aw state params : UInt256) : UInt256 :=
  M (M (M (M (M aw params ⟨32⟩) state ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩)
    (state+UInt256.ofNat 64) ⟨32⟩) (params+UInt256.ofNat 128) ⟨32⟩

def poolSwapLoadedMem (mem : ByteArray) (evm : State) (id state : UInt256) : ByteArray :=
  poolSwapResultInitMem (poolSwapResultZeroMem mem state) state (poolSlot0Word evm id) (poolLiquidityWord evm id)

def poolSwapLoadedAW (aw state params : UInt256) : UInt256 :=
  poolSwapResultInitAW (poolSwapResultZeroAW aw state params) state params

end Benchmarks.UniswapV4PoolManager
