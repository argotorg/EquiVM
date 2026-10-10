import Benchmarks.UniswapV4PoolManager.TickStorage
import Benchmarks.UniswapV4PoolManager.TickLiquidityWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickCrossWrite0 (evm : EVM.State) (id : UInt256) (tick : Int) (growth0 : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tickSlot id tick+⟨1⟩)
    (UInt256.sub growth0 (tickFieldWord evm id tick .feeGrowthOutside0))

def tickCrossPost (evm : EVM.State) (id : UInt256) (tick : Int) (growth0 growth1 : UInt256) : EVM.State :=
  let e0 := tickCrossWrite0 evm id tick growth0
  Solm.EVM.storageStore e0 e0.executionEnv.codeOwner (tickSlot id tick+⟨2⟩)
    (UInt256.sub growth1 (tickFieldWord e0 id tick .feeGrowthOutside1))

def tickCrossNet (evm : EVM.State) (id : UInt256) (tick : Int) (growth0 growth1 : UInt256) : UInt256 :=
  tickNetWord (tickFieldWord (tickCrossPost evm id tick growth0 growth1) id tick .liquidityPacked)

theorem tickCrossNet_fits (evm : EVM.State) (id : UInt256) (tick : Int) (growth0 growth1 : UInt256) :
    signedFits ⟨128, by decide⟩ (EVM.signed (tickCrossNet evm id tick growth0 growth1)) := tickNetWord_fits _

theorem tickCrossPost_executionEnv (evm : EVM.State) (id : UInt256) (tick : Int) (growth0 growth1 : UInt256) :
    (tickCrossPost evm id tick growth0 growth1).executionEnv = evm.executionEnv := by
  simp only [tickCrossPost, tickCrossWrite0, storageStore_executionEnv]

end Benchmarks.UniswapV4PoolManager
