import Benchmarks.UniswapV4PoolManager.PoolLiquidityStorage
import Benchmarks.UniswapV4PoolManager.PoolFeeGrowthStorage
import Benchmarks.UniswapV4PoolManager.Slot0InitializeSource
import Benchmarks.UniswapV4PoolManager.PoolSwapValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolFeeGrowth_write {f : Frame} {evm : State} {name : Ident} {id value : UInt256}
    (hs : f.locals.get? name = some (poolRefValue id)) (second : Bool) :
    assignStorageRef? config f evm .storage {base := name, steps := [.field (poolFeeGrowthName second)]}
      (.int (Int.ofNat value.toNat)) = .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (poolFeeGrowthSlot id second) value) :=
  assignResolvedStorageScalar (resolveStorageAliasField hs (poolFeeGrowth_type second)) rfl
    (poolFeeGrowth_loc id second) (storageLocStore_uint256 evm _ value)

def poolSwapSlot0Word (packed : UInt256) (r : PoolSwapResultWords) : UInt256 :=
  slot0SetSqrtWord (slot0SetTickWord packed r.tick) r.price

def poolSwapSlot0Post (evm : State) (id packed : UInt256) (r : PoolSwapResultWords) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolSlot id) (poolSwapSlot0Word packed r)

def poolSwapLiquidityPost (evm : State) (id liquidity : UInt256) : State :=
  if poolLiquidityWord evm id = liquidity then evm else poolLiquidityStore evm id liquidity

def poolSwapGrowthPost (evm : State) (id growth : UInt256) (zeroForOne : Bool) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolFeeGrowthSlot id (!zeroForOne)) growth

def poolSwapFinishPost (evm : State) (id packed : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) : State :=
  poolSwapGrowthPost (poolSwapLiquidityPost (poolSwapSlot0Post evm id packed r) id r.liquidity)
    id s.feeGrowthGlobal zeroForOne

theorem poolSwapSlot0Post_executionEnv (evm : State) (id packed : UInt256) (r : PoolSwapResultWords) :
    (poolSwapSlot0Post evm id packed r).executionEnv = evm.executionEnv :=
  storageStore_executionEnv ..

theorem poolSwapLiquidityPost_executionEnv (evm : State) (id liquidity : UInt256) :
    (poolSwapLiquidityPost evm id liquidity).executionEnv = evm.executionEnv := by
  unfold poolSwapLiquidityPost
  split
  · rfl
  · exact storageStore_executionEnv ..

theorem poolSwapGrowthPost_executionEnv (evm : State) (id growth : UInt256) (zeroForOne : Bool) :
    (poolSwapGrowthPost evm id growth zeroForOne).executionEnv = evm.executionEnv :=
  storageStore_executionEnv ..

theorem poolSwapFinishPost_executionEnv (evm : State) (id packed : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) :
    (poolSwapFinishPost evm id packed s r zeroForOne).executionEnv = evm.executionEnv := by
  rw [poolSwapFinishPost, poolSwapGrowthPost_executionEnv, poolSwapLiquidityPost_executionEnv,
    poolSwapSlot0Post_executionEnv]

end Benchmarks.UniswapV4PoolManager
