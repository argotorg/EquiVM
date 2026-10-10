import Benchmarks.UniswapV4PoolManager.PoolFeeInsideRegion
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_020
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolFeeInsideRegionPC : FeeGrowthRegion → UInt256
  | .below => ⟨5777⟩ | .above => ⟨6873⟩ | .inside => ⟨6901⟩

def poolFeeInsideRegionStack (region : FeeGrowthRegion)
    (id lower upper cur x0 x1 x2 x3 x4 x5 delta x9 x10 : UInt256) (R : List UInt256) : List UInt256 :=
  match region with
  | .below => cur :: tickSlot id (EVM.signed upper) :: delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 ::
      upper :: tickSlot id (EVM.signed lower) :: lower :: x9 :: x10 :: R
  | _ => tickSlot id (EVM.signed lower) :: delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 ::
      upper :: tickSlot id (EVM.signed upper) :: lower :: x9 :: x10 :: R

def poolFeeInsideOutputStack (lower upper x0 x1 x2 x3 x4 x5 delta x9 x10 fee0 fee1 : UInt256)
    (R : List UInt256) : List UInt256 :=
  x10 :: delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: fee0 :: lower :: x9 :: fee1 :: R

def poolFeeInsideRegionActiveWords (aw : UInt256) : FeeGrowthRegion → UInt256
  | .inside => M aw (UInt256.ofNat 128) ⟨32⟩
  | _ => aw

open poolManagerBlocks in
theorem poolFeeInsideRegionExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper cur x0 x1 x2 x3 x4 x5 delta x9 x10 : UInt256}
    {k C : Nat} {R : List UInt256} (region : FeeGrowthRegion)
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 (poolFeeInsideRegionPC region)
      (poolFeeInsideRegionStack region id lower upper cur x0 x1 x2 x3 x4 x5 delta x9 x10 R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨5802⟩
      (poolFeeInsideOutputStack lower upper x0 x1 x2 x3 x4 x5 delta x9 x10
        (poolFeeInsideRegionWord evm id (EVM.signed lower) (EVM.signed upper) region false)
        (poolFeeInsideRegionWord evm id (EVM.signed lower) (EVM.signed upper) region true) R)
      mem (poolFeeInsideRegionActiveWords aw region) rdata evm.accountMap k' C' := by
  have hread (slot : UInt256) :
      (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD slot ⟨0⟩)) =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I slot (by rw [hI])).symm
  cases region
  · obtain ⟨k1, C1, rd1⟩ := poolManager_block_5777 hstack h
    simp only [poolManager_block_5777_stack, hread] at rd1
    exact ⟨k1, C1, rd1⟩
  · obtain ⟨k1, C1, rd1⟩ := poolManager_block_6873 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_6873_stack, hread] at rd1
    exact ⟨k1, C1, rd1⟩
  · obtain ⟨k1, C1, rd1⟩ := poolManager_block_6901 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_6901_stack, hm, hread, memoryWords_idem] at rd1
    exact ⟨k1, C1, rd1⟩

theorem poolFeeInsideRegionTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper cur x0 x1 x2 x3 x4 x5 delta x9 x10 : UInt256}
    {k C : Nat} {R : List UInt256} (region : FeeGrowthRegion)
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (h : RD (deployedRuntime v) I g s0 (poolFeeInsideRegionPC region)
      (poolFeeInsideRegionStack region id lower upper cur x0 x1 x2 x3 x4 x5 delta x9 x10 R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨5802⟩
      (poolFeeInsideOutputStack lower upper x0 x1 x2 x3 x4 x5 delta x9 x10
        (poolFeeInsideRegionWord evm id (EVM.signed lower) (EVM.signed upper) region false)
        (poolFeeInsideRegionWord evm id (EVM.signed lower) (EVM.signed upper) region true) R)
      mem aw' rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hr⟩ := poolFeeInsideRegionExactTrace region v hstack hI hm h
  exact ⟨_, k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
