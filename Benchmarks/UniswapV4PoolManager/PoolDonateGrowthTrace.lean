import Benchmarks.UniswapV4PoolManager.PoolDonateModel
import Benchmarks.UniswapV4PoolManager.PoolDonateStatic
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolDonateGrowth0Trace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id hook key src amount0 amount1 len liquidity junk : UInt256}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨10246⟩
      (amount1 :: UInt256.sub ⟨0⟩ amount0 :: liquidity :: id :: hook :: key :: src :: amount1 ::
        amount0 :: len :: poolSlot id :: ⟨32⟩ :: junk :: R) mem aw rdata evm.accountMap k C) :
    if amount0 ≠ ⟨0⟩ ∧ I.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨10278⟩
        (poolSlot id :: liquidity :: id :: hook :: key :: src :: amount1 :: amount0 :: len ::
          poolDonateDelta amount0 amount1 :: ⟨32⟩ :: junk :: R)
        mem aw rdata (poolDonateStep evm id false amount0 liquidity).accountMap k' C' := by
  by_cases hz : amount0 = ⟨0⟩
  · rw [if_neg (fun hh => hh.1 hz)]
    have rd := poolManagerBlocks.poolManager_block_10246_fallthrough
      (by simp only [List.length_cons]; omega) hz h
    simp only [poolDonateStep, if_pos hz]
    exact ⟨_, _, by omega, rd⟩
  have rd := poolManagerBlocks.poolManager_block_10246_taken
    (by simp only [List.length_cons]; omega) hz (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hp : I.perm = false
  · rw [if_pos ⟨hz, hp⟩]
    exact poolDonateGrowth0Static (by simp only [poolManagerBlocks.poolManager_block_10246_taken_stack, List.length_cons]; omega) hp rd
  rw [if_neg (fun hh => hp hh.2)]
  have hpt : I.perm = true := by cases he : I.perm <;> simp_all
  obtain ⟨k', C', hc, hr⟩ := RD_retainCost (fun budget start hr =>
    poolManagerBlocks.poolManager_block_10503
      (by simp only [poolManagerBlocks.poolManager_block_10246_taken_stack, List.length_cons]; omega)
      hpt (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hr) rd
  refine ⟨k', C', by omega, ?_⟩
  simpa only [poolDonateStep, if_neg hz, storageStore_accountMap, hI, poolFeeGrowthSlot,
    Bool.false_eq_true, if_false, poolFeeGrowthWord, Solm.EVM.storageLoad,
    poolDonateGrowth_compiled, poolDonateDelta, balanceDeltaWord,
    poolManagerBlocks.poolManager_block_10246_taken_stack] using hr

theorem poolDonateGrowth1Trace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id hook key src amount0 amount1 len liquidity delta junk : UInt256}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+14 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨10278⟩
      (poolSlot id :: liquidity :: id :: hook :: key :: src :: amount1 :: amount0 :: len ::
        delta :: ⟨32⟩ :: junk :: R) mem aw rdata evm.accountMap k C) :
    if amount1 ≠ ⟨0⟩ ∧ I.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ j0 j1 k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨10284⟩
        (j0 :: j1 :: id :: hook :: key :: src :: amount1 :: amount0 :: len :: delta :: ⟨32⟩ :: junk :: R)
        mem aw rdata (poolDonateStep evm id true amount1 liquidity).accountMap k' C' := by
  by_cases hz : amount1 = ⟨0⟩
  · rw [if_neg (fun hh => hh.1 hz)]
    have rd := poolManagerBlocks.poolManager_block_10278_fallthrough
      (by simp only [List.length_cons]; omega) hz h
    simp only [poolDonateStep, if_pos hz]
    exact ⟨_, _, _, _, by omega, rd⟩
  have rd := poolManagerBlocks.poolManager_block_10278_taken
    (by simp only [List.length_cons]; omega) hz (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hp : I.perm = false
  · rw [if_pos ⟨hz, hp⟩]
    exact poolDonateGrowth1Static hstack hp rd
  rw [if_neg (fun hh => hp hh.2)]
  have hpt : I.perm = true := by cases he : I.perm <;> simp_all
  obtain ⟨k', C', hc, hr⟩ := RD_retainCost (fun budget start hr =>
    poolManagerBlocks.poolManager_block_10482 hstack hpt
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hr) rd
  refine ⟨junk, junk, k', C', by omega, ?_⟩
  have hslot : UInt256.ofNat 2 + poolSlot id = poolSlot id + UInt256.ofNat 2 := u256_add_comm ..
  simpa only [poolDonateStep, if_neg hz, storageStore_accountMap, hI, poolFeeGrowthSlot,
    if_true, poolFeeGrowthWord, Solm.EVM.storageLoad, poolDonateGrowth_compiled,
    poolManagerBlocks.poolManager_block_10482_stack, hslot] using hr

end Benchmarks.UniswapV4PoolManager
