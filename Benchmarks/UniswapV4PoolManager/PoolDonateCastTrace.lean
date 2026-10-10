import Benchmarks.UniswapV4PoolManager.PoolDonateModel
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_028
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_029
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolDonateCastTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id hook key src amount0 amount1 len junk j0 j1 : UInt256}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨10191⟩
      (j0 :: j1 :: hook :: key :: src :: amount1 :: amount0 :: len :: poolSlot id :: id :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    if poolLiquidityWord evm id = ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
    if amount0.toNat < 2^127 ∧ amount1.toNat < 2^127 then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨10246⟩
        (amount1 :: UInt256.sub ⟨0⟩ amount0 :: poolLiquidityWord evm id :: id :: hook :: key :: src ::
          amount1 :: amount0 :: len :: poolSlot id :: ⟨32⟩ :: junk :: R) mem aw rdata evm.accountMap k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hread : UInt256.land (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac => ac.storage.getD (poolSlot id+UInt256.ofNat 3) ⟨0⟩))
      (UInt256.ofNat 340282366920938463463374607431768211455) = poolLiquidityWord evm id := by
    simp only [poolLiquidityWord, poolLiquidityPacked, poolLiquiditySlot, Solm.EVM.storageLoad, hI]
    rfl
  by_cases hz : poolLiquidityWord evm id = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_10191_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hread, hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_10523
      (by simp only [poolManagerBlocks.poolManager_block_10191_taken_stack, List.length_cons]; omega) rd1
  rw [if_neg hz]
  obtain ⟨k1, C1, hc1, rd1⟩ := RD_retainCost (fun budget start hr =>
    poolManagerBlocks.poolManager_block_10191_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [hread]; exact isZero_eq_zero_of_ne hz) hr) h
  simp only [poolManagerBlocks.poolManager_block_10191_fallthrough_stack, hread] at rd1
  have rd2 := poolManagerBlocks.poolManager_block_10224
    (by simp only [List.length_cons]; omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  dsimp only [poolManagerBlocks.poolManager_block_10224_stack] at rd2
  by_cases ha : amount0.toNat < 2^127
  swap
  · rw [if_neg (fun hh => ha hh.1)]
    exact uintToInt128TraceReverts v (by simp only [List.length_cons]; omega) ha rd2
  obtain ⟨k3, C3, hc3, rd3⟩ := RD_retainCost (fun budget start hr =>
    uintToInt128Trace v (by simp only [List.length_cons]; omega) ha
      (by rw [deployedRuntime_jumps]; jump_dest) hr) rd2
  have rd4 := poolManagerBlocks.poolManager_block_10235
    (by simp only [List.length_cons]; omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
  dsimp only [poolManagerBlocks.poolManager_block_10235_stack] at rd4
  by_cases hb : amount1.toNat < 2^127
  swap
  · rw [if_neg (fun hh => hb hh.2)]
    exact uintToInt128TraceReverts v (by simp only [List.length_cons]; omega) hb rd4
  rw [if_pos ⟨ha, hb⟩]
  obtain ⟨k5, C5, hc5, rd5⟩ := RD_retainCost (fun budget start hr =>
    uintToInt128Trace v (by simp only [List.length_cons]; omega) hb
      (by rw [deployedRuntime_jumps]; jump_dest) hr) rd4
  exact ⟨k5, C5, by omega, rd5⟩

end Benchmarks.UniswapV4PoolManager
