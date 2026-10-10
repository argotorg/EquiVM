import Benchmarks.UniswapV4PoolManager.PoolSwapCrossWords
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapCrossPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw step state id tag x1 params remaining calculated fee protocol amount : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+22 ≤ 1024)
    (hI : evm.executionEnv = I) (hg : memLoad (step+UInt256.ofNat 224) mem = s.feeGrowthGlobal)
    (h : RD (deployedRuntime v) I g s0 ⟨19984⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, poolSlot id, state] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨20029⟩
      ([step, UInt256.ofNat 32, poolSlot id, UInt256.ofNat 4,
        poolSwapCrossGrowth1 evm id s zeroForOne, poolSwapCrossGrowth0 evm id s zeroForOne,
        state, UInt256.ofNat 20093, UInt256.ofNat (2^128-1), tag, x1, params, remaining, calculated, fee, protocol,
        amount, UInt256.fromBool (!zeroForOne), step, poolSlot id, state] ++ R)
      mem (M aw (step+UInt256.ofNat 224) ⟨32⟩) rdata evm.accountMap k' C' := by
  have hload (second : Bool) : poolFeeGrowthWord evm id second =
      solcSlotWordAt (poolFeeGrowthSlot id second) evm.accountMap I :=
    storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])
  apply RD_retainCost ?_ h
  intro budget first rd
  cases zeroForOne with
  | false =>
    have rd1 := poolManagerBlocks.poolManager_block_19984_taken
      (by change R.length+3+11 ≤ 1024; omega) (by decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨k', C', rd2⟩ := poolManagerBlocks.poolManager_block_20118 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_20118_stack, hg] at rd2
    exact ⟨k', C', by simpa only [poolSwapCrossGrowth0, poolSwapCrossGrowth1,
      Bool.false_eq_true, if_false, hload, poolFeeGrowthSlot] using rd2⟩
  | true =>
    have rd1 := poolManagerBlocks.poolManager_block_19984_fallthrough
      (by change R.length+3+11 ≤ 1024; omega) (by decide) rd
    obtain ⟨k', C', rd2⟩ := poolManagerBlocks.poolManager_block_19990 hstack rd1
    simp only [poolManagerBlocks.poolManager_block_19990_stack, hg] at rd2
    exact ⟨k', C', by simpa only [poolSwapCrossGrowth0, poolSwapCrossGrowth1,
      if_true, hload, poolFeeGrowthSlot] using rd2⟩

end Benchmarks.UniswapV4PoolManager
