import Benchmarks.UniswapV4PoolManager.PoolSwapStepMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_054
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_062
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapStepZeroMem_eq (mem : ByteArray) (step : UInt256) (hf : step.toNat+256 < UInt256.size) :
    poolManagerBlocks.poolManager_block_19090_taken_memory (mem := mem) (x0 := step+UInt256.ofNat 256) (x10 := step) =
      poolSwapStepZeroMem mem step := by
  have h32 := uadd_word_ofNat_toNat step 32 (by omega)
  have h64 := uadd_word_ofNat_toNat step 64 (by omega)
  have h96 := uadd_word_ofNat_toNat step 96 (by omega)
  have h128 := uadd_word_ofNat_toNat step 128 (by omega)
  have h160 := uadd_word_ofNat_toNat step 160 (by omega)
  have h192 := uadd_word_ofNat_toNat step 192 (by omega)
  simp only [poolManagerBlocks.poolManager_block_19090_taken_memory, poolSwapStepZeroMem,
    wordSequenceMemory, Reasoning.Theory.writeWord, h32, h64, h96, h128, h160, h192, Nat.add_assoc]
  rfl

theorem poolSwapStepFillTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id state step params ret packed remaining calculated fee protocol amount : UInt256}
    {zeroForOne : Bool} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hI : evm.executionEnv = I)
    (hf : step.toNat+256 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨19090⟩
      ([step+UInt256.ofNat 256, packed, ret, params, remaining, calculated, fee, protocol, amount,
        UInt256.fromBool (!zeroForOne), step, poolSlot id, state]++R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ C+Cₘ (poolSwapStepFillAW aw step) ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨19155⟩
      ([remaining, ret, params, calculated, packed, fee, protocol, amount, UInt256.fromBool (!zeroForOne),
        step, poolSlot id, state]++R)
      (poolSwapStepInitMem mem evm id step zeroForOne) (poolSwapStepFillAW aw step) rdata evm.accountMap k' C' := by
  have he := poolSwapStepZeroMem_eq mem step hf
  have he' : poolManagerBlocks.poolManager_block_19090_fallthrough_memory (mem := mem)
      (x0 := step+UInt256.ofNat 256) (x10 := step) = poolSwapStepZeroMem mem step := he
  have hfirst : ∃ k' C', C ≤ C' ∧ C+Cₘ (poolSwapStepZeroAW aw step) ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 (if zeroForOne then ⟨19140⟩ else ⟨21940⟩)
      ([packed, ret, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne),
        step, poolSlot id, state]++R) (poolSwapStepZeroMem mem step) (poolSwapStepZeroAW aw step)
      rdata evm.accountMap k' C' := by
    cases zeroForOne
    · have rd := poolManagerBlocks.poolManager_block_19090_taken
        (by change R.length+2+13 ≤ 1024; omega) (by decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      rw [he] at rd
      refine ⟨_, _, by omega, ?_, rd⟩
      dsimp only [poolSwapStepZeroAW, memExpansionCost]
      omega
    · have rd := poolManagerBlocks.poolManager_block_19090_fallthrough
        (by change R.length+2+13 ≤ 1024; omega) rfl h
      rw [he'] at rd
      refine ⟨_, _, by omega, ?_, rd⟩
      dsimp only [poolSwapStepZeroAW, memExpansionCost]
      omega
  obtain ⟨k1, C1, hc1, hp1, rd1⟩ := hfirst
  have hload : ∃ k' C', C1 ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19149⟩
      ([(poolSwapInitialStep evm id zeroForOne).feeGrowthGlobal, remaining, ret, params, calculated,
        packed, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, poolSlot id, state]++R)
      (poolSwapStepZeroMem mem step) (poolSwapStepZeroAW aw step) rdata evm.accountMap k' C' := by
    apply RD_retainCost (h := rd1)
    intro budget start hin
    cases zeroForOne
    · have hg : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (poolSlot id+UInt256.ofNat 2) ⟨0⟩)) = poolFeeGrowthWord evm id true :=
        (storageLoad_codeOwner_eq_solcSlotWordAt evm I (poolSlot id+UInt256.ofNat 2) (by rw [hI])).symm
      obtain ⟨k', C', rd⟩ := poolManagerBlocks.poolManager_block_21940
        (by change R.length+1+13 ≤ 1024; omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hin
      simp only [poolManagerBlocks.poolManager_block_21940_stack, hg] at rd
      exact ⟨k', C', rd⟩
    · have hg : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (poolSlot id+UInt256.ofNat 1) ⟨0⟩)) = poolFeeGrowthWord evm id false :=
        (storageLoad_codeOwner_eq_solcSlotWordAt evm I (poolSlot id+UInt256.ofNat 1) (by rw [hI])).symm
      obtain ⟨k', C', rd⟩ := poolManagerBlocks.poolManager_block_19140
        (by change R.length+1+13 ≤ 1024; omega) hin
      simp only [poolManagerBlocks.poolManager_block_19140_stack, hg] at rd
      exact ⟨k', C', rd⟩
  obtain ⟨k2, C2, hc2, rd2⟩ := hload
  have rd3 := poolManagerBlocks.poolManager_block_19149 (by change R.length+2+13 ≤ 1024; omega) rd2
  simp only [poolManagerBlocks.poolManager_block_19149_stack] at rd3
  change RD _ _ _ _ _ _ (writeWord (poolSwapStepZeroMem mem step) (step+UInt256.ofNat 224).toNat
    (poolSwapInitialStep evm id zeroForOne).feeGrowthGlobal) _ _ _ _ _ at rd3
  rw [poolSwapStepInitMem_eq mem evm id step zeroForOne hf] at rd3
  refine ⟨_, _, by omega, ?_, rd3⟩
  dsimp only [poolSwapStepFillAW, memExpansionCost]
  omega

end Benchmarks.UniswapV4PoolManager
