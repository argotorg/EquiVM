import Benchmarks.UniswapV4PoolManager.PoolSwapCrossWords
import Benchmarks.UniswapV4PoolManager.LiquidityAddTrace
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapCrossLiquidityTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw step state liquidity net tag x1 params remaining calculated fee protocol amount pool : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+18 ≤ 1024)
    (hlc : liquidity.toNat < 2^128) (hn : signedFits ⟨128, by decide⟩ (EVM.signed net))
    (hl : memLoad (state+UInt256.ofNat 64) mem = liquidity)
    (h : RD (deployedRuntime v) I g s0 (if zeroForOne then ⟨20104⟩ else ⟨20082⟩)
      ([state, net, UInt256.ofNat 20093, UInt256.ofNat (2^128-1), tag, x1, params, remaining,
        calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
      mem aw rdata σ k C) :
    if liquidityAddFits liquidity (EVM.signed (poolSwapCrossDelta zeroForOne net)) then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19904⟩
        ([tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
        ((liquidityAddResultWord liquidity (EVM.signed (poolSwapCrossDelta zeroForOne net))).toByteArray.write
          0 mem (state+UInt256.ofNat 64).toNat 32)
        (M aw (state+UInt256.ofNat 64) ⟨32⟩) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hm : UInt256.land (UInt256.ofNat (2^128-1)) liquidity = liquidity :=
    (u256_land_comm _ _).trans (u256LandMaskCleanOfToNat _ _ rfl hlc)
  have hpre : ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨17774⟩
      ([liquidity, poolSwapCrossDelta zeroForOne net, UInt256.ofNat 20093, UInt256.ofNat (2^128-1),
        tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
      mem (M aw (state+UInt256.ofNat 64) ⟨32⟩) rdata σ k' C' := by
    have hneg : ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨20082⟩
        ([state, poolSwapCrossDelta zeroForOne net, UInt256.ofNat 20093, UInt256.ofNat (2^128-1),
          tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
        mem aw rdata σ k' C' := by
      cases zeroForOne with
      | false => exact ⟨k, C, Nat.le_refl _, h⟩
      | true =>
        have rd := poolManagerBlocks.poolManager_block_20104 (by change R.length+14+3 ≤ 1024; omega)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
        simp only [poolManagerBlocks.poolManager_block_20104_stack] at rd
        exact ⟨_, _, by omega, rd⟩
    obtain ⟨k', C', hC, rd⟩ := hneg
    have rd' := poolManagerBlocks.poolManager_block_20082 (by change R.length+12+5 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [poolManagerBlocks.poolManager_block_20082_stack, u256_add_comm (UInt256.ofNat 64) state, hl, hm] at rd'
    exact ⟨_, _, by omega, rd'⟩
  obtain ⟨k1, C1, hC1, rd1⟩ := hpre
  have hdf := poolSwapCrossDelta_fits zeroForOne hn
  have hdelta : EVM.wordOfInt (EVM.signed (poolSwapCrossDelta zeroForOne net)) = poolSwapCrossDelta zeroForOne net :=
    wordOfInt_signed _
  rw [← hdelta] at rd1
  by_cases hfit : liquidityAddFits liquidity (EVM.signed (poolSwapCrossDelta zeroForOne net))
  · rw [if_pos hfit]
    have hpass : ∃ k' C', C1 ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨20093⟩
        ([liquidityAddResultWord liquidity (EVM.signed (poolSwapCrossDelta zeroForOne net)), UInt256.ofNat (2^128-1),
          tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
        mem (M aw (state+UInt256.ofNat 64) ⟨32⟩) rdata σ k' C' := by
      apply RD_retainCost ?_ rd1
      intro budget first rd
      have hr := liquidityAddTrace v (by change R.length+13+5 ≤ 1024; omega) hlc hdf.1 hdf.2
        (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd
      simpa only [if_pos hfit, liquidityAddResultWord] using hr
    obtain ⟨k2, C2, hC2, rd2⟩ := hpass
    have hclean : UInt256.land (liquidityAddResultWord liquidity (EVM.signed (poolSwapCrossDelta zeroForOne net)))
        (UInt256.ofNat (2^128-1)) = liquidityAddResultWord liquidity (EVM.signed (poolSwapCrossDelta zeroForOne net)) :=
      u256LandMaskCleanOfToNat _ _ rfl (liquidityAddResultWord_bound hfit)
    have rd3 := poolManagerBlocks.poolManager_block_20093 (by change R.length+15 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [poolManagerBlocks.poolManager_block_20093_stack, poolManagerBlocks.poolManager_block_20093_memory,
      hclean, memoryWords_idem] at rd3
    exact ⟨_, _, by omega, rd3⟩
  · rw [if_neg hfit]
    have hr := liquidityAddTrace v (by change R.length+13+5 ≤ 1024; omega) hlc hdf.1 hdf.2
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
    simpa only [if_neg hfit] using hr

end Benchmarks.UniswapV4PoolManager
