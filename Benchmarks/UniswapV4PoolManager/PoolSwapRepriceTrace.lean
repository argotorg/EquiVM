import Benchmarks.UniswapV4PoolManager.TickPriceTrace
import Benchmarks.UniswapV4PoolManager.TickPriceCanonical
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapRepriceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw step state price start tag x1 params remaining calculated fee protocol amount dir pool : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024)
    (hpc : price.toNat < 2^160) (hsc : start.toNat < 2^160) (hs : memLoad step mem = start)
    (h : RD (deployedRuntime v) I g s0 ⟨20162⟩
      ([price, tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R)
      mem aw rdata σ k C) :
    if price = start then ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19964⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R)
      mem (M aw step ⟨32⟩) rdata σ k' C'
    else match tickPriceResult price with
      | none => RDrev (deployedRuntime v) g s0
      | some tick => ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19964⟩
          ([tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R)
          (tick.toByteArray.write 0 mem (state+UInt256.ofNat 32).toNat 32)
          (M (M aw step ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' := by
  have hsm : UInt256.land start (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = start :=
    u256LandMaskCleanOfToNat _ _ rfl hsc
  by_cases he : price = start
  · rw [if_pos he]
    have rd1 := poolManagerBlocks.poolManager_block_20162_fallthrough
      (by change R.length+2+13 ≤ 1024; omega)
      (by rw [hs, hsm]; exact u256_sub_eq_zero_iff_eq.mpr he) h
    have rd2 := poolManagerBlocks.poolManager_block_20193
      (by change R.length+12+1 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_20193_stack] at rd2
    exact ⟨_, _, by omega, rd2⟩
  · rw [if_neg he]
    have rd1 := poolManagerBlocks.poolManager_block_20162_taken
      (by change R.length+2+13 ≤ 1024; omega)
      (by rw [hs, hsm]; exact fun hz => he (u256_sub_eq_zero_iff_eq.mp hz))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_20199
      (by change R.length+12+3 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_20199_stack] at rd2
    cases ht : tickPriceResult price with
    | none =>
      rcases tickPriceTrace v (by change R.length+12+22 ≤ 1024; omega)
          (by rw [poolManagerPatchedValidJumps v]; jump_dest) hpc rd2 with ⟨_, hr⟩ | ⟨tick, _, _, hsome, _⟩
      · exact hr
      · rw [ht] at hsome; contradiction
    | some tick =>
      have hpass : ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨20208⟩
          ([tick, tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R)
          mem (M aw step ⟨32⟩) rdata σ k' C' := by
        obtain ⟨k', C', hC, rd⟩ := RD_retainCost (fun budget first hrd => by
          rcases tickPriceTrace v (by change R.length+12+22 ≤ 1024; omega)
              (by rw [poolManagerPatchedValidJumps v]; jump_dest) hpc hrd with
            ⟨hnone, _⟩ | ⟨tick', k', C', hsome, hr⟩
          · rw [ht] at hnone; contradiction
          · have hh : tick' = tick := Option.some.inj (hsome.symm.trans ht)
            subst tick'
            exact ⟨k', C', hr⟩) rd2
        exact ⟨k', C', by omega, rd⟩
      obtain ⟨k', C', hC, rd⟩ := hpass
      have htc : UInt256.signextend (UInt256.ofNat 2) tick = tick :=
        (signextend24_eq_iff _).mpr (tickPriceResult_canonical ht)
      have rd3 := poolManagerBlocks.poolManager_block_20208 (by change R.length+15 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [poolManagerBlocks.poolManager_block_20208_stack, poolManagerBlocks.poolManager_block_20208_memory, htc] at rd3
      have rd4 := poolManagerBlocks.poolManager_block_20193 (by change R.length+12+1 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      simp only [poolManagerBlocks.poolManager_block_20193_stack] at rd4
      exact ⟨_, _, by omega, rd4⟩

end Benchmarks.UniswapV4PoolManager
