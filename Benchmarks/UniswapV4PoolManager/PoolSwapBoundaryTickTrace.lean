import Benchmarks.UniswapV4PoolManager.PoolSwapBoundaryTickSource
import Benchmarks.UniswapV4PoolManager.WordNarrowCast
import Benchmarks.UniswapV4PoolManager.TickLogCompiled
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_056
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapBoundaryTickTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw step state tick tag x1 params remaining calculated fee protocol amount pool : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+15 ≤ 1024)
    (htc : int24Canonical tick) (ht : memLoad (step+UInt256.ofNat 32) mem = tick)
    (h : RD (deployedRuntime v) I g s0 ⟨19904⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19964⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
      ((poolSwapBoundaryTick zeroForOne tick).toByteArray.write 0 mem (state+UInt256.ofNat 32).toNat 32)
      (M (M aw (step+UInt256.ofNat 32) ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' := by
  have hclean : UInt256.signextend (UInt256.ofNat 2) tick = tick := (signextend24_eq_iff tick).mpr htc
  have hpre : ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19955⟩
      ([poolSwapBoundaryTick zeroForOne tick, tag, x1, params, remaining, calculated, fee, protocol,
        amount, UInt256.fromBool (!zeroForOne), step, pool, state] ++ R)
      mem (M aw (step+UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' := by
    cases zeroForOne with
    | false =>
      have rd1 := poolManagerBlocks.poolManager_block_19904_taken
        (by change R.length+3+11 ≤ 1024; omega) (by decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      have rd2 := poolManagerBlocks.poolManager_block_19971
        (by change R.length+2+12 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      simp only [poolManagerBlocks.poolManager_block_19971_stack, ht, hclean] at rd2
      exact ⟨_, _, by omega, rd2⟩
    | true =>
      have rd1 := poolManagerBlocks.poolManager_block_19904_fallthrough
        (by change R.length+3+11 ≤ 1024; omega) (by decide) h
      have rd2 := poolManagerBlocks.poolManager_block_19910
        (by change R.length+2+13 ≤ 1024; omega) rd1
      have hp : tick + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 =
          UInt256.sub tick ⟨1⟩ := wordAddNegSub tick ⟨1⟩
      simp only [poolManagerBlocks.poolManager_block_19910_stack, ht, hclean, hp] at rd2
      exact ⟨_, _, by omega, rd2⟩
  obtain ⟨k', C', hC, rd⟩ := hpre
  have hfinal : UInt256.signextend (UInt256.ofNat 2) (poolSwapBoundaryTick zeroForOne tick) =
      poolSwapBoundaryTick zeroForOne tick := by
    cases zeroForOne
    · exact hclean
    · exact signextend24_idempotent _
  have rd' := poolManagerBlocks.poolManager_block_19955 hstack rd
  simp only [poolManagerBlocks.poolManager_block_19955_stack, poolManagerBlocks.poolManager_block_19955_memory, hfinal] at rd'
  exact ⟨_, _, by omega, rd'⟩

end Benchmarks.UniswapV4PoolManager
