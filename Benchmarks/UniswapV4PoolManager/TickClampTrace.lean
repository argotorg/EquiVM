import Benchmarks.UniswapV4PoolManager.TickClampLowerTrace
import Benchmarks.UniswapV4PoolManager.TickClampUpperTrace
import Benchmarks.UniswapV4PoolManager.TickSqrtCanonicalTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickClampTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw step tick : UInt256} {initialized : Bool}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨19401⟩
      ([initialized.toUInt256, tick, tickMinWord, step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19442⟩
      ([step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64] ++ R)
      (tickClampMemory mem step tick initialized)
      (M (M aw (step+UInt256.ofNat 64) ⟨32⟩) (step+UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' := by
  obtain ⟨k1, C1, hC1, rd1⟩ := tickClampLowerTrace v hstack h
  obtain ⟨k2, C2, hC2, rd2⟩ := tickClampUpperTrace v
    (by change R.length+7 ≤ 1024; omega) (tickClampLowerWord_canonical tick)
    (tickClampLowerMemory_tick mem step tick initialized) rd1
  simp only [memoryWords_idem] at rd2
  exact ⟨k2, C2, hC1.trans hC2, rd2⟩

theorem tickClampPriceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw step tick : UInt256} {initialized : Bool}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨19401⟩
      ([initialized.toUInt256, tick, tickMinWord, step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19479⟩
      ([tickSqrtPrice (EVM.signed (tickClampWord tick)), UInt256.ofNat (2^160-1),
        step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64] ++ R)
      (tickClampMemory mem step tick initialized)
      (M (M aw (step+UInt256.ofNat 64) ⟨32⟩) (step+UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' := by
  apply RD_retainCost ?_ h
  intro budget start rd
  obtain ⟨k1, C1, _, rd1⟩ := tickClampTrace v (by omega) rd
  have rd2 := poolManagerBlocks.poolManager_block_19442
    (by change R.length+8 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hc := tickClampWord_canonical tick
  have hclean : UInt256.signextend (UInt256.ofNat 2) (tickClampWord tick) = tickClampWord tick :=
    (signextend24_eq_iff _).mpr hc
  simp only [poolManagerBlocks.poolManager_block_19442_stack, tickClampMemory_tick,
    hclean, memoryWords_idem] at rd2
  exact tickSqrtCanonicalTrace v (by change R.length+12 ≤ 1024; omega) hc (tickClampWord_natAbs tick)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2

end Benchmarks.UniswapV4PoolManager
