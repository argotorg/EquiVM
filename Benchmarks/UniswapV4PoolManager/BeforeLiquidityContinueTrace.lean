import Benchmarks.UniswapV4PoolManager.BeforeLiquidityStartTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def beforeLiquidityContinuation (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (mem rdata : ByteArray) (σ : AccountMap) (src params len key a b : UInt256) (R : List UInt256) : Prop :=
  ∃ x0 x1 aw k C, Cₘ aw ≤ C ∧ RD (deployedRuntime v) I g s0 ⟨5511⟩
    (x0 :: x1 :: src :: params :: len :: key :: a :: b :: R) mem aw rdata σ k C

theorem beforeLiquidityContinueTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw src params len key a b : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨8036⟩
      (src :: params :: len :: key :: a :: b :: R) mem aw rdata σ k C) :
    beforeLiquidityContinuation v I g s0 mem rdata σ src params len key a b R := by
  have hr := poolManager_block_8036 hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  exact ⟨_, _, _, _, _, by omega, hr⟩

theorem beforeLiquiditySkipTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw junk src params len key a b : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨8057⟩
      (junk :: src :: params :: len :: key :: a :: b :: R) mem aw rdata σ k C) :
    beforeLiquidityContinuation v I g s0 mem rdata σ src params len key a b R := by
  have hr := poolManager_block_8057 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  exact beforeLiquidityContinueTrace v hstack (by omega) hr

theorem beforeLiquidityResumeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw reply src params len key a b : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (add : Bool) (hstack : R.length+9 ≤ 1024) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 (beforeLiquidityCallRet add)
      (reply :: src :: params :: len :: key :: a :: b :: R) mem aw rdata σ k C) :
    beforeLiquidityContinuation v I g s0 mem rdata σ src params len key a b R := by
  cases add with
  | false =>
    have hr := poolManager_block_8129 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact beforeLiquiditySkipTrace v hstack (by omega) hr
  | true =>
    have hr := poolManager_block_8034 (by simp only [List.length_cons]; omega) h
    exact beforeLiquidityContinueTrace v hstack (by omega) hr

end Benchmarks.UniswapV4PoolManager
