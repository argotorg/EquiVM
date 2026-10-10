import Benchmarks.UniswapV4PoolManager.AfterLiquidityMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_040
import Benchmarks.UniswapV4PoolManager.WordBoolean

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def afterLiquidityEncodePc (add : Bool) : UInt256 := if add then ⟨14498⟩ else ⟨14675⟩
def afterLiquidityAllocationRet (add : Bool) : UInt256 := if add then ⟨14619⟩ else ⟨14752⟩
def afterLiquidityEncodeStack (add : Bool) (hook key params delta fees src len ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  (if add then [delta, fees, src, len, key, params, hook, ret, ⟨0⟩, delta]
    else [fees, src, len, key, params, hook, delta, ret, ⟨0⟩, delta]) ++ R

theorem afterLiquidityStartTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free hook keyPtr paramsPtr delta fees src len ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (add : Bool) (hstack : R.length+18 ≤ 1024) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (afterLiquidityEncodePc add)
      (afterLiquidityEncodeStack add hook keyPtr paramsPtr delta fees src len ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+96+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨14227⟩
        ((free+UInt256.ofNat 36) :: accountWord I.source :: keyPtr :: paramsPtr :: delta :: fees :: src :: len ::
          UInt256.ofNat 14575 :: free :: afterLiquidityAllocationRet add :: free :: hook ::
          UInt256.ofNat 14631 :: UInt256.ofNat 14638 :: delta :: ret :: R)
        (writeWord mem (free+UInt256.ofNat 32).toNat (afterLiquiditySelectorWord add)) aw' rdata σ k' C' := by
  cases add with
  | false =>
    have hr := poolManager_block_14675 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_14675_stack, poolManager_block_14675_memory, hfree] at hr
    refine ⟨_, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega
  | true =>
    have hr := poolManager_block_14498 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_14498_stack, poolManager_block_14498_memory, hfree] at hr
    refine ⟨_, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega

theorem afterLiquidityInvokeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr : UInt256} {hook : AccountAddress}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (add : Bool) (hstack : R.length+4 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (afterLiquidityAllocationRet add)
      (ptr :: accountWord hook :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨17823⟩
      (accountWord hook :: ptr :: UInt256.fromBool (afterLiquidityParse hook add) :: R) mem aw rdata σ k' C' := by
  cases add with
  | false =>
    have hr := poolManager_block_14752 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    refine ⟨_, _, ?_, by simpa only [poolManager_block_14752_stack, afterLiquidityParse, afterLiquidityDeltaFlag,
      if_false, wordNonzeroBool] using hr⟩
    omega
  | true =>
    have hr := poolManager_block_14619 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    refine ⟨_, _, ?_, by simpa only [poolManager_block_14619_stack, afterLiquidityParse, afterLiquidityDeltaFlag,
      if_true, wordNonzeroBool] using hr⟩
    omega

end Benchmarks.UniswapV4PoolManager
