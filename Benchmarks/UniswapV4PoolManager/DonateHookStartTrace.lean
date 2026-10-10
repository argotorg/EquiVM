import Benchmarks.UniswapV4PoolManager.DonateHookMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_029

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def donateHookEncodePc (after : Bool) : UInt256 := if after then ⟨10405⟩ else ⟨10577⟩
def donateHookCallRet (after : Bool) : UInt256 := if after then ⟨10470⟩ else ⟨10644⟩
def donateHookSavedStack (after : Bool) (hookPtr key src amount0 amount1 len delta : UInt256)
    (R : List UInt256) : List UInt256 :=
  if after then delta :: ⟨32⟩ :: R else hookPtr :: key :: src :: amount1 :: amount0 :: len :: R
def donateHookEncodeStack (after : Bool) (hook hookPtr key src amount0 amount1 len delta : UInt256)
    (R : List UInt256) : List UInt256 :=
  if after then amount1 :: key :: src :: hook :: amount0 :: len :: delta :: ⟨32⟩ :: R
  else hook :: hookPtr :: key :: src :: amount1 :: amount0 :: len :: R

theorem donateHookStartTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free hook hookPtr keyPtr src amount0 amount1 len delta : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (after : Bool) (hstack : R.length+20 ≤ 1024) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (donateHookEncodePc after)
      (donateHookEncodeStack after hook hookPtr keyPtr src amount0 amount1 len delta R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+71+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨13756⟩
        ((free+UInt256.ofNat 36) :: accountWord I.source :: keyPtr :: amount0 :: amount1 :: src :: len ::
          UInt256.ofNat 7990 :: free :: UInt256.ofNat 4778 :: hook :: free :: donateHookCallRet after ::
          donateHookSavedStack after hookPtr keyPtr src amount0 amount1 len delta R)
        (writeWord mem (free+UInt256.ofNat 32).toNat (donateHookSelectorWord after)) aw' rdata σ k' C' := by
  cases after with
  | false =>
    have hr := poolManager_block_10577 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_10577_stack, poolManager_block_10577_memory, hfree] at hr
    refine ⟨_, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega
  | true =>
    have hr := poolManager_block_10405 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_10405_stack, poolManager_block_10405_memory, hfree] at hr
    refine ⟨_, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega

end Benchmarks.UniswapV4PoolManager
