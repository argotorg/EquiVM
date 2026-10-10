import Benchmarks.UniswapV4PoolManager.BeforeLiquidityMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def beforeLiquidityEncodePc (add : Bool) : UInt256 := if add then ⟨7923⟩ else ⟨8063⟩
def beforeLiquidityCallRet (add : Bool) : UInt256 := if add then ⟨8034⟩ else ⟨8129⟩
def beforeLiquidityEncodeStack (add : Bool) (a b hook src params len key : UInt256) (R : List UInt256) : List UInt256 :=
  (if add then [a, b] else []) ++ hook :: src :: params :: len :: key :: R

theorem beforeLiquidityStartTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free a b hook keyPtr paramsPtr src len : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (add : Bool) (hstack : R.length+17 ≤ 1024) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (beforeLiquidityEncodePc add)
      (beforeLiquidityEncodeStack add a b hook src paramsPtr len keyPtr R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+71+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨14027⟩
        ((free+UInt256.ofNat 36) :: accountWord I.source :: keyPtr :: paramsPtr :: src :: len ::
          UInt256.ofNat 7990 :: free :: UInt256.ofNat 4778 :: hook :: free :: beforeLiquidityCallRet add ::
          src :: paramsPtr :: len :: keyPtr :: R)
        (writeWord mem (free+UInt256.ofNat 32).toNat (beforeLiquiditySelectorWord add)) aw' rdata σ k' C' := by
  cases add with
  | false =>
    have hr := poolManager_block_8063 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_8063_stack, poolManager_block_8063_memory, hfree] at hr
    refine ⟨_, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega
  | true =>
    have hr := poolManager_block_7923 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_7923_stack, poolManager_block_7923_memory, hfree] at hr
    refine ⟨_, _, _, ?_, hr⟩
    dsimp only [memExpansionCost]
    omega

end Benchmarks.UniswapV4PoolManager
