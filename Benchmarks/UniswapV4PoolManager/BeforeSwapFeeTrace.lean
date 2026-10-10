import Benchmarks.UniswapV4PoolManager.BeforeSwapFeeSource
import Benchmarks.UniswapV4PoolManager.BytesObjectWord
import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_043
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

/-- The compiler keeps all 256 bits here; the caller masks the uint24 result. -/
def beforeSwapRawFee (key : PoolKeyWords) (out : ByteArray) : UInt256 :=
  if beforeSwapDynamic key then calldataWord out 64 else ⟨0⟩

theorem beforeSwapRawFee_clean (key : PoolKeyWords) (out : ByteArray) :
    UInt256.land (beforeSwapRawFee key out) ⟨16777215⟩ = beforeSwapFee key out := by
  simp only [beforeSwapRawFee, beforeSwapFee]
  split_ifs
  · rfl
  · decide

theorem beforeSwapFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw keyPtr hook ptr ret : UInt256} {key : PoolKeyWords}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : key.fee.toNat < 2^24)
    (hr : BytesObjectView mem ptr out) (hsize : 96 ≤ out.size)
    (hfit : ptr.toNat+96 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨15473⟩
      (keyPtr :: hook :: ptr :: ret :: ⟨0⟩ :: R) mem aw out σ k C) :
    ∃ aw' k' C', C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨15491⟩
      (hook :: ptr :: ret :: beforeSwapRawFee key out :: R) mem aw' out σ k' C' := by
  have hkey : memLoad (UInt256.ofNat 64+keyPtr) mem = key.fee := by
    rw [u256_add_comm]
    exact hk.load (i := 2) rfl
  have hmask : UInt256.land (UInt256.ofNat 16777215) key.fee = key.fee := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat key.fee ⟨16777215⟩ rfl hc
  by_cases hd : beforeSwapDynamic key
  · have he : UInt256.eq (UInt256.ofNat 8388608)
        (UInt256.land (UInt256.ofNat 16777215) (memLoad (UInt256.ofNat 64+keyPtr) mem)) ≠ ⟨0⟩ := by
      rw [hkey, hmask, show key.fee = ⟨8388608⟩ from hd]
      decide
    have hbranch := poolManager_block_15473_taken (by simp only [List.length_cons]; omega) he
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hload : memLoad (ptr+UInt256.ofNat 96) mem = calldataWord out 64 := by
      apply hr.loadWord hsize
      rw [uadd_word_ofNat_toNat ptr 96 hfit]
    have hfee := poolManager_block_15609 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hbranch
    simp only [poolManager_block_15609_stack, poolManager_block_15473_taken_stack, hload] at hfee
    refine ⟨_, _, _, ?_, by simpa only [beforeSwapRawFee, if_pos hd] using hfee⟩
    dsimp only [memExpansionCost]
    omega
  · have he : UInt256.eq (UInt256.ofNat 8388608)
        (UInt256.land (UInt256.ofNat 16777215) (memLoad (UInt256.ofNat 64+keyPtr) mem)) = ⟨0⟩ := by
      rw [hkey, hmask]
      exact u256_eq_of_ne (Ne.symm hd)
    have hbranch := poolManager_block_15473_fallthrough (by simp only [List.length_cons]; omega) he h
    refine ⟨_, _, _, ?_, by simpa only [beforeSwapRawFee, if_neg hd, poolManager_block_15473_fallthrough_stack] using hbranch⟩
    dsimp only [memExpansionCost]
    omega

end Benchmarks.UniswapV4PoolManager
