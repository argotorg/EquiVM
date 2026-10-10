import Benchmarks.UniswapV4PoolManager.AfterLiquidityActiveTrace
import Benchmarks.UniswapV4PoolManager.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def afterLiquiditySelection (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (mem rdata : ByteArray) (σ : AccountMap) (hook : AccountAddress) (p : ModifyLiquidityWords)
    (key params delta fees src len ret : UInt256) (R : List UInt256) : Prop :=
  if afterLiquidityActive hook p then
    ∃ aw k C, Cₘ aw ≤ C ∧ RD (deployedRuntime v) I g s0 (afterLiquidityEncodePc (afterLiquidityAdd p))
      (afterLiquidityEncodeStack (afterLiquidityAdd p) (accountWord hook) key params delta fees src len ret R)
      mem aw rdata σ k C
  else afterLiquidityReturnTrace v I g s0 mem rdata σ ret delta ⟨0⟩ R

theorem afterLiquiditySelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw key params delta fees src len ret : UInt256} {hook : AccountAddress}
    {p : ModifyLiquidityWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024) (hpaid : Cₘ aw ≤ C)
    (hd : memLoad (params+UInt256.ofNat 64) mem = p.delta)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14466⟩
      (fees :: src :: len :: key :: params :: accountWord hook :: ret :: ⟨0⟩ :: delta :: R)
      mem aw rdata σ k C) :
    afterLiquiditySelection v I g s0 mem rdata σ hook p key params delta fees src len ret R := by
  have hpay : Cₘ (M aw (params+UInt256.ofNat 64) ⟨32⟩) ≤
      C+memExpansionCost aw (params+UInt256.ofNat 64) ⟨32⟩ := by
    dsimp only [memExpansionCost]; omega
  by_cases hpos : 0 < EVM.signed p.delta
  · have hadd : afterLiquidityAdd p = true := decide_eq_true hpos
    have hgt : UInt256.sgt (memLoad (params+UInt256.ofNat 64) mem) ⟨0⟩ = ⟨1⟩ := by
      rw [hd, sgt_signed]
      change UInt256.fromBool (decide (0 < EVM.signed p.delta)) = _
      rw [decide_eq_true hpos]; rfl
    have rd1 := poolManager_block_14466_fallthrough hstack (by rw [hgt]; decide) h
    simp only [poolManager_block_14466_fallthrough_stack] at rd1
    by_cases ha : afterLiquidityActive hook p
    · have hflag : UInt256.land (accountWord hook) (UInt256.ofNat 1024) ≠ ⟨0⟩ := by
        simpa only [afterLiquidityActive, hadd, afterLiquidityFlag, if_true] using ha
      have rd2 := poolManager_block_14480_taken (by simp only [List.length_cons]; omega) hflag
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      rw [afterLiquiditySelection, if_pos ha, hadd]
      exact ⟨_, _, _, by omega, rd2⟩
    · have hflag : UInt256.land (accountWord hook) (UInt256.ofNat 1024) = ⟨0⟩ := by
        simpa only [afterLiquidityActive, hadd, afterLiquidityFlag, if_true, not_not] using ha
      have rd2 := poolManager_block_14480_fallthrough (by simp only [List.length_cons]; omega) hflag rd1
      have rd3 := poolManager_block_14489 (by simp only [List.length_cons]; omega) hret rd2
      rw [afterLiquiditySelection, if_neg ha]
      exact ⟨_, _, _, rd3⟩
  · have hadd : afterLiquidityAdd p = false := decide_eq_false hpos
    have hgt : UInt256.sgt (memLoad (params+UInt256.ofNat 64) mem) ⟨0⟩ = ⟨0⟩ := by
      rw [hd, sgt_signed]
      change UInt256.fromBool (decide (0 < EVM.signed p.delta)) = _
      rw [decide_eq_false hpos]; rfl
    have rd1 := poolManager_block_14466_taken hstack (by rw [hgt]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_14466_taken_stack] at rd1
    by_cases ha : afterLiquidityActive hook p
    · have hflag : UInt256.land (accountWord hook) (UInt256.ofNat 256) ≠ ⟨0⟩ := by
        simpa only [afterLiquidityActive, hadd, afterLiquidityFlag, if_false] using ha
      have rd2 := poolManager_block_14651_taken (by simp only [List.length_cons]; omega) hflag
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      rw [afterLiquiditySelection, if_pos ha, hadd]
      exact ⟨_, _, _, by omega, rd2⟩
    · have hflag : UInt256.land (accountWord hook) (UInt256.ofNat 256) = ⟨0⟩ := by
        simpa only [afterLiquidityActive, hadd, afterLiquidityFlag, if_false, not_not] using ha
      have rd2 := poolManager_block_14651_fallthrough (by simp only [List.length_cons]; omega) hflag rd1
      have rd3 := poolManager_block_14667 (by simp only [List.length_cons]; omega) hret rd2
      rw [afterLiquiditySelection, if_neg ha]
      exact ⟨_, _, _, rd3⟩

end Benchmarks.UniswapV4PoolManager
