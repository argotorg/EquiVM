import Benchmarks.UniswapV4PoolManager.BeforeLiquidityContinueTrace
import Benchmarks.UniswapV4PoolManager.SignedComparison
import Benchmarks.UniswapV4PoolManager.WordBoolean
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def beforeLiquidityBranchTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (mem rdata : ByteArray) (σ : AccountMap) (add : Bool) (hook : AccountAddress)
    (src params len key a b : UInt256) (R : List UInt256) : Prop :=
  ∃ j0 j1 aw k C, Cₘ aw ≤ C ∧ RD (deployedRuntime v) I g s0 (beforeLiquidityEncodePc add)
    (beforeLiquidityEncodeStack add j0 j1 (accountWord hook) src params len key (a :: b :: R)) mem aw rdata σ k C

def beforeLiquiditySelection (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (mem rdata : ByteArray) (σ : AccountMap) (hook : AccountAddress) (p : ModifyLiquidityWords)
    (src params len key a b : UInt256) (R : List UInt256) : Prop :=
  if beforeLiquidityEnabled hook p true then
    beforeLiquidityBranchTrace v I g s0 mem rdata σ true hook src params len key a b R
  else if beforeLiquidityEnabled hook p false then
    beforeLiquidityBranchTrace v I g s0 mem rdata σ false hook src params len key a b R
  else beforeLiquidityContinuation v I g s0 mem rdata σ src params len key a b R

theorem beforeLiquiditySelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw src params len key a b : UInt256} {hook : AccountAddress} {p : ModifyLiquidityWords}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024) (hpaid : Cₘ aw ≤ C)
    (hd : memLoad (params+UInt256.ofNat 64) mem = p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7902⟩
      (accountWord hook :: accountWord hook :: src :: params :: len :: key :: a :: b :: R) mem aw rdata σ k C) :
    beforeLiquiditySelection v I g s0 mem rdata σ hook p src params len key a b R := by
  have hpay : Cₘ (M aw (params+UInt256.ofNat 64) ⟨32⟩) ≤
      C+(40+memExpansionCost aw (params+UInt256.ofNat 64) ⟨32⟩) := by
    dsimp only [memExpansionCost]; omega
  by_cases hpos : 0 < EVM.signed p.delta
  · have hgt : UInt256.sgt (memLoad (params+UInt256.ofNat 64) mem) ⟨0⟩ = ⟨1⟩ := by
      rw [hd, sgt_signed]
      change UInt256.fromBool (decide (0 < EVM.signed p.delta)) = _
      rw [decide_eq_true hpos]; rfl
    have hn : ¬beforeLiquidityEnabled hook p false := by
      intro hh
      change EVM.signed p.delta ≤ 0 ∧ _ at hh
      omega
    have rd1 := poolManager_block_7902_taken (by simp only [List.length_cons]; omega)
      (by rw [hgt]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_7902_taken_stack, hgt] at rd1
    have rd2 := poolManager_block_8150 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    by_cases hz : UInt256.land (accountWord hook) (UInt256.ofNat 2048) = ⟨0⟩
    · have ha : ¬beforeLiquidityEnabled hook p true := fun hh => hh.2 hz
      rw [beforeLiquiditySelection, if_neg ha, if_neg hn]
      simp only [poolManager_block_8150_stack, hz] at rd2
      have rd3 := poolManager_block_7917_taken (by simp only [List.length_cons]; omega)
        (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      have rd4 := poolManager_block_8043_fallthrough (by simp only [List.length_cons]; omega) (by decide) rd3
      have rd5 := poolManager_block_8051_fallthrough (by simp only [List.length_cons]; omega) (by decide) rd4
      exact beforeLiquiditySkipTrace v (by omega) (by omega) rd5
    · have ha : beforeLiquidityEnabled hook p true := ⟨hpos, hz⟩
      rw [beforeLiquiditySelection, if_pos ha]
      simp only [poolManager_block_8150_stack, isZero_eq_zero_of_ne hz] at rd2
      have rd3 := poolManager_block_7917_fallthrough (by simp only [List.length_cons]; omega) (by decide) rd2
      exact ⟨⟨1⟩, accountWord hook, _, _, _, by omega, rd3⟩
  · have hnon : EVM.signed p.delta ≤ 0 := by omega
    have hgt : UInt256.sgt (memLoad (params+UInt256.ofNat 64) mem) ⟨0⟩ = ⟨0⟩ := by
      rw [hd, sgt_signed]
      change UInt256.fromBool (decide (0 < EVM.signed p.delta)) = _
      rw [decide_eq_false hpos]; rfl
    have ha : ¬beforeLiquidityEnabled hook p true := fun hh => hpos hh.1
    rw [beforeLiquiditySelection, if_neg ha]
    have rd1 := poolManager_block_7902_fallthrough (by simp only [List.length_cons]; omega) hgt h
    simp only [poolManager_block_7902_fallthrough_stack, hgt] at rd1
    have rd2 := poolManager_block_7917_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have rd3 := poolManager_block_8043_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := poolManager_block_8136 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    by_cases hz : UInt256.land (accountWord hook) (UInt256.ofNat 512) = ⟨0⟩
    · have hn : ¬beforeLiquidityEnabled hook p false := fun hh => hh.2 hz
      rw [if_neg hn]
      simp only [poolManager_block_8136_stack, hz] at rd4
      have rd5 := poolManager_block_8051_fallthrough (by simp only [List.length_cons]; omega) (by decide) rd4
      exact beforeLiquiditySkipTrace v (by omega) (by omega) rd5
    · have hn : beforeLiquidityEnabled hook p false := ⟨hnon, hz⟩
      rw [if_pos hn]
      simp only [poolManager_block_8136_stack, isZero_eq_zero_of_ne hz] at rd4
      have rd5 := poolManager_block_8051_taken (by simp only [List.length_cons]; omega)
        (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
      exact ⟨⟨0⟩, ⟨0⟩, _, _, _, by omega, rd5⟩

end Benchmarks.UniswapV4PoolManager
