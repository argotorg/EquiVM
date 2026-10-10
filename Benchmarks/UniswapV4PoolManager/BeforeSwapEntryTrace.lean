import Benchmarks.UniswapV4PoolManager.BeforeSwapSource
import Benchmarks.UniswapV4PoolManager.SwapParamsEncodeTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def beforeSwapEntryResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem rdata : ByteArray) (σ : AccountMap) (hook : AccountAddress)
    (keyPtr paramsPtr src len ret amount : UInt256) (R : List UInt256) : Prop :=
  let bypass := ∃ aw k C, Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: ⟨0⟩ :: amount :: R) mem aw rdata σ k C
  if I.source = hook then bypass
  else if beforeSwapActive hook then ∃ aw k C, Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 ⟨15230⟩
      (src :: len :: paramsPtr :: accountWord hook :: keyPtr :: ret :: ⟨0⟩ :: ⟨0⟩ :: amount :: R) mem aw rdata σ k C
  else bypass

theorem beforeSwapEntryTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw keyPtr paramsPtr src len ret : UInt256} {hook : AccountAddress}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hfit : paramsPtr.toNat+96 < UInt256.size) (hpaid : Cₘ aw ≤ C+63)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15172⟩
      (accountWord hook :: keyPtr :: paramsPtr :: src :: len :: ret :: R) mem aw rdata σ k C) :
    beforeSwapEntryResult v I g s0 mem rdata σ hook keyPtr paramsPtr src len ret p.amountSpecified R := by
  have hload : memLoad (paramsPtr+UInt256.ofNat 32) mem = p.amountSpecified :=
    hp.word_load (i := 1) (word := p.amountSpecified) rfl (by rw [uadd_word_ofNat_toNat paramsPtr 32 (by omega)])
  have hclean : UInt256.land (accountWord hook) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      accountWord hook := solcAddrMask_clean (accountWord_canonical hook)
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  by_cases hself : I.source = hook
  · rw [beforeSwapEntryResult, if_pos hself]
    have rd1 := poolManager_block_15172_taken hstack
      (by
        rw [hclean]
        change UInt256.eq (accountWord hook) (accountWord I.source) ≠ UInt256.ofNat 0
        rw [← heq.mp hself, u256_eq_refl]
        decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_15172_taken_stack, hload] at rd1
    have rd2 := poolManager_block_15661 (by simp only [List.length_cons]; omega) hret rd1
    refine ⟨_, _, _, ?_, rd2⟩
    dsimp only [memExpansionCost]; omega
  · rw [beforeSwapEntryResult, if_neg hself]
    have rd1 := poolManager_block_15172_fallthrough hstack
      (by rw [hclean]; exact u256_eq_of_ne (fun he => hself (heq.mpr he.symm))) h
    simp only [poolManager_block_15172_fallthrough_stack, hload] at rd1
    by_cases ha : beforeSwapActive hook
    · rw [if_pos ha]
      have rd2 := poolManager_block_15215_taken (by simp only [List.length_cons]; omega) ha
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      refine ⟨_, _, _, ?_, rd2⟩
      dsimp only [memExpansionCost]; omega
    · rw [if_neg ha]
      have hz : UInt256.land (accountWord hook) (UInt256.ofNat 128) = UInt256.ofNat 0 :=
        Classical.not_not.mp ha
      have rd2 := poolManager_block_15215_fallthrough (by simp only [List.length_cons]; omega) hz rd1
      have rd3 := poolManager_block_15223 (by simp only [List.length_cons]; omega) hret rd2
      refine ⟨_, _, _, ?_, rd3⟩
      dsimp only [memExpansionCost]; omega

end Benchmarks.UniswapV4PoolManager
