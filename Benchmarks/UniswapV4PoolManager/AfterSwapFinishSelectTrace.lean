import Benchmarks.UniswapV4PoolManager.AfterSwapFinishActiveTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterSwapFinishSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr delta ret x0 x1 x2 x3 x4 : UInt256} {specified unspecified : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hs : signedFits ⟨128, by decide⟩ specified) (hu : signedFits ⟨128, by decide⟩ unspecified)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15800⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: EVM.wordOfInt unspecified :: EVM.wordOfInt specified :: delta :: ret :: ptr :: R)
      mem aw rdata σ k C) :
    if unspecified ≠ 0 ∨ specified ≠ 0 then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨15832⟩
        (ptr :: EVM.wordOfInt unspecified :: EVM.wordOfInt specified :: delta :: ret :: ⟨0⟩ :: R) mem aw rdata σ k' C'
    else ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: delta :: R) mem aw rdata σ k' C' := by
  have hsc : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt specified) = EVM.wordOfInt specified :=
    signextend128_wordOfInt hs.1 hs.2
  have huc : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt unspecified) = EVM.wordOfInt unspecified :=
    signextend128_wordOfInt hu.1 hu.2
  by_cases huz : unspecified = 0
  · subst unspecified
    have rd1 := poolManager_block_15800_taken hstack (by decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_15800_taken_stack] at rd1
    have rd2 := poolManager_block_15924 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManager_block_15924_stack] at rd2
    by_cases hsz : specified = 0
    · subst specified
      rw [if_neg (by decide : ¬((0 : Int) ≠ 0 ∨ (0 : Int) ≠ 0))]
      have rd3 := poolManager_block_15820_fallthrough (by simp only [List.length_cons]; omega) (by decide +kernel) rd2
      have rd4 := poolManager_block_15825 (by omega) hret rd3
      exact ⟨_, _, by omega, rd4⟩
    · rw [if_pos (Or.inr hsz)]
      have hws : UInt256.isZero (EVM.wordOfInt specified) = ⟨0⟩ :=
        isZero_eq_zero_of_ne (fun he => hsz ((wordOfInt_eq_zero_iff (signedFits128_int256 hs)).mp he))
      have rd3 := poolManager_block_15820_taken (by simp only [List.length_cons]; omega)
        (by rw [hsc, hws]; decide +kernel)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact ⟨_, _, by omega, rd3⟩
  · rw [if_pos (Or.inl huz)]
    have hwu : UInt256.isZero (EVM.wordOfInt unspecified) = ⟨0⟩ :=
      isZero_eq_zero_of_ne (fun he => huz ((wordOfInt_eq_zero_iff (signedFits128_int256 hu)).mp he))
    have rd1 := poolManager_block_15800_fallthrough hstack (by rw [huc, hwu]; rfl) h
    simp only [poolManager_block_15800_fallthrough_stack] at rd1
    have rd2 := poolManager_block_15820_taken (by simp only [List.length_cons]; omega)
      (by rw [huc, hwu]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact ⟨_, _, by omega, rd2⟩

end Benchmarks.UniswapV4PoolManager
