import Benchmarks.UniswapV4PoolManager.WordBoolean
import Benchmarks.UniswapV4PoolManager.HookValidationSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_040
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_041

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem hookPairTraceCore {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw test next ret hook fee required extra : UInt256} {σ : AccountMap} {R : List UInt256}
    (hmissing : UInt256.land hook required = ⟨0⟩ → ∃ k C, RD code I g s0 test
      (UInt256.isZero (UInt256.isZero (UInt256.land hook extra)) :: hook :: fee :: ret :: R) mem aw rdata σ k C)
    (hpresent : UInt256.land hook required ≠ ⟨0⟩ → ∃ k C, RD code I g s0 test
      (⟨0⟩ :: hook :: fee :: ret :: R) mem aw rdata σ k C)
    (hzero : ∀ {k C}, RD code I g s0 test (⟨0⟩ :: hook :: fee :: ret :: R) mem aw rdata σ k C →
      ∃ k' C', RD code I g s0 next (hook :: fee :: ret :: R) mem aw rdata σ k' C')
    (hone : ∀ {k C}, RD code I g s0 test (⟨1⟩ :: hook :: fee :: ret :: R) mem aw rdata σ k C →
      ∃ k' C', RD code I g s0 ret (⟨0⟩ :: R) mem aw rdata σ k' C') :
    if hookPairInvalid hook required extra then
      ∃ k' C', RD code I g s0 ret (⟨0⟩ :: R) mem aw rdata σ k' C'
    else ∃ k' C', RD code I g s0 next (hook :: fee :: ret :: R) mem aw rdata σ k' C' := by
  have htest : ∃ k C, RD code I g s0 test
      ((hookPairInvalid hook required extra).toUInt256 :: hook :: fee :: ret :: R) mem aw rdata σ k C := by
    by_cases hz : UInt256.land hook required = ⟨0⟩
    · simpa only [hookPairInvalid, hz, decide_true, Bool.true_and, wordNonzeroBool] using hmissing hz
    · simpa only [hookPairInvalid, hz, decide_false, Bool.false_and] using hpresent hz
  obtain ⟨k1, C1, rd1⟩ := htest
  cases hb : hookPairInvalid hook required extra with
  | false =>
    simp only [hb, Bool.false_eq_true, if_false] at rd1 ⊢
    exact hzero rd1
  | true =>
    simp only [hb, if_true] at rd1 ⊢
    exact hone rd1

theorem hookPair0Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret hook fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14775⟩ (hook :: fee :: ret :: R) mem aw rdata σ k C) :
    if hookPairInvalid hook (UInt256.ofNat 128) (UInt256.ofNat 8) then
      ∃ k' C', RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: R) mem aw rdata σ k' C'
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14791⟩ (hook :: fee :: ret :: R) mem aw rdata σ k' C' := by
  apply hookPairTraceCore (test := UInt256.ofNat 14786)
  · intro hz
    have rd1 := poolManagerBlocks.poolManager_block_14775_taken (by simp only [List.length_cons]; omega)
      (by rw [hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14953 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1⟩
  · intro hn
    have rd1 := poolManagerBlocks.poolManager_block_14775_fallthrough (by simp only [List.length_cons]; omega)
      (isZero_eq_zero_of_ne hn) h
    simpa only [poolManagerBlocks.poolManager_block_14775_fallthrough_stack, isZero_eq_zero_of_ne hn] using
      (show ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14786⟩ _ mem aw rdata σ k' C' from ⟨_, _, rd1⟩)
  · intro k1 C1 rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14786_fallthrough (by simp only [List.length_cons]; omega) rfl rd1⟩
  · intro k1 C1 rd1
    have rd2 := poolManagerBlocks.poolManager_block_14786_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14911 (by omega) hret rd2⟩

theorem hookPair1Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret hook fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14791⟩ (hook :: fee :: ret :: R) mem aw rdata σ k C) :
    if hookPairInvalid hook (UInt256.ofNat 64) (UInt256.ofNat 4) then
      ∃ k' C', RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: R) mem aw rdata σ k' C'
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14806⟩ (hook :: fee :: ret :: R) mem aw rdata σ k' C' := by
  apply hookPairTraceCore (test := UInt256.ofNat 14801)
  · intro hz
    have rd1 := poolManagerBlocks.poolManager_block_14791_taken (by simp only [List.length_cons]; omega)
      (by rw [hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14941 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1⟩
  · intro hn
    have rd1 := poolManagerBlocks.poolManager_block_14791_fallthrough (by simp only [List.length_cons]; omega)
      (isZero_eq_zero_of_ne hn) h
    simpa only [poolManagerBlocks.poolManager_block_14791_fallthrough_stack, isZero_eq_zero_of_ne hn] using
      (show ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14801⟩ _ mem aw rdata σ k' C' from ⟨_, _, rd1⟩)
  · intro k1 C1 rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14801_fallthrough (by simp only [List.length_cons]; omega) rfl rd1⟩
  · intro k1 C1 rd1
    have rd2 := poolManagerBlocks.poolManager_block_14801_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14911 (by omega) hret rd2⟩

theorem hookPair2Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret hook fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14806⟩ (hook :: fee :: ret :: R) mem aw rdata σ k C) :
    if hookPairInvalid hook (UInt256.ofNat 1024) (UInt256.ofNat 2) then
      ∃ k' C', RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: R) mem aw rdata σ k' C'
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14822⟩ (hook :: fee :: ret :: R) mem aw rdata σ k' C' := by
  apply hookPairTraceCore (test := UInt256.ofNat 14817)
  · intro hz
    have rd1 := poolManagerBlocks.poolManager_block_14806_taken (by simp only [List.length_cons]; omega)
      (by rw [hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14929 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1⟩
  · intro hn
    have rd1 := poolManagerBlocks.poolManager_block_14806_fallthrough (by simp only [List.length_cons]; omega)
      (isZero_eq_zero_of_ne hn) h
    simpa only [poolManagerBlocks.poolManager_block_14806_fallthrough_stack, isZero_eq_zero_of_ne hn] using
      (show ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14817⟩ _ mem aw rdata σ k' C' from ⟨_, _, rd1⟩)
  · intro k1 C1 rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14817_fallthrough (by simp only [List.length_cons]; omega) rfl rd1⟩
  · intro k1 C1 rd1
    have rd2 := poolManagerBlocks.poolManager_block_14817_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14911 (by omega) hret rd2⟩

theorem hookPair3Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret hook fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14822⟩ (hook :: fee :: ret :: R) mem aw rdata σ k C) :
    if hookPairInvalid hook (UInt256.ofNat 256) (UInt256.ofNat 1) then
      ∃ k' C', RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: R) mem aw rdata σ k' C'
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14838⟩ (hook :: fee :: ret :: R) mem aw rdata σ k' C' := by
  apply hookPairTraceCore (test := UInt256.ofNat 14833)
  · intro hz
    have rd1 := poolManagerBlocks.poolManager_block_14822_taken (by simp only [List.length_cons]; omega)
      (by rw [hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14917 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1⟩
  · intro hn
    have rd1 := poolManagerBlocks.poolManager_block_14822_fallthrough (by simp only [List.length_cons]; omega)
      (isZero_eq_zero_of_ne hn) h
    simpa only [poolManagerBlocks.poolManager_block_14822_fallthrough_stack, isZero_eq_zero_of_ne hn] using
      (show ∃ k' C', RD (deployedRuntime v) I g s0 ⟨14833⟩ _ mem aw rdata σ k' C' from ⟨_, _, rd1⟩)
  · intro k1 C1 rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14833_fallthrough (by simp only [List.length_cons]; omega) rfl rd1⟩
  · intro k1 C1 rd1
    have rd2 := poolManagerBlocks.poolManager_block_14833_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14911 (by omega) hret rd2⟩

end Benchmarks.UniswapV4PoolManager
