import Benchmarks.UniswapV4PoolManager.HookPairTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: equality and negation of EVM boolean words.
theorem wordEqualBool (a b : UInt256) : UInt256.eq a b = (decide (a = b)).toUInt256 := rfl
theorem wordIsZeroBool (b : Bool) : UInt256.isZero b.toUInt256 = (!b).toUInt256 := by cases b <;> decide

theorem hookBaseValidTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret hook fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hh : hook.toNat < 2^160) (hf : fee.toNat < 2^24)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14838⟩ (hook :: fee :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret ((hookBaseValid hook fee).toUInt256 :: R) mem aw rdata σ k' C' := by
  have hhclean : UInt256.land hook (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = hook :=
    solcAddrMask_clean hh
  have hfclean : UInt256.land (UInt256.ofNat 16777215) fee = fee :=
    (u256_land_comm _ _).trans (u256LandMaskCleanOfToNat _ _ rfl hf)
  by_cases hz : hook = ⟨0⟩
  · have rd1 := poolManagerBlocks.poolManager_block_14838_fallthrough (by simp only [List.length_cons]; omega)
      (hhclean.trans hz) h
    have rd2 := poolManagerBlocks.poolManager_block_14865 (by omega) hret rd1
    simp only [poolManagerBlocks.poolManager_block_14865_stack, hfclean, wordEqualBool, wordIsZeroBool,
      ← decide_not, ne_comm] at rd2
    simp only [hookBaseValid, if_pos hz]
    exact ⟨_, _, rd2⟩
  · have rd1 := poolManagerBlocks.poolManager_block_14838_taken (by simp only [List.length_cons]; omega)
      (fun he => hz (hhclean.symm.trans he)) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hcomm := u256_land_comm (UInt256.ofNat 16383) hook
    by_cases hn : UInt256.land hook (UInt256.ofNat 16383) = ⟨0⟩
    · have rd2 := poolManagerBlocks.poolManager_block_14879_taken (by simp only [List.length_cons]; omega)
        (by rw [hcomm, hn]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have rd3 := poolManagerBlocks.poolManager_block_14896 (by omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_14896_stack, hfclean, wordEqualBool] at rd3
      simp only [hookBaseValid, if_neg hz, hn, ne_eq, not_true_eq_false, decide_false, Bool.false_or]
      exact ⟨_, _, rd3⟩
    · have rd2 := poolManagerBlocks.poolManager_block_14879_fallthrough (by simp only [List.length_cons]; omega)
        (by rw [hcomm]; exact isZero_eq_zero_of_ne hn) rd1
      have rd3 := poolManagerBlocks.poolManager_block_14893 (by omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_14893_stack,
        poolManagerBlocks.poolManager_block_14879_fallthrough_stack, hcomm, wordNonzeroBool, decide_eq_true hn] at rd3
      simp only [hookBaseValid, if_neg hz, decide_eq_true hn, Bool.true_or]
      exact ⟨_, _, rd3⟩

theorem hookValidationTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret hook fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hh : hook.toNat < 2^160) (hf : fee.toNat < 2^24)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14775⟩ (hook :: fee :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret ((hookAddressValid hook fee).toUInt256 :: R) mem aw rdata σ k' C' := by
  have ht0 := hookPair0Trace v hstack hret h
  unfold hookAddressValid
  cases h0 : hookPairInvalid hook (UInt256.ofNat 128) (UInt256.ofNat 8) with
  | true => simpa only [h0, if_true] using ht0
  | false =>
    simp only [h0, Bool.false_eq_true, if_false] at ht0 ⊢
    obtain ⟨k1, C1, rd1⟩ := ht0
    have ht1 := hookPair1Trace v hstack hret rd1
    cases h1 : hookPairInvalid hook (UInt256.ofNat 64) (UInt256.ofNat 4) with
    | true => simpa only [h1, if_true] using ht1
    | false =>
      simp only [h1, Bool.false_eq_true, if_false] at ht1 ⊢
      obtain ⟨k2, C2, rd2⟩ := ht1
      have ht2 := hookPair2Trace v hstack hret rd2
      cases h2 : hookPairInvalid hook (UInt256.ofNat 1024) (UInt256.ofNat 2) with
      | true => simpa only [h2, if_true] using ht2
      | false =>
        simp only [h2, Bool.false_eq_true, if_false] at ht2 ⊢
        obtain ⟨k3, C3, rd3⟩ := ht2
        have ht3 := hookPair3Trace v hstack hret rd3
        cases h3 : hookPairInvalid hook (UInt256.ofNat 256) (UInt256.ofNat 1) with
        | true => simpa only [h3, if_true] using ht3
        | false =>
          simp only [h3, Bool.false_eq_true, if_false] at ht3 ⊢
          obtain ⟨k4, C4, rd4⟩ := ht3
          exact hookBaseValidTrace v hstack hh hf hret rd4

end Benchmarks.UniswapV4PoolManager
