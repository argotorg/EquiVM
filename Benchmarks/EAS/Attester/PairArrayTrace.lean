import Benchmarks.EAS.Attester.PairInitTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem pairArrayAllocate264 {words : String → UInt256} {I g s0 σ mem aw out k C R} {free n : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨264⟩
      (UInt256.ofNat n :: R) mem aw out σ k C)
    (hstack : R.length + 9 ≤ 1024) (hfree : 96 ≤ free)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hn : 0 < n) (hcap : n ≤ solcMaxU64) (hfit : free + 32 + 96 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      (⟨0⟩ :: UInt256.ofNat free :: UInt256.ofNat n :: R)
      (pairArrayMemory mem free n ⟨96⟩) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by omega
  have hfreefit : free < UInt256.size := by omega
  have hnz : UInt256.ofNat n ≠ ⟨0⟩ := by
    intro hz
    have hz' := congrArg UInt256.toNat hz
    rw [ulit_toNat' _ hnfit] at hz'
    change n = 0 at hz'; omega
  have h' := attesterRuntime_block_264_taken (by omega)
    (by rw [ugt_zero (by rw [ulit_toNat' _ hnfit]; exact hcap)]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_291_fallthrough_packed
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) h'
  simp only [attesterRuntime_block_291_fallthrough_stack,
      attesterRuntime_block_291_fallthrough_memory,
    hptr, ofNat_mul_words, ofNat_add_words, ulit_toNat' _ hfreefit] at h''
  have h''' := attesterRuntime_block_317 (by simp only [List.length_cons]; omega) h''
  simp only [attesterRuntime_block_317_stack, ofNat_add_words] at h'''
  have hmem : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨321⟩
      (UInt256.ofNat (free + 32) :: UInt256.ofNat n :: UInt256.ofNat free ::
        UInt256.ofNat 0 :: UInt256.ofNat n :: R)
      (arrayHeaderMemory mem free n) aw' out σ (k' + 3) (C' + 9) := by
    simpa only [arrayHeaderMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm,
        Nat.add_left_comm,
      Nat.add_assoc] using h'''
  obtain ⟨aw'', k'', C'', hinit⟩ := pairInitRun pairInitStep321 hmem
    (by simp only [List.length_cons]; omega) (by omega) (by omega)
    (arrayHeaderMemory_freePtr _ _ _) (by omega) (by omega) hn
  have hpost := attesterRuntime_block_359 (by simp only [List.length_cons]; omega) hinit
  have hdone := attesterRuntime_block_361 (by simp only [List.length_cons]; omega) hpost
  exact ⟨_, _, _, hdone⟩

theorem pairArrayAllocate479 {words : String → UInt256} {I g s0 σ mem aw out k C R} {free n : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨479⟩
      (UInt256.ofNat n :: R) mem aw out σ k C)
    (hstack : R.length + 9 ≤ 1024) (hfree : 96 ≤ free)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hn : 0 < n) (hcap : n ≤ solcMaxU64) (hfit : free + 32 + 96 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨581⟩
      (⟨0⟩ :: UInt256.ofNat free :: UInt256.ofNat n :: R)
      (pairArrayMemory mem free n ⟨0⟩) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by omega
  have hfreefit : free < UInt256.size := by omega
  have hnz : UInt256.ofNat n ≠ ⟨0⟩ := by
    intro hz
    have hz' := congrArg UInt256.toNat hz
    rw [ulit_toNat' _ hnfit] at hz'
    change n = 0 at hz'; omega
  have h' := attesterRuntime_block_479_taken (by omega)
    (by rw [ugt_zero (by rw [ulit_toNat' _ hnfit]; exact hcap)]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_506_fallthrough_packed
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) h'
  simp only [attesterRuntime_block_506_fallthrough_stack,
      attesterRuntime_block_506_fallthrough_memory,
    hptr, ofNat_mul_words, ofNat_add_words, ulit_toNat' _ hfreefit] at h''
  have h''' := attesterRuntime_block_532 (by simp only [List.length_cons]; omega) h''
  simp only [attesterRuntime_block_532_stack, ofNat_add_words] at h'''
  have hmem : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨536⟩
      (UInt256.ofNat (free + 32) :: UInt256.ofNat n :: UInt256.ofNat free ::
        UInt256.ofNat 0 :: UInt256.ofNat n :: R)
      (arrayHeaderMemory mem free n) aw' out σ (k' + 3) (C' + 9) := by
    simpa only [arrayHeaderMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm,
        Nat.add_left_comm,
      Nat.add_assoc] using h'''
  obtain ⟨aw'', k'', C'', hinit⟩ := pairInitRun pairInitStep536 hmem
    (by simp only [List.length_cons]; omega) (by omega) (by omega)
    (arrayHeaderMemory_freePtr _ _ _) (by omega) (by omega) hn
  have hpost := attesterRuntime_block_573 (by simp only [List.length_cons]; omega) hinit
  have hdone := attesterRuntime_block_575 (by simp only [List.length_cons]; omega) hpost
  exact ⟨_, _, _, hdone⟩

theorem pairArrayAllocate1006 {words : String → UInt256} {I g s0 σ mem aw out k C R} {free n : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1006⟩
      (UInt256.ofNat n :: R) mem aw out σ k C)
    (hstack : R.length + 9 ≤ 1024) (hfree : 96 ≤ free)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hn : 0 < n) (hcap : n ≤ solcMaxU64) (hfit : free + 32 + 96 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1109⟩
      (⟨0⟩ :: UInt256.ofNat free :: UInt256.ofNat n :: R)
      (pairArrayMemory mem free n ⟨96⟩) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by omega
  have hfreefit : free < UInt256.size := by omega
  have hnz : UInt256.ofNat n ≠ ⟨0⟩ := by
    intro hz
    have hz' := congrArg UInt256.toNat hz
    rw [ulit_toNat' _ hnfit] at hz'
    change n = 0 at hz'; omega
  have h' := attesterRuntime_block_1006_taken (by omega)
    (by rw [ugt_zero (by rw [ulit_toNat' _ hnfit]; exact hcap)]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_1033_fallthrough_packed
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) h'
  simp only [attesterRuntime_block_1033_fallthrough_stack,
      attesterRuntime_block_1033_fallthrough_memory,
    hptr, ofNat_mul_words, ofNat_add_words, ulit_toNat' _ hfreefit] at h''
  have h''' := attesterRuntime_block_1059 (by simp only [List.length_cons]; omega) h''
  simp only [attesterRuntime_block_1059_stack, ofNat_add_words] at h'''
  have hmem : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1063⟩
      (UInt256.ofNat (free + 32) :: UInt256.ofNat n :: UInt256.ofNat free ::
        UInt256.ofNat 0 :: UInt256.ofNat n :: R)
      (arrayHeaderMemory mem free n) aw' out σ (k' + 3) (C' + 9) := by
    simpa only [arrayHeaderMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm,
        Nat.add_left_comm,
      Nat.add_assoc] using h'''
  obtain ⟨aw'', k'', C'', hinit⟩ := pairInitRun pairInitStep1063 hmem
    (by simp only [List.length_cons]; omega) (by omega) (by omega)
    (arrayHeaderMemory_freePtr _ _ _) (by omega) (by omega) hn
  have hpost := attesterRuntime_block_1101 (by simp only [List.length_cons]; omega) hinit
  have hdone := attesterRuntime_block_1103 (by simp only [List.length_cons]; omega) hpost
  exact ⟨_, _, _, hdone⟩

end Benchmarks.EAS.Attester
