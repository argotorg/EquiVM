import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.StructAllocMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def StructInitStep (loop done stackSpace : Nat) (fields : List UInt256) : Prop :=
  ∀ {words : String → UInt256} {I g s0 σ mem aw out k C R} {free slot n : Nat},
    memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free →
    free + 32 * fields.length < UInt256.size → slot + 32 < UInt256.size →
    0 < n → n < UInt256.size → R.length + stackSpace ≤ 1024 →
    RD (immutableLayout.runtime attesterBytecode words) I g s0 (UInt256.ofNat loop)
      (UInt256.ofNat slot :: UInt256.ofNat n :: R) mem aw out σ k C →
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0
      (UInt256.ofNat (if n = 1 then done else loop))
      (UInt256.ofNat (slot + 32) :: UInt256.ofNat (n - 1) :: R)
      (structSlotMemory mem free slot fields) aw' out σ k' C'

theorem structInitRun {loop done stackSpace : Nat} {fields : List UInt256}
    (hstep : StructInitStep loop done stackSpace fields) (hne : fields ≠ [])
    {words : String → UInt256} {I g s0 σ mem aw out k C R} {free slot n : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 (UInt256.ofNat loop)
      (UInt256.ofNat slot :: UInt256.ofNat n :: R) mem aw out σ k C)
    (hstack : R.length + stackSpace ≤ 1024) (hfree : 96 ≤ free) (hslot : 96 ≤ slot)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hf : free + 32 * fields.length * n < UInt256.size)
    (hs : slot + 32 * n < UInt256.size) (hn : 0 < n) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 (UInt256.ofNat done)
      (UInt256.ofNat (slot + 32 * n) :: UInt256.ofNat 0 :: R)
      (structSlotsMemory mem free slot fields n) aw' out σ k' C' := by
  have hlen : 0 < fields.length := List.length_pos_iff.mpr hne
  induction n generalizing mem free slot aw k C with
  | zero => omega
  | succ n ih =>
      have hf' : free + 32 * fields.length < UInt256.size := by
        simp only [Nat.mul_succ] at hf; omega
      obtain ⟨aw', k', C', h'⟩ := hstep hptr hf' (by omega) (by omega) (by omega) hstack h
      by_cases hz : n = 0
      · subst n
        exact ⟨aw', k', C', by simpa only [structSlotsMemory] using h'⟩
      have hn1 : n + 1 ≠ 1 := by omega
      simp only [if_neg hn1, Nat.add_sub_cancel] at h'
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' (by omega) (by omega)
        (structSlotMemory_freePtr hfree hslot)
        (by simp only [Nat.mul_succ] at hf; omega) (by omega) (by omega)
      exact ⟨aw'', k'', C'', by simpa only [structSlotsMemory,
        show slot + 32 + 32 * n = slot + 32 * (n + 1) by omega] using h''⟩

def attestDefaultFields : List UInt256 := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨96⟩, ⟨0⟩]

theorem structInitStep1278 : StructInitStep 1278 1371 8 attestDefaultFields := by
  intro words I g s0 σ mem aw out k C R free slot n hptr hfree hslot hn hnfit hstack h
  change free + 192 < UInt256.size at hfree
  have hf : free < UInt256.size := by omega
  have hs : slot < UInt256.size := by omega
  have hf32 : free + 32 < UInt256.size := by omega
  have hf64 : free + 64 < UInt256.size := by omega
  have hf96 : free + 96 < UInt256.size := by omega
  have hf128 : free + 128 < UInt256.size := by omega
  have hf160 : free + 160 < UInt256.size := by omega
  have hsub : UInt256.ofNat n + UInt256.ofNat (UInt256.size - 1) = UInt256.ofNat (n - 1) := by
    rw [u256_add_comm]
    exact ofNat_size_sub_add (by decide) (by omega) hnfit
  change UInt256.ofNat n +
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 =
    UInt256.ofNat (n - 1) at hsub
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_1278_fallthrough_packed
      hstack (by decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_pos rfl, attesterRuntime_block_1278_fallthrough_stack,
      attesterRuntime_block_1278_fallthrough_memory, hptr, hsub,
      ofNat_add_words, ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      ulit_toNat' _ hf64, ulit_toNat' _ hf96, ulit_toNat' _ hf128, ulit_toNat' _ hf160,
      structSlotMemory, attestDefaultFields, List.length_cons, List.length_nil,
      wordSequenceMemory, Reasoning.Theory.writeWord, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using h'
  · have hnz : UInt256.ofNat n +
        UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935
            ≠
        UInt256.ofNat 0 := by
      rw [hsub]
      intro hz
      have hz' := congrArg UInt256.toNat hz
      rw [ulit_toNat' _ (by omega)] at hz'
      change n - 1 = 0 at hz'; omega
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_1278_taken_packed hstack hnz
      (by rw [attesterRuntime_validJumps]; native_decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_neg hn1, attesterRuntime_block_1278_taken_stack,
      attesterRuntime_block_1278_taken_memory, hptr, hsub,
      ofNat_add_words, ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      ulit_toNat' _ hf64, ulit_toNat' _ hf96, ulit_toNat' _ hf128, ulit_toNat' _ hf160,
      structSlotMemory, attestDefaultFields, List.length_cons, List.length_nil,
      wordSequenceMemory, Reasoning.Theory.writeWord, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using h'

theorem structArrayAllocate1221 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free n : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1221⟩
      (UInt256.ofNat n :: R) mem aw out σ k C)
    (hstack : R.length + 11 ≤ 1024) (hfree : 96 ≤ free)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hn : 0 < n) (hcap : n ≤ solcMaxU64) (hfit : free + 32 + 224 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1379⟩
      (⟨0⟩ :: UInt256.ofNat free :: UInt256.ofNat n :: R)
      (structArrayMemory mem free n attestDefaultFields) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by omega
  have hfreefit : free < UInt256.size := by omega
  have hnz : UInt256.ofNat n ≠ ⟨0⟩ := by
    intro hz
    have hz' := congrArg UInt256.toNat hz
    rw [ulit_toNat' _ hnfit] at hz'
    change n = 0 at hz'; omega
  have h' := attesterRuntime_block_1221_taken (by omega)
    (by rw [ugt_zero (by rw [ulit_toNat' _ hnfit]; exact hcap)]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_1248_fallthrough_packed
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) h'
  simp only [attesterRuntime_block_1248_fallthrough_stack,
    attesterRuntime_block_1248_fallthrough_memory, hptr, ofNat_mul_words, ofNat_add_words,
    ulit_toNat' _ hfreefit] at h''
  have h''' := attesterRuntime_block_1274 (by simp only [List.length_cons]; omega) h''
  simp only [attesterRuntime_block_1274_stack, ofNat_add_words] at h'''
  have hmem : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1278⟩
      (UInt256.ofNat (free + 32) :: UInt256.ofNat n :: UInt256.ofNat free ::
        UInt256.ofNat 0 :: UInt256.ofNat n :: R)
      (arrayHeaderMemory mem free n) aw' out σ (k' + 3) (C' + 9) := by
    simpa only [arrayHeaderMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using h'''
  obtain ⟨aw'', k'', C'', hinit⟩ := structInitRun structInitStep1278 (by decide) hmem
    (by simp only [List.length_cons]; omega) (by omega) (by omega)
    (arrayHeaderMemory_freePtr _ _ _)
    (by change free + 32 + 32 * n + 192 * n < UInt256.size; omega) (by omega) hn
  have hpost := attesterRuntime_block_1371 (by simp only [List.length_cons]; omega) hinit
  have hdone := attesterRuntime_block_1373 (by simp only [List.length_cons]; omega) hpost
  exact ⟨_, _, _, hdone⟩

end Benchmarks.EAS.Attester
