import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.PairAllocMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def PairInitStep (loop done : Nat) (second : UInt256) : Prop :=
  ∀ {words : String → UInt256} {I g s0 σ mem aw out k C R} {free slot n : Nat},
    memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free →
    free + 64 < UInt256.size → slot + 32 < UInt256.size →
    0 < n → n < UInt256.size → R.length + 6 ≤ 1024 →
    RD (immutableLayout.runtime attesterBytecode words) I g s0 (UInt256.ofNat loop)
      (UInt256.ofNat slot :: UInt256.ofNat n :: R) mem aw out σ k C →
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0
      (UInt256.ofNat (if n = 1 then done else loop))
      (UInt256.ofNat (slot + 32) :: UInt256.ofNat (n - 1) :: R)
      (pairSlotMemory mem free slot ⟨0⟩ second) aw' out σ k' C'

theorem pairInitStep321 : PairInitStep 321 359 ⟨96⟩ := by
  intro words I g s0 σ mem aw out k C R free slot n hptr hfree hslot hn hnfit hstack h
  have hf : free < UInt256.size := by omega
  have hs : slot < UInt256.size := by omega
  have hf32 : free + 32 < UInt256.size := by omega
  have hsub := ofNat_sub_words (b := 1) (by omega : 1 ≤ n) hnfit
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_321_fallthrough_packed hstack (by decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_pos rfl, attesterRuntime_block_321_fallthrough_stack,
      attesterRuntime_block_321_fallthrough_memory, hptr, ofNat_add_words, hsub,
      ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      pairSlotMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm] using h'
  · have hnz : UInt256.sub (UInt256.ofNat n) (UInt256.ofNat 1) ≠ UInt256.ofNat 0 := by
      rw [hsub]
      intro hz
      have hz' := congrArg UInt256.toNat hz
      rw [ulit_toNat' _ (by omega)] at hz'
      change n - 1 = 0 at hz'; omega
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_321_taken_packed hstack hnz
      (by rw [attesterRuntime_validJumps]; native_decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_neg hn1, attesterRuntime_block_321_taken_stack,
      attesterRuntime_block_321_taken_memory, hptr, ofNat_add_words, hsub,
      ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      pairSlotMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm] using h'

theorem pairInitStep536 : PairInitStep 536 573 ⟨0⟩ := by
  intro words I g s0 σ mem aw out k C R free slot n hptr hfree hslot hn hnfit hstack h
  have hf : free < UInt256.size := by omega
  have hs : slot < UInt256.size := by omega
  have hf32 : free + 32 < UInt256.size := by omega
  have hsub := ofNat_sub_words (b := 1) (by omega : 1 ≤ n) hnfit
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_536_fallthrough_packed hstack (by decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_pos rfl, attesterRuntime_block_536_fallthrough_stack,
      attesterRuntime_block_536_fallthrough_memory, hptr, ofNat_add_words, hsub,
      ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      pairSlotMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm] using h'
  · have hnz : UInt256.sub (UInt256.ofNat n) (UInt256.ofNat 1) ≠ UInt256.ofNat 0 := by
      rw [hsub]
      intro hz
      have hz' := congrArg UInt256.toNat hz
      rw [ulit_toNat' _ (by omega)] at hz'
      change n - 1 = 0 at hz'; omega
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_536_taken_packed hstack hnz
      (by rw [attesterRuntime_validJumps]; native_decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_neg hn1, attesterRuntime_block_536_taken_stack,
      attesterRuntime_block_536_taken_memory, hptr, ofNat_add_words, hsub,
      ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      pairSlotMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm] using h'

theorem pairInitStep1063 : PairInitStep 1063 1101 ⟨96⟩ := by
  intro words I g s0 σ mem aw out k C R free slot n hptr hfree hslot hn hnfit hstack h
  have hf : free < UInt256.size := by omega
  have hs : slot < UInt256.size := by omega
  have hf32 : free + 32 < UInt256.size := by omega
  have hsub := ofNat_sub_words (b := 1) (by omega : 1 ≤ n) hnfit
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_1063_fallthrough_packed hstack (by decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_pos rfl, attesterRuntime_block_1063_fallthrough_stack,
      attesterRuntime_block_1063_fallthrough_memory, hptr, ofNat_add_words, hsub,
      ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      pairSlotMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm] using h'
  · have hnz : UInt256.sub (UInt256.ofNat n) (UInt256.ofNat 1) ≠ UInt256.ofNat 0 := by
      rw [hsub]
      intro hz
      have hz' := congrArg UInt256.toNat hz
      rw [ulit_toNat' _ (by omega)] at hz'
      change n - 1 = 0 at hz'; omega
    obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_1063_taken_packed hstack hnz
      (by rw [attesterRuntime_validJumps]; native_decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_neg hn1, attesterRuntime_block_1063_taken_stack,
      attesterRuntime_block_1063_taken_memory, hptr, ofNat_add_words, hsub,
      ulit_toNat' _ hf, ulit_toNat' _ hs, ulit_toNat' _ hf32,
      pairSlotMemory, writeCascade, Reasoning.Theory.writeWord, Nat.add_comm] using h'

theorem pairInitRun {loop done : Nat} {second : UInt256} (hstep : PairInitStep loop done second)
    {words : String → UInt256} {I g s0 σ mem aw out k C R} {free slot n : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 (UInt256.ofNat loop)
      (UInt256.ofNat slot :: UInt256.ofNat n :: R) mem aw out σ k C)
    (hstack : R.length + 6 ≤ 1024) (hfree : 96 ≤ free) (hslot : 96 ≤ slot)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hf : free + 64 * n < UInt256.size) (hs : slot + 32 * n < UInt256.size)
    (hn : 0 < n) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 (UInt256.ofNat done)
      (UInt256.ofNat (slot + 32 * n) :: UInt256.ofNat 0 :: R)
      (pairSlotsMemory mem free slot second n) aw' out σ k' C' := by
  induction n generalizing mem free slot aw k C with
  | zero => omega
  | succ n ih =>
      obtain ⟨aw', k', C', h'⟩ := hstep hptr (by omega) (by omega) (by omega) (by omega) hstack h
      by_cases hz : n = 0
      · subst n
        exact ⟨aw', k', C', by simpa only [pairSlotsMemory] using h'⟩
      have hn1 : n + 1 ≠ 1 := by omega
      simp only [if_neg hn1, Nat.add_sub_cancel] at h'
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' (by omega) (by omega)
        (pairSlotMemory_freePtr hfree hslot) (by omega) (by omega) (by omega)
      exact ⟨aw'', k'', C'', by simpa only [pairSlotsMemory,
        show slot + 32 + 32 * n = slot + 32 * (n + 1) by omega] using h''⟩

end Benchmarks.EAS.Attester
