import Benchmarks.EAS.Attester.PairArrayTrace
import Benchmarks.EAS.Attester.PairFillMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiRevokeInnerStep {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n i cdptr : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨581⟩
      ([UInt256.ofNat i, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
          UInt256.ofNat cdptr] ++ R)
      mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hni : i < n) (hfree : free + 64 < UInt256.size) (hcd : cdptr + 32 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨581⟩
      ([UInt256.ofNat (i + 1), UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
          UInt256.ofNat cdptr] ++ R)
      (pairSlotMemory mem free (base + 32 + 32 * i) (calldataWord I.calldata (cdptr + 32 * i)) ⟨0⟩)
      aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by omega
  have hifit : i < UInt256.size := by omega
  have hffit : free < UInt256.size := by omega
  have hbfit : base < UInt256.size := by omega
  have hf32 : 32 + free < UInt256.size := by omega
  have hdifit : 32 * i + cdptr < UInt256.size := by omega
  have hbifit : 32 * i + base + 32 < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ hifit, ulit_toNat' _ hnfit]; exact hni)
  have h' := attesterRuntime_block_581_fallthrough
    (R := UInt256.ofNat n :: UInt256.ofNat cdptr :: R)
    (by simp only [List.length_cons]; omega)
    (by rw [hlt]; rfl) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_590_taken_packed (R := R)
    (by omega)
    (by rw [hlt]; decide) (by rw [attesterRuntime_validJumps]; native_decide) h'
  simp only [attesterRuntime_block_590_taken_stack, attesterRuntime_block_590_taken_memory,
    hptr, ofNat_add_words] at h''
  have hfields : attesterRuntime_block_618_taken_memory (ee := I)
      (mem := (UInt256.ofNat (64 + free)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)
      (x0 := UInt256.ofNat i) (x2 := UInt256.ofNat cdptr) (x3 := UInt256.ofNat free) =
      pairStructMemory mem free (calldataWord I.calldata (cdptr + 32 * i)) ⟨0⟩ := by
    simp only [attesterRuntime_block_618_taken_memory, ofNat_mul_words, ofNat_add_words,
      ulit_toNat' _ hffit, ulit_toNat' _ hf32, ulit_toNat' _ hdifit,
      pairStructMemory, writeCascade, Reasoning.Theory.writeWord]
    simp only [Nat.add_comm]
    rfl
  have hload : memLoad (UInt256.ofNat base)
      (pairStructMemory mem free (calldataWord I.calldata (cdptr + 32 * i)) ⟨0⟩) = UInt256.ofNat n
          :=
    ((pairStructMemory_prefix _ _ _ _).load_preserved hbase (by omega) hin hbfit).trans hlen
  obtain ⟨aw'', k'', C'', h'''⟩ := attesterRuntime_block_618_taken_packed
    (x0 := UInt256.ofNat i) (x1 := UInt256.ofNat n) (x2 := UInt256.ofNat cdptr)
    (x3 := UInt256.ofNat free) (x4 := UInt256.ofNat free)
    (x5 := UInt256.ofNat i) (x6 := UInt256.ofNat base)
    (by simp only [List.length_cons]; omega)
    (by change UInt256.lt (UInt256.ofNat i)
          (memLoad (UInt256.ofNat base) (attesterRuntime_block_618_taken_memory
            (ee := I) (mem := (UInt256.ofNat (64 + free)).toByteArray.write 0 mem (UInt256.ofNat
                64).toNat 32)
            (x0 := UInt256.ofNat i) (x2 := UInt256.ofNat cdptr) (x3 := UInt256.ofNat free))) ≠ _
        rw [hfields, hload, hlt]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  simp only [attesterRuntime_block_618_taken_stack, hfields] at h'''
  obtain ⟨awf, kf, Cf, hf⟩ := attesterRuntime_block_653_packed
    (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h'''
  refine ⟨awf, kf, Cf, ?_⟩
  simp only [attesterRuntime_block_653_stack, attesterRuntime_block_653_memory,
    ofNat_mul_words, ofNat_add_words, ulit_toNat' _ hbifit] at hf
  simpa only [pairStructMemory, pairSlotMemory, writeCascade, Reasoning.Theory.writeWord,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf

theorem multiRevokeInnerRun {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n i remaining cdptr : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨581⟩
      ([UInt256.ofNat i, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        UInt256.ofNat cdptr] ++ R) mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hi : i + remaining = n) (hfree : free + 64 * remaining < UInt256.size)
    (hcd : cdptr + 32 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨672⟩
      ([UInt256.ofNat n, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        UInt256.ofNat cdptr] ++ R)
      (pairFillMemory mem free (base + 32)
        (fun j ↦ (calldataWord I.calldata (cdptr + 32 * j), ⟨0⟩)) i remaining)
      aw' out σ k' C' := by
  induction remaining generalizing mem free i aw k C with
  | zero =>
      have hi' : i = n := by omega
      subst i
      obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_581_taken_packed
        (R := UInt256.ofNat n :: UInt256.ofNat cdptr :: R)
        (by simp only [List.length_cons]; omega)
        (by rw [ult_zero (Nat.le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw', k', C', h'⟩
  | succ remaining ih =>
      obtain ⟨aw', k', C', h'⟩ := multiRevokeInnerStep h hstack hbase hin hspan hlen hptr
        (by omega) (by omega) hcd
      have hm := pairSlotMemory_prefix mem free (base + 32 + 32 * i) (base + 32)
        (calldataWord I.calldata (cdptr + 32 * i)) ⟨0⟩ (by omega) (by omega)
      have hsize := hm.size
      have hl := (hm.load_preserved hbase (le_refl _) hin (by omega)).trans hlen
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' (by omega) (by omega) hl
        (pairSlotMemory_freePtr (by omega) (by omega)) (by omega) (by omega)
      exact ⟨aw'', k'', C'', h''⟩

end Benchmarks.EAS.Attester
