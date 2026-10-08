import Benchmarks.EAS.Attester.StructInitTrace
import Benchmarks.EAS.Attester.AttestCellMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiAttestInnerStep {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n i cdptr : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1379⟩
      ([UInt256.ofNat i, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        UInt256.ofNat cdptr] ++ R) mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hni : i < n) (hfree : free + 256 < UInt256.size) (hcd : cdptr + 32 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1379⟩
      ([UInt256.ofNat (i + 1), UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        UInt256.ofNat cdptr] ++ R)
      (attestCellSlotMemory mem free (base + 32 + 32 * i)
        (calldataWord I.calldata (cdptr + 32 * i))) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by omega
  have hifit : i < UInt256.size := by omega
  have hbfit : base < UInt256.size := by omega
  have hffit : free < UInt256.size := by omega
  have hf32 : 32 + free < UInt256.size := by omega
  have hf64 : 32 + (32 + free) < UInt256.size := by omega
  have hf96 : 32 + (32 + (32 + free)) < UInt256.size := by omega
  have hf128 : 32 + (32 + (32 + (32 + free))) < UInt256.size := by omega
  have hf160 : 32 + (32 + (32 + (32 + (32 + free)))) < UInt256.size := by omega
  have hf192 : free + 192 < UInt256.size := by omega
  have hf224 : 32 + (free + 192) < UInt256.size := by omega
  have hdifit : 32 * i + cdptr < UInt256.size := by omega
  have hbifit : 32 * i + base + 32 < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ hifit, ulit_toNat' _ hnfit]; exact hni)
  have h' := attesterRuntime_block_1379_fallthrough
    (R := UInt256.ofNat n :: UInt256.ofNat cdptr :: R)
    (by simp only [List.length_cons]; omega) (by rw [hlt]; rfl) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_1388_taken_packed (R := R)
    hstack (by rw [hlt]; decide) (by rw [attesterRuntime_validJumps]; native_decide) h'
  have hh : attesterRuntime_block_1388_taken_memory (mem := mem) =
      attestCellHeaderMemory mem free := by
    simp only [attesterRuntime_block_1388_taken_memory, hptr, ofNat_add_words,
      ulit_toNat' _ hffit, ulit_toNat' _ hf32, ulit_toNat' _ hf64, ulit_toNat' _ hf96,
      attestCellHeaderMemory, writeCascade, Reasoning.Theory.writeWord,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    simp (disch := omega) only [ulit_toNat', u256_land_zero_right]
    rfl
  simp only [attesterRuntime_block_1388_taken_stack, hh, hptr, ofNat_add_words] at h''
  obtain ⟨aw1, k1, C1, h1⟩ := attesterRuntime_block_1480_packed
    (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  have hhptr := attestCellHeaderMemory_freePtr (mem := mem) (free := free) (by omega)
  have hpptr := attestCellPayloadMemory_freePtr (mem := mem) (free := free)
    (input := calldataWord I.calldata (cdptr + 32 * i)) (by omega)
  have hp : attesterRuntime_block_1480_memory (ee := I)
      (mem := attestCellHeaderMemory mem free) (x0 := UInt256.ofNat i)
      (x2 := UInt256.ofNat cdptr) =
      attestCellPayloadMemory mem free (calldataWord I.calldata (cdptr + 32 * i)) := by
    simp only [attesterRuntime_block_1480_memory, hhptr,
      ofNat_mul_words, ofNat_add_words, ulit_toNat' _ hdifit, ulit_toNat' _ hf224,
      attestCellPayloadMemory, Reasoning.Theory.writeWord, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
    simp (disch := omega) only [ulit_toNat']
  simp only [attesterRuntime_block_1480_stack, hp,
    hhptr, ofNat_add_words] at h1
  have hfields : attesterRuntime_block_1505_taken_memory
      (mem := attestCellPayloadMemory mem free (calldataWord I.calldata (cdptr + 32 * i)))
      (x0 := UInt256.ofNat (32 + (32 + (free + 192))))
      (x1 := UInt256.ofNat (32 + (32 + (32 + (32 + free))))) =
      attestCellMemory mem free (calldataWord I.calldata (cdptr + 32 * i)) := by
    have hsub0 : UInt256.sub (UInt256.ofNat (32 + (32 + (free + 192))))
        (UInt256.ofNat (free + 192)) = ⟨64⟩ := by
      rw [ofNat_sub_words (by omega) (by omega)]
      rw [show 32 + (32 + (free + 192)) - (free + 192) = 64 by omega]
      rfl
    simp only [attesterRuntime_block_1505_taken_memory, hpptr, hsub0]
    simp only [ofNat_add_words, ulit_toNat' _ hf192, ulit_toNat' _ hf128, ulit_toNat' _ hf160,
      attestCellMemory, writeCascade, Reasoning.Theory.writeWord,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    simp (disch := omega) only [ulit_toNat']
    rfl
  have hload : memLoad (UInt256.ofNat base)
      (attestCellMemory mem free (calldataWord I.calldata (cdptr + 32 * i))) = UInt256.ofNat n :=
    ((attestCellMemory_prefix _ _ _).load_preserved hbase (by omega) hin hbfit).trans hlen
  obtain ⟨aw2, k2, C2, h2⟩ := attesterRuntime_block_1505_taken_packed
    (x0 := UInt256.ofNat (32 + (32 + (free + 192))))
    (x1 := UInt256.ofNat (32 + (32 + (32 + (32 + free)))))
    (x2 := UInt256.ofNat free) (x3 := UInt256.ofNat i) (x4 := UInt256.ofNat base)
    (by simp only [List.length_cons]; omega)
    (by change UInt256.lt (UInt256.ofNat i)
          (memLoad (UInt256.ofNat base) (attesterRuntime_block_1505_taken_memory
            (mem := attestCellPayloadMemory mem free (calldataWord I.calldata (cdptr + 32 * i)))
            (x0 := UInt256.ofNat (32 + (32 + (free + 192))))
            (x1 := UInt256.ofNat (32 + (32 + (32 + (32 + free))))))) ≠ _
        rw [hfields, hload, hlt]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h1
  simp only [attesterRuntime_block_1505_taken_stack, hfields] at h2
  obtain ⟨aw3, k3, C3, h3⟩ := attesterRuntime_block_1548_packed
    (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h2
  simp only [attesterRuntime_block_1548_stack, attesterRuntime_block_1548_memory,
    ofNat_add_words, ofNat_mul_words, ulit_toNat' _ hbifit] at h3
  refine ⟨aw3, k3, C3, ?_⟩
  simpa only [attestCellSlotMemory, Reasoning.Theory.writeWord, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using h3

set_option maxRecDepth 1000 in
theorem multiAttestInnerRun {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n i remaining cdptr : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1379⟩
      ([UInt256.ofNat i, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        UInt256.ofNat cdptr] ++ R) mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hi : i + remaining = n) (hfree : free + 256 * remaining < UInt256.size)
    (hcd : cdptr + 32 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1567⟩
      ([UInt256.ofNat n, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        UInt256.ofNat cdptr] ++ R)
      (attestFillMemory mem free (base + 32)
        (fun j ↦ calldataWord I.calldata (cdptr + 32 * j)) i remaining) aw' out σ k' C' := by
  induction remaining generalizing mem free i aw k C with
  | zero =>
      have hi' : i = n := by omega
      subst i
      obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_1379_taken_packed
        (R := UInt256.ofNat n :: UInt256.ofNat cdptr :: R)
        (by simp only [List.length_cons]; omega)
        (by rw [ult_zero (Nat.le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw', k', C', h'⟩
  | succ remaining ih =>
      obtain ⟨aw', k', C', h'⟩ := multiAttestInnerStep h hstack hbase hin hspan hlen hptr
        (by omega) (by omega) hcd
      have hm := attestCellSlotMemory_prefix mem free (base + 32 + 32 * i) (base + 32)
        (calldataWord I.calldata (cdptr + 32 * i)) (by omega) (by omega)
      have hsize := hm.size
      have hl := (hm.load_preserved hbase (le_refl _) hin (by omega)).trans hlen
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' (by omega) (by omega) hl
        (attestCellSlotMemory_freePtr (by omega) (by omega)) (by omega) (by omega)
      exact ⟨aw'', k'', C'', h''⟩

end Benchmarks.EAS.Attester
