import Benchmarks.EAS.Attester.ReturnArrayMemory
import Benchmarks.EAS.Attester.ReturnArrayABI
import Benchmarks.EAS.Attester.NestedBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def ReturnArrayHeaderChecks (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ returnArrayOffset out ≤ solcMaxU64 ∧
    returnArrayOffset out + 32 ≤ out.size ∧ returnArrayCount out ≤ solcMaxU64

theorem ReturnArrayChecks.header {out : ByteArray} (h : ReturnArrayChecks out) :
    ReturnArrayHeaderChecks out := ⟨h.head, h.offset, h.lengthWord, h.length⟩

theorem returnArrayDecodeHeader {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {base : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3547⟩
      (UInt256.ofNat base :: UInt256.ofNat (base + out.size) :: R)
      (returnArrayInputMemory mem base out) aw out σ k C)
    (hstack : R.length + 10 ≤ 1024) (hlo : 96 ≤ base) (hb : base ≤ mem.size)
    (hbound : base + out.size + 31 ≤ 2 ^ 200) :
    (¬ ReturnArrayHeaderChecks out ∧ RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
    (ReturnArrayHeaderChecks out ∧ ∃ aw' k' C',
      RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3631⟩
        ([UInt256.ofNat (returnArrayCount out), UInt256.ofNat (base + returnArrayOffset out),
          ⟨0⟩, UInt256.ofNat base, UInt256.ofNat (base + out.size)] ++ R)
        (returnArrayInputMemory mem base out) aw' out σ k' C') := by
  have hsign : out.size < 2 ^ 255 := by omega
  have hfit : base + out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hbase : base < UInt256.size := by omega
  have hsub : UInt256.sub (UInt256.ofNat (base + out.size)) (UInt256.ofNat base) =
      UInt256.ofNat out.size := by
    rw [ofNat_sub_words (by omega) hfit, Nat.add_sub_cancel_left]
  by_cases hhead : 32 ≤ out.size
  · have hslt : UInt256.slt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ :=
      slt_ofNat_lit_zero (by decide) hhead hsign
    have h1 := attesterRuntime_block_3547_taken (by omega)
      (by rw [hsub, hslt]; decide)
      (by rw [attesterRuntime_validJumps]; native_decide) h
    have hload : memLoad (UInt256.ofNat base) (returnArrayInputMemory mem base out) =
        UInt256.ofNat (returnArrayOffset out) := by
      have hh := returnArrayInputMemory_load (off := 0) hlo hb (by omega) (by omega)
      simpa only [Nat.add_zero, returnArrayOffset, u256_ofNat_toNat] using hh
    by_cases hoff : returnArrayOffset out ≤ solcMaxU64
    · obtain ⟨aw2, k2, C2, h2⟩ := attesterRuntime_block_3565_taken_packed
        (by simp only [List.length_cons]; omega)
        (by rw [hload, ugt_zero (by
              rw [ulit_toNat' _ (by
                change (calldataWord out 0).toNat < UInt256.size
                exact (calldataWord out 0).val.isLt)]
              exact hoff)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h1
      simp only [attesterRuntime_block_3565_taken_stack, hload,
        attesterRuntime_block_3547_taken_stack] at h2
      have ho : base + returnArrayOffset out + 31 < 2 ^ 255 := by
        change returnArrayOffset out ≤ 18446744073709551615 at hoff
        omega
      have hend : (UInt256.ofNat (base + out.size)).toNat < 2 ^ 255 := by
        rw [ulit_toNat' _ hfit]; omega
      have hgt : UInt256.sgt (UInt256.ofNat (base + out.size))
          ((UInt256.ofNat base + UInt256.ofNat (returnArrayOffset out)) + UInt256.ofNat 31) =
          UInt256.sgt (UInt256.ofNat (base + out.size))
            (UInt256.ofNat (base + returnArrayOffset out + 31)) := by rw [ofNat_add_words,
                ofNat_add_words]
      by_cases hword : returnArrayOffset out + 32 ≤ out.size
      · have hsgt := sgt_lit_one (a := UInt256.ofNat (base + out.size)) ho
          (by rw [ulit_toNat' _ hfit]; omega) hend
        have h3 := attesterRuntime_block_3588_taken
          (by omega) (by rw [hgt, hsgt]; decide)
          (by rw [attesterRuntime_validJumps]; native_decide) h2
        simp only [attesterRuntime_block_3588_taken_stack, ofNat_add_words] at h3
        have hlen : memLoad (UInt256.ofNat (base + returnArrayOffset out))
            (returnArrayInputMemory mem base out) = UInt256.ofNat (returnArrayCount out) := by
          have hh := returnArrayInputMemory_load hlo hb hword
            (by change _ < 2 ^ 256; omega)
          simpa only [returnArrayCount, u256_ofNat_toNat] using hh
        by_cases hcount : returnArrayCount out ≤ solcMaxU64
        · obtain ⟨aw4, k4, C4, h4⟩ := attesterRuntime_block_3605_taken_packed
            (by simp only [List.length_cons]; omega)
            (by rw [hlen, ugt_zero (by
                  rw [ulit_toNat' 18446744073709551615 (by decide), ulit_toNat' _ (by
                    change (calldataWord out (returnArrayOffset out)).toNat < UInt256.size
                    exact (calldataWord out (returnArrayOffset out)).val.isLt)]
                  exact hcount)]; decide)
            (by rw [attesterRuntime_validJumps]; native_decide) h3
          refine .inr ⟨⟨hhead, hoff, hword, hcount⟩, aw4, k4, C4, ?_⟩
          simpa only [attesterRuntime_block_3605_taken_stack, hlen] using h4
        · have h4 := attesterRuntime_block_3605_fallthrough
            (by simp only [List.length_cons]; omega)
            (by rw [hlen, ugt_one (by
                  rw [ulit_toNat' 18446744073709551615 (by decide), ulit_toNat' _ (by
                    change (calldataWord out (returnArrayOffset out)).toNat < UInt256.size
                    exact (calldataWord out (returnArrayOffset out)).val.isLt)]
                  exact Nat.lt_of_not_ge hcount)]; rfl) h3
          have h5 := attesterRuntime_block_3624
            (by simp only [attesterRuntime_block_3605_fallthrough_stack, List.length_cons]; omega)
            (by rw [attesterRuntime_validJumps]; native_decide) h4
          refine .inl ⟨fun hc ↦ hcount hc.2.2.2, ?_⟩
          exact attesterRuntime_block_2696
            (by simp only [attesterRuntime_block_3624_stack,
              attesterRuntime_block_3605_fallthrough_stack, List.length_cons]; omega) h5
      · have hsgt : UInt256.sgt (UInt256.ofNat (base + out.size))
            (UInt256.ofNat (base + returnArrayOffset out + 31)) = ⟨0⟩ :=
          sgt_zero_low hend (by rw [ulit_toNat' _ (lt_size_of_lt_sign ho)]; exact ho)
            (by rw [ulit_toNat' _ hfit, ulit_toNat' _ (lt_size_of_lt_sign ho)]; omega)
        have h3 := attesterRuntime_block_3588_fallthrough
          (by omega) (by rw [hgt, hsgt]; rfl) h2
        refine .inl ⟨fun hc ↦ hword hc.2.2.1, ?_⟩
        exact attesterRuntime_block_3601
          (by simp only [attesterRuntime_block_3588_fallthrough_stack, List.length_cons]; omega) h3
    · have h2 := attesterRuntime_block_3565_fallthrough
        (by simp only [List.length_cons]; omega)
        (by rw [hload, ugt_one (by
              rw [ulit_toNat' 18446744073709551615 (by decide), ulit_toNat' _ (by
                change (calldataWord out 0).toNat < UInt256.size
                exact (calldataWord out 0).val.isLt)]
              exact Nat.lt_of_not_ge hoff)]; rfl) h1
      refine .inl ⟨fun hc ↦ hoff hc.2.1, ?_⟩
      exact attesterRuntime_block_3584
        (by simp only [attesterRuntime_block_3565_fallthrough_stack,
          attesterRuntime_block_3547_taken_stack, List.length_cons]; omega) h2
  · have hslt : UInt256.slt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ :=
      slt_ofNat_lit_one_low (by decide) (by omega)
    have h1 := attesterRuntime_block_3547_fallthrough (by omega) (by rw [hsub, hslt]; rfl) h
    refine .inl ⟨fun hc ↦ hhead hc.1, ?_⟩
    exact attesterRuntime_block_3561
      (by simp only [attesterRuntime_block_3547_fallthrough_stack, List.length_cons]; omega) h1

end Benchmarks.EAS.Attester
