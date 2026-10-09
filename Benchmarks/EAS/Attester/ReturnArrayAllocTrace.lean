import Benchmarks.EAS.Attester.ReturnArrayHeadTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def returnArrayEnd (base : Nat) (out : ByteArray) : Nat :=
  returnArrayFree base out + 32 * (returnArrayCount out + 1)

def wordArrayHeaderMemory (mem : ByteArray) (free n : Nat) : ByteArray :=
  writeWord (writeWord mem 64 (UInt256.ofNat (free + 32 * (n + 1)))) free (UInt256.ofNat n)

theorem wordArrayAllocRound {n : Nat} (hn : n ≤ solcMaxU64) :
    UInt256.land (UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) + UInt256.ofNat 63)
      (UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904) =
      UInt256.ofNat (32 * (n + 1)) := by
  change n ≤ 18446744073709551615 at hn
  have hf : 32 * n < UInt256.size := by change _ < 2 ^ 256; omega
  rw [show UInt256.ofNat 5 = (⟨5⟩ : UInt256) from rfl, shiftLeft5_ofNat_eq hf]
  change UInt256.land (UInt256.ofNat (32 * n) + ⟨63⟩) (UInt256.lnot ⟨31⟩) = _
  rw [u256_land_comm, alloc_round _ n (ulit_toNat' _ hf)
    (by rw [ulit_toNat' _ hf]; omega)]
  rw [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl, ofNat_add_words]
  congr 1

theorem returnArrayAllocate {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {free n : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3631⟩
      (UInt256.ofNat n :: R) mem aw out σ k C)
    (hstack : R.length + 7 ≤ 1024)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hfree : free ≤ 2 ^ 200) (hn : n ≤ solcMaxU64) :
    (¬ free + 32 * (n + 1) ≤ solcMaxU64 ∧
      RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
    (free + 32 * (n + 1) ≤ solcMaxU64 ∧ ∃ aw' k' C',
      RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3706⟩
        ([UInt256.ofNat (free + 32 * (n + 1)), UInt256.ofNat free,
          UInt256.ofNat (32 * n), UInt256.ofNat n] ++ R) mem aw' out σ k' C') := by
  have hnf : 32 * n < UInt256.size := by
    change n ≤ 18446744073709551615 at hn
    change _ < 2 ^ 256; omega
  have hff : free < UInt256.size := by change _ < 2 ^ 256; omega
  have hef : free + 32 * (n + 1) < UInt256.size := by
    change n ≤ 18446744073709551615 at hn
    change _ < 2 ^ 256; omega
  have hlt : UInt256.lt (UInt256.ofNat (free + 32 * (n + 1))) (UInt256.ofNat free) = ⟨0⟩ :=
    ult_zero (by rw [ulit_toNat' _ hff, ulit_toNat' _ hef]; omega)
  by_cases hcap : free + 32 * (n + 1) ≤ solcMaxU64
  · obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_3631_taken_packed hstack
      (by rw [hptr, wordArrayAllocRound hn, ofNat_add_words, hlt, u256_lor_zero,
          ugt_zero (by rw [ulit_toNat' _ hef]; exact hcap)]; decide)
      (by rw [attesterRuntime_validJumps]; native_decide) h
    refine .inr ⟨hcap, aw', k', C', ?_⟩
    simp only [attesterRuntime_block_3631_taken_stack, hptr, wordArrayAllocRound hn] at h'
    simpa only [ofNat_add_words, show UInt256.ofNat 5 = (⟨5⟩ : UInt256) from rfl,
      shiftLeft5_ofNat_eq hnf] using h'
  · have h' := attesterRuntime_block_3631_fallthrough hstack
      (by rw [hptr, wordArrayAllocRound hn, ofNat_add_words, hlt, u256_lor_zero,
          ugt_one (by rw [ulit_toNat' 18446744073709551615 (by decide), ulit_toNat' _ hef]
                      exact Nat.lt_of_not_ge hcap)]; rfl) h
    have h'' := attesterRuntime_block_3699
      (by simp only [attesterRuntime_block_3631_fallthrough_stack, List.length_cons]; omega)
      (by rw [attesterRuntime_validJumps]; native_decide) h'
    exact .inl ⟨hcap, attesterRuntime_block_2696
      (by simp only [attesterRuntime_block_3699_stack,
        attesterRuntime_block_3631_fallthrough_stack, List.length_cons]; omega) h''⟩

theorem returnArrayDecodeStart {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {base : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3547⟩
      (UInt256.ofNat base :: UInt256.ofNat (base + out.size) :: R)
      (returnArrayInputMemory mem base out) aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hlo : 96 ≤ base) (hb : base ≤ mem.size)
    (hbound : base + out.size + 31 ≤ 2 ^ 200) :
    ((¬ ReturnArrayChecks out ∨ ¬ returnArrayEnd base out ≤ solcMaxU64) ∧
      RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
    (ReturnArrayChecks out ∧ returnArrayEnd base out ≤ solcMaxU64 ∧ ∃ aw' k' C',
      RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3743⟩
        ([UInt256.ofNat (returnArrayFree base out + 32), UInt256.ofNat (returnArrayFree base out),
          UInt256.ofNat (32 * returnArrayCount out),
          UInt256.ofNat (base + returnArrayOffset out + 32 + 32 * returnArrayCount out),
          UInt256.ofNat (base + returnArrayOffset out + 32), ⟨0⟩, UInt256.ofNat base,
          UInt256.ofNat (base + out.size)] ++ R)
        (wordArrayHeaderMemory (returnArrayInputMemory mem base out)
          (returnArrayFree base out) (returnArrayCount out)) aw' out σ k' C') := by
  rcases returnArrayDecodeHeader h (by omega) hlo hb hbound with ⟨hbad, hr⟩ | ⟨hc, aw1, k1, C1, h1⟩
  · exact .inl ⟨.inl (fun hh ↦ hbad hh.header), hr⟩
  obtain ⟨hhead, hoff, hword, hcount⟩ := hc
  rcases returnArrayAllocate h1 (by simp only [List.append, List.length_cons]; omega)
      (returnArrayInputMemory_freePtr _ _ _)
      (by have := (returnArrayFree_bounds base out).2; omega) hcount with
    ⟨hbad, hr⟩ | ⟨hcap, aw2, k2, C2, h2⟩
  · exact .inl ⟨.inr hbad, hr⟩
  simp only [List.append] at h2
  have hsrc : 32 + (base + returnArrayOffset out + 32 * returnArrayCount out) < UInt256.size := by
    change returnArrayOffset out ≤ 18446744073709551615 at hoff
    change returnArrayCount out ≤ 18446744073709551615 at hcount
    change _ < 2 ^ 256; omega
  have he : base + out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hf : returnArrayFree base out < UInt256.size := by
    change returnArrayFree base out + 32 * (returnArrayCount out + 1) ≤
      18446744073709551615 at hcap
    change _ < 2 ^ 256; omega
  by_cases hdata : returnArrayOffset out + 32 + 32 * returnArrayCount out ≤ out.size
  · obtain ⟨aw3, k3, C3, h3⟩ := attesterRuntime_block_3706_taken_packed (by omega)
      (by rw [ofNat_add_words, ofNat_add_words, ugt_zero
            (by rw [ulit_toNat' _ hsrc, ulit_toNat' _ he]; omega)]; decide)
      (by rw [attesterRuntime_validJumps]; native_decide) h2
    simp only [attesterRuntime_block_3706_taken_stack] at h3
    have h4 := attesterRuntime_block_3736 (by simp only [List.length_cons]; omega) h3
    refine .inr ⟨⟨hhead, hoff, hword, hcount, hdata⟩, hcap, aw3, k3 + 6, C3 + 15, ?_⟩
    simpa only [attesterRuntime_block_3736_stack, attesterRuntime_block_3706_taken_memory,
      wordArrayHeaderMemory, Reasoning.Theory.writeWord, ofNat_add_words, ulit_toNat' _ hf,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h4
  · have h3 := attesterRuntime_block_3706_fallthrough (by omega)
      (by rw [ofNat_add_words, ofNat_add_words, ugt_one
            (by rw [ulit_toNat' _ he, ulit_toNat' _ hsrc]; omega)]; rfl) h2
    refine .inl ⟨.inl (fun hh ↦ hdata hh.data), ?_⟩
    exact attesterRuntime_block_3732
      (by simp only [attesterRuntime_block_3706_fallthrough_stack, List.length_cons]; omega) h3

end Benchmarks.EAS.Attester
