import Benchmarks.EAS.Attester.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem wordArrayCopyRun {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {ptr junk : UInt256} {src dst i n : Nat} {values : Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3743⟩
      ([UInt256.ofNat dst, ptr, junk, UInt256.ofNat (src + 32 * n), UInt256.ofNat src] ++ R)
      mem aw out σ k C)
    (hstack : R.length + 8 ≤ 1024) (hlo : 96 ≤ src) (hin : src + 32 * n ≤ mem.size)
    (hdis : src + 32 * n ≤ dst) (hfit : dst + 32 * n < UInt256.size)
    (hloads : ∀ j, j < n → memLoad (UInt256.ofNat (src + 32 * j)) mem = values (i + j)) :
    ∃ aw' k' C' junk', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3771⟩
      ([UInt256.ofNat (dst + 32 * n), ptr, junk', UInt256.ofNat (src + 32 * n),
        UInt256.ofNat (src + 32 * n)] ++ R)
      (wordSequenceMemory mem dst (wordArrayWords values i n)) aw' out σ k' C' := by
  induction n generalizing mem aw k C junk src dst i with
  | zero =>
      obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_3743_taken_packed (R := R) (by omega)
        (by simp only [Nat.mul_zero, Nat.add_zero]; rw [ult_zero (le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw', k', C', junk, h'⟩
  | succ n ih =>
      have hf : src < UInt256.size := by omega
      have he : src + 32 * (n + 1) < UInt256.size := by omega
      have hd : dst < UInt256.size := by omega
      have hlt : UInt256.lt (UInt256.ofNat src) (UInt256.ofNat (src + 32 * (n + 1))) = ⟨1⟩ :=
        ult_one (by rw [ulit_toNat' _ hf, ulit_toNat' _ he]; omega)
      have h1 := attesterRuntime_block_3743_fallthrough (R := R)
        (by omega) (by rw [hlt]; rfl) h
      obtain ⟨aw2, k2, C2, h2⟩ := attesterRuntime_block_3752_packed hstack
        (by rw [attesterRuntime_validJumps]; native_decide) h1
      have hload : memLoad (UInt256.ofNat src) mem = values i := by
        simpa only [Nat.mul_zero, Nat.add_zero] using hloads 0 (by omega)
      simp only [attesterRuntime_block_3752_stack, attesterRuntime_block_3752_memory,
        hload, ofNat_add_words, ulit_toNat' _ hd] at h2
      rw [show 32 + dst = dst + 32 by omega, show 32 + src = src + 32 by omega,
        show src + 32 * (n + 1) = src + 32 + 32 * n by omega] at h2
      have hnext : ∀ j, j < n →
          memLoad (UInt256.ofNat (src + 32 + 32 * j)) (writeWord mem dst (values i)) =
            values (i + 1 + j) := by
        intro j hj
        have hp := memoryPrefix_sparse_writeWord mem dst dst (values i) (.inl (le_refl _))
        rw [hp.load_preserved (by omega) (by omega) (by omega) (by omega),
          show src + 32 + 32 * j = src + 32 * (j + 1) by omega,
          hloads (j + 1) (by omega)]
        congr 1; omega
      obtain ⟨aw3, k3, C3, junk3, h3⟩ := ih h2 (by omega)
        (by rw [wordWrite_size]; omega) (by omega) (by omega) hnext
      refine ⟨aw3, k3, C3, junk3, ?_⟩
      simpa only [wordArrayWords, wordSequenceMemory,
        show src + 32 + 32 * n = src + 32 * (n + 1) by omega,
        show dst + 32 + 32 * n = dst + 32 * (n + 1) by omega] using h3

theorem returnArrayDecode {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {base : Nat} {ret : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3547⟩
      ([UInt256.ofNat base, UInt256.ofNat (base + out.size), ret] ++ R)
      (returnArrayInputMemory mem base out) aw out σ k C)
    (hstack : R.length + 13 ≤ 1024) (hlo : 96 ≤ base) (hb : base ≤ mem.size)
    (hbound : base + out.size + 31 ≤ 2 ^ 200)
    (hret : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    ((¬ ReturnArrayChecks out ∨ ¬ returnArrayEnd base out ≤ solcMaxU64) ∧
      RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
    (ReturnArrayChecks out ∧ returnArrayEnd base out ≤ solcMaxU64 ∧ ∃ aw' k' C',
      RD (immutableLayout.runtime attesterBytecode words) I g s0 ret
        (UInt256.ofNat (returnArrayFree base out) :: R)
        (returnArrayDecodedMemory mem base out) aw' out σ k' C') := by
  rcases returnArrayDecodeStart h
      (by simp only [List.append, List.length_cons]; omega) hlo hb hbound with
    ⟨hbad, hr⟩ | ⟨hc, hcap, aw1, k1, C1, h1⟩
  · exact .inl ⟨hbad, hr⟩
  have hb' := returnArrayFree_bounds base out
  have hd := hc.data
  have hf : returnArrayEnd base out < UInt256.size := by
    change returnArrayEnd base out ≤ 18446744073709551615 at hcap
    change _ < 2 ^ 256; omega
  have hinput := returnArrayInputMemory_size (out := out) hlo hb
  obtain ⟨aw2, k2, C2, junk2, h2⟩ := wordArrayCopyRun (i := 0) h1
    (by simp only [List.append, List.length_cons]; omega) (by omega)
    (by rw [wordArrayHeaderMemory_size _ _ _ (by omega), hinput]; omega) (by omega)
    (by change returnArrayFree base out + 32 + 32 * returnArrayCount out < UInt256.size
        unfold returnArrayEnd at hf; omega)
    (by intro j hj; simpa only [Nat.zero_add] using returnArrayHeaderMemory_data hlo hb hc hj
          (by change _ < 2 ^ 256; omega))
  obtain ⟨aw3, k3, C3, h3⟩ := attesterRuntime_block_3771_packed
    (by simp only [List.append]; omega) hret h2
  exact .inr ⟨hc, hcap, aw3, k3, C3, h3⟩

end Benchmarks.EAS.Attester
