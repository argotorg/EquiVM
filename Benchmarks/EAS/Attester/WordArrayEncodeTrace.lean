import Benchmarks.EAS.Attester.WordArrayCopyTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def wordArrayEncodeMemory (mem : ByteArray) (dst n : Nat) (values : Nat → UInt256) : ByteArray :=
  wordSequenceMemory mem dst ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n)

theorem wordArrayEncodeRun {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {src dst i n remaining : Nat} {values : Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2621⟩
      ([UInt256.ofNat i, UInt256.ofNat n, UInt256.ofNat dst, UInt256.ofNat src] ++ R)
      mem aw out σ k C)
    (hstack : R.length + 6 ≤ 1024) (hlo : 96 ≤ src)
    (hin : src + 32 * remaining ≤ mem.size) (hdis : src + 32 * remaining ≤ dst)
    (hfit : dst + 32 * remaining < UInt256.size) (hn : n < UInt256.size)
    (hi : i + remaining = n)
    (hloads : ∀ j, j < remaining →
      memLoad (UInt256.ofNat (src + 32 * j)) mem = values (i + j)) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2651⟩
      ([UInt256.ofNat n, UInt256.ofNat n, UInt256.ofNat (dst + 32 * remaining),
        UInt256.ofNat (src + 32 * remaining)] ++ R)
      (wordSequenceMemory mem dst (wordArrayWords values i remaining)) aw' out σ k' C' := by
  induction remaining generalizing mem aw k C src dst i with
  | zero =>
      have heq : i = n := by omega
      subst i
      obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_2621_taken_packed
        (by simp only [List.append, List.length_cons]; omega)
        (by rw [ult_zero (le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw', k', C', h'⟩
  | succ remaining ih =>
      have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
        ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hn]; omega)
      have h1 := attesterRuntime_block_2621_fallthrough
        (by simp only [List.append, List.length_cons]; omega) (by rw [hlt]; rfl) h
      obtain ⟨aw2, k2, C2, h2⟩ := attesterRuntime_block_2630_packed (R := R) hstack
        (by rw [attesterRuntime_validJumps]; native_decide) h1
      have hload : memLoad (UInt256.ofNat src) mem = values i := by
        simpa only [Nat.mul_zero, Nat.add_zero] using hloads 0 (by omega)
      simp only [attesterRuntime_block_2630_stack, attesterRuntime_block_2630_memory, hload,
        ofNat_add_words, ulit_toNat' _ (by omega : dst < UInt256.size)] at h2
      rw [show 1 + i = i + 1 by omega, show 32 + src = src + 32 by omega] at h2
      have hnext : ∀ j, j < remaining →
          memLoad (UInt256.ofNat (src + 32 + 32 * j)) (writeWord mem dst (values i)) =
            values (i + 1 + j) := by
        intro j hj
        have hp := memoryPrefix_sparse_writeWord mem dst dst (values i) (.inl (le_refl _))
        rw [hp.load_preserved (by omega) (by omega) (by omega) (by omega),
          show src + 32 + 32 * j = src + 32 * (j + 1) by omega,
          hloads (j + 1) (by omega)]
        congr 1; omega
      obtain ⟨aw3, k3, C3, h3⟩ := ih h2 (by omega)
        (by rw [wordWrite_size]; omega) (by omega) (by omega) (by omega) hnext
      refine ⟨aw3, k3, C3, ?_⟩
      simpa only [wordArrayWords, wordSequenceMemory,
        show src + 32 + 32 * remaining = src + 32 * (remaining + 1) by omega,
        show dst + 32 + 32 * remaining = dst + 32 * (remaining + 1) by omega] using h3

theorem wordArrayEncode {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {base dst n : Nat} {values : Nat → UInt256} {ret : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2595⟩
      ([UInt256.ofNat dst, UInt256.ofNat base, ret] ++ R) mem aw out σ k C)
    (hstack : R.length + 10 ≤ 1024) (hlo : 96 ≤ base)
    (hin : base + 32 * (n + 1) ≤ mem.size) (hdis : base + 32 * (n + 1) ≤ dst)
    (hfit : dst + 64 + 32 * n < UInt256.size)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hloads : ∀ j, j < n → memLoad (UInt256.ofNat (base + 32 + 32 * j)) mem = values j)
    (hret : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ret
      (UInt256.ofNat (dst + 64 + 32 * n) :: R)
      (wordArrayEncodeMemory mem dst n values) aw' out σ k' C' := by
  have hdf : dst < UInt256.size := by omega
  have hlen' : memLoad (UInt256.ofNat base) (writeWord mem dst (UInt256.ofNat 32)) =
      UInt256.ofNat n := by
    have hp := memoryPrefix_sparse_writeWord mem dst dst (UInt256.ofNat 32) (.inl (le_refl _))
    exact (hp.load_preserved hlo (by omega) (by omega) (by omega)).trans hlen
  obtain ⟨aw1, k1, C1, h1⟩ := attesterRuntime_block_2595_packed
    (by simp only [List.append, List.length_cons]; omega) h
  have hh : attesterRuntime_block_2595_memory (mem := mem)
      (x0 := UInt256.ofNat dst) (x1 := UInt256.ofNat base) =
      wordSequenceMemory mem dst [UInt256.ofNat 32, UInt256.ofNat n] := by
    simp only [attesterRuntime_block_2595_memory, ulit_toNat' _ hdf]
    change (memLoad (UInt256.ofNat base) (writeWord mem dst (UInt256.ofNat 32))).toByteArray.write
      0 (writeWord mem dst (UInt256.ofNat 32)) (UInt256.ofNat 32 + UInt256.ofNat dst).toNat 32 = _
    rw [hlen', ofNat_add_words, ulit_toNat' _ (by omega)]
    simp only [wordSequenceMemory, Reasoning.Theory.writeWord, Nat.add_comm dst 32]
  simp only [attesterRuntime_block_2595_stack, ulit_toNat' _ hdf,
    show memLoad (UInt256.ofNat base) ((UInt256.ofNat 32).toByteArray.write 0 mem dst 32) =
      UInt256.ofNat n from hlen', ofNat_add_words, hh] at h1
  have hp := wordSequenceMemory_prefix mem dst [UInt256.ofNat 32, UInt256.ofNat n]
  obtain ⟨aw2, k2, C2, h2⟩ := wordArrayEncodeRun (i := 0) (remaining := n) (values := values) h1
    (by simp only [List.append, List.length_cons]; omega) (by omega)
    (by have := hp.size; omega) (by omega) hfit (by omega) (by omega)
    (by intro j hj
        rw [hp.load_preserved (by omega) (by omega) (by omega) (by omega), hloads j hj]
        simp only [Nat.zero_add])
  obtain ⟨aw3, k3, C3, h3⟩ := attesterRuntime_block_2651_packed
    (by simp only [List.append]; omega) hret h2
  exact ⟨aw3, k3, C3, h3⟩

theorem wordArrayReturn {words : String → UInt256} {I g s0 σ mem out aw k C R}
    {base dst n : Nat} {values : Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨121⟩
      (UInt256.ofNat base :: R) mem aw out σ k C)
    (hstack : R.length + 10 ≤ 1024) (hlo : 96 ≤ base)
    (hin : base + 32 * (n + 1) ≤ mem.size) (hdis : base + 32 * (n + 1) ≤ dst)
    (hfit : dst + 64 + 32 * n < UInt256.size)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat dst)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hloads : ∀ j, j < n → memLoad (UInt256.ofNat (base + 32 + 32 * j)) mem = values j) :
    RDret (immutableLayout.runtime attesterBytecode words) g s0 σ
      (wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n)) := by
  obtain ⟨aw1, k1, C1, h1⟩ := attesterRuntime_block_121_packed (by omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attesterRuntime_block_121_stack, hptr] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := wordArrayEncode h1 hstack hlo hin hdis hfit hlen hloads
    (by rw [attesterRuntime_validJumps]; native_decide)
  have h3 := attesterRuntime_block_134 (by omega) h2
  have hfp : memLoad (UInt256.ofNat 64) (wordArrayEncodeMemory mem dst n values) =
      UInt256.ofNat dst := by
    rw [wordArrayEncodeMemory, wordSequenceMemory_load_below _ (by omega) (by omega) (by decide)]
    exact hptr
  rw [hfp, ofNat_sub_words (by omega) hfit, ulit_toNat' _ (by omega),
    ulit_toNat' _ (by omega)] at h3
  have heq : dst + 64 + 32 * n - dst =
      32 * ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, wordArrayWords_length]
    omega
  rw [heq, wordArrayEncodeMemory, wordSequenceMemory_read] at h3
  exact h3

end Benchmarks.EAS.Attester
