import Benchmarks.EAS.Attester.AttestRequestHeaderTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attestRequestsEncodeStep3344 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {limit base n i origin table dst : Nat} {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3344⟩
      ([UInt256.ofNat i, UInt256.ofNat (base + 32 + 32 * i), UInt256.ofNat n,
        UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R) mem aw out σ k C)
    (hstack : R.length + 24 ≤ 1024) (heap : AttestRequestsAt mem 96 limit base n schemas counts
        values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table) (htable : table + 32 ≤ dst)
    (horigin : origin + 64 ≤ dst) (hi : i < n)
    (hfit : dst + 96 + 288 * counts i + 32 < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3344⟩
      ([UInt256.ofNat (i + 1), UInt256.ofNat (base + 32 + 32 * (i + 1)), UInt256.ofNat n,
        UInt256.ofNat (table + 32), UInt256.ofNat (dst + 96 + 288 * counts i), ⟨0⟩,
        UInt256.ofNat origin] ++ R)
      (attestRequestEncodedMemory mem origin table dst (schemas i) (counts i) (values i))
      aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by have := heap.upper; omega
  have hifit : i < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ hifit, ulit_toNat' _ hnfit]; exact hi)
  have h' := attesterRuntime_block_3344_fallthrough
    (R := [UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R)
    (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
    (by rw [hlt]; rfl) h
  obtain ⟨ptr, hslot, hr⟩ := heap.cells i hi
  obtain ⟨inner, ha, aw', k', C', h''⟩ := attestRequestHeader3353 h' (by omega)
    (by have := heap.lower; omega) (by have := heap.upper; omega) hslot hr hsize ht (by omega)
    htable horigin (by omega)
  have hp := pairRequestHeaderMemory_prefix mem origin table dst limit (counts i) (schemas i)
    ht (by omega)
  have ha' := ha.congr (by
    intro off hlo hhi
    exact hp.load_preserved hlo hhi (by omega) (by omega))
  obtain ⟨aw'', k'', C'', h'''⟩ := attestArrayEncodeRun3441
    (R := ⟨0⟩ :: UInt256.ofNat origin :: R) (i := 0) (remaining := counts i)
    (by simpa only [Nat.mul_zero, Nat.add_zero] using h'')
    (by simp only [List.length_cons]; omega)
    ha' (by have := hp.size; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨awf, kf, Cf, hdone⟩ := attesterRuntime_block_3521_packed
    (R := ⟨0⟩ :: UInt256.ofNat origin :: R)
    (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h'''
  refine ⟨awf, kf, Cf, ?_⟩
  simpa only [attesterRuntime_block_3521_stack, attestRequestEncodedMemory, ofNat_add_words,
    show 1 + i = i + 1 by omega, show 32 + table = table + 32 by omega,
    show 32 + (base + 32 + 32 * i) = base + 32 + 32 * (i + 1) by omega,
    show dst + 96 + 32 * counts i + 256 * counts i = dst + 96 + 288 * counts i by omega]
    using hdone

theorem attestRequestsEncodeRun3344 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {limit base n i remaining origin table dst : Nat} {schemas : Nat → UInt256}
    {counts : Nat → Nat} {values : Nat → Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3344⟩
      ([UInt256.ofNat i, UInt256.ofNat (base + 32 + 32 * i), UInt256.ofNat n,
        UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R) mem aw out σ k C)
    (hstack : R.length + 24 ≤ 1024) (heap : AttestRequestsAt mem 96 limit base n schemas counts
        values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table) (htable : table + 32 * remaining ≤ dst)
    (horigin : origin + 64 ≤ dst) (hi : i + remaining = n)
    (hfit : attestRequestsEncodedEnd dst counts i remaining + 32 < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3097⟩
      ([UInt256.ofNat n, UInt256.ofNat (base + 32 + 32 * n), UInt256.ofNat n,
        UInt256.ofNat (table + 32 * remaining),
        UInt256.ofNat (attestRequestsEncodedEnd dst counts i remaining), ⟨0⟩,
        UInt256.ofNat origin] ++ R)
      (attestRequestsEncodedMemory mem origin table dst schemas counts values i remaining)
      aw' out σ k' C' := by
  induction remaining generalizing mem aw k C table dst i with
  | zero =>
      have hin : i = n := by omega
      subst i
      have h' := attesterRuntime_block_3344_taken
        (R := [UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R)
        (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
        (by rw [ult_zero (Nat.le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw, k + 7, C + 26, h'⟩
  | succ remaining ih =>
      have hend := attestRequestsEncodedEnd_lower (dst + 96 + 288 * counts i) counts (i + 1)
          remaining
      rw [attestRequestsEncodedEnd] at hfit
      obtain ⟨aw', k', C', h'⟩ := attestRequestsEncodeStep3344 h hstack heap hsize ht (by omega)
        horigin (by omega) (by omega)
      have hp := attestRequestEncodedMemory_prefix mem origin table dst limit (counts i)
        (schemas i) (values i) ht (by omega)
      have heap' := heap.congr (by
        intro off hlo hhi
        exact hp.load_preserved hlo hhi (by omega) (by omega))
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' heap' (by have := hp.size; omega)
        (by omega) (by omega) (by omega) (by omega) hfit
      refine ⟨aw'', k'', C'', ?_⟩
      simpa only [attestRequestsEncodedMemory, attestRequestsEncodedEnd,
        show table + 32 + 32 * remaining = table + 32 * (remaining + 1) by omega] using h''

theorem attestRequestsEncode3304 {words : String → UInt256} {I g s0 σ mem aw out k C R ret}
    {limit base n origin : Nat} {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3304⟩
      (UInt256.ofNat origin :: UInt256.ofNat base :: ret :: R) mem aw out σ k C)
    (hstack : R.length + 26 ≤ 1024)
    (heap : AttestRequestsAt mem 96 limit base n schemas counts values)
    (hsize : limit ≤ mem.size) (hsep : limit ≤ origin)
    (hfit : attestRequestsABIEnd origin n counts + 32 < UInt256.size)
    (hret : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ret
      (UInt256.ofNat (attestRequestsABIEnd origin n counts) :: R)
      (attestRequestsABIMemory mem origin n schemas counts values) aw' out σ k' C' := by
  have hend := attestRequestsEncodedEnd_lower (origin + 64 + 32 * n) counts 0 n
  change origin + 64 + 32 * n ≤ attestRequestsABIEnd origin n counts at hend
  have ho : origin < UInt256.size := by omega
  have ho32 : origin + 32 < UInt256.size := by omega
  have hp := memoryPrefix_sparse_writeWord mem origin limit (UInt256.ofNat 32) (.inl hsep)
  have hl : memLoad (UInt256.ofNat base)
      ((UInt256.ofNat 32).toByteArray.write 0 mem origin 32) = UInt256.ofNat n :=
    (hp.load_preserved heap.lower (by have := heap.upper; omega)
      (by have := heap.upper; omega) (by have := heap.upper; omega)).trans heap.length
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) = UInt256.ofNat (32 * n) :=
    shiftLeft5_ofNat_eq (by omega)
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_3304_packed
    (by simp only [List.length_cons]; omega) h
  simp only [attesterRuntime_block_3304_stack, attesterRuntime_block_3304_memory,
    ulit_toNat' _ ho, hl, hshift,
    ofNat_add_words, ulit_toNat' _ ho32] at h'
  have hstart : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3344⟩
      ([⟨0⟩, UInt256.ofNat (base + 32), UInt256.ofNat n, UInt256.ofNat (origin + 64),
        UInt256.ofNat (origin + 64 + 32 * n), ⟨0⟩, UInt256.ofNat origin,
        UInt256.ofNat base, ret] ++ R)
      (pairRequestsABIHeaderMemory mem origin n) aw' out σ k' C' := by
    simpa only [pairRequestsABIHeaderMemory, writeCascade, Reasoning.Theory.writeWord,
      show origin + 32 * n + 64 = origin + 64 + 32 * n by omega] using h'
  have hprefix := pairRequestsABIHeaderMemory_prefix mem origin n limit hsep
  have heap' := heap.congr (by
    intro off hlo hhi
    exact hprefix.load_preserved hlo hhi (by omega) (by omega))
  obtain ⟨aw'', k'', C'', h''⟩ := attestRequestsEncodeRun3344
    (R := UInt256.ofNat base :: ret :: R) (i := 0) (remaining := n)
    (by simpa only [Nat.mul_zero, Nat.add_zero] using hstart)
    (by simp only [List.length_cons]; omega) heap' (by have := hprefix.size; omega)
    (by omega) (by omega) (by omega) (by omega) hfit
  have hdone := attesterRuntime_block_3097 (by omega) hret h''
  exact ⟨aw'', k'' + 12, C'' + 32, hdone⟩

end Benchmarks.EAS.Attester
