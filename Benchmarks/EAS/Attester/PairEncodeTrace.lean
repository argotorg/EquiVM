import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.PairHeap
import Benchmarks.EAS.Attester.WordSequenceMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem pairEncodeStep3021 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {limit base n i dst : Nat} {values : Nat → UInt256 × UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3021⟩
      ([UInt256.ofNat n, UInt256.ofNat dst, UInt256.ofNat i,
        UInt256.ofNat (base + 32 + 32 * i)] ++ R) mem aw out σ k C)
    (hstack : R.length + 9 ≤ 1024) (heap : PairArrayAt mem 96 limit base n values)
    (hsize : limit ≤ mem.size) (hsep : limit ≤ dst) (hi : i < n)
    (hfit : dst + 64 < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3021⟩
      ([UInt256.ofNat n, UInt256.ofNat (dst + 64), UInt256.ofNat (i + 1),
        UInt256.ofNat (base + 32 + 32 * (i + 1))] ++ R)
      (wordSequenceMemory mem dst [(values i).1, (values i).2]) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by have := heap.upper; omega
  have hifit : i < UInt256.size := by omega
  have hd : dst < UInt256.size := by omega
  have hd32 : dst + 32 < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ hifit, ulit_toNat' _ hnfit]; exact hi)
  have h' := attesterRuntime_block_3021_fallthrough
    (R := UInt256.ofNat (base + 32 + 32 * i) :: R)
    (by simp only [List.length_cons]; omega) (by rw [hlt]; rfl) h
  obtain ⟨ptr, hlo, hhi, hslot, hfirst, hsecond⟩ := heap.cells i hi
  have hm : attesterRuntime_block_3030_memory (mem := mem)
      (x1 := UInt256.ofNat dst) (x3 := UInt256.ofNat (base + 32 + 32 * i)) =
      wordSequenceMemory mem dst [(values i).1, (values i).2] := by
    simp only [attesterRuntime_block_3030_memory, hslot, hfirst, ofNat_add_words,
      show 32 + ptr = ptr + 32 by omega, ulit_toNat' _ hd, ulit_toNat' _ hd32]
    rw [memLoad_write_disjoint _ _ _ _
      (by rw [ulit_toNat' _ (by omega : ptr + 32 < UInt256.size)]; omega)
      (.inl (by rw [ulit_toNat' _ (by omega : ptr + 32 < UInt256.size)]; omega)), hsecond]
    rfl
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_3030_packed hstack
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  rw [hm] at h''
  have h''' := attesterRuntime_block_3050 (by omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  refine ⟨aw', k' + 18, C' + 54, ?_⟩
  simpa only [attesterRuntime_block_3050_stack, ofNat_add_words,
    show base + 32 + 32 * i + 32 = base + 32 + 32 * (i + 1) by omega] using h'''

theorem pairEncodeRun3021 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {limit base n i remaining dst : Nat} {values : Nat → UInt256 × UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3021⟩
      ([UInt256.ofNat n, UInt256.ofNat dst, UInt256.ofNat i,
        UInt256.ofNat (base + 32 + 32 * i)] ++ R) mem aw out σ k C)
    (hstack : R.length + 9 ≤ 1024) (heap : PairArrayAt mem 96 limit base n values)
    (hsize : limit ≤ mem.size) (hsep : limit ≤ dst) (hi : i + remaining = n)
    (hfit : dst + 64 * remaining < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3073⟩
      ([UInt256.ofNat n, UInt256.ofNat (dst + 64 * remaining), UInt256.ofNat n,
        UInt256.ofNat (base + 32 + 32 * n)] ++ R)
      (wordSequenceMemory mem dst (pairSequenceWords values i remaining)) aw' out σ k' C' := by
  induction remaining generalizing mem aw k C dst i with
  | zero =>
      have hin : i = n := by omega
      subst i
      have h' := attesterRuntime_block_3021_taken
        (R := UInt256.ofNat (base + 32 + 32 * n) :: R)
        (by simp only [List.length_cons]; omega)
        (by rw [ult_zero (Nat.le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw, k + 7, C + 26, h'⟩
  | succ remaining ih =>
      obtain ⟨aw', k', C', h'⟩ := pairEncodeStep3021 h hstack heap hsize hsep (by omega) (by omega)
      have hp := wordSequenceMemory_prefix mem dst [(values i).1, (values i).2]
      have heap' := heap.congr (by
        intro off hlo hhi
        exact hp.load_preserved hlo (by omega) (by omega) (by omega))
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' heap' (by have := hp.size; omega)
        (by omega) (by omega) (by omega)
      refine ⟨aw'', k'', C'', ?_⟩
      simpa only [pairSequenceWords, wordSequenceMemory, Nat.add_assoc, Nat.reduceAdd,
        show dst + 64 + 64 * remaining = dst + 64 * (remaining + 1) by omega] using h''

end Benchmarks.EAS.Attester
