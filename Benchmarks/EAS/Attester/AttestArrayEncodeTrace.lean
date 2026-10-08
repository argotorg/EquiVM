import Benchmarks.EAS.Attester.AttestCellEncodeTrace
import Benchmarks.EAS.Attester.AttestArrayEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attestArrayEncodeStep3441 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {a b c d : UInt256} {limit base n i origin table dst : Nat} {values : Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3441⟩
      ([UInt256.ofNat i, UInt256.ofNat n, UInt256.ofNat table, UInt256.ofNat dst,
        UInt256.ofNat (base + 32 + 32 * i), a, b, c, d, UInt256.ofNat origin] ++ R)
      mem aw out σ k C)
    (hstack : R.length + 22 ≤ 1024) (heap : AttestArrayAt mem 96 limit base n values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table) (htable : table + 32 ≤ dst)
    (horigin : origin + 96 ≤ dst) (hi : i < n) (hfit : dst + 288 < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3441⟩
      ([UInt256.ofNat (i + 1), UInt256.ofNat n, UInt256.ofNat (table + 32),
        UInt256.ofNat (dst + 256), UInt256.ofNat (base + 32 + 32 * (i + 1)),
        a, b, c, d, UInt256.ofNat origin] ++ R)
      (attestArrayItemEncodedMemory mem origin table dst (values i)) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by have := heap.upper; omega
  have hifit : i < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ hifit, ulit_toNat' _ hnfit]; exact hi)
  have h' := attesterRuntime_block_3441_fallthrough
    (R := [UInt256.ofNat table, UInt256.ofNat dst, UInt256.ofNat (base + 32 + 32 * i),
      a, b, c, d, UInt256.ofNat origin] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [hlt]; rfl) h
  let delta := UInt256.ofNat (dst - origin - 96)
  let pre := writeWord mem table delta
  have hdelta : UInt256.sub (UInt256.ofNat dst) (UInt256.ofNat origin) +
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840 =
      delta := by
    rw [u256_add_comm, ofNat_sub_words (by omega) (by omega)]
    exact ofNat_size_sub_add (c := 96) (n := dst - origin) (by decide) (by omega) (by omega)
  have hp : MemoryPrefix mem pre limit := memoryPrefix_sparse_writeWord _ _ _ _ (.inl ht)
  obtain ⟨ptr, hslot, hc⟩ := heap.cells i hi
  have hslot' : memLoad (UInt256.ofNat (base + 32 + 32 * i)) pre = UInt256.ofNat ptr :=
    (hp.load_preserved (by have := heap.lower; omega) (by have := heap.upper; omega)
      (by have := heap.upper; omega) (by have := heap.upper; omega)).trans hslot
  have hc' := hc.congr (by
    intro off hlo hhi
    exact hp.load_preserved hlo hhi (by omega) (by omega))
  dsimp only [pre, Reasoning.Theory.writeWord] at hslot'
  obtain ⟨aw1, k1, C1, h1⟩ := attesterRuntime_block_3450_packed
    (by simp only [List.append]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  simp only [attesterRuntime_block_3450_stack, attesterRuntime_block_3450_memory,
    hdelta, ulit_toNat' _ (by omega : table < UInt256.size), hslot'] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := attestCellEncode3109
    (R := [UInt256.ofNat i, UInt256.ofNat n, UInt256.ofNat table, UInt256.ofNat dst,
      UInt256.ofNat (base + 32 + 32 * i), a, b, c, d, UInt256.ofNat origin] ++ R)
    h1 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hc' (le_trans hsize hp.size) (by omega) hfit
    (by rw [attesterRuntime_validJumps]; native_decide)
  obtain ⟨aw3, k3, C3, h3⟩ := attesterRuntime_block_3499_packed
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h2
  refine ⟨aw3, k3, C3, ?_⟩
  simpa only [attesterRuntime_block_3499_stack, ofNat_add_words,
    show 1 + i = i + 1 by omega, show 32 + table = table + 32 by omega,
    show 32 + (base + 32 + 32 * i) = base + 32 + 32 * (i + 1) by omega,
    attestArrayItemEncodedMemory] using h3

set_option maxRecDepth 1000 in
theorem attestArrayEncodeRun3441 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {a b c d : UInt256} {limit base n i remaining origin table dst : Nat}
    {values : Nat → UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3441⟩
      ([UInt256.ofNat i, UInt256.ofNat n, UInt256.ofNat table, UInt256.ofNat dst,
        UInt256.ofNat (base + 32 + 32 * i), a, b, c, d, UInt256.ofNat origin] ++ R)
      mem aw out σ k C)
    (hstack : R.length + 22 ≤ 1024) (heap : AttestArrayAt mem 96 limit base n values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table)
    (htable : table + 32 * remaining ≤ dst) (horigin : origin + 96 ≤ dst)
    (hi : i + remaining = n) (hfit : dst + 256 * remaining + 32 < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3521⟩
      ([UInt256.ofNat n, UInt256.ofNat n, UInt256.ofNat (table + 32 * remaining),
        UInt256.ofNat (dst + 256 * remaining), UInt256.ofNat (base + 32 + 32 * n),
        a, b, c, d, UInt256.ofNat origin] ++ R)
      (attestArrayEncodedMemory mem origin table dst values i remaining) aw' out σ k' C' := by
  induction remaining generalizing mem aw k C table dst i with
  | zero =>
      have hin : i = n := by omega
      subst i
      obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_3441_taken_packed
        (R := [UInt256.ofNat table, UInt256.ofNat dst, UInt256.ofNat (base + 32 + 32 * n),
          a, b, c, d, UInt256.ofNat origin] ++ R)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by rw [ult_zero (Nat.le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw', k', C', h'⟩
  | succ remaining ih =>
      obtain ⟨aw', k', C', h'⟩ := attestArrayEncodeStep3441 h hstack heap hsize ht
        (by omega) horigin (by omega) (by omega)
      have hp := attestArrayItemEncodedMemory_prefix mem origin table dst limit (values i)
        ht (by omega)
      have heap' := heap.congr (by
        intro off hlo hhi
        exact hp.load_preserved hlo hhi (by omega) (by omega))
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' heap' (by have := hp.size; omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨aw'', k'', C'', ?_⟩
      simpa only [attestArrayEncodedMemory,
        show table + 32 + 32 * remaining = table + 32 * (remaining + 1) by omega,
        show dst + 256 + 256 * remaining = dst + 256 * (remaining + 1) by omega] using h''

end Benchmarks.EAS.Attester
