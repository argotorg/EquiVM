import Benchmarks.EAS.Attester.PairEncodeTrace
import Benchmarks.EAS.Attester.PairRequestsEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem pairRequestHeader2943 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {x0 x2 x5 schema : UInt256} {limit slot ptr origin table dst n : Nat}
    {values : Nat → UInt256 × UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2943⟩
      ([x0, UInt256.ofNat slot, x2, UInt256.ofNat table, UInt256.ofNat dst, x5,
        UInt256.ofNat origin] ++ R) mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hslotlo : 96 ≤ slot) (hslotend : slot + 32 ≤ limit)
    (hslot : memLoad (UInt256.ofNat slot) mem = UInt256.ofNat ptr)
    (request : PairRequestAt mem 96 limit ptr schema n values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table) (hd : limit ≤ dst)
    (htable : table + 32 ≤ dst) (horigin : origin + 64 ≤ dst)
    (hfit : dst + 96 < UInt256.size) :
    ∃ base, PairArrayAt mem 96 limit base n values ∧ ∃ aw' k' C',
      RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3021⟩
        ([UInt256.ofNat n, UInt256.ofNat (dst + 96), ⟨0⟩, UInt256.ofNat (base + 32),
          x0, UInt256.ofNat slot, x2, UInt256.ofNat table, UInt256.ofNat dst, x5,
          UInt256.ofNat origin] ++ R)
        (pairRequestHeaderMemory mem origin table dst schema n) aw' out σ k' C' := by
  obtain ⟨base, hbase, ha⟩ := request.data
  let delta := UInt256.ofNat (dst - origin - 64)
  let pre0 := writeWord mem table delta
  let pre1 := writeWord pre0 dst schema
  let pre2 := writeWord pre1 (dst + 32) (UInt256.ofNat 64)
  have hp0 : MemoryPrefix mem pre0 limit :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl ht)
  have hp1 : MemoryPrefix mem pre1 limit := hp0.trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl hd))
  have hp2 : MemoryPrefix mem pre2 limit := hp1.trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega)))
  have hs0 : memLoad (UInt256.ofNat slot) pre0 = UInt256.ofNat ptr :=
    (hp0.load_preserved hslotlo hslotend (by omega) (by omega)).trans hslot
  have hf0 : memLoad (UInt256.ofNat ptr) pre0 = schema :=
    (hp0.load_preserved request.lower (by have := request.upper; omega)
      (by have := request.upper; omega) (by have := request.upper; omega)).trans request.first
  have hb1 : memLoad (UInt256.ofNat (ptr + 32)) pre1 = UInt256.ofNat base :=
    (hp1.load_preserved (by have := request.lower; omega) (by have := request.upper; omega)
      (by have := request.upper; omega) (by have := request.upper; omega)).trans hbase
  have hl2 : memLoad (UInt256.ofNat base) pre2 = UInt256.ofNat n :=
    (hp2.load_preserved ha.lower (by have := ha.upper; omega)
      (by have := ha.upper; omega) (by have := ha.upper; omega)).trans ha.length
  dsimp only [pre0, pre1, pre2, Reasoning.Theory.writeWord] at hs0 hf0 hb1 hl2
  have hdelta : UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639872 +
      UInt256.sub (UInt256.ofNat dst) (UInt256.ofNat origin) = delta := by
    rw [ofNat_sub_words (by omega) (by omega)]
    exact ofNat_size_sub_add (c := 64) (n := dst - origin) (by decide) (by omega) (by omega)
  have hdt : table < UInt256.size := by omega
  have hdd : dst < UInt256.size := by omega
  have hdd32 : dst + 32 < UInt256.size := by omega
  have hdd64 : dst + 64 < UInt256.size := by omega
  have hm : attesterRuntime_block_2943_memory (mem := mem)
      (x1 := UInt256.ofNat slot) (x3 := UInt256.ofNat table)
      (x4 := UInt256.ofNat dst) (x6 := UInt256.ofNat origin) =
      pairRequestHeaderMemory mem origin table dst schema n := by
    simp only [attesterRuntime_block_2943_memory, hdelta, ofNat_add_words,
      ulit_toNat' _ hdt, ulit_toNat' _ hdd, ulit_toNat' _ hdd32, ulit_toNat' _ hdd64,
      hs0, hf0, show 32 + ptr = ptr + 32 by omega, hb1, hl2]
    rfl
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_2943_packed hstack h
  rw [hm] at h'
  refine ⟨base, ha, aw', k', C', ?_⟩
  simpa only [attesterRuntime_block_2943_stack, hdelta, ofNat_add_words,
    ulit_toNat' _ hdt, ulit_toNat' _ hdd, ulit_toNat' _ hdd32,
    hs0, hf0, show 32 + ptr = ptr + 32 by omega, hb1, hl2,
    show 32 + base = base + 32 by omega] using h'

theorem pairRequestsEncodeStep2934 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {limit base n i origin table dst : Nat} {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256 × UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2934⟩
      ([UInt256.ofNat i, UInt256.ofNat (base + 32 + 32 * i), UInt256.ofNat n,
        UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R) mem aw out σ k C)
    (hstack : R.length + 16 ≤ 1024) (heap : PairRequestsAt mem 96 limit base n schemas counts
        values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table) (htable : table + 32 ≤ dst)
    (horigin : origin + 64 ≤ dst) (hi : i < n)
    (hfit : dst + 96 + 64 * counts i < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2934⟩
      ([UInt256.ofNat (i + 1), UInt256.ofNat (base + 32 + 32 * (i + 1)), UInt256.ofNat n,
        UInt256.ofNat (table + 32), UInt256.ofNat (dst + 96 + 64 * counts i), ⟨0⟩,
        UInt256.ofNat origin] ++ R)
      (pairRequestEncodedMemory mem origin table dst (schemas i) (counts i) (values i))
      aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by have := heap.upper; omega
  have hifit : i < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ hifit, ulit_toNat' _ hnfit]; exact hi)
  have h' := attesterRuntime_block_2934_fallthrough
    (R := [UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R)
    (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
    (by rw [hlt]; rfl) h
  obtain ⟨ptr, hslot, hr⟩ := heap.cells i hi
  obtain ⟨inner, ha, aw', k', C', h''⟩ := pairRequestHeader2943 h' (by omega)
    (by have := heap.lower; omega) (by have := heap.upper; omega) hslot hr hsize ht (by omega)
    htable horigin (by omega)
  have hp := pairRequestHeaderMemory_prefix mem origin table dst limit (counts i) (schemas i)
    ht (by omega)
  have ha' := ha.congr (by
    intro off hlo hhi
    exact hp.load_preserved hlo hhi (by omega) (by omega))
  obtain ⟨aw'', k'', C'', h'''⟩ := pairEncodeRun3021
    (R := [UInt256.ofNat i, UInt256.ofNat (base + 32 + 32 * i), UInt256.ofNat n,
      UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R)
    (i := 0) (remaining := counts i) (by simpa only [Nat.mul_zero, Nat.add_zero] using h'')
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    ha' (by have := hp.size; omega) (by omega) (by omega) hfit
  have hdone := attesterRuntime_block_3073
    (R := ⟨0⟩ :: UInt256.ofNat origin :: R)
    (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h'''
  refine ⟨aw'', k'' + 20, C'' + 59, ?_⟩
  simpa only [attesterRuntime_block_3073_stack, pairRequestEncodedMemory, ofNat_add_words,
    show 1 + i = i + 1 by omega, show 32 + table = table + 32 by omega,
    show 32 + (base + 32 + 32 * i) = base + 32 + 32 * (i + 1) by omega] using hdone

theorem pairRequestsEncodeRun2934 {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {limit base n i remaining origin table dst : Nat} {schemas : Nat → UInt256}
    {counts : Nat → Nat} {values : Nat → Nat → UInt256 × UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2934⟩
      ([UInt256.ofNat i, UInt256.ofNat (base + 32 + 32 * i), UInt256.ofNat n,
        UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R) mem aw out σ k C)
    (hstack : R.length + 16 ≤ 1024) (heap : PairRequestsAt mem 96 limit base n schemas counts
        values)
    (hsize : limit ≤ mem.size) (ht : limit ≤ table) (htable : table + 32 * remaining ≤ dst)
    (horigin : origin + 64 ≤ dst) (hi : i + remaining = n)
    (hfit : pairRequestsEncodedEnd dst counts i remaining < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3097⟩
      ([UInt256.ofNat n, UInt256.ofNat (base + 32 + 32 * n), UInt256.ofNat n,
        UInt256.ofNat (table + 32 * remaining),
        UInt256.ofNat (pairRequestsEncodedEnd dst counts i remaining), ⟨0⟩,
        UInt256.ofNat origin] ++ R)
      (pairRequestsEncodedMemory mem origin table dst schemas counts values i remaining)
      aw' out σ k' C' := by
  induction remaining generalizing mem aw k C table dst i with
  | zero =>
      have hin : i = n := by omega
      subst i
      have h' := attesterRuntime_block_2934_taken
        (R := [UInt256.ofNat table, UInt256.ofNat dst, ⟨0⟩, UInt256.ofNat origin] ++ R)
        (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
        (by rw [ult_zero (Nat.le_refl _)]; decide)
        (by rw [attesterRuntime_validJumps]; native_decide) h
      exact ⟨aw, k + 7, C + 26, h'⟩
  | succ remaining ih =>
      have hend := pairRequestsEncodedEnd_lower (dst + 96 + 64 * counts i) counts (i + 1) remaining
      rw [pairRequestsEncodedEnd] at hfit
      obtain ⟨aw', k', C', h'⟩ := pairRequestsEncodeStep2934 h hstack heap hsize ht (by omega)
        horigin (by omega) (by omega)
      have hp := pairRequestEncodedMemory_prefix mem origin table dst limit (counts i)
        (schemas i) (values i) ht (by omega)
      have heap' := heap.congr (by
        intro off hlo hhi
        exact hp.load_preserved hlo hhi (by omega) (by omega))
      obtain ⟨aw'', k'', C'', h''⟩ := ih h' heap' (by have := hp.size; omega)
        (by omega) (by omega) (by omega) (by omega) hfit
      refine ⟨aw'', k'', C'', ?_⟩
      simpa only [pairRequestsEncodedMemory, pairRequestsEncodedEnd,
        show table + 32 + 32 * remaining = table + 32 * (remaining + 1) by omega] using h''

theorem pairRequestsEncode2894 {words : String → UInt256} {I g s0 σ mem aw out k C R ret}
    {limit base n origin : Nat} {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256 × UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2894⟩
      (UInt256.ofNat origin :: UInt256.ofNat base :: ret :: R) mem aw out σ k C)
    (hstack : R.length + 18 ≤ 1024)
    (heap : PairRequestsAt mem 96 limit base n schemas counts values)
    (hsize : limit ≤ mem.size) (hsep : limit ≤ origin)
    (hfit : pairRequestsABIEnd origin n counts < UInt256.size)
    (hret : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ret
      (UInt256.ofNat (pairRequestsABIEnd origin n counts) :: R)
      (pairRequestsABIMemory mem origin n schemas counts values) aw' out σ k' C' := by
  have hend := pairRequestsEncodedEnd_lower (origin + 64 + 32 * n) counts 0 n
  change origin + 64 + 32 * n ≤ pairRequestsABIEnd origin n counts at hend
  have ho : origin < UInt256.size := by omega
  have ho32 : origin + 32 < UInt256.size := by omega
  have hp := memoryPrefix_sparse_writeWord mem origin limit (UInt256.ofNat 32) (.inl hsep)
  have hl : memLoad (UInt256.ofNat base)
      ((UInt256.ofNat 32).toByteArray.write 0 mem origin 32) = UInt256.ofNat n :=
    (hp.load_preserved heap.lower (by have := heap.upper; omega)
      (by have := heap.upper; omega) (by have := heap.upper; omega)).trans heap.length
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) = UInt256.ofNat (32 * n) :=
    shiftLeft5_ofNat_eq (by omega)
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_2894_packed
    (by simp only [List.length_cons]; omega) h
  simp only [attesterRuntime_block_2894_stack, attesterRuntime_block_2894_memory,
    ulit_toNat' _ ho, hl, hshift,
    ofNat_add_words, ulit_toNat' _ ho32] at h'
  have hstart : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2934⟩
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
  obtain ⟨aw'', k'', C'', h''⟩ := pairRequestsEncodeRun2934
    (R := UInt256.ofNat base :: ret :: R) (i := 0) (remaining := n)
    (by simpa only [Nat.mul_zero, Nat.add_zero] using hstart)
    (by simp only [List.length_cons]; omega) heap' (by have := hprefix.size; omega)
    (by omega) (by omega) (by omega) (by omega) hfit
  have hdone := attesterRuntime_block_3097 (by omega) hret h''
  exact ⟨aw'', k'' + 12, C'' + 32, hdone⟩

end Benchmarks.EAS.Attester
