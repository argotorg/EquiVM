import Benchmarks.EAS.Attester.AttestCellEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attestCellEncode3109 {words : String → UInt256} {I g s0 σ mem aw out k C R ret}
    {limit ptr dst : Nat} {input : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3109⟩
      (UInt256.ofNat ptr :: UInt256.ofNat dst :: ret :: R) mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (heap : AttestCellAt mem 96 limit ptr input)
    (hsize : limit ≤ mem.size) (hsep : limit ≤ dst) (hfit : dst + 288 < UInt256.size)
    (hret : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ret
      (UInt256.ofNat (dst + 256) :: R) (attestCellEncodedMemory mem dst input)
      aw' out σ k' C' := by
  obtain ⟨data, hdlo, hdhi, hinput, hstk⟩ :=
    attestCellEncodedHead_stack heap hsize hsep hfit (ret :: R)
  obtain ⟨aw1, k1, C1, h1⟩ := attesterRuntime_block_3109_packed
    (by first | omega | (simp only [List.append, List.length_cons, List.append_cons,
        List.nil_append]; omega)) h
  rw [hstk, attestCellEncodedHead_summary heap hsize hsep hfit] at h1
  have h2 := attesterRuntime_block_3202_fallthrough
    (by first | omega | (simp only [List.append, List.length_cons, List.append_cons,
        List.nil_append]; omega)) (by decide) h1
  have hp := attestCellEncodedHead_prefix mem dst
  have hinput' := (hp.load_preserved (by omega : 96 ≤ data + 32)
    (by omega) (by omega) (by omega)).trans hinput
  obtain ⟨aw3, k3, C3, h3⟩ := attesterRuntime_block_3211_packed
    (by first | omega | (simp only [List.append, List.length_cons, List.append_cons,
        List.nil_append]; omega))
    (by rw [attesterRuntime_validJumps]; native_decide) h2
  have hm3 : attesterRuntime_block_3211_memory (mem := attestCellEncodedHead mem dst)
      (x0 := UInt256.ofNat 0) (x2 := UInt256.ofNat data) (x5 := UInt256.ofNat dst) =
      attestCellEncodedPayload mem dst input := by
    simp only [attesterRuntime_block_3211_memory, ofNat_add_words, Nat.add_zero, Nat.zero_add,
      show 32 + data = data + 32 by omega, hinput', ulit_toNat' _ (by omega : dst + 224 < _)]
    rfl
  simp only [attesterRuntime_block_3211_stack, hm3] at h3
  have h4 := attesterRuntime_block_3202_taken
    (by first | omega | (simp only [List.append, List.length_cons, List.append_cons,
        List.nil_append]; omega)) (by decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h3
  have hval := heap.2.2.choose_spec.2.2.2.2.2.2.2.1
  have hptr := heap.1
  have hptrhi := heap.2.1
  have hp' : MemoryPrefix mem
      (writeWord (attestCellEncodedPayload mem dst input) (dst + 256) ⟨0⟩) dst :=
    (hp.trans (memoryPrefix_sparse_writeWord _ _ _ input (.inl (by omega)))).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega)))
  have hval' : memLoad (UInt256.ofNat (ptr + 160))
      (writeWord (attestCellEncodedPayload mem dst input) (dst + 256) ⟨0⟩) = ⟨0⟩ :=
    (hp'.load_preserved (by omega) (by omega) (by omega) (by omega)).trans hval
  change memLoad (UInt256.ofNat (ptr + 160))
    ((UInt256.ofNat 0).toByteArray.write 0 (attestCellEncodedPayload mem dst input)
      (dst + 256) 32) = UInt256.ofNat 0 at hval'
  have hm5 : attesterRuntime_block_3231_memory (mem := attestCellEncodedPayload mem dst input)
      (x1 := UInt256.ofNat 32) (x4 := UInt256.ofNat ptr) (x5 := UInt256.ofNat dst) =
      attestCellEncodedMemory mem dst input := by
    simp only [attesterRuntime_block_3231_memory, ofNat_add_words,
      show dst + 32 + 224 = dst + 256 by omega,
      ulit_toNat' _ (by omega : dst + 256 < _), ulit_toNat' _ (by omega : dst + 160 < _), hval']
    rfl
  obtain ⟨aw5, k5, C5, h5⟩ := attesterRuntime_block_3231_packed
    (by first | omega | (simp only [List.append, List.length_cons, List.append_cons,
        List.nil_append]; omega)) hret h4
  rw [hm5] at h5
  have hround : UInt256.land (UInt256.ofNat 32 + UInt256.ofNat 31)
      (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904)
          =
      UInt256.ofNat 32 := by decide +kernel
  simp only [attesterRuntime_block_3231_stack, hround] at h5
  refine ⟨aw5, k5, C5, ?_⟩
  simpa only [ofNat_add_words,
    show dst + 32 + 224 = dst + 256 by omega] using h5

end Benchmarks.EAS.Attester
