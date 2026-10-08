import Benchmarks.EAS.Attester.MultiAttestEncodeMemory
import Benchmarks.EAS.Attester.AttestRequestsEncodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiAttestPrepare {words : String → UInt256} {I g s0 σ k C aw R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1657⟩
      (UInt256.ofNat (arrayCount I.calldata 4) :: ⟨128⟩ :: R)
      (multiAttestBuiltMemory I.calldata) aw ByteArray.empty σ k C)
    (hstack : R.length + 29 ≤ 1024) (hc : MultiHeadChecks I.calldata)
    (hshape : BatchShape I.calldata) (hrows : BatchRowsValid I.calldata) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1772⟩
      ([UInt256.ofNat (multiAttestEncodedEnd I.calldata), ⟨1152239886⟩,
        UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      (multiAttestEncodedMemory I.calldata) aw' ByteArray.empty σ k' C' := by
  have hf := multiAttestBuiltMemory_bounds hc hshape hrows
  have he := multiAttestEncodedEnd_bounds hc hshape hrows
  have hm := multiAttestBuiltMemory_size hshape hrows
  let pre := writeWord (multiAttestBuiltMemory I.calldata) (multiAttestBuiltFree I.calldata)
    multiAttestSelectorWord
  have hp : MemoryPrefix (multiAttestBuiltMemory I.calldata) pre
      (multiAttestBuiltFree I.calldata) :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  have heap := (multiAttestBuiltMemory_heap hc hshape hrows).congr (mem' := pre)
    (by intro off hlo hhi; exact hp.load_preserved hlo hhi (by omega) (by omega))
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_1657_packed (by omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  have hstart : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3304⟩
      ([UInt256.ofNat (multiAttestBuiltFree I.calldata + 4), ⟨128⟩, ⟨1772⟩,
        ⟨1152239886⟩, UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      pre aw' ByteArray.empty σ k' C' := by
    simpa only [attesterRuntime_block_1657_stack, attesterRuntime_block_1657_memory,
      multiAttestBuiltMemory_freePtr, ofNat_add_words, ulit_toNat' _ hf.2.2,
      show 4 + multiAttestBuiltFree I.calldata = multiAttestBuiltFree I.calldata + 4 by omega]
      using h'
  exact attestRequestsEncode3304
    (R := [⟨1152239886⟩, UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
    hstart (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    heap (by change multiAttestBuiltFree I.calldata ≤ pre.size; have := hp.size; omega)
    (by omega) he.2
    (by rw [attesterRuntime_validJumps]; native_decide)

theorem multiAttestReachCall {words : String → UInt256} {I g s0 σ k C aw R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1772⟩
      ([UInt256.ofNat (multiAttestEncodedEnd I.calldata), ⟨1152239886⟩,
        UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      (multiAttestEncodedMemory I.calldata) aw ByteArray.empty σ k C)
    (hstack : R.length + 11 ≤ 1024) (hc : MultiHeadChecks I.calldata)
    (hshape : BatchShape I.calldata) (hrows : BatchRowsValid I.calldata) :
    ∃ gasArg aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1786⟩
      ([gasArg, UInt256.land (words "_eas") solcAddrMask, ⟨0⟩,
        UInt256.ofNat (multiAttestBuiltFree I.calldata),
        UInt256.ofNat (multiAttestEncodedEnd I.calldata - multiAttestBuiltFree I.calldata),
        UInt256.ofNat (multiAttestBuiltFree I.calldata), ⟨0⟩,
        UInt256.ofNat (multiAttestEncodedEnd I.calldata), ⟨1152239886⟩,
        UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      (multiAttestEncodedMemory I.calldata) aw' ByteArray.empty σ k' C' := by
  have he := multiAttestEncodedEnd_bounds hc hshape hrows
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_1772_packed
    (R := ⟨128⟩ :: R) (by simp only [List.length_cons]; omega) h
  simp only [attesterRuntime_block_1772_stack,
    multiAttestEncodedMemory_freePtr hc hshape hrows,
    ofNat_sub_words (by omega : multiAttestBuiltFree I.calldata ≤ multiAttestEncodedEnd I.calldata)
      (by omega : multiAttestEncodedEnd I.calldata < UInt256.size)] at h'
  exact ⟨_, _, _, _, h'⟩

theorem multiAttestAfterCallFailure {words : String → UInt256} {I g s0 σ k C mem aw out R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1787⟩
      (⟨0⟩ :: R) mem aw out σ k C) (hstack : R.length + 4 ≤ 1024) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  have h' := attesterRuntime_block_1787_fallthrough (by omega) (by decide) h
  exact attesterRuntime_block_1794
    (by simpa only [attesterRuntime_block_1787_fallthrough_stack, List.length_cons] using hstack) h'

end Benchmarks.EAS.Attester
