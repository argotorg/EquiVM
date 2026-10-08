import Benchmarks.EAS.Attester.MultiRevokeEncodeMemory
import Benchmarks.EAS.Attester.PairRequestsEncodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiRevokePrepare {words : String → UInt256} {I g s0 σ k C aw R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨762⟩
      (UInt256.ofNat (arrayCount I.calldata 4) :: ⟨128⟩ :: R)
      (multiRevokeBuiltMemory I.calldata) aw ByteArray.empty σ k C)
    (hstack : R.length + 21 ≤ 1024) (hc : MultiHeadChecks I.calldata)
    (hshape : BatchShape I.calldata) (hrows : BatchRowsValid I.calldata) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨877⟩
      ([UInt256.ofNat (multiRevokeEncodedEnd I.calldata), ⟨1287121381⟩,
        UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      (multiRevokeEncodedMemory I.calldata) aw' ByteArray.empty σ k' C' := by
  have hf := multiRevokeBuiltMemory_bounds hc hshape hrows
  have he := multiRevokeEncodedEnd_bounds hc hshape hrows
  have hm := multiRevokeBuiltMemory_size hshape hrows
  let pre := writeWord (multiRevokeBuiltMemory I.calldata) (multiRevokeBuiltFree I.calldata)
    multiRevokeSelectorWord
  have hp : MemoryPrefix (multiRevokeBuiltMemory I.calldata) pre
      (multiRevokeBuiltFree I.calldata) :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  have heap := (multiRevokeBuiltMemory_heap hc hshape hrows).congr (mem' := pre)
    (by intro off hlo hhi; exact hp.load_preserved hlo hhi (by omega) (by omega))
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_762_packed (by omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  have hstart : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2894⟩
      ([UInt256.ofNat (multiRevokeBuiltFree I.calldata + 4), ⟨128⟩, ⟨877⟩,
        ⟨1287121381⟩, UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      pre aw' ByteArray.empty σ k' C' := by
    simpa only [attesterRuntime_block_762_stack, attesterRuntime_block_762_memory,
      multiRevokeBuiltMemory_freePtr, ofNat_add_words, ulit_toNat' _ hf.2.2,
      show 4 + multiRevokeBuiltFree I.calldata = multiRevokeBuiltFree I.calldata + 4 by omega]
      using h'
  exact pairRequestsEncode2894
    (R := [⟨1287121381⟩, UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
    hstart (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    heap (by change multiRevokeBuiltFree I.calldata ≤ pre.size; have := hp.size; omega)
    (by omega) he.2
    (by rw [attesterRuntime_validJumps]; native_decide)

theorem multiRevokeNoCode {words : String → UInt256} {I g s0 σ k C mem aw out endptr sel target R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨877⟩
      (endptr :: sel :: target :: R) mem aw out σ k C)
    (hstack : R.length + 12 ≤ 1024) (hzero : extCodeSizeWord σ target = ⟨0⟩) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  obtain ⟨k', C', h'⟩ := attesterRuntime_block_877_fallthrough hstack
    (by rw [hzero]; rfl) h
  exact attesterRuntime_block_899
    (by simpa only [attesterRuntime_block_877_fallthrough_stack, List.length_cons] using hstack) h'

theorem multiRevokeReachCall {words : String → UInt256} {I g s0 σ k C aw R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨877⟩
      ([UInt256.ofNat (multiRevokeEncodedEnd I.calldata), ⟨1287121381⟩,
        UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      (multiRevokeEncodedMemory I.calldata) aw ByteArray.empty σ k C)
    (hstack : R.length + 13 ≤ 1024) (hc : MultiHeadChecks I.calldata)
    (hshape : BatchShape I.calldata) (hrows : BatchRowsValid I.calldata)
    (hne : extCodeSizeWord σ (UInt256.land (words "_eas") solcAddrMask) ≠ ⟨0⟩) :
    ∃ gasArg aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨906⟩
      ([gasArg, UInt256.land (words "_eas") solcAddrMask, ⟨0⟩,
        UInt256.ofNat (multiRevokeBuiltFree I.calldata),
        UInt256.ofNat (multiRevokeEncodedEnd I.calldata - multiRevokeBuiltFree I.calldata),
        UInt256.ofNat (multiRevokeBuiltFree I.calldata), ⟨0⟩,
        UInt256.ofNat (multiRevokeEncodedEnd I.calldata), ⟨1287121381⟩,
        UInt256.land (words "_eas") solcAddrMask, ⟨128⟩] ++ R)
      (multiRevokeEncodedMemory I.calldata) aw' ByteArray.empty σ k' C' := by
  have he := multiRevokeEncodedEnd_bounds hc hshape hrows
  obtain ⟨k', C', h'⟩ := attesterRuntime_block_877_taken
    (R := ⟨128⟩ :: R) (by simp only [List.length_cons]; omega)
    (by rw [isZero_eq_zero_of_ne hne]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attesterRuntime_block_877_taken_stack,
    multiRevokeEncodedMemory_freePtr hc hshape hrows,
    ofNat_sub_words (by omega : multiRevokeBuiltFree I.calldata ≤ multiRevokeEncodedEnd I.calldata)
      he.2] at h'
  have h'' := attesterRuntime_block_903 (by simp only [List.length_cons]; omega) h'
  exact ⟨_, _, _, _, h''⟩

theorem multiRevokeAfterCallFailure {words : String → UInt256} {I g s0 σ k C mem aw out R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨907⟩
      (⟨0⟩ :: R) mem aw out σ k C) (hstack : R.length + 4 ≤ 1024) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  have h' := attesterRuntime_block_907_fallthrough (by omega) (by decide) h
  exact attesterRuntime_block_914
    (by simpa only [attesterRuntime_block_907_fallthrough_stack, List.length_cons] using hstack) h'

theorem multiRevokeAfterCallSuccess {words : String → UInt256} {I g s0 σ k C mem aw out sel}
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨907⟩
      [⟨1⟩, x0, x1, x2, x3, x4, x5, x6, x7, x8, ⟨100⟩, sel] mem aw out σ k C) :
    RDret (immutableLayout.runtime attesterBytecode words) g s0 σ ByteArray.empty := by
  have h' := attesterRuntime_block_907_taken (by simp) (by decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  have h'' := attesterRuntime_block_923 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  exact attesterRuntime_block_100 (by simp [attesterRuntime_block_923_stack]) h''

end Benchmarks.EAS.Attester
