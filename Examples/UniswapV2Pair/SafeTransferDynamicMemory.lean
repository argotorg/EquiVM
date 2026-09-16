import Examples.UniswapV2Pair.MemorySteps
import Examples.UniswapV2Pair.SkimSafeTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

noncomputable def safeTransferDynamicMem0 (base : ByteArray) (ptr : UInt256) : ByteArray :=
  (ptr + ⟨64⟩).toByteArray.write 0 base 64 32

noncomputable def safeTransferDynamicMem1 (base : ByteArray) (ptr : UInt256) : ByteArray :=
  (⟨25⟩ : UInt256).toByteArray.write 0 (safeTransferDynamicMem0 base ptr) ptr.toNat 32

noncomputable def safeTransferDynamicMem2 (base : ByteArray) (ptr : UInt256) : ByteArray :=
  skimSafeTransferSignatureWord.toByteArray.write 0 (safeTransferDynamicMem1 base ptr) (ptr + ⟨32⟩).toNat 32

abbrev safeTransferDynamicWords2 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (memoryWordActiveWords aw ptr) (ptr + ⟨32⟩)

noncomputable def safeTransferDynamicMem3 (base : ByteArray) (ptr toWord : UInt256) : ByteArray :=
  (UInt256.land solcAddrMask toWord).toByteArray.write 0 (safeTransferDynamicMem2 base ptr)
    (ptr + ⟨100⟩).toNat 32

noncomputable def safeTransferDynamicMem4 (base : ByteArray) (ptr toWord value : UInt256) : ByteArray :=
  value.toByteArray.write 0 (safeTransferDynamicMem3 base ptr toWord) (ptr + ⟨132⟩).toNat 32

abbrev safeTransferDynamicWords3 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (safeTransferDynamicWords2 aw ptr) (ptr + ⟨100⟩)

abbrev safeTransferDynamicWords4 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (safeTransferDynamicWords3 aw ptr) (ptr + ⟨132⟩)

theorem safeTransferDynamicMem0_size {base : ByteArray} (ptr : UInt256) (hin : 96 ≤ base.size) :
    (safeTransferDynamicMem0 base ptr).size = base.size := by
  unfold safeTransferDynamicMem0
  have h := toByteArray_write32_size_of_le base (ptr + ⟨64⟩) 64 base.size base.size rfl (by omega) (by omega)
  exact h

theorem safeTransferDynamicMem1_size {base : ByteArray} (ptr : UInt256) (hin : 96 ≤ base.size)
    (hgap : ptr.toNat - base.size < USize.size) :
    (safeTransferDynamicMem1 base ptr).size = max base.size (ptr.toNat + 32) := by
  exact (writeWord_size (safeTransferDynamicMem0 base ptr) ptr.toNat ⟨25⟩
    (by rwa [safeTransferDynamicMem0_size ptr hin])).trans
      (by rw [safeTransferDynamicMem0_size ptr hin])

theorem safeTransferDynamicMem2_size {base : ByteArray} (ptr : UInt256) (hin : 96 ≤ base.size)
    (hgap : ptr.toNat - base.size < USize.size) (hptr : ptr.toNat + 32 < UInt256.size) :
    (safeTransferDynamicMem2 base ptr).size = max base.size (ptr.toNat + 64) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := by
    rw [u256_add_comm ptr ⟨32⟩]
    exact uadd_lit32_toNat ptr hptr
  have hsize1 := safeTransferDynamicMem1_size ptr hin hgap
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  have hsize := writeWord_size (safeTransferDynamicMem1 base ptr) (ptr + ⟨32⟩).toNat
    skimSafeTransferSignatureWord (by rw [h32, hsize1]; omega)
  change (safeTransferDynamicMem2 base ptr).size = _ at hsize
  rw [h32, hsize1] at hsize
  exact hsize.trans (by omega)

theorem safeTransferDynamicMem2_read64 {base : ByteArray} (ptr : UInt256) (hin : 96 ≤ base.size)
    (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 32 < UInt256.size) :
    (safeTransferDynamicMem2 base ptr).readWithPadding 64 32 = (ptr + ⟨64⟩).toByteArray := by
  have hsize0 := safeTransferDynamicMem0_size ptr hin
  have hsize1 := safeTransferDynamicMem1_size ptr hin hgap
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := by
    rw [u256_add_comm ptr ⟨32⟩]
    exact uadd_lit32_toNat ptr hptr
  unfold safeTransferDynamicMem2
  rw [write32_read_below _ _ (ptr + ⟨32⟩).toNat 64 (by rw [toByteArray_size])
    (by rw [h32, hsize1]; omega) (by rw [h32]; omega)]
  unfold safeTransferDynamicMem1
  rw [toByteArray_write_read_below_of_gap _ _ ptr.toNat 64
    (by rw [hsize0]; omega) hptrLo (by rwa [hsize0])]
  unfold safeTransferDynamicMem0
  have h := toByteArray_write_read_back_of_gap (ptr + ⟨64⟩) base 64 (by
    have hu : 0 < USize.size := lt_usize 0 (by omega)
    omega)
  exact h

theorem safeTransferDynamicWords2_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 95 < UInt256.size) :
    (safeTransferDynamicWords2 aw ptr).toNat * 32 < UInt256.size ∧
    ptr.toNat + 64 ≤ (safeTransferDynamicWords2 aw ptr).toNat * 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := by
    rw [u256_add_comm ptr ⟨32⟩]
    exact uadd_lit32_toNat ptr (by omega)
  have haw1 := UInt256_ofNat_M_mul32_lt aw ptr haw (by omega)
  have hbound := UInt256_ofNat_M_mul32_lt (memoryWordActiveWords aw ptr) (ptr + ⟨32⟩)
    haw1 (by rw [h32]; omega)
  have hcover := UInt256_ofNat_M_covers (memoryWordActiveWords aw ptr) (ptr + ⟨32⟩)
    haw1 (by rw [h32]; omega)
  change (ptr + ⟨32⟩).toNat + 32 ≤ (safeTransferDynamicWords2 aw ptr).toNat * 32 at hcover
  refine ⟨hbound, ?_⟩
  simpa only [h32, Nat.add_assoc] using hcover

theorem safeTransferDynamicMem2_mload64 {base : ByteArray} (aw ptr : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 95 < UInt256.size) :
    memoryWordLoad (safeTransferDynamicMem2 base ptr) (safeTransferDynamicWords2 aw ptr) ⟨64⟩ = ptr + ⟨64⟩ ∧
    memoryWordActiveWords (safeTransferDynamicWords2 aw ptr) ⟨64⟩ = safeTransferDynamicWords2 aw ptr := by
  obtain ⟨hbound, hcover⟩ := safeTransferDynamicWords2_bounds aw ptr haw hptr
  have hsize := safeTransferDynamicMem2_size ptr hin hgap (by omega)
  have h96 : (⟨64⟩ : UInt256).toNat + 32 ≤ (safeTransferDynamicWords2 aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _
    omega
  constructor
  · exact mloadWordValue_of_readWithPadding
      (by change 64 < _; rw [hsize]; omega)
      (UInt256_mload_haw_of_cover _ _ hbound h96)
      (safeTransferDynamicMem2_read64 ptr hin hgap hptrLo (by omega))
  · exact UInt256_M_same_of_cover _ _ hbound h96

theorem safeTransferDynamicMem3_size {base : ByteArray} (ptr toWord : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 132 < UInt256.size) :
    (safeTransferDynamicMem3 base ptr toWord).size = max base.size (ptr.toNat + 132) := by
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 :=
    uadd_word_ofNat_toNat ptr 100 (by omega)
  have hsize2 := safeTransferDynamicMem2_size ptr hin hgap (by omega)
  have hu : 36 < USize.size := lt_usize 36 (by omega)
  have hsize := writeWord_size (safeTransferDynamicMem2 base ptr) (ptr + ⟨100⟩).toNat
    (UInt256.land solcAddrMask toWord) (by rw [h100, hsize2]; omega)
  change (safeTransferDynamicMem3 base ptr toWord).size = _ at hsize
  rw [h100, hsize2] at hsize
  exact hsize.trans (by omega)

theorem safeTransferDynamicMem4_size {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem4 base ptr toWord value).size = max base.size (ptr.toNat + 164) := by
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 :=
    uadd_word_ofNat_toNat ptr 132 (by omega)
  have hsize3 := safeTransferDynamicMem3_size ptr toWord hin hgap (by omega)
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  have hsize := writeWord_size (safeTransferDynamicMem3 base ptr toWord) (ptr + ⟨132⟩).toNat
    value (by rw [h132, hsize3]; omega)
  change (safeTransferDynamicMem4 base ptr toWord value).size = _ at hsize
  rw [h132, hsize3] at hsize
  exact hsize.trans (by omega)

theorem safeTransferDynamicMem4_read64 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem4 base ptr toWord value).readWithPadding 64 32 = (ptr + ⟨64⟩).toByteArray := by
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 :=
    uadd_word_ofNat_toNat ptr 100 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 :=
    uadd_word_ofNat_toNat ptr 132 (by omega)
  have hsize2 := safeTransferDynamicMem2_size ptr hin hgap (by omega)
  have hsize3 := safeTransferDynamicMem3_size ptr toWord hin hgap (by omega)
  have hu : 36 < USize.size := lt_usize 36 (by omega)
  unfold safeTransferDynamicMem4
  rw [write32_read_below _ _ (ptr + ⟨132⟩).toNat 64 (by rw [toByteArray_size])
    (by rw [h132, hsize3]; omega) (by rw [h132]; omega)]
  unfold safeTransferDynamicMem3
  rw [toByteArray_write_read_below_of_gap _ _ (ptr + ⟨100⟩).toNat 64
    (by rw [hsize2]; omega) (by rw [h100]; omega) (by rw [h100, hsize2]; omega)]
  exact safeTransferDynamicMem2_read64 ptr hin hgap hptrLo (by omega)

theorem safeTransferDynamicWords4_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 195 < UInt256.size) :
    (safeTransferDynamicWords4 aw ptr).toNat * 32 < UInt256.size ∧
    ptr.toNat + 164 ≤ (safeTransferDynamicWords4 aw ptr).toNat * 32 := by
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 :=
    uadd_word_ofNat_toNat ptr 100 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 :=
    uadd_word_ofNat_toNat ptr 132 (by omega)
  have hb2 := (safeTransferDynamicWords2_bounds aw ptr haw (by omega)).1
  have hb3 := UInt256_ofNat_M_mul32_lt (safeTransferDynamicWords2 aw ptr) (ptr + ⟨100⟩)
    hb2 (by rw [h100]; omega)
  have hb4 := UInt256_ofNat_M_mul32_lt (safeTransferDynamicWords3 aw ptr) (ptr + ⟨132⟩)
    hb3 (by rw [h132]; omega)
  have hc4 := UInt256_ofNat_M_covers (safeTransferDynamicWords3 aw ptr) (ptr + ⟨132⟩)
    hb3 (by rw [h132]; omega)
  change (ptr + ⟨132⟩).toNat + 32 ≤ (safeTransferDynamicWords4 aw ptr).toNat * 32 at hc4
  exact ⟨hb4, by simpa only [h132, Nat.add_assoc] using hc4⟩

theorem safeTransferDynamicMem4_mload64 {base : ByteArray} (aw ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 195 < UInt256.size) :
    memoryWordLoad (safeTransferDynamicMem4 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) ⟨64⟩ = ptr + ⟨64⟩ ∧
    memoryWordActiveWords (safeTransferDynamicWords4 aw ptr) ⟨64⟩ = safeTransferDynamicWords4 aw ptr := by
  obtain ⟨hbound, hcover⟩ := safeTransferDynamicWords4_bounds aw ptr haw hptr
  have hsize := safeTransferDynamicMem4_size ptr toWord value hin hgap (by omega)
  have h96 : (⟨64⟩ : UInt256).toNat + 32 ≤ (safeTransferDynamicWords4 aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _
    omega
  constructor
  · exact mloadWordValue_of_readWithPadding
      (by change 64 < _; rw [hsize]; omega)
      (UInt256_mload_haw_of_cover _ _ hbound h96)
      (safeTransferDynamicMem4_read64 ptr toWord value hin hgap hptrLo (by omega))
  · exact UInt256_M_same_of_cover _ _ hbound h96

noncomputable def safeTransferDynamicMem5 (base : ByteArray) (ptr toWord value : UInt256) : ByteArray :=
  (⟨68⟩ : UInt256).toByteArray.write 0 (safeTransferDynamicMem4 base ptr toWord value) (ptr + ⟨64⟩).toNat 32

noncomputable def safeTransferDynamicMem6 (base : ByteArray) (ptr toWord value : UInt256) : ByteArray :=
  (ptr + ⟨164⟩).toByteArray.write 0 (safeTransferDynamicMem5 base ptr toWord value) 64 32

theorem safeTransferDynamicMem5_size {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem5 base ptr toWord value).size = max base.size (ptr.toNat + 164) := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hs4 := safeTransferDynamicMem4_size ptr toWord value hin hgap hptr
  have h := toByteArray_write32_size_of_le (safeTransferDynamicMem4 base ptr toWord value)
    ⟨68⟩ (ptr + ⟨64⟩).toNat _ (max base.size (ptr.toNat + 164)) hs4 (by rw [h64, hs4]; omega) (by rw [h64]; omega)
  exact h

theorem safeTransferDynamicMem6_size {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem6 base ptr toWord value).size = max base.size (ptr.toNat + 164) := by
  have hs5 := safeTransferDynamicMem5_size ptr toWord value hin hgap hptr
  have h := toByteArray_write32_size_of_le (safeTransferDynamicMem5 base ptr toWord value)
    (ptr + ⟨164⟩) 64 _ (max base.size (ptr.toNat + 164)) hs5 (by rw [hs5]; omega) (by omega)
  exact h

noncomputable def safeTransferDynamicWord96 (base : ByteArray) (ptr toWord value : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    ((safeTransferDynamicMem6 base ptr toWord value).readWithPadding (ptr + ⟨96⟩).toNat 32))

noncomputable def safeTransferDynamicPatchedSelectorWord (base : ByteArray) (ptr toWord value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft transferSelectorWord ⟨224⟩)
    (UInt256.land skimSafeTransferSelectorPatchMask
      (safeTransferDynamicWord96 base ptr toWord value))

noncomputable def safeTransferDynamicMem7 (base : ByteArray) (ptr toWord value : UInt256) : ByteArray :=
  (safeTransferDynamicPatchedSelectorWord base ptr toWord value).toByteArray.write 0
    (safeTransferDynamicMem6 base ptr toWord value) (ptr + ⟨96⟩).toNat 32

theorem safeTransferDynamicMem6_mload96 {base : ByteArray} (aw ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 195 < UInt256.size) :
    memoryWordLoad (safeTransferDynamicMem6 base ptr toWord value) (safeTransferDynamicWords4 aw ptr)
      (ptr + ⟨96⟩) = safeTransferDynamicWord96 base ptr toWord value ∧
    memoryWordActiveWords (safeTransferDynamicWords4 aw ptr) (ptr + ⟨96⟩) = safeTransferDynamicWords4 aw ptr := by
  obtain ⟨hb4, hc4⟩ := safeTransferDynamicWords4_bounds aw ptr haw hptr
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have hc : (ptr + ⟨96⟩).toNat + 32 ≤ (safeTransferDynamicWords4 aw ptr).toNat * 32 := by rw [h96]; omega
  constructor
  · exact mloadValue_eq_readWithPadding_of_lt_size _ _ _ _
      (safeTransferDynamicMem6_size ptr toWord value hin hgap (by omega))
      (by rw [h96]; omega) (UInt256_mload_haw_of_cover _ _ hb4 hc)
  · exact UInt256_M_same_of_cover _ _ hb4 hc

theorem safeTransferDynamicMem7_size {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem7 base ptr toWord value).size = max base.size (ptr.toNat + 164) := by
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have hs6 := safeTransferDynamicMem6_size ptr toWord value hin hgap hptr
  have h := toByteArray_write32_size_of_le (safeTransferDynamicMem6 base ptr toWord value)
    (safeTransferDynamicPatchedSelectorWord base ptr toWord value) (ptr + ⟨96⟩).toNat _
    (max base.size (ptr.toNat + 164)) hs6 (by rw [h96, hs6]; omega) (by rw [h96]; omega)
  exact h

theorem safeTransferDynamicMem7_reads {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem7 base ptr toWord value).readWithPadding 64 32 = (ptr + ⟨164⟩).toByteArray ∧
    (safeTransferDynamicMem7 base ptr toWord value).readWithPadding (ptr + ⟨64⟩).toNat 32 = (⟨68⟩ : UInt256).toByteArray ∧
    (safeTransferDynamicMem7 base ptr toWord value).readWithPadding (ptr + ⟨96⟩).toNat 32 =
      (safeTransferDynamicPatchedSelectorWord base ptr toWord value).toByteArray := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have hs4 := safeTransferDynamicMem4_size ptr toWord value hin hgap hptr
  have hs5 := safeTransferDynamicMem5_size ptr toWord value hin hgap hptr
  have hs6 := safeTransferDynamicMem6_size ptr toWord value hin hgap hptr
  refine ⟨?_, ?_, ?_⟩
  · unfold safeTransferDynamicMem7
    rw [write32_read_below _ _ (ptr + ⟨96⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [h96, hs6]; omega) (by rw [h96]; omega)]
    unfold safeTransferDynamicMem6
    have h := toByteArray_write32_read_back (safeTransferDynamicMem5 base ptr toWord value)
      (ptr + ⟨164⟩) 64 (by rw [hs5]; omega)
    exact h
  · unfold safeTransferDynamicMem7
    rw [write32_read_below _ _ (ptr + ⟨96⟩).toNat (ptr + ⟨64⟩).toNat (by rw [toByteArray_size])
      (by rw [h96, hs6]; omega) (by rw [h64, h96])]
    unfold safeTransferDynamicMem6
    rw [write32_read_above _ _ 64 (ptr + ⟨64⟩).toNat (by rw [toByteArray_size])
      (by rw [hs5]; omega) (by rw [h64]; omega) (by rw [h64, hs5]; omega)]
    unfold safeTransferDynamicMem5
    have h := toByteArray_write32_read_back (safeTransferDynamicMem4 base ptr toWord value)
      ⟨68⟩ (ptr + ⟨64⟩).toNat (by rw [h64, hs4]; omega)
    exact h
  · unfold safeTransferDynamicMem7
    have h := toByteArray_write32_read_back (safeTransferDynamicMem6 base ptr toWord value)
      (safeTransferDynamicPatchedSelectorWord base ptr toWord value) (ptr + ⟨96⟩).toNat
      (by rw [h96, hs6]; omega)
    exact h

end UniswapV2Pair
