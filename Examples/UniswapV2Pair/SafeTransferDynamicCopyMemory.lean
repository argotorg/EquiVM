import Examples.UniswapV2Pair.SafeTransferDynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

noncomputable def safeTransferDynamicCallMem0 (base : ByteArray) (ptr toWord value : UInt256) : ByteArray :=
  (safeTransferDynamicPatchedSelectorWord base ptr toWord value).toByteArray.write 0
    (safeTransferDynamicMem7 base ptr toWord value) (ptr + ⟨164⟩).toNat 32

abbrev safeTransferDynamicCallWords0 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (safeTransferDynamicWords4 aw ptr) (ptr + ⟨164⟩)

noncomputable def safeTransferDynamicCopyWord1 (base : ByteArray) (ptr toWord value : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    ((safeTransferDynamicCallMem0 base ptr toWord value).readWithPadding (ptr + ⟨128⟩).toNat 32))

noncomputable def safeTransferDynamicCallMem1 (base : ByteArray) (ptr toWord value : UInt256) : ByteArray :=
  (safeTransferDynamicCopyWord1 base ptr toWord value).toByteArray.write 0
    (safeTransferDynamicCallMem0 base ptr toWord value) (ptr + ⟨196⟩).toNat 32

abbrev safeTransferDynamicCallWords1 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (safeTransferDynamicCallWords0 aw ptr) (ptr + ⟨196⟩)

noncomputable def safeTransferDynamicTailSourceWord (base : ByteArray) (ptr toWord value : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    ((safeTransferDynamicCallMem1 base ptr toWord value).readWithPadding (ptr + ⟨160⟩).toNat 32))

noncomputable def safeTransferDynamicTailWord (base : ByteArray) (ptr toWord value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land (safeTransferDynamicTailSourceWord base ptr toWord value)
    (UInt256.lnot skimSafeTransferTailMask))
    (UInt256.land ⟨0⟩ skimSafeTransferTailMask)

noncomputable def safeTransferDynamicCallMem2 (base : ByteArray) (ptr toWord value : UInt256) : ByteArray :=
  (safeTransferDynamicTailWord base ptr toWord value).toByteArray.write 0
    (safeTransferDynamicCallMem1 base ptr toWord value) (ptr + ⟨228⟩).toNat 32

abbrev safeTransferDynamicCallWords2 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (safeTransferDynamicCallWords1 aw ptr) (ptr + ⟨228⟩)

theorem safeTransferDynamicCallMem0_size {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicCallMem0 base ptr toWord value).size = max base.size (ptr.toNat + 196) := by
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 hptr
  have hs7 := safeTransferDynamicMem7_size ptr toWord value hin hgap hptr
  have h := toByteArray_write32_size_of_le (safeTransferDynamicMem7 base ptr toWord value)
    (safeTransferDynamicPatchedSelectorWord base ptr toWord value) (ptr + ⟨164⟩).toNat _
    (max base.size (ptr.toNat + 196)) hs7 (by rw [h164, hs7]; omega) (by rw [h164]; omega)
  exact h

theorem safeTransferDynamicCallMem1_size {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 196 < UInt256.size) :
    (safeTransferDynamicCallMem1 base ptr toWord value).size = max base.size (ptr.toNat + 228) := by
  have h196 : (ptr + ⟨196⟩).toNat = ptr.toNat + 196 := uadd_word_ofNat_toNat ptr 196 hptr
  have hs0 := safeTransferDynamicCallMem0_size ptr toWord value hin hgap (by omega)
  have h := toByteArray_write32_size_of_le (safeTransferDynamicCallMem0 base ptr toWord value)
    (safeTransferDynamicCopyWord1 base ptr toWord value) (ptr + ⟨196⟩).toNat _
    (max base.size (ptr.toNat + 228)) hs0 (by rw [h196, hs0]; omega) (by rw [h196]; omega)
  exact h

theorem safeTransferDynamicCallMem2_size {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 228 < UInt256.size) :
    (safeTransferDynamicCallMem2 base ptr toWord value).size = max base.size (ptr.toNat + 260) := by
  have h228 : (ptr + ⟨228⟩).toNat = ptr.toNat + 228 := uadd_word_ofNat_toNat ptr 228 hptr
  have hs1 := safeTransferDynamicCallMem1_size ptr toWord value hin hgap (by omega)
  have h := toByteArray_write32_size_of_le (safeTransferDynamicCallMem1 base ptr toWord value)
    (safeTransferDynamicTailWord base ptr toWord value) (ptr + ⟨228⟩).toNat _
    (max base.size (ptr.toNat + 260)) hs1 (by rw [h228, hs1]; omega) (by rw [h228]; omega)
  exact h

theorem safeTransferDynamicCallWords_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size) :
    ((safeTransferDynamicCallWords0 aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 196 ≤ (safeTransferDynamicCallWords0 aw ptr).toNat * 32) ∧
    ((safeTransferDynamicCallWords1 aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 228 ≤ (safeTransferDynamicCallWords1 aw ptr).toNat * 32) ∧
    ((safeTransferDynamicCallWords2 aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 260 ≤ (safeTransferDynamicCallWords2 aw ptr).toNat * 32) := by
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have h196 : (ptr + ⟨196⟩).toNat = ptr.toNat + 196 := uadd_word_ofNat_toNat ptr 196 (by omega)
  have h228 : (ptr + ⟨228⟩).toNat = ptr.toNat + 228 := uadd_word_ofNat_toNat ptr 228 (by omega)
  have hb4 := (safeTransferDynamicWords4_bounds aw ptr haw (by omega)).1
  have hb0 := UInt256_ofNat_M_mul32_lt (safeTransferDynamicWords4 aw ptr) (ptr + ⟨164⟩) hb4 (by rw [h164]; omega)
  have hc0 := UInt256_ofNat_M_covers (safeTransferDynamicWords4 aw ptr) (ptr + ⟨164⟩) hb4 (by rw [h164]; omega)
  have hb1 := UInt256_ofNat_M_mul32_lt (safeTransferDynamicCallWords0 aw ptr) (ptr + ⟨196⟩) hb0 (by rw [h196]; omega)
  have hc1 := UInt256_ofNat_M_covers (safeTransferDynamicCallWords0 aw ptr) (ptr + ⟨196⟩) hb0 (by rw [h196]; omega)
  have hb2 := UInt256_ofNat_M_mul32_lt (safeTransferDynamicCallWords1 aw ptr) (ptr + ⟨228⟩) hb1 (by rw [h228]; omega)
  have hc2 := UInt256_ofNat_M_covers (safeTransferDynamicCallWords1 aw ptr) (ptr + ⟨228⟩) hb1 (by rw [h228]; omega)
  change (ptr + ⟨164⟩).toNat + 32 ≤ (safeTransferDynamicCallWords0 aw ptr).toNat * 32 at hc0
  change (ptr + ⟨196⟩).toNat + 32 ≤ (safeTransferDynamicCallWords1 aw ptr).toNat * 32 at hc1
  change (ptr + ⟨228⟩).toNat + 32 ≤ (safeTransferDynamicCallWords2 aw ptr).toNat * 32 at hc2
  refine ⟨⟨hb0, ?_⟩, ⟨hb1, ?_⟩, ⟨hb2, ?_⟩⟩
  · simpa only [h164, Nat.add_assoc] using hc0
  · simpa only [h196, Nat.add_assoc] using hc1
  · simpa only [h228, Nat.add_assoc] using hc2

theorem safeTransferDynamicCallMem2_read64 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 228 < UInt256.size) :
    (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding 64 32 = (ptr + ⟨164⟩).toByteArray := by
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have h196 : (ptr + ⟨196⟩).toNat = ptr.toNat + 196 := uadd_word_ofNat_toNat ptr 196 (by omega)
  have h228 : (ptr + ⟨228⟩).toNat = ptr.toNat + 228 := uadd_word_ofNat_toNat ptr 228 hptr
  have hs7 := safeTransferDynamicMem7_size ptr toWord value hin hgap (by omega)
  have hs0 := safeTransferDynamicCallMem0_size ptr toWord value hin hgap (by omega)
  have hs1 := safeTransferDynamicCallMem1_size ptr toWord value hin hgap (by omega)
  unfold safeTransferDynamicCallMem2
  rw [write32_read_below _ _ (ptr + ⟨228⟩).toNat 64 (by rw [toByteArray_size])
    (by rw [h228, hs1]; omega) (by rw [h228]; omega)]
  unfold safeTransferDynamicCallMem1
  rw [write32_read_below _ _ (ptr + ⟨196⟩).toNat 64 (by rw [toByteArray_size])
    (by rw [h196, hs0]; omega) (by rw [h196]; omega)]
  unfold safeTransferDynamicCallMem0
  rw [write32_read_below _ _ (ptr + ⟨164⟩).toNat 64 (by rw [toByteArray_size])
    (by rw [h164, hs7]; omega) (by rw [h164]; omega)]
  exact (safeTransferDynamicMem7_reads ptr toWord value hin hgap hptrLo (by omega)).1

theorem safeTransferDynamicCallMem2_read96 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 128 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 128 ≤ ptr.toNat)
    (hptr : ptr.toNat + 228 < UInt256.size) :
    (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding 96 32 = base.readWithPadding 96 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 := uadd_word_ofNat_toNat ptr 100 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 := uadd_word_ofNat_toNat ptr 132 (by omega)
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have h196 : (ptr + ⟨196⟩).toNat = ptr.toNat + 196 := uadd_word_ofNat_toNat ptr 196 (by omega)
  have h228 : (ptr + ⟨228⟩).toNat = ptr.toNat + 228 := uadd_word_ofNat_toNat ptr 228 hptr
  have hu : 36 < USize.size := lt_usize 36 (by omega)
  unfold safeTransferDynamicCallMem2 safeTransferDynamicCallMem1 safeTransferDynamicCallMem0
    safeTransferDynamicMem7 safeTransferDynamicMem6 safeTransferDynamicMem5 safeTransferDynamicMem4
    safeTransferDynamicMem3 safeTransferDynamicMem2 safeTransferDynamicMem1 safeTransferDynamicMem0
  rw [h32, h64, h96, h100, h132, h164, h196, h228]
  change (writeCascade base [(64, ptr + ⟨64⟩), (ptr.toNat, ⟨25⟩), (ptr.toNat + 32, skimSafeTransferSignatureWord),
    (ptr.toNat + 100, UInt256.land solcAddrMask toWord), (ptr.toNat + 132, value),
    (ptr.toNat + 64, ⟨68⟩), (64, ptr + ⟨164⟩),
    (ptr.toNat + 96, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
    (ptr.toNat + 164, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
    (ptr.toNat + 196, safeTransferDynamicCopyWord1 base ptr toWord value),
    (ptr.toNat + 228, safeTransferDynamicTailWord base ptr toWord value)]).readWithPadding 96 32 = _
  apply writeCascade_read_preserved
  simp only [WindowDisjointFromWrites]
  refine ⟨?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
    ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
    ?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
    ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

end UniswapV2Pair
