import Examples.UniswapV2Pair.SafeTransferDynamicCopyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem safeTransferDynamicMem6_read100_28 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem6 base ptr toWord value).readWithPadding (ptr.toNat + 100) 28 =
      (UInt256.land solcAddrMask toWord).toByteArray.extract 0 28 := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 := uadd_word_ofNat_toNat ptr 100 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 := uadd_word_ofNat_toNat ptr 132 (by omega)
  have hs2 := safeTransferDynamicMem2_size ptr hin hgap (by omega)
  have hu : 36 < USize.size := lt_usize 36 (by omega)
  unfold safeTransferDynamicMem6 safeTransferDynamicMem5 safeTransferDynamicMem4 safeTransferDynamicMem3
  rw [h64, h100, h132]
  change (writeCascade (safeTransferDynamicMem2 base ptr)
    [(ptr.toNat + 100, UInt256.land solcAddrMask toWord), (ptr.toNat + 132, value),
      (ptr.toNat + 64, ⟨68⟩), (64, ptr + ⟨164⟩)]).readWithPadding (ptr.toNat + 100) 28 = _
  have h := writeCascade_read_window_of_head (safeTransferDynamicMem2 base ptr) (ptr.toNat + 100) 0 28
    (UInt256.land solcAddrMask toWord) [(ptr.toNat + 132, value), (ptr.toNat + 64, ⟨68⟩), (64, ptr + ⟨164⟩)]
    (by rw [hs2]; omega)
    (by
      rw [hs2]
      simp only [WindowDisjointFromWrites]
      refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inr ⟨?_, ?_⟩, trivial⟩ <;> omega)
    (by omega) (by omega) (by omega)
  exact h

theorem safeTransferDynamicWord96_extract4_32 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicWord96 base ptr toWord value).toByteArray.extract 4 32 =
      (UInt256.land solcAddrMask toWord).toByteArray.extract 0 28 := by
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  unfold safeTransferDynamicWord96
  rw [h96, toByteArray_readWord_extract _ _ 4 28
    (by rw [safeTransferDynamicMem6_size ptr toWord value hin hgap hptr]; omega) (by omega) (by omega)]
  exact safeTransferDynamicMem6_read100_28 ptr toWord value hin hgap hptr

theorem safeTransferDynamicMem4_read128_32 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hbase : base.size ≤ ptr.toNat + 132) (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicMem4 base ptr toWord value).readWithPadding (ptr.toNat + 128) 32 =
      (UInt256.land solcAddrMask toWord).toByteArray.extract 28 32 ++ value.toByteArray.extract 0 28 := by
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 := uadd_word_ofNat_toNat ptr 100 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 := uadd_word_ofNat_toNat ptr 132 (by omega)
  have hs3 : (safeTransferDynamicMem3 base ptr toWord).size = ptr.toNat + 132 := by
    rw [safeTransferDynamicMem3_size ptr toWord hin hgap (by omega), Nat.max_eq_right hbase]
  have hleft : (safeTransferDynamicMem3 base ptr toWord).readWithPadding (ptr.toNat + 132 - 4) 4 =
      (UInt256.land solcAddrMask toWord).toByteArray.extract 28 32 := by
    unfold safeTransferDynamicMem3
    rw [h100]
    have h := toByteArray_write_read_window_of_gap (UInt256.land solcAddrMask toWord)
      (safeTransferDynamicMem2 base ptr) (ptr.toNat + 100) 28 4 (by omega) (by omega) (by omega)
      (by
        rw [safeTransferDynamicMem2_size ptr hin hgap (by omega)]
        have hu : 36 < USize.size := lt_usize 36 (by omega)
        omega)
    simpa only [show ptr.toNat + 132 - 4 = ptr.toNat + 100 + 28 by omega] using h
  unfold safeTransferDynamicMem4
  rw [h132]
  have h := safeTransferCalldata_read_boundary_word (safeTransferDynamicMem3 base ptr toWord)
    (UInt256.land solcAddrMask toWord) value (ptr.toNat + 132) (by omega) hs3 hleft
  simpa only [show ptr.toNat + 132 - 4 = ptr.toNat + 128 by omega] using h

theorem safeTransferDynamicCallMem0_read128_32 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hbase : base.size ≤ ptr.toNat + 132) (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicCallMem0 base ptr toWord value).readWithPadding (ptr.toNat + 128) 32 =
      (UInt256.land solcAddrMask toWord).toByteArray.extract 28 32 ++ value.toByteArray.extract 0 28 := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 hptr
  have hs4 := safeTransferDynamicMem4_size ptr toWord value hin hgap hptr
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  unfold safeTransferDynamicCallMem0 safeTransferDynamicMem7 safeTransferDynamicMem6 safeTransferDynamicMem5
  rw [h64, h96, h164]
  change (writeCascade (safeTransferDynamicMem4 base ptr toWord value)
    [(ptr.toNat + 64, ⟨68⟩), (64, ptr + ⟨164⟩),
      (ptr.toNat + 96, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
      (ptr.toNat + 164, safeTransferDynamicPatchedSelectorWord base ptr toWord value)]).readWithPadding (ptr.toNat + 128) 32 = _
  rw [writeCascade_read_preserved _ _ _ (by
    rw [hs4]
    simp only [WindowDisjointFromWrites]
    refine ⟨?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inr ⟨?_, ?_⟩,
      ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega)]
  exact safeTransferDynamicMem4_read128_32 ptr toWord value hin hgap hbase hptr

theorem safeTransferDynamicCopyWord1_toByteArray {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hbase : base.size ≤ ptr.toNat + 132) (hptr : ptr.toNat + 164 < UInt256.size) :
    (safeTransferDynamicCopyWord1 base ptr toWord value).toByteArray =
      (UInt256.land solcAddrMask toWord).toByteArray.extract 28 32 ++ value.toByteArray.extract 0 28 := by
  have h128 : (ptr + ⟨128⟩).toNat = ptr.toNat + 128 := uadd_word_ofNat_toNat ptr 128 (by omega)
  unfold safeTransferDynamicCopyWord1
  rw [h128, safeTransferDynamicCallMem0_read128_32 ptr toWord value hin hgap hbase hptr]
  apply toByteArray_ofNat_fromByteArrayBigEndian_of_size
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, toByteArray_size]
  omega

theorem safeTransferDynamicCallMem1_read160_4 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 196 < UInt256.size) :
    (safeTransferDynamicCallMem1 base ptr toWord value).readWithPadding (ptr.toNat + 160) 4 =
      value.toByteArray.extract 28 32 := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 := uadd_word_ofNat_toNat ptr 132 (by omega)
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have h196 : (ptr + ⟨196⟩).toNat = ptr.toNat + 196 := uadd_word_ofNat_toNat ptr 196 hptr
  have hs3 := safeTransferDynamicMem3_size ptr toWord hin hgap (by omega)
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  unfold safeTransferDynamicCallMem1 safeTransferDynamicCallMem0 safeTransferDynamicMem7
    safeTransferDynamicMem6 safeTransferDynamicMem5 safeTransferDynamicMem4
  rw [h64, h96, h132, h164, h196]
  change (writeCascade (safeTransferDynamicMem3 base ptr toWord)
    [(ptr.toNat + 132, value), (ptr.toNat + 64, ⟨68⟩), (64, ptr + ⟨164⟩),
      (ptr.toNat + 96, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
      (ptr.toNat + 164, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
      (ptr.toNat + 196, safeTransferDynamicCopyWord1 base ptr toWord value)]).readWithPadding (ptr.toNat + 160) 4 = _
  have h := writeCascade_read_window_of_head (safeTransferDynamicMem3 base ptr toWord) (ptr.toNat + 132) 28 4 value
    [(ptr.toNat + 64, ⟨68⟩), (64, ptr + ⟨164⟩),
      (ptr.toNat + 96, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
      (ptr.toNat + 164, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
      (ptr.toNat + 196, safeTransferDynamicCopyWord1 base ptr toWord value)]
    (by rw [hs3]; omega)
    (by
      rw [hs3]
      simp only [WindowDisjointFromWrites]
      refine ⟨?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inr ⟨?_, ?_⟩,
        ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega)
    (by omega) (by omega) (by omega)
  exact h

theorem safeTransferDynamicTailWord_extract0_4 {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 196 < UInt256.size) :
    (safeTransferDynamicTailWord base ptr toWord value).toByteArray.extract 0 4 = value.toByteArray.extract 28 32 := by
  have h160 : (ptr + ⟨160⟩).toNat = ptr.toNat + 160 := uadd_word_ofNat_toNat ptr 160 (by omega)
  rw [safeTransferDynamicTailWord, skimSafeTransferTailWord_extract0_4_of_source]
  unfold safeTransferDynamicTailSourceWord
  rw [h160, toByteArray_readWord_extract _ _ 0 4
    (by rw [safeTransferDynamicCallMem1_size ptr toWord value hin hgap hptr]; omega) (by omega) (by omega)]
  exact safeTransferDynamicCallMem1_read160_4 ptr toWord value hin hgap hptr

theorem safeTransferDynamicCallMem2_reads {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptr : ptr.toNat + 228 < UInt256.size) :
    (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding (ptr.toNat + 164) 32 =
      (safeTransferDynamicPatchedSelectorWord base ptr toWord value).toByteArray ∧
    (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding (ptr.toNat + 196) 32 =
      (safeTransferDynamicCopyWord1 base ptr toWord value).toByteArray ∧
    (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding (ptr.toNat + 228) 4 =
      (safeTransferDynamicTailWord base ptr toWord value).toByteArray.extract 0 4 := by
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have h196 : (ptr + ⟨196⟩).toNat = ptr.toNat + 196 := uadd_word_ofNat_toNat ptr 196 (by omega)
  have h228 : (ptr + ⟨228⟩).toNat = ptr.toNat + 228 := uadd_word_ofNat_toNat ptr 228 hptr
  have hs7 := safeTransferDynamicMem7_size ptr toWord value hin hgap (by omega)
  have hs0 := safeTransferDynamicCallMem0_size ptr toWord value hin hgap (by omega)
  have hs1 := safeTransferDynamicCallMem1_size ptr toWord value hin hgap (by omega)
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold safeTransferDynamicCallMem2 safeTransferDynamicCallMem1 safeTransferDynamicCallMem0
    rw [h164, h196, h228]
    change (writeCascade (safeTransferDynamicMem7 base ptr toWord value)
      [(ptr.toNat + 164, safeTransferDynamicPatchedSelectorWord base ptr toWord value),
        (ptr.toNat + 196, safeTransferDynamicCopyWord1 base ptr toWord value),
        (ptr.toNat + 228, safeTransferDynamicTailWord base ptr toWord value)]).readWithPadding (ptr.toNat + 164) 32 = _
    have h := writeCascade_read_word_of_head (safeTransferDynamicMem7 base ptr toWord value) (ptr.toNat + 164)
      (safeTransferDynamicPatchedSelectorWord base ptr toWord value)
      [(ptr.toNat + 196, safeTransferDynamicCopyWord1 base ptr toWord value),
        (ptr.toNat + 228, safeTransferDynamicTailWord base ptr toWord value)]
      (by rw [hs7]; omega)
      (by
        rw [hs7]
        simp only [WindowDisjointFromWrites]
        refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega)
    exact h
  · unfold safeTransferDynamicCallMem2
    rw [h228, write32_read_below _ _ (ptr.toNat + 228) (ptr.toNat + 196) (by rw [toByteArray_size])
      (by rw [hs1]; omega) (by omega)]
    unfold safeTransferDynamicCallMem1
    rw [h196]
    have h := toByteArray_write32_read_back (safeTransferDynamicCallMem0 base ptr toWord value)
      (safeTransferDynamicCopyWord1 base ptr toWord value) (ptr.toNat + 196) (by rw [hs0]; omega)
    exact h
  · unfold safeTransferDynamicCallMem2
    rw [h228]
    exact write32_read_prefix_len _ _ (ptr.toNat + 228) 4 (by rw [toByteArray_size])
      (by rw [hs1]; omega) (by omega) (by omega) (by omega)

theorem safeTransferDynamicCallMem2_calldata {base : ByteArray} (ptr toWord value : UInt256)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hbase : base.size ≤ ptr.toNat + 132) (hptr : ptr.toNat + 228 < UInt256.size) :
    (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding (ptr.toNat + 164) 68 =
      (transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68 := by
  obtain ⟨hr0, hr1, hr2⟩ := safeTransferDynamicCallMem2_reads ptr toWord value hin hgap hptr
  have hs := safeTransferDynamicCallMem2_size ptr toWord value hin hgap hptr
  rw [transferCalldataMem_read128_68,
    byteArray_readWithPadding_split _ (ptr.toNat + 164) 32 36 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hs]; omega)]
  rw [show ptr.toNat + 164 + 32 = ptr.toNat + 196 by omega,
    byteArray_readWithPadding_split _ (ptr.toNat + 196) 32 4 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hs]; omega)]
  rw [show ptr.toNat + 196 + 32 = ptr.toNat + 228 by omega, hr0, hr1, hr2,
    safeTransferDynamicPatchedSelectorWord, skimSafeTransferPatchedSelector_toByteArray,
    safeTransferDynamicWord96_extract4_32 ptr toWord value hin hgap (by omega),
    safeTransferDynamicCopyWord1_toByteArray ptr toWord value hin hgap hbase (by omega),
    safeTransferDynamicTailWord_extract0_4 ptr toWord value hin hgap (by omega)]
  have hjoin (word : UInt256) : word.toByteArray.extract 0 28 ++ word.toByteArray.extract 28 32 = word.toByteArray := by
    rw [ByteArray.extract_append_extract]
    exact toByteArray_extract_all word
  simp only [ByteArray.append_assoc]
  rw [← @ByteArray.append_assoc ((UInt256.land solcAddrMask toWord).toByteArray.extract 0 28)
    ((UInt256.land solcAddrMask toWord).toByteArray.extract 28 32)
    (value.toByteArray.extract 0 28 ++ value.toByteArray.extract 28 32), hjoin, hjoin]

end UniswapV2Pair
