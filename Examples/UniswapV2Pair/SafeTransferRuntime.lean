import Examples.UniswapV2Pair.SkimSafeTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! Shared runtime helpers for the `_safeTransfer` routine. -/

noncomputable def safeTransferRuntimeMem0 (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨192⟩ : UInt256)).write 0 base 64 32

noncomputable def safeTransferRuntimeMem1 (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0 (safeTransferRuntimeMem0 base) 128 32

noncomputable def safeTransferRuntimeMem2 (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray skimSafeTransferSignatureWord).write 0
    (safeTransferRuntimeMem1 base) 160 32

noncomputable def safeTransferRuntimeMem3
    (base : ByteArray) (toWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).write 0
    (safeTransferRuntimeMem2 base) 228 32

noncomputable def safeTransferRuntimeMem4
    (base : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (safeTransferRuntimeMem3 base toWord) 260 32

noncomputable def safeTransferRuntimeMem5
    (base : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨68⟩ : UInt256)).write 0
    (safeTransferRuntimeMem4 base toWord value) 192 32

noncomputable def safeTransferRuntimeMem5WritesAfter64
    (toWord value : UInt256) : List (Nat × UInt256) :=
  [(128, (⟨25⟩ : UInt256)),
   (160, skimSafeTransferSignatureWord),
   (228, UInt256.land solcAddrMask toWord),
   (260, value),
   (192, (⟨68⟩ : UInt256))]

noncomputable def safeTransferRuntimeMem5Writes
    (toWord value : UInt256) : List (Nat × UInt256) :=
  (64, (⟨192⟩ : UInt256)) :: safeTransferRuntimeMem5WritesAfter64 toWord value

theorem safeTransferRuntimeMem5_eq_writeCascade
    (base : ByteArray) (toWord value : UInt256) :
    safeTransferRuntimeMem5 base toWord value =
      writeCascade base (safeTransferRuntimeMem5Writes toWord value) := by
  rfl

theorem safeTransferRuntimeMem5Writes_size (toWord value : UInt256) :
    writeCascadeSize 164 (safeTransferRuntimeMem5Writes toWord value) = 292 := by
  rfl

theorem safeTransferRuntimeMem5Writes_gaps (toWord value : UInt256) :
    WriteGapsOk 164 (safeTransferRuntimeMem5Writes toWord value) := by
  simp [WriteGapsOk, safeTransferRuntimeMem5Writes,
    safeTransferRuntimeMem5WritesAfter64]
  exact lt_usize 36 (by norm_num)

theorem safeTransferRuntimeMem5WritesAfter64_disjoint64 (toWord value : UInt256) :
    WindowDisjointFromWrites 164 64 32
      (safeTransferRuntimeMem5WritesAfter64 toWord value) := by
  simp [WindowDisjointFromWrites, safeTransferRuntimeMem5WritesAfter64]
  exact lt_usize 36 (by norm_num)

noncomputable def safeTransferRuntimeMem6
    (base : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨292⟩ : UInt256)).write 0
    (safeTransferRuntimeMem5 base toWord value) 64 32

noncomputable def safeTransferRuntimeWord224
    (base : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian ((safeTransferRuntimeMem6 base toWord value).readWithPadding 224 32))

noncomputable def safeTransferRuntimePatchedSelectorWord
    (base : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft transferSelectorWord ⟨224⟩)
    (UInt256.land skimSafeTransferSelectorPatchMask
      (safeTransferRuntimeWord224 base toWord value))

noncomputable def safeTransferRuntimeMem7
    (base : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value)).write 0
    (safeTransferRuntimeMem6 base toWord value) 224 32

theorem safeTransferRuntimeMem0_size {base : ByteArray}
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem0 base).size = 164 := by
  unfold safeTransferRuntimeMem0
  exact toByteArray_write32_size_of_le _ _ 64 164 164 hbase
    (by rw [hbase]; omega) (by norm_num)

theorem safeTransferRuntimeMem1_size {base : ByteArray}
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem1 base).size = 164 := by
  unfold safeTransferRuntimeMem1
  exact toByteArray_write32_size_of_le _ _ 128 164 164
    (safeTransferRuntimeMem0_size hbase)
    (by rw [safeTransferRuntimeMem0_size hbase]; omega)
    (by norm_num)

theorem safeTransferRuntimeMem2_size {base : ByteArray}
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem2 base).size = 192 := by
  unfold safeTransferRuntimeMem2
  exact toByteArray_write32_size_of_le _ _ 160 164 192
    (safeTransferRuntimeMem1_size hbase)
    (by rw [safeTransferRuntimeMem1_size hbase]; omega)
    (by norm_num)

theorem safeTransferRuntimeMem0_read64 {base : ByteArray}
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem0 base).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold safeTransferRuntimeMem0
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size]) (by rw [hbase]; omega)]
  rw [show (UInt256.toByteArray (⟨192⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨192⟩ : UInt256)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem safeTransferRuntimeMem1_read64 {base : ByteArray}
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem1 base).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold safeTransferRuntimeMem1
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem0_size hbase]; omega) (by omega)]
  exact safeTransferRuntimeMem0_read64 hbase

theorem safeTransferRuntimeMem2_read64 {base : ByteArray}
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem2 base).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold safeTransferRuntimeMem2 safeTransferRuntimeMem1 safeTransferRuntimeMem0
  simpa [writeCascade, Reasoning.Theory.writeWord] using
    writeCascade_read_word_of_head_of_base
      base (base := 164) (off := 64) (⟨192⟩ : UInt256)
      [(128, (⟨25⟩ : UInt256)), (160, skimSafeTransferSignatureWord)]
      hbase
      (lt_usize 0 (by norm_num))
      (by simp [WindowDisjointFromWrites])

theorem safeTransferRuntimeMem2_mload64 {base : ByteArray}
    (hbase : base.size = 164) :
    (if (⟨64⟩ : UInt256).toNat ≥ (safeTransferRuntimeMem2 base).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeMem2 base).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [safeTransferRuntimeMem2_size hbase]; decide)
    (by native_decide) (safeTransferRuntimeMem2_read64 hbase)

theorem safeTransferRuntimeMem3_size
    {base : ByteArray} (toWord : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem3 base toWord).size = 260 := by
  unfold safeTransferRuntimeMem3
  exact toByteArray_write32_size_of_ge _ _ 228 192 260
    (safeTransferRuntimeMem2_size hbase)
    (by norm_num) (lt_usize 36 (by norm_num)) (by norm_num)

theorem safeTransferRuntimeMem3_read64
    {base : ByteArray} (toWord : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem3 base toWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold safeTransferRuntimeMem3
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask toWord) _ 228 64
      (by rw [safeTransferRuntimeMem2_size hbase]; omega) (by omega)
      (by rw [safeTransferRuntimeMem2_size hbase]; exact lt_usize _ (by norm_num))]
  exact safeTransferRuntimeMem2_read64 hbase

theorem safeTransferRuntimeMem4_size
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem4 base toWord value).size = 292 := by
  unfold safeTransferRuntimeMem4
  exact toByteArray_write32_size_of_ge _ _ 260 260 292
    (safeTransferRuntimeMem3_size toWord hbase)
    (by norm_num) (lt_usize 0 (by norm_num)) (by norm_num)

theorem safeTransferRuntimeMem4_read64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem4 base toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold safeTransferRuntimeMem4 safeTransferRuntimeMem3
  change (writeCascade (safeTransferRuntimeMem2 base)
      [(228, UInt256.land solcAddrMask toWord), (260, value)]).readWithPadding 64 32 =
    UInt256.toByteArray (⟨192⟩ : UInt256)
  rw [writeCascade_read_preserved_len]
  · exact safeTransferRuntimeMem2_read64 hbase
  · rw [safeTransferRuntimeMem2_size hbase]
    simp [WindowDisjointFromWrites]
    exact lt_usize 36 (by norm_num)
  · norm_num
  · norm_num

theorem safeTransferRuntimeMem4_mload64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨64⟩ : UInt256).toNat ≥ (safeTransferRuntimeMem4 base toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeMem4 base toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [safeTransferRuntimeMem4_size toWord value hbase]; decide)
    (by native_decide) (safeTransferRuntimeMem4_read64 toWord value hbase)

theorem safeTransferRuntimeMem5_size
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem5 base toWord value).size = 292 := by
  rw [safeTransferRuntimeMem5_eq_writeCascade]
  exact safeTransferCalldata_writeCascade_size _ _ 164 292
    hbase
    (by
      rw [hbase]
      exact safeTransferRuntimeMem5Writes_gaps toWord value)
    (safeTransferRuntimeMem5Writes_size toWord value)

theorem safeTransferRuntimeMem6_size
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem6 base toWord value).size = 292 := by
  unfold safeTransferRuntimeMem6
  exact toByteArray_write32_size_of_le _ _ 64 292 292
    (safeTransferRuntimeMem5_size toWord value hbase)
    (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)
    (by norm_num)

theorem safeTransferRuntimeMem5_read64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem5 base toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  rw [safeTransferRuntimeMem5_eq_writeCascade]
  exact writeCascade_read_word_of_head_of_base base (base := 164) (off := 64)
    (⟨192⟩ : UInt256) (safeTransferRuntimeMem5WritesAfter64 toWord value)
    hbase (lt_usize 0 (by norm_num))
    (safeTransferRuntimeMem5WritesAfter64_disjoint64 toWord value)

theorem safeTransferRuntimeMem6_read64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem6 base toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold safeTransferRuntimeMem6
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)]
  rw [show (UInt256.toByteArray (⟨292⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨292⟩ : UInt256)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem safeTransferRuntimeMem7_size
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem7 base toWord value).size = 292 := by
  unfold safeTransferRuntimeMem7
  exact toByteArray_write32_size_of_le _ _ 224 292 292
    (safeTransferRuntimeMem6_size toWord value hbase)
    (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)
    (by norm_num)

theorem safeTransferRuntimeMem7_read64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem7 base toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold safeTransferRuntimeMem7
  rw [write32_read_below _ _ 224 64 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega) (by omega)]
  exact safeTransferRuntimeMem6_read64 toWord value hbase

theorem safeTransferRuntimeMem7_mload64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨64⟩ : UInt256).toNat ≥ (safeTransferRuntimeMem7 base toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeMem7 base toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [safeTransferRuntimeMem7_size toWord value hbase]; decide)
    (by native_decide) (safeTransferRuntimeMem7_read64 toWord value hbase)

theorem safeTransferRuntimeMem5_read192
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem5 base toWord value).readWithPadding 192 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold safeTransferRuntimeMem5
  rw [write32_read_back _ _ 192 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem4_size toWord value hbase]; omega)]
  rw [show (UInt256.toByteArray (⟨68⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨68⟩ : UInt256)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem safeTransferRuntimeMem6_read192
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem6 base toWord value).readWithPadding 192 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold safeTransferRuntimeMem6
  rw [write32_read_above _ _ 64 192 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)]
  exact safeTransferRuntimeMem5_read192 toWord value hbase

theorem safeTransferRuntimeMem7_read192
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem7 base toWord value).readWithPadding 192 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold safeTransferRuntimeMem7
  rw [write32_read_below _ _ 224 192 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega) (by omega)]
  exact safeTransferRuntimeMem6_read192 toWord value hbase

theorem safeTransferRuntimeMem7_mload192
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨192⟩ : UInt256).toNat ≥ (safeTransferRuntimeMem7 base toWord value).size
        ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeMem7 base toWord value).readWithPadding
          (⟨192⟩ : UInt256).toNat 32)))
      = ⟨68⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [safeTransferRuntimeMem7_size toWord value hbase]; decide)
    (by native_decide) (safeTransferRuntimeMem7_read192 toWord value hbase)

theorem safeTransferRuntimeMem6_mload224
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨224⟩ : UInt256).toNat ≥ (safeTransferRuntimeMem6 base toWord value).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeMem6 base toWord value).readWithPadding
          (⟨224⟩ : UInt256).toNat 32)))
      = safeTransferRuntimeWord224 base toWord value := by
  unfold safeTransferRuntimeWord224
  exact mloadValue_eq_readWithPadding_of_lt_size _ (UInt256.ofNat 10) ⟨224⟩ 292
    (safeTransferRuntimeMem6_size toWord value hbase)
    (by native_decide) (by native_decide)

theorem safeTransferRuntimeMem7_read224
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem7 base toWord value).readWithPadding 224 32 =
      UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value) := by
  unfold safeTransferRuntimeMem7
  rw [write32_read_back _ _ 224 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)]
  rw [show (UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value)).extract 0 32 =
      UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value) by
    rw [show 32 =
        (UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem safeTransferRuntimeMem7_mload224
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨224⟩ : UInt256).toNat ≥ (safeTransferRuntimeMem7 base toWord value).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeMem7 base toWord value).readWithPadding
          (⟨224⟩ : UInt256).toNat 32)))
      = safeTransferRuntimePatchedSelectorWord base toWord value :=
  mloadWordValue_of_readWithPadding
    (by rw [safeTransferRuntimeMem7_size toWord value hbase]; decide)
    (by native_decide) (safeTransferRuntimeMem7_read224 toWord value hbase)

noncomputable def safeTransferRuntimeCallMem0
    (base : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value)).write 0
    (safeTransferRuntimeMem7 base toWord value) 292 32

noncomputable def safeTransferRuntimeCopyWord1
    (base : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((safeTransferRuntimeCallMem0 base toWord value).readWithPadding 256 32))

noncomputable def safeTransferRuntimeCallMem1
    (base : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (safeTransferRuntimeCopyWord1 base toWord value)).write 0
    (safeTransferRuntimeCallMem0 base toWord value) 324 32

noncomputable def safeTransferRuntimeTailSourceWord
    (base : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((safeTransferRuntimeCallMem1 base toWord value).readWithPadding 288 32))

noncomputable def safeTransferRuntimeTailWord
    (base : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (safeTransferRuntimeTailSourceWord base toWord value)
      (UInt256.lnot skimSafeTransferTailMask))
    (UInt256.land ⟨0⟩ skimSafeTransferTailMask)

noncomputable def safeTransferRuntimeCallMem2
    (base : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (safeTransferRuntimeTailWord base toWord value)).write 0
    (safeTransferRuntimeCallMem1 base toWord value) 356 32

theorem safeTransferRuntimeCallMem0_size
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem0 base toWord value).size = 324 := by
  unfold safeTransferRuntimeCallMem0
  rw [toByteArray_write_eq _ _ 292
      (by rw [safeTransferRuntimeMem7_size toWord value hbase])
      (by
        rw [safeTransferRuntimeMem7_size toWord value hbase]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    safeTransferRuntimeMem7_size toWord value hbase, ByteArray_zeroes_size,
    toByteArray_size]

theorem safeTransferRuntimeCallMem1_size
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem1 base toWord value).size = 356 := by
  unfold safeTransferRuntimeCallMem1
  rw [toByteArray_write_eq _ _ 324
      (by rw [safeTransferRuntimeCallMem0_size toWord value hbase])
      (by
        rw [safeTransferRuntimeCallMem0_size toWord value hbase]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    safeTransferRuntimeCallMem0_size toWord value hbase, ByteArray_zeroes_size,
    toByteArray_size]

theorem safeTransferRuntimeCallMem2_size
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem2 base toWord value).size = 388 := by
  unfold safeTransferRuntimeCallMem2
  rw [toByteArray_write_eq _ _ 356
      (by rw [safeTransferRuntimeCallMem1_size toWord value hbase])
      (by
        rw [safeTransferRuntimeCallMem1_size toWord value hbase]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    safeTransferRuntimeCallMem1_size toWord value hbase, ByteArray_zeroes_size,
    toByteArray_size]

theorem safeTransferRuntimeCallMem0_mload256
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨256⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem0 base toWord value).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeCallMem0 base toWord value).readWithPadding
          (⟨256⟩ : UInt256).toNat 32)))
      = safeTransferRuntimeCopyWord1 base toWord value := by
  have hguard :
      ¬((⟨256⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem0 base toWord value).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩) := by
    exact not_or.mpr ⟨by
      rw [safeTransferRuntimeCallMem0_size toWord value hbase]
      native_decide, by native_decide⟩
  rw [if_neg hguard]
  rfl

theorem safeTransferRuntimeCallMem1_mload288
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨288⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem1 base toWord value).size
        ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeCallMem1 base toWord value).readWithPadding
          (⟨288⟩ : UInt256).toNat 32)))
      = safeTransferRuntimeTailSourceWord base toWord value := by
  have hguard :
      ¬((⟨288⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem1 base toWord value).size
        ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩) := by
    exact not_or.mpr ⟨by
      rw [safeTransferRuntimeCallMem1_size toWord value hbase]
      native_decide, by native_decide⟩
  rw [if_neg hguard]
  rfl

theorem safeTransferRuntimeCallMem1_mload356
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨356⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem1 base toWord value).size
        ∨ (⟨356⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeCallMem1 base toWord value).readWithPadding
          (⟨356⟩ : UInt256).toNat 32)))
      = ⟨0⟩ := by
  have hguard :
      (⟨356⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem1 base toWord value).size
        ∨ (⟨356⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ := by
    left
    rw [safeTransferRuntimeCallMem1_size toWord value hbase]
    native_decide
  rw [if_pos hguard]

theorem safeTransferRuntimeCallMem2_read64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem2 base toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold safeTransferRuntimeCallMem2
  rw [write32_read_below _ _ 356 64 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem1_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeCallMem1
  rw [write32_read_below _ _ 324 64 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem0_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeCallMem0
  rw [toByteArray_write_read_below_of_gap
      (safeTransferRuntimePatchedSelectorWord base toWord value) _ 292 64
      (by rw [safeTransferRuntimeMem7_size toWord value hbase]; omega)
      (by omega)
      (by
        rw [safeTransferRuntimeMem7_size toWord value hbase]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num))]
  exact safeTransferRuntimeMem7_read64 toWord value hbase

theorem safeTransferRuntimeCallMem2_read96_zero
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164)
    (hbaseRead96 : base.readWithPadding 96 32 = UInt256.toByteArray (⟨0⟩ : UInt256)) :
    (safeTransferRuntimeCallMem2 base toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold safeTransferRuntimeCallMem2
  rw [write32_read_below _ _ 356 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem1_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeCallMem1
  rw [write32_read_below _ _ 324 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem0_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeCallMem0
  rw [write32_read_below _ _ 292 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem7_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeMem7
  rw [write32_read_below _ _ 224 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega) (by omega)]
  unfold safeTransferRuntimeMem6
  rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega) (by omega)
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)]
  unfold safeTransferRuntimeMem5
  rw [write32_read_below _ _ 192 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem4_size toWord value hbase]; omega) (by omega)]
  unfold safeTransferRuntimeMem4
  rw [write32_read_below _ _ 260 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem3_size toWord hbase]) (by omega)]
  unfold safeTransferRuntimeMem3
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask toWord)
      (safeTransferRuntimeMem2 base) 228 96
      (by rw [safeTransferRuntimeMem2_size hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem2_size hbase]; exact lt_usize _ (by norm_num))]
  unfold safeTransferRuntimeMem2
  rw [write32_read_below _ _ 160 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem1_size hbase]; omega) (by omega)]
  unfold safeTransferRuntimeMem1
  rw [write32_read_below _ _ 128 96 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem0_size hbase]; omega) (by omega)]
  unfold safeTransferRuntimeMem0
  rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])
      (by rw [hbase]; omega) (by omega) (by rw [hbase]; omega)]
  exact hbaseRead96

theorem safeTransferRuntimeCallMem2_mload96_zero
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164)
    (hbaseRead96 : base.readWithPadding 96 32 = UInt256.toByteArray (⟨0⟩ : UInt256)) :
    (if (⟨96⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem2 base toWord value).size
        ∨ (⟨96⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeCallMem2 base toWord value).readWithPadding
          (⟨96⟩ : UInt256).toNat 32)))
      = ⟨0⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [safeTransferRuntimeCallMem2_size toWord value hbase]; decide)
    (by native_decide)
    (safeTransferRuntimeCallMem2_read96_zero toWord value hbase hbaseRead96)

theorem safeTransferRuntimeMem6_read228_28
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem6 base toWord value).readWithPadding 228 28 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28 := by
  unfold safeTransferRuntimeMem6 safeTransferRuntimeMem5 safeTransferRuntimeMem4
    safeTransferRuntimeMem3
  change ByteArray.readWithPadding (writeCascade (safeTransferRuntimeMem2 base)
      [(228, UInt256.land solcAddrMask toWord), (260, value), (192, (⟨68⟩ : UInt256)),
        (64, (⟨292⟩ : UInt256))]) 228 28 =
    (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28
  simpa using
    writeCascade_read_window_of_head (safeTransferRuntimeMem2 base) 228 0 28
      (UInt256.land solcAddrMask toWord)
      [(260, value), (192, (⟨68⟩ : UInt256)), (64, (⟨292⟩ : UInt256))]
      (by rw [safeTransferRuntimeMem2_size hbase]; exact lt_usize 36 (by norm_num))
      (by rw [safeTransferRuntimeMem2_size hbase]; simp [WindowDisjointFromWrites])
      (by norm_num) (by norm_num) (by norm_num)

theorem safeTransferRuntimeWord224_extract4_32
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (UInt256.toByteArray (safeTransferRuntimeWord224 base toWord value)).extract 4 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28 := by
  unfold safeTransferRuntimeWord224
  have hreadSize :
      ((safeTransferRuntimeMem6 base toWord value).readWithPadding 224 32).size = 32 := by
    rw [readWithPadding_eq_extract' _ 224 32 (by norm_num) (by norm_num)
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)]
    rw [ByteArray.size_extract]
    rw [safeTransferRuntimeMem6_size toWord value hbase]
    omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize]
  rw [readWithPadding_eq_extract' _ 224 32 (by norm_num) (by norm_num)
    (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)]
  rw [extract_extract_BA]
  rw [show 224 + 4 = 228 by omega, show min (224 + 32) (224 + 32) = 256 by omega]
  rw [← readWithPadding_eq_extract' _ 228 28 (by norm_num) (by norm_num)
    (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)]
  exact safeTransferRuntimeMem6_read228_28 toWord value hbase

theorem safeTransferRuntimeMem3_read256_4
    {base : ByteArray} (toWord : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem3 base toWord).readWithPadding 256 4 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 := by
  unfold safeTransferRuntimeMem3
  exact toByteArray_write_read_window_of_gap (UInt256.land solcAddrMask toWord) _ 228 28 4
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [safeTransferRuntimeMem2_size hbase]; exact lt_usize _ (by norm_num))

theorem safeTransferRuntimeMem4_read256_32
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem4 base toWord value).readWithPadding 256 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold safeTransferRuntimeMem4
  exact safeTransferCalldata_read_boundary_word _ _ _ 260 (by norm_num)
    (safeTransferRuntimeMem3_size toWord hbase)
    (safeTransferRuntimeMem3_read256_4 toWord hbase)

theorem safeTransferRuntimeCallMem0_read256_32
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem0 base toWord value).readWithPadding 256 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold safeTransferRuntimeCallMem0
  rw [write32_read_below _ _ 292 256 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem7_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeMem7
  rw [write32_read_above _ _ 224 256 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)]
  unfold safeTransferRuntimeMem6
  rw [write32_read_above _ _ 64 256 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)]
  unfold safeTransferRuntimeMem5
  rw [write32_read_above _ _ 192 256 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem4_size toWord value hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem4_size toWord value hbase]; omega)]
  exact safeTransferRuntimeMem4_read256_32 toWord value hbase

theorem safeTransferRuntimeCopyWord1_toByteArray
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    UInt256.toByteArray (safeTransferRuntimeCopyWord1 base toWord value) =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold safeTransferRuntimeCopyWord1
  rw [safeTransferRuntimeCallMem0_read256_32 toWord value hbase]
  apply toByteArray_ofNat_fromByteArrayBigEndian_of_size
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    toByteArray_size]
  norm_num

theorem safeTransferRuntimeMem4_read288_4
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeMem4 base toWord value).readWithPadding 288 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold safeTransferRuntimeMem4
  exact toByteArray_write_read_window_of_gap value _ 260 28 4
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [safeTransferRuntimeMem3_size toWord hbase]; exact lt_usize _ (by norm_num))

theorem safeTransferRuntimeCallMem1_read288_4
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem1 base toWord value).readWithPadding 288 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold safeTransferRuntimeCallMem1
  rw [write32_read_below_len _ _ 324 288 4 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem0_size toWord value hbase])
      (by omega)
      (by rw [safeTransferRuntimeCallMem0_size toWord value hbase]; omega)
      (by norm_num) (by norm_num)]
  unfold safeTransferRuntimeCallMem0
  rw [write32_read_below_len _ _ 292 288 4 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem7_size toWord value hbase])
      (by omega)
      (by rw [safeTransferRuntimeMem7_size toWord value hbase])
      (by norm_num) (by norm_num)]
  unfold safeTransferRuntimeMem7
  rw [write32_read_above_len _ _ 224 288 4 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem6_size toWord value hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem6_size toWord value hbase])
      (by norm_num) (by norm_num)]
  unfold safeTransferRuntimeMem6
  rw [write32_read_above_len _ _ 64 288 4 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem5_size toWord value hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem5_size toWord value hbase])
      (by norm_num) (by norm_num)]
  unfold safeTransferRuntimeMem5
  rw [write32_read_above_len _ _ 192 288 4 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeMem4_size toWord value hbase]; omega)
      (by omega)
      (by rw [safeTransferRuntimeMem4_size toWord value hbase])
      (by norm_num) (by norm_num)]
  exact safeTransferRuntimeMem4_read288_4 toWord value hbase

theorem safeTransferRuntimeTailSourceWord_extract0_4
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (UInt256.toByteArray (safeTransferRuntimeTailSourceWord base toWord value)).extract 0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold safeTransferRuntimeTailSourceWord
  have hreadSize :
      ((safeTransferRuntimeCallMem1 base toWord value).readWithPadding 288 32).size =
        32 := by
    rw [readWithPadding_eq_extract' _ 288 32 (by norm_num) (by norm_num)
      (by rw [safeTransferRuntimeCallMem1_size toWord value hbase]; omega)]
    rw [ByteArray.size_extract]
    rw [safeTransferRuntimeCallMem1_size toWord value hbase]
    omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize]
  rw [readWithPadding_eq_extract' _ 288 32 (by norm_num) (by norm_num)
    (by rw [safeTransferRuntimeCallMem1_size toWord value hbase]; omega)]
  rw [extract_extract_BA]
  rw [show 288 + 0 = 288 by omega, show min (288 + 4) (288 + 32) = 292 by omega]
  rw [← readWithPadding_eq_extract' _ 288 4 (by norm_num) (by norm_num)
    (by rw [safeTransferRuntimeCallMem1_size toWord value hbase]; omega)]
  exact safeTransferRuntimeCallMem1_read288_4 toWord value hbase

theorem safeTransferRuntimeTailWord_extract0_4
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (UInt256.toByteArray (safeTransferRuntimeTailWord base toWord value)).extract 0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  rw [safeTransferRuntimeTailWord]
  rw [skimSafeTransferTailWord_extract0_4_of_source]
  exact safeTransferRuntimeTailSourceWord_extract0_4 toWord value hbase

theorem safeTransferRuntimeCallMem2_read292_32
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem2 base toWord value).readWithPadding 292 32 =
      UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value) := by
  unfold safeTransferRuntimeCallMem2
  rw [write32_read_below _ _ 356 292 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem1_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeCallMem1
  rw [write32_read_below _ _ 324 292 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem0_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeCallMem0
  exact toByteArray_write_read_back_of_gap
    (safeTransferRuntimePatchedSelectorWord base toWord value) _ 292
    (by rw [safeTransferRuntimeMem7_size toWord value hbase]; norm_num)

theorem safeTransferRuntimeCallMem2_read324_32
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem2 base toWord value).readWithPadding 324 32 =
      UInt256.toByteArray (safeTransferRuntimeCopyWord1 base toWord value) := by
  unfold safeTransferRuntimeCallMem2
  rw [write32_read_below _ _ 356 324 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem1_size toWord value hbase]) (by omega)]
  unfold safeTransferRuntimeCallMem1
  exact toByteArray_write_read_back_of_gap
    (safeTransferRuntimeCopyWord1 base toWord value) _ 324
    (by rw [safeTransferRuntimeCallMem0_size toWord value hbase]; norm_num)

theorem safeTransferRuntimeCallMem2_read356_4
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem2 base toWord value).readWithPadding 356 4 =
      (UInt256.toByteArray (safeTransferRuntimeTailWord base toWord value)).extract 0 4 := by
  unfold safeTransferRuntimeCallMem2
  rw [write32_read_prefix_len _ _ 356 4 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem1_size toWord value hbase])
      (by norm_num) (by norm_num) (by norm_num)]

theorem safeTransferRuntimeCallMem2_read292_68
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (safeTransferRuntimeCallMem2 base toWord value).readWithPadding 292 68 =
      (transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68 := by
  rw [transferCalldataMem_read128_68]
  rw [byteArray_readWithPadding_split _ 292 32 36 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [safeTransferRuntimeCallMem2_size toWord value hbase]; norm_num)]
  rw [byteArray_readWithPadding_split _ 324 32 4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [safeTransferRuntimeCallMem2_size toWord value hbase]; norm_num)]
  rw [safeTransferRuntimeCallMem2_read292_32 toWord value hbase,
    safeTransferRuntimeCallMem2_read324_32 toWord value hbase]
  change UInt256.toByteArray (safeTransferRuntimePatchedSelectorWord base toWord value) ++
      (UInt256.toByteArray (safeTransferRuntimeCopyWord1 base toWord value) ++
        (safeTransferRuntimeCallMem2 base toWord value).readWithPadding 356 4) =
    transferSelector ++ (UInt256.land solcAddrMask toWord).toByteArray ++ value.toByteArray
  rw [safeTransferRuntimeCallMem2_read356_4 toWord value hbase]
  rw [safeTransferRuntimePatchedSelectorWord, skimSafeTransferPatchedSelector_toByteArray]
  rw [safeTransferRuntimeWord224_extract4_32 toWord value hbase,
    safeTransferRuntimeCopyWord1_toByteArray toWord value hbase,
    safeTransferRuntimeTailWord_extract0_4 toWord value hbase]
  let addrBytes := UInt256.toByteArray (UInt256.land solcAddrMask toWord)
  let valueBytes := UInt256.toByteArray value
  have haddr : addrBytes.extract 0 28 ++ addrBytes.extract 28 32 = addrBytes := by
    dsimp [addrBytes]
    rw [ByteArray.extract_append_extract]
    rw [show min 0 28 = 0 by norm_num, show max 28 32 = 32 by norm_num]
    rw [show (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 32 =
        UInt256.toByteArray (UInt256.land solcAddrMask toWord) by
      rw [show 32 = (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).size by
        rw [toByteArray_size]]
      exact byteArray_extract_self _]
  have hvalue : valueBytes.extract 0 28 ++ valueBytes.extract 28 32 = valueBytes := by
    dsimp [valueBytes]
    rw [ByteArray.extract_append_extract]
    rw [show min 0 28 = 0 by norm_num, show max 28 32 = 32 by norm_num]
    rw [show (UInt256.toByteArray value).extract 0 32 = UInt256.toByteArray value by
      rw [show 32 = (UInt256.toByteArray value).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]
  change transferSelector ++ addrBytes.extract 0 28 ++
      ((addrBytes.extract 28 32 ++ valueBytes.extract 0 28) ++ valueBytes.extract 28 32) =
    transferSelector ++ addrBytes ++ valueBytes
  simp only [ByteArray.append_assoc]
  have htail :
      addrBytes.extract 0 28 ++
          (addrBytes.extract 28 32 ++
            (valueBytes.extract 0 28 ++ valueBytes.extract 28 32)) =
        addrBytes ++ valueBytes := by
    rw [← ByteArray.append_assoc]
    rw [haddr, hvalue]
  rw [htail]

theorem safeTransferRuntimeCallMem2_mload64
    {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 164) :
    (if (⟨64⟩ : UInt256).toNat ≥ (safeTransferRuntimeCallMem2 base toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeCallMem2 base toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [safeTransferRuntimeCallMem2_size toWord value hbase]; decide)
    (by native_decide) (safeTransferRuntimeCallMem2_read64 toWord value hbase)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferEntryToCallMade {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord token ret : UInt256}
    {R : List UInt256} {base rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6370⟩
      (value :: toWord :: token :: ret :: R)
      base balanceOfThisStaticcallActiveWords rdata (cA, σ) k C)
    (hbase : base.size = 164)
    (hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ base.size
          ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (base.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hdepth : ee.depth.val < 1024)
    (hR : R.length + 20 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A_in : Substate) (callGas _gasArg : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ ee.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
            (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask))
            (toExecute σ (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask)))
            callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
            ((safeTransferRuntimeCallMem2 base toWord value).readWithPadding 292 68)
            (ee.depth + 1) ee.header ee.perm)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨360⟩ ::
            UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
            value :: toWord :: token :: ret :: R)
          (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out
          (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  have rd6375 := evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by native_decide)
      mem_cost hbaseMload64 (by native_decide) (by evm_ov)]
  have rd6380 := evm_run rd6375 with [
    dup1, dup3, add, dup3,
    raw mstore 0 (safeTransferRuntimeMem0 base) balanceOfThisStaticcallActiveWords
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem0; rfl) (by native_decide) (by evm_ov)]
  have rd6384 := evm_run rd6380 with [
    push1 ⟨25⟩, dup2,
    raw mstore 0 (safeTransferRuntimeMem1 base) balanceOfThisStaticcallActiveWords
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem1; rfl) (by native_decide) (by evm_ov)]
  have rd6417 := rd6384.pushConst skimSafeTransferSignatureWord (width := 32)
    (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd6423 := evm_run rd6417 with [
    push1 ⟨32⟩, swap2, dup3, add,
    raw mstore 0 (safeTransferRuntimeMem2 base) balanceOfThisStaticcallActiveWords
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem2; rfl) (by native_decide) (by evm_ov)]
  have rd6425 := evm_run rd6423 with [
    dup2,
    raw mload 0 ⟨192⟩ balanceOfThisStaticcallActiveWords
      (by native_decide) mem_cost
      (safeTransferRuntimeMem2_mload64 hbase)
      (by native_decide) (by evm_ov)]
  have rd6441 := evm_run rd6425 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, dup2, and,
    push1 ⟨36⟩, dup4, add,
    raw mstore 9 (safeTransferRuntimeMem3 base toWord) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem3; rfl) (by native_decide) (by evm_ov)]
  have rd6449 := evm_run rd6441 with [
    push1 ⟨68⟩, dup1, dup4, add, dup7, swap1,
    raw mstore 3 (safeTransferRuntimeMem4 base toWord value) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem4; rfl) (by native_decide) (by evm_ov)]
  have rd6451 := evm_run rd6449 with [
    dup5,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (safeTransferRuntimeMem4_mload64 toWord value hbase)
      (by native_decide) (by evm_ov)]
  have rd6459 := evm_run rd6451 with [
    dup1, dup5, sub, swap1, swap2, add, dup2,
    raw mstore 0 (safeTransferRuntimeMem5 base toWord value) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem5; rfl) (by native_decide) (by evm_ov)]
  have rd6466 := evm_run rd6459 with [
    push1 ⟨100⟩, swap1, swap3, add, dup5,
    raw mstore 0 (safeTransferRuntimeMem6 base toWord value) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem6; rfl) (by native_decide) (by evm_ov)]
  have rd6471 := evm_run rd6466 with [
    swap2, dup2, add, dup1,
    raw mload 0 (safeTransferRuntimeWord224 base toWord value) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (safeTransferRuntimeMem6_mload224 toWord value hbase)
      (by native_decide) (by evm_ov)]
  have rd6480 := evm_run rd6471 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and]
  have rd6485 := rd6480.pushConst transferSelectorWord (width := 4) (op := .PUSH4)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd6491 := evm_run rd6485 with [
    push1 ⟨224⟩, shl, lor, dup2,
    raw mstore 0 (safeTransferRuntimeMem7 base toWord value) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeMem7 safeTransferRuntimePatchedSelectorWord; rfl)
      (by native_decide) (by evm_ov)]
  have rd6512 := evm_run rd6491 with [
    swap3,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (safeTransferRuntimeMem7_mload64 toWord value hbase)
      (by native_decide) (by evm_ov),
    dup2,
    raw mload 0 ⟨68⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (safeTransferRuntimeMem7_mload192 toWord value hbase)
      (by native_decide) (by evm_ov),
    push1 ⟨0⟩, swap5, push1 ⟨96⟩, swap5, dup10, and,
    swap4, swap3, swap2, dup3, swap2, swap1, dup1, dup4, dup4]
  have rd6521a := evm_run rd6512 with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539a := evm_run rd6521a with [
    dup1,
    raw mload 0 (safeTransferRuntimePatchedSelectorWord base toWord value)
      (UInt256.ofNat 10) (by native_decide)
      mem_cost (safeTransferRuntimeMem7_mload224 toWord value hbase)
      (by native_decide) (by evm_ov),
    dup3,
    raw mstore 3 (safeTransferRuntimeCallMem0 base toWord value) (UInt256.ofNat 11)
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeCallMem0; rfl) (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512a := rd6539a.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [show (⟨192⟩ : UInt256) + ⟨32⟩ = ⟨224⟩ by native_decide,
    show (⟨32⟩ : UInt256) + ⟨224⟩ = ⟨256⟩ by native_decide,
    show (⟨32⟩ : UInt256) + ⟨292⟩ = ⟨324⟩ by native_decide,
    show (⟨68⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨36⟩ by native_decide]
    at rd6512a
  have rd6521b := evm_run rd6512a with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539b := evm_run rd6521b with [
    dup1,
    raw mload 0 (safeTransferRuntimeCopyWord1 base toWord value)
      (UInt256.ofNat 11) (by native_decide)
      mem_cost (safeTransferRuntimeCallMem0_mload256 toWord value hbase)
      (by native_decide) (by evm_ov),
    dup3,
    raw mstore 3 (safeTransferRuntimeCallMem1 base toWord value) (UInt256.ofNat 12)
      (by native_decide) mem_cost
      (by unfold safeTransferRuntimeCallMem1; rfl) (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512b := rd6539b.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨256⟩ = ⟨288⟩ by native_decide,
    show (⟨32⟩ : UInt256) + ⟨324⟩ = ⟨356⟩ by native_decide,
    show (⟨36⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨4⟩ by native_decide]
    at rd6512b
  have rd6543 := evm_run rd6512b with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd6575 := evm_run rd6543 with [
    jumpdest, push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub,
    dup1, not, dup3,
    raw mload 0 (safeTransferRuntimeTailSourceWord base toWord value)
      (UInt256.ofNat 12) (by native_decide)
      mem_cost (safeTransferRuntimeCallMem1_mload288 toWord value hbase)
      (by native_decide) (by evm_ov),
    and, dup2, dup5,
    raw mload 3 ⟨0⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost (safeTransferRuntimeCallMem1_mload356 toWord value hbase)
      (by native_decide) (by evm_ov),
    and, dup1, dup3, lor, dup6,
    raw mstore 0 (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by
        unfold safeTransferRuntimeCallMem2 safeTransferRuntimeTailWord skimSafeTransferTailMask
        rfl)
      (by native_decide) (by evm_ov),
    pop, pop, pop, pop, pop, pop]
  have rd6593 := evm_run rd6575 with [
    swap1, pop, add, swap2, pop, pop, push1 ⟨0⟩, push1 ⟨64⟩,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost (safeTransferRuntimeCallMem2_mload64 toWord value hbase)
      (by native_decide) (by evm_ov),
    dup1, dup4, sub, dup2, push1 ⟨0⟩, dup7]
  obtain ⟨gasArg, rd6594⟩ := rd6593.gas (by native_decide) (by evm_ov)
  rw [show (⟨68⟩ : UInt256) + ⟨292⟩ = ⟨360⟩ by native_decide,
    show UInt256.sub (⟨360⟩ : UInt256) ⟨292⟩ = ⟨68⟩ by native_decide]
    at rd6594
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘ, rd6595, houtSize⟩ :=
    rd6594.call (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, A_in, callGas, gasArg, k', C', ?_, ?_, houtSize⟩
  · simpa using hΘ
  · have hlen :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
        exact Nat.zero_le _
      simp [min, hle]
    have haw :
        UInt256.ofNat
          (MachineState.M
            (MachineState.M (UInt256.ofNat 13).toNat (⟨292⟩ : UInt256).toNat
              (⟨68⟩ : UInt256).toNat)
            (⟨292⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
          UInt256.ofNat 13 := by
      native_decide
    rw [hlen, byteArray_write_len_zero, haw] at rd6595
    exact rd6595

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferEmptyFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {callRetOffset maskedToken value toWord token ret : UInt256}
    {R : List UInt256} {mem out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: callRetOffset :: maskedToken :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      mem aw out acc k C)
    (hout : out.size = 0) (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6607' := rd6607
  rw [hout] at rd6607'
  have rd6641 := evm_run rd6607' with [jumpiT (by native_decide) (by jump_dest)]
  have rd6652 := evm_run rd6641 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap2, pop, swap2, pop]
  exact RD.uniswapSafeTransferReturnNonemptyFailureReverts (R := R) rd6652 hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferEmptyReturnToRet {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {callRetOffset maskedToken value toWord token ret : UInt256}
    {R : List UInt256} {mem out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: callRetOffset :: maskedToken :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      mem aw out acc k C)
    (hout : out.size = 0)
    (hload96 :
      (if (⟨96⟩ : UInt256).toNat ≥ mem.size ∨ (⟨96⟩ : UInt256) ≥ aw * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨96⟩ : UInt256).toNat 32))) =
        ⟨0⟩)
    (haw96 : UInt256.ofNat (MachineState.M aw.toNat (⟨96⟩ : UInt256).toNat 32) = aw)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hR : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R mem aw out acc k' C' := by
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6607' := rd6607
  rw [hout] at rd6607'
  have rd6641 := evm_run rd6607' with [jumpiT (by native_decide) (by jump_dest)]
  have rd6652 := evm_run rd6641 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap2, pop, swap2, pop]
  have rd6658 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiNT (by native_decide)]
  have rd6661 := evm_run rd6658 with [pop, dup1]
  have rd6662 := RD.mload 0 ⟨0⟩ aw rd6661 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw96])
    hload96 haw96
    (by simp only [List.length_cons]; omega)
  have rd6668 := evm_run rd6662 with [
    iszero, dup1, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6773 := evm_run rd6668 with [jumpdest, push2 ⟨6773⟩,
    jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop, jump hret]⟩

def safeTransferRuntimeReturnDataRounded (out : ByteArray) : UInt256 :=
  UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)

def safeTransferRuntimeReturnDataPtr (out : ByteArray) : UInt256 :=
  (⟨292⟩ : UInt256) + safeTransferRuntimeReturnDataRounded out

noncomputable def safeTransferRuntimeReturnDataPtrMem
    (base : ByteArray) (toWord value : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (safeTransferRuntimeReturnDataPtr out)).write 0
    (safeTransferRuntimeCallMem2 base toWord value) 64 32

noncomputable def safeTransferRuntimeReturnDataSizeMem
    (base : ByteArray) (toWord value : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat out.size)).write 0
    (safeTransferRuntimeReturnDataPtrMem base toWord value out) 292 32

noncomputable def safeTransferRuntimeReturnDataMem
    (base : ByteArray) (toWord value : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (safeTransferRuntimeReturnDataSizeMem base toWord value out) 324 out.size

noncomputable def safeTransferRuntimeReturnDataActiveWords (out : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (UInt256.ofNat 13).toNat 324 out.size)

theorem safeTransferRuntimeReturnDataPtrMem_size
    {base : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (hbase : base.size = 164) :
    (safeTransferRuntimeReturnDataPtrMem base toWord value out).size = 388 := by
  unfold safeTransferRuntimeReturnDataPtrMem
  rw [write32_eq _ _ 64 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeCallMem2_size toWord value hbase]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    safeTransferRuntimeCallMem2_size toWord value hbase, toByteArray_size]
  omega

theorem safeTransferRuntimeReturnDataSizeMem_size
    {base : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (hbase : base.size = 164) :
    (safeTransferRuntimeReturnDataSizeMem base toWord value out).size = 388 := by
  unfold safeTransferRuntimeReturnDataSizeMem
  rw [write32_eq _ _ 292 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeReturnDataPtrMem_size toWord value out hbase]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    safeTransferRuntimeReturnDataPtrMem_size toWord value out hbase, toByteArray_size]
  omega

theorem safeTransferRuntimeReturnDataSizeMem_read292
    {base : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (hbase : base.size = 164) (houtSize : out.size < UInt256.size) :
    (safeTransferRuntimeReturnDataSizeMem base toWord value out).readWithPadding 292 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) := by
  unfold safeTransferRuntimeReturnDataSizeMem
  rw [write32_read_back _ _ 292 (by rw [toByteArray_size])
      (by rw [safeTransferRuntimeReturnDataPtrMem_size toWord value out hbase]; omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat out.size)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat out.size)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem safeTransferRuntimeReturnDataMem_read292
    {base : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (hbase : base.size = 164)
    (houtNe : out.size ≠ 0) (houtSize : out.size < UInt256.size) :
    (safeTransferRuntimeReturnDataMem base toWord value out).readWithPadding 292 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) := by
  unfold safeTransferRuntimeReturnDataMem
  by_cases hin :
      324 + out.size ≤ (safeTransferRuntimeReturnDataSizeMem base toWord value out).size
  · rw [write_read_below_gen out
      (safeTransferRuntimeReturnDataSizeMem base toWord value out)
      324 out.size 292 houtNe le_rfl hin (by omega)]
    exact safeTransferRuntimeReturnDataSizeMem_read292 toWord value out hbase houtSize
  · have hbaseSize :
        (safeTransferRuntimeReturnDataSizeMem base toWord value out).size = 388 :=
      safeTransferRuntimeReturnDataSizeMem_size toWord value out hbase
    have hext :
        (safeTransferRuntimeReturnDataSizeMem base toWord value out).size <
          324 + out.size := by omega
    rw [write_eq_gen_extend out
      (safeTransferRuntimeReturnDataSizeMem base toWord value out)
      324 out.size houtNe le_rfl (by rw [hbaseSize]; omega) hext]
    rw [readWithPadding_eq_extract _ 292 (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ 292 324 (by
      rw [ByteArray.size_extract]
      omega)]
    rw [extract_prefix _ 324 292 324 (by omega)]
    rw [← readWithPadding_eq_extract
      (safeTransferRuntimeReturnDataSizeMem base toWord value out) 292
      (by rw [hbaseSize]; omega)]
    exact safeTransferRuntimeReturnDataSizeMem_read292 toWord value out hbase houtSize

theorem safeTransferRuntimeReturnDataActiveWords_M_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    MachineState.M (UInt256.ofNat 13).toNat 324 out.size * 32 < UInt256.size := by
  rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
  unfold MachineState.M
  split
  · norm_num [UInt256.size]
  · by_cases hle : 13 ≤ (324 + out.size + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv : ((324 + out.size + 31) / 32) * 32 ≤ 324 + out.size + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 355 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      norm_num [UInt256.size]

theorem safeTransferRuntimeReturnDataActiveWords_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (safeTransferRuntimeReturnDataActiveWords out).toNat := by
  unfold safeTransferRuntimeReturnDataActiveWords
  have hmul := safeTransferRuntimeReturnDataActiveWords_M_mul32_lt out houtSize
  have hMlt : MachineState.M (UInt256.ofNat 13).toNat 324 out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
  unfold MachineState.M
  split
  · norm_num
  · exact Nat.le_max_left _ _

theorem safeTransferRuntimeReturnDataActiveWords_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (safeTransferRuntimeReturnDataActiveWords out).toNat * 32 < UInt256.size := by
  unfold safeTransferRuntimeReturnDataActiveWords
  have hmul := safeTransferRuntimeReturnDataActiveWords_M_mul32_lt out houtSize
  have hMlt : MachineState.M (UInt256.ofNat 13).toNat 324 out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hmul

theorem safeTransferRuntimeReturnDataActiveWords_mload292_haw (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    ¬ (⟨292⟩ : UInt256) ≥ safeTransferRuntimeReturnDataActiveWords out * ⟨32⟩ := by
  intro h
  have hle :
      (safeTransferRuntimeReturnDataActiveWords out * ⟨32⟩).toNat ≤
        (⟨292⟩ : UInt256).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (safeTransferRuntimeReturnDataActiveWords_mul32_lt out houtSize),
    show (⟨292⟩ : UInt256).toNat = 292 from by decide] at hle
  have hge := safeTransferRuntimeReturnDataActiveWords_toNat_ge out houtSize
  omega

theorem safeTransferRuntimeReturnDataActiveWords_mload292_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M (safeTransferRuntimeReturnDataActiveWords out).toNat
          (⟨292⟩ : UInt256).toNat 32) =
      safeTransferRuntimeReturnDataActiveWords out := by
  have hM :
      MachineState.M (safeTransferRuntimeReturnDataActiveWords out).toNat
          (⟨292⟩ : UInt256).toNat 32 =
        (safeTransferRuntimeReturnDataActiveWords out).toNat := by
    rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
    simp [MachineState.M]
    have hge := safeTransferRuntimeReturnDataActiveWords_toNat_ge out houtSize
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem safeTransferRuntimeReturnDataMem_mload292
    {base : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (hbase : base.size = 164)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (if (⟨292⟩ : UInt256).toNat ≥
          (safeTransferRuntimeReturnDataMem base toWord value out).size
        ∨ (⟨292⟩ : UInt256) ≥ safeTransferRuntimeReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeReturnDataMem base toWord value out).readWithPadding
          (⟨292⟩ : UInt256).toNat 32))) =
      UInt256.ofNat out.size := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨292⟩ : UInt256)) (aw := safeTransferRuntimeReturnDataActiveWords out)
    (v := UInt256.ofNat out.size)
    (by
      rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
      unfold safeTransferRuntimeReturnDataMem
      by_cases hin :
          324 + out.size ≤
            (safeTransferRuntimeReturnDataSizeMem base toWord value out).size
      · rw [write_eq_gen out
          (safeTransferRuntimeReturnDataSizeMem base toWord value out)
          324 out.size houtNe le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbaseSize :
            (safeTransferRuntimeReturnDataSizeMem base toWord value out).size = 388 :=
          safeTransferRuntimeReturnDataSizeMem_size toWord value out hbase
        have hext :
            (safeTransferRuntimeReturnDataSizeMem base toWord value out).size <
              324 + out.size := by omega
        rw [write_eq_gen_extend out
          (safeTransferRuntimeReturnDataSizeMem base toWord value out)
          324 out.size houtNe le_rfl (by rw [hbaseSize]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)
    (safeTransferRuntimeReturnDataActiveWords_mload292_haw out houtSize)
    (by
      simpa [show (⟨292⟩ : UInt256).toNat = 292 from by decide] using
        safeTransferRuntimeReturnDataMem_read292 toWord value out hbase houtNe
          (lt_size_of_lt_sign houtSize))

theorem safeTransferRuntimeReturnDataMem_mload324
    {base : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (hbase : base.size = 164)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255) :
    (if (⟨324⟩ : UInt256).toNat ≥
          (safeTransferRuntimeReturnDataMem base toWord value out).size
        ∨ (⟨324⟩ : UInt256) ≥ safeTransferRuntimeReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((safeTransferRuntimeReturnDataMem base toWord value out).readWithPadding
          (⟨324⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨324⟩ : UInt256).toNat = 324 from by decide]
    let baseMem := safeTransferRuntimeReturnDataSizeMem base toWord value out
    have hbaseMem : baseMem.size = 388 :=
      safeTransferRuntimeReturnDataSizeMem_size toWord value out hbase
    unfold safeTransferRuntimeReturnDataMem
    change UInt256.ofNat
        (fromByteArrayBigEndian ((out.write 0 baseMem 324 out.size).readWithPadding 324 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    by_cases hin : 324 + out.size ≤ baseMem.size
    · rw [write_eq_gen out baseMem 324 out.size (by omega) le_rfl hin]
      rw [ByteArray.append_assoc]
      rw [readWithPadding_eq_extract _ 324 (by
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ 324 356 (by
        rw [ByteArray.size_extract]
        omega)]
      rw [show (baseMem.extract 0 324).size = 324 by
        rw [ByteArray.size_extract, hbaseMem]
        omega]
      rw [Nat.sub_self, show 356 - 324 = 32 by omega]
      rw [extract_append_left _ _ 0 32 (by
        rw [ByteArray.size_extract]
        omega)]
      rw [extract_prefix _ out.size 0 32 (by omega)]
    · have hext : baseMem.size < 324 + out.size := by omega
      rw [write_eq_gen_extend out baseMem 324 out.size (by omega) le_rfl
          (by rw [hbaseMem]; omega) hext]
      rw [readWithPadding_eq_extract _ 324 (by
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ 324 356 (by
        rw [ByteArray.size_extract, hbaseMem]
        omega)]
      rw [show (baseMem.extract 0 324).size = 324 by
        rw [ByteArray.size_extract, hbaseMem]
        omega]
      rw [Nat.sub_self, show 356 - 324 = 32 by omega]
      rw [extract_prefix _ out.size 0 32 (by omega)]
  · rw [not_or]
    constructor
    · rw [show (⟨324⟩ : UInt256).toNat = 324 from by decide]
      unfold safeTransferRuntimeReturnDataMem
      by_cases hin :
          324 + out.size ≤
            (safeTransferRuntimeReturnDataSizeMem base toWord value out).size
      · rw [write_eq_gen out (safeTransferRuntimeReturnDataSizeMem base toWord value out)
          324 out.size (by omega) le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbaseSize :
            (safeTransferRuntimeReturnDataSizeMem base toWord value out).size = 388 :=
          safeTransferRuntimeReturnDataSizeMem_size toWord value out hbase
        have hext :
            (safeTransferRuntimeReturnDataSizeMem base toWord value out).size <
              324 + out.size := by omega
        rw [write_eq_gen_extend out
          (safeTransferRuntimeReturnDataSizeMem base toWord value out)
          324 out.size (by omega) le_rfl (by rw [hbaseSize]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega
    · intro h
      have hle :
          (safeTransferRuntimeReturnDataActiveWords out * ⟨32⟩).toNat ≤
            (⟨324⟩ : UInt256).toNat := h
      rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt (safeTransferRuntimeReturnDataActiveWords_mul32_lt out houtSize),
        show (⟨324⟩ : UInt256).toNat = 324 from by decide] at hle
      unfold safeTransferRuntimeReturnDataActiveWords at hle
      have hMlt : MachineState.M (UInt256.ofNat 13).toNat 324 out.size < UInt256.size := by
        have hmul := safeTransferRuntimeReturnDataActiveWords_M_mul32_lt out houtSize
        omega
      rw [UInt256.toNat_ofNat_of_lt hMlt] at hle
      rw [show (UInt256.ofNat 13).toNat = 13 from by decide] at hle
      unfold MachineState.M at hle
      split at hle
      · norm_num at hle
      · have hge : 13 ≤ max 13 ((324 + out.size + 31) / 32) := Nat.le_max_left _ _
        have hcontra : 416 ≤ 324 := by
          calc
            416 = 13 * 32 := by norm_num
            _ ≤ max 13 ((324 + out.size + 31) / 32) * 32 :=
              Nat.mul_le_mul_right 32 hge
            _ ≤ 324 := hle
        norm_num at hcontra

theorem safeTransferRuntimeReturnDataActiveWords_mload324_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M (safeTransferRuntimeReturnDataActiveWords out).toNat
          (⟨324⟩ : UInt256).toNat 32) =
      safeTransferRuntimeReturnDataActiveWords out := by
  have hM :
      MachineState.M (safeTransferRuntimeReturnDataActiveWords out).toNat
          (⟨324⟩ : UInt256).toNat 32 =
        (safeTransferRuntimeReturnDataActiveWords out).toNat := by
    rw [show (⟨324⟩ : UInt256).toNat = 324 from by decide]
    simp [MachineState.M]
    have hge := safeTransferRuntimeReturnDataActiveWords_toNat_ge out houtSize
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem safeTransferRuntimeReturnDataHugeCopyMemCost_gt_g
    (g : Sat256) (out : ByteArray)
    (hhi : 2 ^ 255 ≤ out.size) (hlo : out.size < UInt256.size) :
    g.toNat <
      Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 13).toNat 324 out.size)) -
        Cₘ (UInt256.ofNat 13) := by
  let M := MachineState.M (UInt256.ofNat 13).toNat 324 out.size
  have hMge : 2 ^ 250 ≤ M := by
    simp only [M]
    rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
    unfold MachineState.M
    split
    · omega
    · apply le_trans ?_ (Nat.le_max_right _ _)
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      norm_num
      omega
  have hMlt : M < UInt256.size := by
    simp only [M]
    rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
    unfold MachineState.M
    split
    · norm_num [UInt256.size]
    · apply max_lt
      · norm_num [UInt256.size]
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        norm_num [UInt256.size] at hlo ⊢
        omega
  have hdivLower : 2 ^ 491 ≤ M * M / 512 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hMM : (2 ^ 250) * (2 ^ 250) ≤ M * M := Nat.mul_le_mul hMge hMge
    have hpow : (2 ^ 491) * 512 = (2 ^ 250) * (2 ^ 250) := by decide
    rwa [hpow]
  have hbig :
      UInt256.size + Cₘ (UInt256.ofNat 13) <
        Cₘ (UInt256.ofNat M) := by
    rw [show Cₘ (UInt256.ofNat 13) = 39 from by decide]
    rw [Cₘ, UInt256.toNat_ofNat_of_lt hMlt]
    simp only [GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
    have hpow : UInt256.size + 39 < 2 ^ 491 := by decide
    omega
  have hg : g.toNat < UInt256.size := g.isLt
  have hcost :
      UInt256.size <
        Cₘ (UInt256.ofNat M) - Cₘ (UInt256.ofNat 13) := by
    omega
  simpa [M] using lt_trans hg hcost

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCallMem2NonemptyReturnToCheck
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {status value toWord token ret : UInt256} {R : List UInt256}
    {base out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (hbase : base.size = 164) (hR : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (⟨292⟩ :: status :: value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeReturnDataMem base toWord value out)
      (safeTransferRuntimeReturnDataActiveWords out) out acc k' C' := by
  exact RD.uniswapSafeTransferReturnNonemptyReturnToCheck
    (dataPtr := ⟨292⟩)
    (finalAw := safeTransferRuntimeReturnDataActiveWords out)
    (memFinal := safeTransferRuntimeReturnDataMem base toWord value out)
    h houtNe houtSize
    (safeTransferRuntimeCallMem2_mload64 toWord value hbase)
    (by native_decide)
    (by native_decide)
    (by
      rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide,
        show ((⟨292⟩ : UInt256) + ⟨32⟩).toNat = 324 from by decide]
      rfl)
    (by
      unfold safeTransferRuntimeReturnDataActiveWords
      rw [show ((⟨292⟩ : UInt256) + ⟨32⟩).toNat = 324 from by decide])
    hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCallMem2NonemptyHugeReverts
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {status value toWord token ret : UInt256} {R : List UInt256}
    {base out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (hhi : 2 ^ 255 ≤ out.size)
    (houtSize : out.size < UInt256.size)
    (hbase : base.size = 164) (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapSafeTransferReturnNonemptyHugeReverts
    (base := (⟨292⟩ : UInt256)) (gasMarker := UInt256.ofNat 13) (R := R)
    h houtNe houtSize
    (safeTransferRuntimeCallMem2_mload64 toWord value hbase)
    (by decide)
    (by decide)
    (by
      rw [show (((⟨292⟩ : UInt256) + ⟨32⟩).toNat) = 324 from by decide]
      simpa [safeTransferRuntimeReturnDataActiveWords] using
        safeTransferRuntimeReturnDataHugeCopyMemCost_gt_g g out hhi houtSize)
    hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCallMem2NonemptyFailureReverts
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {value toWord token ret : UInt256} {R : List UInt256}
    {base out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (hbase : base.size = 164) (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6652⟩ :=
    RD.uniswapSafeTransferCallMem2NonemptyReturnToCheck
      h houtNe houtSize hbase hR
  exact RD.uniswapSafeTransferReturnNonemptyFailureReverts (R := R) rd6652 hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCallMem2NonemptyTrueStatusToLengthLoaded
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {value toWord token ret : UInt256} {R : List UInt256}
    {base out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (hbase : base.size = 164) (hR : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: ⟨324⟩ :: ⟨292⟩ :: ⟨1⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeReturnDataMem base toWord value out)
      (safeTransferRuntimeReturnDataActiveWords out) out acc k' C' := by
  obtain ⟨_, _, rd6652⟩ :=
    RD.uniswapSafeTransferCallMem2NonemptyReturnToCheck
      h houtNe houtSize hbase hR
  exact RD.uniswapSafeTransferReturnNonemptyTrueStatusToLengthLoaded
    (retPtr := (⟨324⟩ : UInt256)) (R := R)
    rd6652 houtNe houtSize
    (safeTransferRuntimeReturnDataMem_mload292 toWord value out hbase houtNe houtSize)
    (safeTransferRuntimeReturnDataActiveWords_mload292_same out houtSize)
    (by native_decide)
    hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCallMem2NonemptyShortReverts
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {value toWord token ret : UInt256} {R : List UInt256}
    {base out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (hshort : out.size < 32) (houtSize : out.size < 2 ^ 255)
    (hbase : base.size = 164) (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6676⟩ :=
    RD.uniswapSafeTransferCallMem2NonemptyTrueStatusToLengthLoaded
      h houtNe houtSize hbase hR
  exact RD.uniswapSafeTransferReturnNonemptyShortReverts rd6676 hshort houtSize
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCallMem2NonemptyFalseReverts
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {value toWord token ret : UInt256} {R : List UInt256}
    {base out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩)
    (hbase : base.size = 164) (hR : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6676⟩ :=
    RD.uniswapSafeTransferCallMem2NonemptyTrueStatusToLengthLoaded
      h houtNe houtSize hbase hR
  exact RD.uniswapSafeTransferReturnNonemptyFalseReverts
    (R := R)
    rd6676 hout32 houtSize hword
    (safeTransferRuntimeReturnDataMem_mload324 toWord value out hbase hout32 houtSize)
    (safeTransferRuntimeReturnDataActiveWords_mload324_same out houtSize)
    hR

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferCallMem2NonemptyTrueToRet
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {value toWord token ret : UInt256} {R : List UInt256}
    {base out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferRuntimeCallMem2 base toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (hbase : base.size = 164) (hR : R.length + 16 ≤ 1024)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (safeTransferRuntimeReturnDataMem base toWord value out)
      (safeTransferRuntimeReturnDataActiveWords out) out acc k' C' := by
  obtain ⟨_, _, rd6676⟩ :=
    RD.uniswapSafeTransferCallMem2NonemptyTrueStatusToLengthLoaded
      h houtNe houtSize hbase hR
  exact RD.uniswapSafeTransferReturnNonemptyTrueToRet
    (R := R)
    rd6676 hout32 houtSize hword
    (safeTransferRuntimeReturnDataMem_mload324 toWord value out hbase hout32 houtSize)
    (safeTransferRuntimeReturnDataActiveWords_mload324_same out houtSize)
    hret hR

end UniswapV2Pair
