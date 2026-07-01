import Examples.UniswapV2Pair.SkimRuntime
import Examples.UniswapV2Pair.StringReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` `_safeTransfer` runtime tail -/

theorem balanceOfThisSelectorMem_read96_zero :
    balanceOfThisSelectorMem.readWithPadding 96 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfThisSelectorMem solcFreePtrMem
  native_decide

theorem balanceOfThisCalldataMem_read96_zero (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_below _ _ 132 96 (by rw [toByteArray_size])
      (by rw [balanceOfThisSelectorMem_size]; omega) (by omega)]
  exact balanceOfThisSelectorMem_read96_zero

theorem balanceOfThisStaticcallMem_read96_zero_of_size_ge
    (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfThisStaticcallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
    simpa using
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) ho32 hoSize
  rw [hlen]
  rw [write_read_below_gen o (balanceOfThisCalldataMem self) 128 32 96
      (by decide) ho32 (by rw [balanceOfThisCalldataMem_size]; omega) (by omega)]
  exact balanceOfThisCalldataMem_read96_zero self

theorem skimSafeTransferMem0_read96_zero
    (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem0 self o).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem0
  rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])
      (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize]; omega) (by omega)
      (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize]; omega)]
  exact balanceOfThisStaticcallMem_read96_zero_of_size_ge self ho32 hoSize

theorem skimSafeTransferMem1_read96_zero
    (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem1 self o).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem1
  rw [write32_read_below _ _ 128 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem0_size self ho32 hoSize]; omega) (by omega)]
  exact skimSafeTransferMem0_read96_zero self ho32 hoSize

theorem skimSafeTransferMem2_read96_zero
    (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem2 self o).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem2
  rw [write32_read_below _ _ 160 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem1_size self ho32 hoSize]; omega) (by omega)]
  exact skimSafeTransferMem1_read96_zero self ho32 hoSize

theorem skimSafeTransferMem3_read96_zero
    (self : UInt256) {o : ByteArray} (toWord : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem3 self o toWord).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem3
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask toWord)
      (skimSafeTransferMem2 self o) 228 96
      (by rw [skimSafeTransferMem2_size self ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem2_size self ho32 hoSize]; exact lt_usize _ (by norm_num))]
  exact skimSafeTransferMem2_read96_zero self ho32 hoSize

theorem skimSafeTransferMem4_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem4 self o toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem4
  rw [write32_read_below _ _ 260 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem3_size self toWord ho32 hoSize]) (by omega)]
  exact skimSafeTransferMem3_read96_zero self toWord ho32 hoSize

theorem skimSafeTransferMem5_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem5 self o toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem5
  rw [write32_read_below _ _ 192 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega) (by omega)]
  exact skimSafeTransferMem4_read96_zero self toWord value ho32 hoSize

theorem skimSafeTransferMem6_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem6 self o toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem6
  rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega) (by omega)
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)]
  exact skimSafeTransferMem5_read96_zero self toWord value ho32 hoSize

theorem skimSafeTransferMem7_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem7 self o toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferMem7
  rw [write32_read_below _ _ 224 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega) (by omega)]
  exact skimSafeTransferMem6_read96_zero self toWord value ho32 hoSize

theorem skimSafeTransferMem5_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem5 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  rw [skimSafeTransferMem5_eq_writeCascade]
  simpa [skimSafeTransferMem5Writes] using
    writeCascade_read_word_of_head
      (balanceOfThisStaticcallMem self o) 64 (⟨192⟩ : UInt256)
      (skimSafeTransferMem5WritesAfter64 toWord value)
      (by
        rw [balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize]
        native_decide)
      (by
        rw [balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize]
        exact skimSafeTransferMem5WritesAfter64_disjoint64 toWord value)

theorem skimSafeTransferMem6_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem6 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSafeTransferMem6
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)]
  rw [show (UInt256.toByteArray (⟨292⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨292⟩ : UInt256)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSafeTransferMem7_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem7 self o toWord value).size = 292 := by
  unfold skimSafeTransferMem7
  rw [write32_eq _ _ 224 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSafeTransferMem6_size self toWord value ho32 hoSize, toByteArray_size]
  omega

theorem skimSafeTransferMem7_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem7 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSafeTransferMem7
  rw [write32_read_below _ _ 224 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega) (by omega)]
  exact skimSafeTransferMem6_read64 self toWord value ho32 hoSize

theorem skimSafeTransferMem7_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (skimSafeTransferMem7 self o toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferMem7 self o toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]; decide)
    (by native_decide) (skimSafeTransferMem7_read64 self toWord value ho32 hoSize)

theorem skimSafeTransferMem5_read192
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem5 self o toWord value).readWithPadding 192 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold skimSafeTransferMem5
  rw [write32_read_back _ _ 192 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega)]
  rw [show (UInt256.toByteArray (⟨68⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨68⟩ : UInt256)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSafeTransferMem6_read192
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem6 self o toWord value).readWithPadding 192 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold skimSafeTransferMem6
  rw [write32_read_above _ _ 64 192 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)]
  exact skimSafeTransferMem5_read192 self toWord value ho32 hoSize

theorem skimSafeTransferMem7_read192
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem7 self o toWord value).readWithPadding 192 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold skimSafeTransferMem7
  rw [write32_read_below _ _ 224 192 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega) (by omega)]
  exact skimSafeTransferMem6_read192 self toWord value ho32 hoSize

theorem skimSafeTransferMem7_mload192
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨192⟩ : UInt256).toNat ≥ (skimSafeTransferMem7 self o toWord value).size
        ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferMem7 self o toWord value).readWithPadding
          (⟨192⟩ : UInt256).toNat 32)))
      = ⟨68⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]; decide)
    (by native_decide) (skimSafeTransferMem7_read192 self toWord value ho32 hoSize)

theorem skimSafeTransferMem7_read224
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem7 self o toWord value).readWithPadding 224 32 =
      UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value) := by
  unfold skimSafeTransferMem7
  rw [write32_read_back _ _ 224 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega)]
  rw [show (UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value)).extract 0 32 =
      UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value) by
    rw [show 32 =
      (UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value)).size by
        rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSafeTransferMem7_mload224
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨224⟩ : UInt256).toNat ≥ (skimSafeTransferMem7 self o toWord value).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferMem7 self o toWord value).readWithPadding
          (⟨224⟩ : UInt256).toNat 32)))
      = skimSafeTransferPatchedSelectorWord self o toWord value :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]; decide)
    (by native_decide) (skimSafeTransferMem7_read224 self toWord value ho32 hoSize)

noncomputable def skimSafeTransferCallMem0
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value)).write 0
    (skimSafeTransferMem7 self o toWord value) 292 32

noncomputable def skimSafeTransferCopyWord1
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSafeTransferCallMem0 self o toWord value).readWithPadding 256 32))

noncomputable def skimSafeTransferCallMem1
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (skimSafeTransferCopyWord1 self o toWord value)).write 0
    (skimSafeTransferCallMem0 self o toWord value) 324 32

noncomputable def skimSafeTransferTailSourceWord
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSafeTransferCallMem1 self o toWord value).readWithPadding 288 32))

abbrev skimSafeTransferTailMask : UInt256 :=
  UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ ⟨4⟩)) ⟨1⟩

noncomputable def skimSafeTransferTailWord
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (skimSafeTransferTailSourceWord self o toWord value)
      (UInt256.lnot skimSafeTransferTailMask))
    (UInt256.land ⟨0⟩ skimSafeTransferTailMask)

noncomputable def skimSafeTransferCallMem2
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (skimSafeTransferTailWord self o toWord value)).write 0
    (skimSafeTransferCallMem1 self o toWord value) 356 32

theorem skimSafeTransferCallMem0_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem0 self o toWord value).size = 324 := by
  unfold skimSafeTransferCallMem0
  rw [toByteArray_write_eq _ _ 292
      (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize])
      (by
        rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    skimSafeTransferMem7_size self toWord value ho32 hoSize, ByteArray_zeroes_size,
    show (USize.ofNat (292 - 292)).toNat = 0 from
      USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem skimSafeTransferCallMem1_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem1 self o toWord value).size = 356 := by
  unfold skimSafeTransferCallMem1
  rw [toByteArray_write_eq _ _ 324
      (by rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize])
      (by
        rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    skimSafeTransferCallMem0_size self toWord value ho32 hoSize, ByteArray_zeroes_size,
    show (USize.ofNat (324 - 324)).toNat = 0 from
      USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem skimSafeTransferCallMem2_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem2 self o toWord value).size = 388 := by
  unfold skimSafeTransferCallMem2
  rw [toByteArray_write_eq _ _ 356
      (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize])
      (by
        rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    skimSafeTransferCallMem1_size self toWord value ho32 hoSize, ByteArray_zeroes_size,
    show (USize.ofNat (356 - 356)).toNat = 0 from
      USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem skimSafeTransferCallMem0_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem0 self o toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferCallMem0
  rw [write32_read_below _ _ 292 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]) (by omega)]
  exact skimSafeTransferMem7_read96_zero self toWord value ho32 hoSize

theorem skimSafeTransferCallMem1_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem1 self o toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferCallMem1
  rw [write32_read_below _ _ 324 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize]) (by omega)]
  exact skimSafeTransferCallMem0_read96_zero self toWord value ho32 hoSize

theorem skimSafeTransferCallMem2_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem2 self o toWord value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferCallMem2
  rw [write32_read_below _ _ 356 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]) (by omega)]
  exact skimSafeTransferCallMem1_read96_zero self toWord value ho32 hoSize

theorem skimSafeTransferCallMem0_mload256
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥ (skimSafeTransferCallMem0 self o toWord value).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferCallMem0 self o toWord value).readWithPadding
          (⟨256⟩ : UInt256).toNat 32)))
      = skimSafeTransferCopyWord1 self o toWord value := by
  have hguard :
      ¬((⟨256⟩ : UInt256).toNat ≥ (skimSafeTransferCallMem0 self o toWord value).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩) := by
    exact not_or.mpr ⟨by
      rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize]
      native_decide, by native_decide⟩
  rw [if_neg hguard]
  rfl

theorem skimSafeTransferCallMem1_mload288
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨288⟩ : UInt256).toNat ≥ (skimSafeTransferCallMem1 self o toWord value).size
        ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferCallMem1 self o toWord value).readWithPadding
          (⟨288⟩ : UInt256).toNat 32)))
      = skimSafeTransferTailSourceWord self o toWord value := by
  have hguard :
      ¬((⟨288⟩ : UInt256).toNat ≥ (skimSafeTransferCallMem1 self o toWord value).size
        ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩) := by
    exact not_or.mpr ⟨by
      rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]
      native_decide, by native_decide⟩
  rw [if_neg hguard]
  rfl

theorem skimSafeTransferCallMem1_mload356
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨356⟩ : UInt256).toNat ≥ (skimSafeTransferCallMem1 self o toWord value).size
        ∨ (⟨356⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferCallMem1 self o toWord value).readWithPadding
          (⟨356⟩ : UInt256).toNat 32)))
      = ⟨0⟩ := by
  have hguard :
      (⟨356⟩ : UInt256).toNat ≥ (skimSafeTransferCallMem1 self o toWord value).size
        ∨ (⟨356⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ := by
    left
    rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]
    native_decide
  rw [if_pos hguard]

theorem skimSafeTransferCallMem2_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem2 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSafeTransferCallMem2
  rw [write32_read_below _ _ 356 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize])
      (by omega)]
  unfold skimSafeTransferCallMem1
  rw [write32_read_below _ _ 324 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize])
      (by omega)]
  unfold skimSafeTransferCallMem0
  rw [toByteArray_write_read_below_of_gap
      (skimSafeTransferPatchedSelectorWord self o toWord value) _ 292 64
      (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by
        rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num))]
  exact skimSafeTransferMem7_read64 self toWord value ho32 hoSize

theorem skimSafeTransferCallMem2_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (skimSafeTransferCallMem2 self o toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferCallMem2 self o toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; decide)
    (by native_decide) (skimSafeTransferCallMem2_read64 self toWord value ho32 hoSize)

theorem skimFromBytesBigEndian_append (a b : List UInt8) :
    fromBytesBigEndian (a ++ b) =
      fromBytesBigEndian a * 2 ^ (8 * b.length) + fromBytesBigEndian b := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, fromBytes'_append, List.length_reverse]
  ring

theorem skimFromBytesBigEndian_bound (xs : List UInt8) :
    fromBytesBigEndian xs < 2 ^ (8 * xs.length) := by
  unfold fromBytesBigEndian Function.comp
  simpa [List.length_reverse] using (fromBytes'_le (bs := xs.reverse))

theorem skimFromByteArrayBigEndian_append (a b : ByteArray) :
    fromByteArrayBigEndian (a ++ b) =
      fromByteArrayBigEndian a * 2 ^ (8 * b.size) + fromByteArrayBigEndian b := by
  simp [fromByteArrayBigEndian, byteArray_toList_eq, skimFromBytesBigEndian_append]

theorem toByteArray_ofNat_fromByteArrayBigEndian_of_size {arr : ByteArray}
    (hsize : arr.size = 32) :
    UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian arr)) = arr := by
  rw [← uInt256OfByteArray_eq arr]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (uInt256OfByteArray arr)]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]
  simpa [byteArray_toList_eq] using toBytesBE_uInt256OfByteArray_of_size hsize

theorem toByteArray_extract4_32_toList (w : UInt256) :
    ((UInt256.toByteArray w).extract 4 32).toList =
      (UInt256.toByteArray w).toList.drop 4 := by
  rw [byteArray_toList_eq, byteArray_toList_eq]
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [List.extract_eq_take_drop]
  have hlen : (UInt256.toByteArray w).data.toList.length = 32 := by
    rw [← byteArray_toList_eq]
    have hs := toByteArray_size w
    simpa [byteArray_toList_eq] using congrArg (fun n => n) hs
  rw [List.take_of_length_le]
  rw [List.length_drop, hlen]

theorem fromByteArrayBigEndian_toByteArray_extract4_32 (w : UInt256) :
    fromByteArrayBigEndian ((UInt256.toByteArray w).extract 4 32) =
      w.toNat % 2 ^ 224 := by
  let xs := (UInt256.toByteArray w).toList
  have hxsLen : xs.length = 32 := by
    dsimp [xs]
    simpa [byteArray_toList_eq] using toByteArray_size w
  have htailLen : (xs.drop 4).length = 28 := by
    rw [List.length_drop, hxsLen]
  have htailBound : fromBytesBigEndian (xs.drop 4) < 2 ^ 224 := by
    have hb := skimFromBytesBigEndian_bound (xs.drop 4)
    rw [htailLen] at hb
    simpa using hb
  have hfull : fromBytesBigEndian xs = w.toNat := by
    dsimp [xs]
    simpa [fromByteArrayBigEndian] using fromByteArrayBigEndian_toByteArray w
  have hsplit :
      fromBytesBigEndian xs =
        fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
    calc
      fromBytesBigEndian xs = fromBytesBigEndian (xs.take 4 ++ xs.drop 4) := by
        exact congrArg fromBytesBigEndian (List.take_append_drop 4 xs).symm
      _ = fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
        rw [skimFromBytesBigEndian_append, htailLen]
  have hfull' :
      w.toNat =
        fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
    rw [← hfull, hsplit]
  unfold fromByteArrayBigEndian
  rw [toByteArray_extract4_32_toList]
  dsimp [xs] at htailLen htailBound hfull' ⊢
  rw [hfull']
  change fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList) =
    (fromBytesBigEndian (List.take 4 (UInt256.toByteArray w).toList) * 2 ^ 224 +
      fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList)) % 2 ^ 224
  rw [show fromBytesBigEndian (List.take 4 (UInt256.toByteArray w).toList) * 2 ^ 224 +
        fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList) =
      fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList) +
        2 ^ 224 * fromBytesBigEndian (List.take 4 (UInt256.toByteArray w).toList) by ring]
  rw [Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt htailBound).symm

theorem toByteArray_extract0_4_toList (w : UInt256) :
    ((UInt256.toByteArray w).extract 0 4).toList =
      (UInt256.toByteArray w).toList.take 4 := by
  rw [byteArray_toList_eq, byteArray_toList_eq]
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [List.extract_eq_take_drop, List.drop_zero]

theorem fromByteArrayBigEndian_toByteArray_extract0_4 (w : UInt256) :
    fromByteArrayBigEndian ((UInt256.toByteArray w).extract 0 4) =
      w.toNat / 2 ^ 224 := by
  let xs := (UInt256.toByteArray w).toList
  have hxsLen : xs.length = 32 := by
    dsimp [xs]
    simpa [byteArray_toList_eq] using toByteArray_size w
  have htailLen : (xs.drop 4).length = 28 := by
    rw [List.length_drop, hxsLen]
  have hfull : fromBytesBigEndian xs = w.toNat := by
    dsimp [xs]
    simpa [fromByteArrayBigEndian] using fromByteArrayBigEndian_toByteArray w
  have hdiv : fromBytesBigEndian xs / 2 ^ 224 = fromBytesBigEndian (xs.take 4) := by
    conv_lhs => rw [← List.take_append_drop 4 xs]
    rw [show (224 : ℕ) = 8 * (xs.drop 4).length by rw [htailLen],
      fromBytesBigEndian_append_div]
  unfold fromByteArrayBigEndian
  rw [toByteArray_extract0_4_toList]
  dsimp [xs] at hfull hdiv ⊢
  rw [← hdiv, hfull]

theorem skimSafeTransferSelectorPatchMask_toNat :
    skimSafeTransferSelectorPatchMask.toNat = 2 ^ 224 - 1 := by
  native_decide

theorem transferSelectorShifted_toNat :
    (UInt256.shiftLeft transferSelectorWord ⟨224⟩).toNat =
      transferSelectorWord.toNat * 2 ^ 224 := by
  native_decide

theorem skimSafeTransferSelectorPatch_low224 (w : UInt256) :
    (UInt256.land skimSafeTransferSelectorPatchMask w).toNat = w.toNat % 2 ^ 224 := by
  rw [u256_land_toNat]
  rw [skimSafeTransferSelectorPatchMask_toNat]
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  have hlt : w.toNat % 2 ^ 224 < UInt256.size := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 224)) (by
      change 2 ^ 224 ≤ UInt256.size
      native_decide)
  exact Nat.mod_eq_of_lt hlt

theorem skimSafeTransferPatchedSelector_toNat (w : UInt256) :
    (UInt256.lor (UInt256.shiftLeft transferSelectorWord ⟨224⟩)
      (UInt256.land skimSafeTransferSelectorPatchMask w)).toNat =
      transferSelectorWord.toNat * 2 ^ 224 + w.toNat % 2 ^ 224 := by
  rw [u256_lor_toNat]
  rw [transferSelectorShifted_toNat, skimSafeTransferSelectorPatch_low224]
  rw [nat_lor_comm]
  rw [nat_lor_shift_add]
  · have hlow : w.toNat % 2 ^ 224 < 2 ^ 224 :=
      Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 224)
    have hlt : w.toNat % 2 ^ 224 + transferSelectorWord.toNat * 2 ^ 224 < UInt256.size := by
      change w.toNat % 2 ^ 224 + 2835717307 * 2 ^ 224 < 2 ^ 256
      omega
    rw [Nat.mod_eq_of_lt hlt]
    rw [Nat.add_comm]
  · exact Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 224)

theorem transferSelector_fromByteArrayBigEndian :
    fromByteArrayBigEndian transferSelector = transferSelectorWord.toNat := by
  native_decide

theorem skimSafeTransferPatchedSelector_toByteArray (w : UInt256) :
    UInt256.toByteArray (UInt256.lor (UInt256.shiftLeft transferSelectorWord ⟨224⟩)
      (UInt256.land skimSafeTransferSelectorPatchMask w)) =
      transferSelector ++ (UInt256.toByteArray w).extract 4 32 := by
  have hselSize : transferSelector.size = 4 := by native_decide
  have hsize : (transferSelector ++ (UInt256.toByteArray w).extract 4 32).size = 32 := by
    rw [ByteArray.size_append, ByteArray.size_extract, hselSize, toByteArray_size]
    omega
  rw [← toByteArray_ofNat_fromByteArrayBigEndian_of_size hsize]
  congr 1
  apply u256_inj
  rw [skimSafeTransferPatchedSelector_toNat]
  rw [UInt256.toNat_ofNat_of_lt]
  · rw [skimFromByteArrayBigEndian_append]
    rw [transferSelector_fromByteArrayBigEndian, fromByteArrayBigEndian_toByteArray_extract4_32]
    rw [ByteArray.size_extract, toByteArray_size]
    rw [show 8 * (min 32 32 - 4) = 224 by norm_num]
  · rw [skimFromByteArrayBigEndian_append]
    rw [transferSelector_fromByteArrayBigEndian, fromByteArrayBigEndian_toByteArray_extract4_32]
    rw [ByteArray.size_extract, toByteArray_size]
    rw [show 8 * (min 32 32 - 4) = 224 by norm_num]
    have hlow : w.toNat % 2 ^ 224 < 2 ^ 224 := Nat.mod_lt _ (by positivity)
    have hsel : transferSelectorWord.toNat = 2835717307 := rfl
    rw [hsel]
    calc
      2835717307 * 2 ^ 224 + w.toNat % 2 ^ 224
          < 2835717307 * 2 ^ 224 + 2 ^ 224 := by omega
      _ = 2835717308 * 2 ^ 224 := by ring
      _ < 2 ^ 32 * 2 ^ 224 := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _ = UInt256.size := by norm_num [UInt256.size, Nat.pow_add]

theorem skimSafeTransferMem6_read228_28
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem6 self o toWord value).readWithPadding 228 28 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28 := by
  unfold skimSafeTransferMem6
  rw [write32_read_above_len _ _ 64 228 28 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)
      (by norm_num) (by norm_num)]
  unfold skimSafeTransferMem5
  rw [write32_read_above_len _ _ 192 228 28 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega)
      (by norm_num) (by norm_num)]
  unfold skimSafeTransferMem4
  rw [write32_read_below_len _ _ 260 228 28 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem3_size self toWord ho32 hoSize])
      (by omega)
      (by rw [skimSafeTransferMem3_size self toWord ho32 hoSize]; omega)
      (by norm_num) (by norm_num)]
  unfold skimSafeTransferMem3
  exact toByteArray_write_read_window_of_gap (UInt256.land solcAddrMask toWord) _ 228 0 28
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [skimSafeTransferMem2_size self ho32 hoSize]; exact lt_usize _ (by norm_num))

theorem skimSafeTransferWord224_extract4_32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (UInt256.toByteArray (skimSafeTransferWord224 self o toWord value)).extract 4 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28 := by
  unfold skimSafeTransferWord224
  have hreadSize :
      ((skimSafeTransferMem6 self o toWord value).readWithPadding 224 32).size = 32 := by
    rw [readWithPadding_eq_extract' _ 224 32 (by norm_num) (by norm_num)
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega)]
    rw [ByteArray.size_extract]
    rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]
    omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize]
  rw [readWithPadding_eq_extract' _ 224 32 (by norm_num) (by norm_num)
    (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega)]
  rw [extract_extract_BA]
  rw [show 224 + 4 = 228 by omega, show min (224 + 32) (224 + 32) = 256 by omega]
  rw [← readWithPadding_eq_extract' _ 228 28 (by norm_num) (by norm_num)
    (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega)]
  exact skimSafeTransferMem6_read228_28 self toWord value ho32 hoSize

theorem skimSafeTransferMem3_read256_4
    (self : UInt256) {o : ByteArray} (toWord : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem3 self o toWord).readWithPadding 256 4 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 := by
  unfold skimSafeTransferMem3
  exact toByteArray_write_read_window_of_gap (UInt256.land solcAddrMask toWord) _ 228 28 4
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [skimSafeTransferMem2_size self ho32 hoSize]; exact lt_usize _ (by norm_num))

theorem skimSafeTransferMem4_read256_32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem4 self o toWord value).readWithPadding 256 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  let mem4 := skimSafeTransferMem4 self o toWord value
  have hleft :
      mem4.extract 256 260 =
        (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 := by
    rw [← readWithPadding_eq_extract' mem4 256 4 (by norm_num) (by norm_num) (by
      dsimp [mem4]
      rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]
      omega)]
    dsimp [mem4]
    unfold skimSafeTransferMem4
    rw [write32_read_below_len _ _ 260 256 4 (by rw [toByteArray_size])
        (by rw [skimSafeTransferMem3_size self toWord ho32 hoSize])
        (by omega)
        (by rw [skimSafeTransferMem3_size self toWord ho32 hoSize])
        (by norm_num) (by norm_num)]
    exact skimSafeTransferMem3_read256_4 self toWord ho32 hoSize
  have hright :
      mem4.extract 260 288 = (UInt256.toByteArray value).extract 0 28 := by
    rw [← readWithPadding_eq_extract' mem4 260 28 (by norm_num) (by norm_num) (by
      dsimp [mem4]
      rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]
      omega)]
    dsimp [mem4]
    unfold skimSafeTransferMem4
    exact toByteArray_write_read_window_of_gap value _ 260 0 28
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [skimSafeTransferMem3_size self toWord ho32 hoSize]; exact lt_usize _ (by norm_num))
  dsimp [mem4] at hleft hright ⊢
  rw [readWithPadding_eq_extract' _ 256 32 (by norm_num) (by norm_num)
    (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega)]
  rw [show (skimSafeTransferMem4 self o toWord value).extract 256 (256 + 32) =
      (skimSafeTransferMem4 self o toWord value).extract 256 260 ++
        (skimSafeTransferMem4 self o toWord value).extract 260 288 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

theorem skimSafeTransferCallMem0_read256_32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem0 self o toWord value).readWithPadding 256 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold skimSafeTransferCallMem0
  rw [write32_read_below _ _ 292 256 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]) (by omega)]
  unfold skimSafeTransferMem7
  rw [write32_read_above _ _ 224 256 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega)]
  unfold skimSafeTransferMem6
  rw [write32_read_above _ _ 64 256 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)]
  unfold skimSafeTransferMem5
  rw [write32_read_above _ _ 192 256 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega)]
  exact skimSafeTransferMem4_read256_32 self toWord value ho32 hoSize

theorem skimSafeTransferCopyWord1_toByteArray
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    UInt256.toByteArray (skimSafeTransferCopyWord1 self o toWord value) =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold skimSafeTransferCopyWord1
  rw [skimSafeTransferCallMem0_read256_32 self toWord value ho32 hoSize]
  apply toByteArray_ofNat_fromByteArrayBigEndian_of_size
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    toByteArray_size]
  norm_num

theorem skimSafeTransferMem4_read288_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem4 self o toWord value).readWithPadding 288 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold skimSafeTransferMem4
  exact toByteArray_write_read_window_of_gap value _ 260 28 4
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [skimSafeTransferMem3_size self toWord ho32 hoSize]; exact lt_usize _ (by norm_num))

theorem skimSafeTransferCallMem1_read288_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem1 self o toWord value).readWithPadding 288 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold skimSafeTransferCallMem1
  rw [write32_read_below_len _ _ 324 288 4 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize])
      (by omega)
      (by rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize]; omega)
      (by norm_num) (by norm_num)]
  unfold skimSafeTransferCallMem0
  rw [write32_read_below_len _ _ 292 288 4 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize])
      (by omega)
      (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize])
      (by norm_num) (by norm_num)]
  unfold skimSafeTransferMem7
  rw [write32_read_above_len _ _ 224 288 4 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem6_size self toWord value ho32 hoSize])
      (by norm_num) (by norm_num)]
  unfold skimSafeTransferMem6
  rw [write32_read_above_len _ _ 64 288 4 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize])
      (by norm_num) (by norm_num)]
  unfold skimSafeTransferMem5
  rw [write32_read_above_len _ _ 192 288 4 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize])
      (by norm_num) (by norm_num)]
  exact skimSafeTransferMem4_read288_4 self toWord value ho32 hoSize

theorem skimSafeTransferTailSourceWord_extract0_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (UInt256.toByteArray (skimSafeTransferTailSourceWord self o toWord value)).extract 0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold skimSafeTransferTailSourceWord
  have hreadSize :
      ((skimSafeTransferCallMem1 self o toWord value).readWithPadding 288 32).size = 32 := by
    rw [readWithPadding_eq_extract' _ 288 32 (by norm_num) (by norm_num)
      (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]; omega)]
    rw [ByteArray.size_extract]
    rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]
    omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize]
  rw [readWithPadding_eq_extract' _ 288 32 (by norm_num) (by norm_num)
    (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]; omega)]
  rw [extract_extract_BA]
  rw [show 288 + 0 = 288 by omega, show min (288 + 4) (288 + 32) = 292 by omega]
  rw [← readWithPadding_eq_extract' _ 288 4 (by norm_num) (by norm_num)
    (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]; omega)]
  exact skimSafeTransferCallMem1_read288_4 self toWord value ho32 hoSize

theorem skimSafeTransferTailMask_toNat :
    skimSafeTransferTailMask.toNat = 2 ^ 224 - 1 := by
  native_decide

theorem skimSafeTransferTailClear_toNat (w : UInt256) :
    (UInt256.land w (UInt256.lnot skimSafeTransferTailMask)).toNat =
      (w.toNat / 2 ^ 224) * 2 ^ 224 := by
  rw [u256_land_toNat]
  have hlnot : (UInt256.lnot skimSafeTransferTailMask).toNat = 2 ^ 256 - 2 ^ 224 := by
    native_decide
  rw [hlnot]
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    exact w.val.isLt
  rw [natLandClearLow w.toNat 224 (by norm_num) hwlt]
  have hlt : w.toNat / 2 ^ 224 * 2 ^ 224 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hlt]

theorem skimSafeTransferTailWord_toNat_of_source (w : UInt256) :
    (UInt256.lor (UInt256.land w (UInt256.lnot skimSafeTransferTailMask))
      (UInt256.land ⟨0⟩ skimSafeTransferTailMask)).toNat =
      (w.toNat / 2 ^ 224) * 2 ^ 224 := by
  have hzero : UInt256.land (⟨0⟩ : UInt256) skimSafeTransferTailMask = ⟨0⟩ := by
    apply u256_inj
    rw [u256_land_toNat]
    native_decide
  rw [hzero, u256_lor_zero, skimSafeTransferTailClear_toNat]

theorem skimSafeTransferTailWord_extract0_4_of_source (w : UInt256) :
    (UInt256.toByteArray
      (UInt256.lor (UInt256.land w (UInt256.lnot skimSafeTransferTailMask))
        (UInt256.land ⟨0⟩ skimSafeTransferTailMask))).extract 0 4 =
      (UInt256.toByteArray w).extract 0 4 := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq, byteArray_toList_eq]
    rw [show ((UInt256.toByteArray
        (UInt256.lor (UInt256.land w (UInt256.lnot skimSafeTransferTailMask))
          (UInt256.land ⟨0⟩ skimSafeTransferTailMask))).extract 0 4).data.toList.length =
        ((UInt256.toByteArray
          (UInt256.lor (UInt256.land w (UInt256.lnot skimSafeTransferTailMask))
            (UInt256.land ⟨0⟩ skimSafeTransferTailMask))).extract 0 4).size by rfl]
    rw [show ((UInt256.toByteArray w).extract 0 4).data.toList.length =
        ((UInt256.toByteArray w).extract 0 4).size by rfl]
    rw [ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, toByteArray_size]
  · rw [← fromByteArrayBigEndian, ← fromByteArrayBigEndian]
    rw [fromByteArrayBigEndian_toByteArray_extract0_4,
      fromByteArrayBigEndian_toByteArray_extract0_4]
    rw [skimSafeTransferTailWord_toNat_of_source]
    rw [Nat.mul_comm (w.toNat / 2 ^ 224) (2 ^ 224)]
    rw [Nat.mul_div_right _ (by positivity : 0 < (2 : Nat) ^ 224)]

theorem skimSafeTransferTailWord_extract0_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (UInt256.toByteArray (skimSafeTransferTailWord self o toWord value)).extract 0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  rw [skimSafeTransferTailWord]
  rw [skimSafeTransferTailWord_extract0_4_of_source]
  exact skimSafeTransferTailSourceWord_extract0_4 self toWord value ho32 hoSize

theorem skimSafeTransferCallMem2_read292_32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem2 self o toWord value).readWithPadding 292 32 =
      UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value) := by
  unfold skimSafeTransferCallMem2
  rw [write32_read_below _ _ 356 292 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]) (by omega)]
  unfold skimSafeTransferCallMem1
  rw [write32_read_below _ _ 324 292 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize]) (by omega)]
  unfold skimSafeTransferCallMem0
  exact toByteArray_write_read_back_of_gap
    (skimSafeTransferPatchedSelectorWord self o toWord value) _ 292
    (by rw [skimSafeTransferMem7_size self toWord value ho32 hoSize]; norm_num)

theorem skimSafeTransferCallMem2_read324_32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem2 self o toWord value).readWithPadding 324 32 =
      UInt256.toByteArray (skimSafeTransferCopyWord1 self o toWord value) := by
  unfold skimSafeTransferCallMem2
  rw [write32_read_below _ _ 356 324 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize]) (by omega)]
  unfold skimSafeTransferCallMem1
  exact toByteArray_write_read_back_of_gap
    (skimSafeTransferCopyWord1 self o toWord value) _ 324
    (by rw [skimSafeTransferCallMem0_size self toWord value ho32 hoSize]; norm_num)

theorem skimSafeTransferCallMem2_read356_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem2 self o toWord value).readWithPadding 356 4 =
      (UInt256.toByteArray (skimSafeTransferTailWord self o toWord value)).extract 0 4 := by
  unfold skimSafeTransferCallMem2
  rw [write32_read_prefix_len _ _ 356 4 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem1_size self toWord value ho32 hoSize])
      (by norm_num) (by norm_num) (by norm_num)]

theorem skimSafeTransferCallMem2_read292_68
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (_ho32 : 32 ≤ o.size) (_hoSize : o.size < UInt256.size) :
    (skimSafeTransferCallMem2 self o toWord value).readWithPadding 292 68 =
      (transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68 := by
  rw [transferCalldataMem_read128_68]
  rw [byteArray_readWithPadding_split _ 292 32 36 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [skimSafeTransferCallMem2_size self toWord value _ho32 _hoSize]; norm_num)]
  rw [byteArray_readWithPadding_split _ 324 32 4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [skimSafeTransferCallMem2_size self toWord value _ho32 _hoSize]; norm_num)]
  rw [skimSafeTransferCallMem2_read292_32 self toWord value _ho32 _hoSize,
    skimSafeTransferCallMem2_read324_32 self toWord value _ho32 _hoSize]
  change UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value) ++
      (UInt256.toByteArray (skimSafeTransferCopyWord1 self o toWord value) ++
        (skimSafeTransferCallMem2 self o toWord value).readWithPadding 356 4) =
    transferSelector ++ (UInt256.land solcAddrMask toWord).toByteArray ++ value.toByteArray
  rw [skimSafeTransferCallMem2_read356_4 self toWord value _ho32 _hoSize]
  rw [skimSafeTransferPatchedSelectorWord, skimSafeTransferPatchedSelector_toByteArray]
  rw [skimSafeTransferWord224_extract4_32 self toWord value _ho32 _hoSize,
    skimSafeTransferCopyWord1_toByteArray self toWord value _ho32 _hoSize,
    skimSafeTransferTailWord_extract0_4 self toWord value _ho32 _hoSize]
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

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferCopySetupToSelectorPatch {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6466⟩
      (solcAddrMask :: ⟨192⟩ :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem6 self o toWord value) (UInt256.ofNat 10) o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6491⟩
      (⟨224⟩ :: ⟨192⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem7 self o toWord value) (UInt256.ofNat 10) o acc k' C' := by
  have rd6471 := evm_run h with [
    swap2, dup2, add, dup1,
    raw mload 0 (skimSafeTransferWord224 self o toWord value) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (skimSafeTransferMem6_mload224 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov)]
  have rd6480 := evm_run rd6471 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and]
  have rd6485 := rd6480.pushConst transferSelectorWord (width := 4) (op := .PUSH4)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd6491 := evm_run rd6485 with [
    push1 ⟨224⟩, shl, lor, dup2,
    raw mstore 0 (skimSafeTransferMem7 self o toWord value) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferMem7 skimSafeTransferPatchedSelectorWord; rfl)
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa [skimSafeTransferSelectorPatchMask] using rd6491⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferSelectorPatchToCopyLoop {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6491⟩
      (⟨224⟩ :: ⟨192⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem7 self o toWord value) (UInt256.ofNat 10) o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6512⟩
      (⟨224⟩ :: ⟨292⟩ :: ⟨68⟩ :: ⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ ::
        ⟨192⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem7 self o toWord value) (UInt256.ofNat 10) o acc k' C' := by
  have rd6512 := evm_run h with [
    swap3,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (skimSafeTransferMem7_mload64 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    dup2,
    raw mload 0 ⟨68⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (skimSafeTransferMem7_mload192 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    push1 ⟨0⟩, swap5, push1 ⟨96⟩, swap5, dup10, and,
    swap4, swap3, swap2, dup3, swap2, swap1, dup1, dup4, dup4]
  exact ⟨_, _, by simpa using rd6512⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferCopyLoopFirst {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6512⟩
      (⟨224⟩ :: ⟨292⟩ :: ⟨68⟩ :: ⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ ::
        ⟨192⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem7 self o toWord value) (UInt256.ofNat 10) o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6512⟩
      (⟨256⟩ :: ⟨324⟩ :: ⟨36⟩ :: ⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ ::
        ⟨192⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem0 self o toWord value) (UInt256.ofNat 11) o acc k' C' := by
  have rd6521 := evm_run h with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539 := evm_run rd6521 with [
    dup1,
    raw mload 0 (skimSafeTransferPatchedSelectorWord self o toWord value)
      (UInt256.ofNat 10) (by native_decide)
      mem_cost (skimSafeTransferMem7_mload224 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    dup3,
    raw mstore 3 (skimSafeTransferCallMem0 self o toWord value) (UInt256.ofNat 11)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferCallMem0; rfl) (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512 := rd6539.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨224⟩ = ⟨256⟩ by native_decide,
    show (⟨32⟩ : UInt256) + ⟨292⟩ = ⟨324⟩ by native_decide,
    show (⟨68⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨36⟩ by native_decide]
    at rd6512
  exact ⟨_, _, by simpa using rd6512⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferCopyLoopSecond {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6512⟩
      (⟨256⟩ :: ⟨324⟩ :: ⟨36⟩ :: ⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ ::
        ⟨192⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem0 self o toWord value) (UInt256.ofNat 11) o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6512⟩
      (⟨288⟩ :: ⟨356⟩ :: ⟨4⟩ :: ⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ ::
        ⟨192⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem1 self o toWord value) (UInt256.ofNat 12) o acc k' C' := by
  have rd6521 := evm_run h with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539 := evm_run rd6521 with [
    dup1,
    raw mload 0 (skimSafeTransferCopyWord1 self o toWord value)
      (UInt256.ofNat 11) (by native_decide)
      mem_cost (skimSafeTransferCallMem0_mload256 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    dup3,
    raw mstore 3 (skimSafeTransferCallMem1 self o toWord value) (UInt256.ofNat 12)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferCallMem1; rfl) (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512 := rd6539.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨256⟩ = ⟨288⟩ by native_decide,
    show (⟨32⟩ : UInt256) + ⟨324⟩ = ⟨356⟩ by native_decide,
    show (⟨36⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨4⟩ by native_decide]
    at rd6512
  exact ⟨_, _, by simpa using rd6512⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferCopyTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6512⟩
      (⟨288⟩ :: ⟨356⟩ :: ⟨4⟩ :: ⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ ::
        ⟨192⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem1 self o toWord value) (UInt256.ofNat 12) o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6575⟩
      (⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ :: ⟨192⟩ ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) o acc k' C' := by
  have rd6543 := evm_run h with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd6575 := evm_run rd6543 with [
    jumpdest, push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub,
    dup1, not, dup3,
    raw mload 0 (skimSafeTransferTailSourceWord self o toWord value)
      (UInt256.ofNat 12) (by native_decide)
      mem_cost (skimSafeTransferCallMem1_mload288 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    and, dup2, dup5,
    raw mload 3 ⟨0⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost (skimSafeTransferCallMem1_mload356 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    and, dup1, dup3, lor, dup6,
    raw mstore 0 (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferCallMem2 skimSafeTransferTailWord skimSafeTransferTailMask; rfl)
      (by native_decide) (by evm_ov),
    pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, by simpa [skimSafeTransferTailMask] using rd6575⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferBuiltToCall {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6575⟩
      (⟨68⟩ :: ⟨224⟩ :: ⟨292⟩ :: ⟨292⟩ :: ⟨192⟩ ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ gasArg k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6594⟩
      (gasArg :: UInt256.land token solcAddrMask :: ⟨0⟩ :: ⟨292⟩ :: ⟨68⟩ ::
        ⟨292⟩ :: ⟨0⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ ::
        ⟨0⟩ :: value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) o acc k' C' := by
  have rd6593 := evm_run h with [
    swap1, pop, add, swap2, pop, pop, push1 ⟨0⟩, push1 ⟨64⟩,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost (skimSafeTransferCallMem2_mload64 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    dup1, dup4, sub, dup2, push1 ⟨0⟩, dup7]
  obtain ⟨gasArg, rd6594⟩ := rd6593.gas (by native_decide) (by evm_ov)
  rw [show (⟨68⟩ : UInt256) + ⟨292⟩ = ⟨360⟩ by native_decide,
    show UInt256.sub (⟨360⟩ : UInt256) ⟨292⟩ = ⟨68⟩ by native_decide]
    at rd6594
  exact ⟨gasArg, _, _, by simpa using rd6594⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferCallMade {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel gasArg : UInt256}
    {o : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6594⟩
      (gasArg :: UInt256.land token solcAddrMask :: ⟨0⟩ :: ⟨292⟩ :: ⟨68⟩ ::
        ⟨292⟩ :: ⟨0⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ ::
        ⟨0⟩ :: value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) o (cA, σ) k C)
    (hdepth : ee.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ ee.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
            (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask))
            (toExecute σ (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask)))
            callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
            ((skimSafeTransferCallMem2 self o toWord value).readWithPadding 292 68)
            (ee.depth + 1) ee.header ee.perm)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨360⟩ ::
            UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
            value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
            sel :: [])
          (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘ, rd6595, houtSize⟩ :=
    h.call (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, A_in, callGas, k', C', ?_, ?_, houtSize⟩
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
theorem RD.uniswapSkimSafeTransferEntryToCallMade {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6370⟩
      (value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (balanceOfThisStaticcallMem self o) balanceOfThisStaticcallActiveWords o (cA, σ) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hdepth : ee.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A_in : Substate) (callGas gasArg : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ ee.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
            (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask))
            (toExecute σ (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask)))
            callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
            ((skimSafeTransferCallMem2 self o toWord value).readWithPadding 292 68)
            (ee.depth + 1) ee.header ee.perm)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨360⟩ ::
            UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
            value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
            sel :: [])
          (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out
          (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨_, _, rd6375⟩ :=
    RD.uniswapSkimSafeTransferEntryToFreePtr h ho32 hoSize
  obtain ⟨_, _, rd6380⟩ :=
    RD.uniswapSkimSafeTransferFreePtrToMem0 rd6375
  obtain ⟨_, _, rd6384⟩ :=
    RD.uniswapSkimSafeTransferMem0ToMem1 rd6380
  obtain ⟨_, _, rd6417⟩ :=
    RD.uniswapSkimSafeTransferMem1ToSignatureWord rd6384
  obtain ⟨_, _, rd6423⟩ :=
    RD.uniswapSkimSafeTransferSignatureWordToMem2 rd6417
  obtain ⟨_, _, rd6441⟩ :=
    RD.uniswapSkimSafeTransferMem2ToRecipientStore rd6423 ho32 hoSize
  obtain ⟨_, _, rd6449⟩ :=
    RD.uniswapSkimSafeTransferRecipientStoreToValueStore rd6441
  obtain ⟨_, _, rd6466⟩ :=
    RD.uniswapSkimSafeTransferValueStoreToCopySetup rd6449 ho32 hoSize
  obtain ⟨_, _, rd6491⟩ :=
    RD.uniswapSkimSafeTransferCopySetupToSelectorPatch rd6466 ho32 hoSize
  obtain ⟨_, _, rd6512⟩ :=
    RD.uniswapSkimSafeTransferSelectorPatchToCopyLoop rd6491 ho32 hoSize
  obtain ⟨_, _, rd6512a⟩ :=
    RD.uniswapSkimSafeTransferCopyLoopFirst rd6512 ho32 hoSize
  obtain ⟨_, _, rd6512b⟩ :=
    RD.uniswapSkimSafeTransferCopyLoopSecond rd6512a ho32 hoSize
  obtain ⟨_, _, rd6575⟩ :=
    RD.uniswapSkimSafeTransferCopyTail rd6512b ho32 hoSize
  obtain ⟨gasArg, _, _, rd6594⟩ :=
    RD.uniswapSkimSafeTransferBuiltToCall rd6575 ho32 hoSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘ, rd6595, houtSize⟩ :=
    RD.uniswapSkimSafeTransferCallMade rd6594 hdepth
  exact ⟨cA', σ', z, out, A_in, callGas, gasArg, k', C', hΘ, rd6595, houtSize⟩

def uniswapSafeTransferFailedStringWord : UInt256 :=
  ⟨38641673103035791731704587915945305821834519506660595196760963476668136030208⟩

noncomputable def skimSafeTransferFailedMem0
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray uniswapErrorStringSelector).write 0
    (skimSafeTransferCallMem2 self o toWord value) 292 32

noncomputable def skimSafeTransferFailedMem1
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (skimSafeTransferFailedMem0 self o toWord value) 296 32

noncomputable def skimSafeTransferFailedMem2
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨26⟩ : UInt256)).write 0
    (skimSafeTransferFailedMem1 self o toWord value) 328 32

noncomputable def skimSafeTransferFailedMem3
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray uniswapSafeTransferFailedStringWord).write 0
    (skimSafeTransferFailedMem2 self o toWord value) 360 32

theorem skimSafeTransferFailedMem0_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem0 self o toWord value).size = 388 := by
  unfold skimSafeTransferFailedMem0
  rw [write32_eq _ _ 292 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSafeTransferCallMem2_size self toWord value ho32 hoSize, toByteArray_size]
  omega

theorem skimSafeTransferFailedMem1_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem1 self o toWord value).size = 388 := by
  unfold skimSafeTransferFailedMem1
  rw [write32_eq _ _ 296 (by rw [toByteArray_size])
      (by rw [skimSafeTransferFailedMem0_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSafeTransferFailedMem0_size self toWord value ho32 hoSize, toByteArray_size]
  omega

theorem skimSafeTransferFailedMem2_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem2 self o toWord value).size = 388 := by
  unfold skimSafeTransferFailedMem2
  rw [write32_eq _ _ 328 (by rw [toByteArray_size])
      (by rw [skimSafeTransferFailedMem1_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSafeTransferFailedMem1_size self toWord value ho32 hoSize, toByteArray_size]
  omega

theorem skimSafeTransferFailedMem3_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem3 self o toWord value).size = 392 := by
  unfold skimSafeTransferFailedMem3
  rw [write32_eq _ _ 360 (by rw [toByteArray_size])
      (by rw [skimSafeTransferFailedMem2_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSafeTransferFailedMem2_size self toWord value ho32 hoSize, toByteArray_size]
  omega

theorem skimSafeTransferFailedMem0_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem0 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSafeTransferFailedMem0
  rw [write32_read_below _ _ 292 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; native_decide)
      (by omega)]
  exact skimSafeTransferCallMem2_read64 self toWord value ho32 hoSize

theorem skimSafeTransferFailedMem1_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem1 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSafeTransferFailedMem1
  rw [write32_read_below _ _ 296 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferFailedMem0_size self toWord value ho32 hoSize]; native_decide)
      (by omega)]
  exact skimSafeTransferFailedMem0_read64 self toWord value ho32 hoSize

theorem skimSafeTransferFailedMem2_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem2 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSafeTransferFailedMem2
  rw [write32_read_below _ _ 328 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferFailedMem1_size self toWord value ho32 hoSize]; native_decide)
      (by omega)]
  exact skimSafeTransferFailedMem1_read64 self toWord value ho32 hoSize

theorem skimSafeTransferFailedMem3_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferFailedMem3 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSafeTransferFailedMem3
  rw [write32_read_below _ _ 360 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferFailedMem2_size self toWord value ho32 hoSize]; native_decide)
      (by omega)]
  exact skimSafeTransferFailedMem2_read64 self toWord value ho32 hoSize

theorem skimSafeTransferFailedMem3_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (skimSafeTransferFailedMem3 self o toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferFailedMem3 self o toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSafeTransferFailedMem3_size self toWord value ho32 hoSize]; native_decide)
    (by native_decide)
    (skimSafeTransferFailedMem3_read64 self toWord value ho32 hoSize)

def skimSafeTransferReturnDataRounded (out : ByteArray) : UInt256 :=
  UInt256.land (UInt256.add (UInt256.ofNat out.size) ⟨63⟩) (UInt256.lnot ⟨31⟩)

def skimSafeTransferReturnDataPtr (out : ByteArray) : UInt256 :=
  (⟨292⟩ : UInt256) + skimSafeTransferReturnDataRounded out

noncomputable def skimSafeTransferReturnDataPtrMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (skimSafeTransferReturnDataPtr out)).write 0
    (skimSafeTransferCallMem2 self o toWord value) 64 32

noncomputable def skimSafeTransferReturnDataSizeMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat out.size)).write 0
    (skimSafeTransferReturnDataPtrMem self o toWord value out) 292 32

noncomputable def skimSafeTransferReturnDataMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out : ByteArray) :
    ByteArray :=
  out.write 0 (skimSafeTransferReturnDataSizeMem self o toWord value out) 324 out.size

def skimSafeTransferReturnDataActiveWords (out : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (UInt256.ofNat 13).toNat 324 out.size)

theorem skimSafeTransferReturnDataRounded_le (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataRounded out).toNat ≤ out.size + 63 := by
  unfold skimSafeTransferReturnDataRounded UInt256.land UInt256.toNat
  refine le_trans (show
      (Fin.land ((UInt256.ofNat out.size + ⟨63⟩ : UInt256).val)
        (UInt256.lnot ⟨31⟩).val).val ≤
        ((UInt256.ofNat out.size + ⟨63⟩ : UInt256).val).val from by
      simp [Fin.land]
      exact le_trans (Nat.mod_le _ _) (by
        refine Nat.le_of_testBit fun i hi => ?_
        change (((UInt256.ofNat out.size + ⟨63⟩ : UInt256).val.val &&&
            (UInt256.lnot ⟨31⟩).val.val).testBit i = true) at hi
        rw [Nat.testBit_and] at hi
        simp only [Bool.and_eq_true] at hi
        exact hi.1)) ?_
  change ((UInt256.ofNat out.size + ⟨63⟩ : UInt256).toNat) ≤ out.size + 63
  rw [uadd_toNat]
  have hof : (UInt256.ofNat out.size).toNat = out.size := by
    exact UInt256.toNat_ofNat_of_lt (by
      have hpow : 2 ^ 255 < UInt256.size := by norm_num [UInt256.size]
      omega)
  rw [hof]
  exact Nat.mod_le _ _

theorem skimSafeTransferReturnDataPtr_toNat_le (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataPtr out).toNat ≤ 355 + out.size := by
  have hround := skimSafeTransferReturnDataRounded_le out houtSize
  unfold skimSafeTransferReturnDataPtr
  rw [uadd_toNat]
  have hlt :
      (⟨292⟩ : UInt256).toNat + (skimSafeTransferReturnDataRounded out).toNat <
        UInt256.size := by
    have hpow : 2 ^ 255 + 355 < UInt256.size := by norm_num [UInt256.size]
    rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
    omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
  omega

theorem skimSafeTransferReturnDataPtr_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    96 ≤ (skimSafeTransferReturnDataPtr out).toNat := by
  unfold skimSafeTransferReturnDataPtr
  rw [uadd_toNat]
  have hroundLe :=
    skimSafeTransferReturnDataRounded_le out houtSize
  have hlt :
      (⟨292⟩ : UInt256).toNat + (skimSafeTransferReturnDataRounded out).toNat <
        UInt256.size := by
    have hpow : 2 ^ 255 + 355 < UInt256.size := by norm_num [UInt256.size]
    rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
    omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
  omega

theorem skimSafeTransferReturnDataPtrMem_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferReturnDataPtrMem self o toWord value out).size = 388 := by
  unfold skimSafeTransferReturnDataPtrMem
  rw [write32_eq _ _ 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSafeTransferCallMem2_size self toWord value ho32 hoSize, toByteArray_size]
  omega

theorem skimSafeTransferReturnDataSizeMem_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferReturnDataSizeMem self o toWord value out).size = 388 := by
  unfold skimSafeTransferReturnDataSizeMem
  rw [write32_eq _ _ 292 (by rw [toByteArray_size])
      (by rw [skimSafeTransferReturnDataPtrMem_size self toWord value out ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSafeTransferReturnDataPtrMem_size self toWord value out ho32 hoSize, toByteArray_size]
  omega

theorem skimSafeTransferReturnDataPtrMem_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferReturnDataPtrMem self o toWord value out).readWithPadding 64 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out) := by
  unfold skimSafeTransferReturnDataPtrMem
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; omega)]
  rw [show (UInt256.toByteArray (skimSafeTransferReturnDataPtr out)).extract 0 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out) by
    rw [show 32 = (UInt256.toByteArray (skimSafeTransferReturnDataPtr out)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSafeTransferReturnDataSizeMem_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferReturnDataSizeMem self o toWord value out).readWithPadding 64 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out) := by
  unfold skimSafeTransferReturnDataSizeMem
  rw [write32_read_below _ _ 292 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferReturnDataPtrMem_size self toWord value out ho32 hoSize]; omega)
      (by omega)]
  exact skimSafeTransferReturnDataPtrMem_read64 self toWord value out ho32 hoSize

theorem skimSafeTransferReturnDataSizeMem_read292
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtSize : out.size < UInt256.size) :
    (skimSafeTransferReturnDataSizeMem self o toWord value out).readWithPadding 292 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) := by
  unfold skimSafeTransferReturnDataSizeMem
  rw [write32_read_back _ _ 292 (by rw [toByteArray_size])
      (by rw [skimSafeTransferReturnDataPtrMem_size self toWord value out ho32 hoSize]; omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat out.size)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat out.size)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSafeTransferReturnDataMem_read292
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < UInt256.size) :
    (skimSafeTransferReturnDataMem self o toWord value out).readWithPadding 292 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) := by
  unfold skimSafeTransferReturnDataMem
  by_cases hin :
      324 + out.size ≤
        (skimSafeTransferReturnDataSizeMem self o toWord value out).size
  · rw [write_read_below_gen out
      (skimSafeTransferReturnDataSizeMem self o toWord value out)
      324 out.size 292 houtNe le_rfl hin (by omega)]
    exact skimSafeTransferReturnDataSizeMem_read292 self toWord value out ho32 hoSize houtSize
  · have hbase :
        (skimSafeTransferReturnDataSizeMem self o toWord value out).size = 388 :=
      skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize
    have hext :
        (skimSafeTransferReturnDataSizeMem self o toWord value out).size <
          324 + out.size := by omega
    rw [write_eq_gen_extend out
      (skimSafeTransferReturnDataSizeMem self o toWord value out)
      324 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
    rw [readWithPadding_eq_extract _ 292 (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ 292 324 (by
      rw [ByteArray.size_extract]
      omega)]
    rw [extract_prefix _ 324 292 324 (by omega)]
    rw [← readWithPadding_eq_extract
      (skimSafeTransferReturnDataSizeMem self o toWord value out) 292 (by rw [hbase]; omega)]
    exact skimSafeTransferReturnDataSizeMem_read292 self toWord value out ho32 hoSize houtSize

theorem skimSafeTransferReturnDataMem_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) :
    (skimSafeTransferReturnDataMem self o toWord value out).readWithPadding 64 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out) := by
  unfold skimSafeTransferReturnDataMem
  by_cases hin :
      324 + out.size ≤
        (skimSafeTransferReturnDataSizeMem self o toWord value out).size
  · rw [write_read_below_gen out
      (skimSafeTransferReturnDataSizeMem self o toWord value out)
      324 out.size 64 houtNe le_rfl hin (by omega)]
    exact skimSafeTransferReturnDataSizeMem_read64 self toWord value out ho32 hoSize
  · have hbase :
        (skimSafeTransferReturnDataSizeMem self o toWord value out).size = 388 :=
      skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize
    have hext :
        (skimSafeTransferReturnDataSizeMem self o toWord value out).size <
          324 + out.size := by
      omega
    rw [write_eq_gen_extend out
      (skimSafeTransferReturnDataSizeMem self o toWord value out)
      324 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
    rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ 64 96 (by
      rw [ByteArray.size_extract]
      omega)]
    rw [extract_prefix _ 324 64 96 (by omega)]
    rw [← readWithPadding_eq_extract
      (skimSafeTransferReturnDataSizeMem self o toWord value out) 64 (by rw [hbase]; omega)]
    exact skimSafeTransferReturnDataSizeMem_read64 self toWord value out ho32 hoSize

theorem skimSafeTransferReturnDataActiveWords_M_mul32_lt (out : ByteArray)
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

theorem skimSafeTransferReturnDataActiveWords_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSafeTransferReturnDataActiveWords out).toNat := by
  unfold skimSafeTransferReturnDataActiveWords
  have hmul := skimSafeTransferReturnDataActiveWords_M_mul32_lt out houtSize
  have hMlt : MachineState.M (UInt256.ofNat 13).toNat 324 out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
  unfold MachineState.M
  split
  · norm_num
  · exact Nat.le_max_left _ _

theorem skimSafeTransferReturnDataActiveWords_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataActiveWords out).toNat * 32 < UInt256.size := by
  unfold skimSafeTransferReturnDataActiveWords
  have hmul := skimSafeTransferReturnDataActiveWords_M_mul32_lt out houtSize
  have hMlt : MachineState.M (UInt256.ofNat 13).toNat 324 out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hmul

theorem skimSafeTransferReturnDataActiveWords_mload64_haw (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    ¬ (⟨64⟩ : UInt256) ≥ skimSafeTransferReturnDataActiveWords out * ⟨32⟩ := by
  intro h
  have hle :
      (skimSafeTransferReturnDataActiveWords out * ⟨32⟩).toNat ≤
        (⟨64⟩ : UInt256).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (skimSafeTransferReturnDataActiveWords_mul32_lt out houtSize),
    show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
  have hge := skimSafeTransferReturnDataActiveWords_toNat_ge out houtSize
  omega

theorem skimSafeTransferReturnDataMem_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSafeTransferReturnDataMem self o toWord value out).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSafeTransferReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferReturnDataMem self o toWord value out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSafeTransferReturnDataPtr out := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSafeTransferReturnDataActiveWords out)
    (v := skimSafeTransferReturnDataPtr out)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold skimSafeTransferReturnDataMem
      by_cases hin :
          324 + out.size ≤
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size
      · rw [write_eq_gen out
          (skimSafeTransferReturnDataSizeMem self o toWord value out)
          324 out.size houtNe le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbase :
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size = 388 :=
          skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize
        have hext :
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size <
              324 + out.size := by omega
        rw [write_eq_gen_extend out
          (skimSafeTransferReturnDataSizeMem self o toWord value out)
          324 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)
    (skimSafeTransferReturnDataActiveWords_mload64_haw out houtSize)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        skimSafeTransferReturnDataMem_read64 self toWord value out ho32 hoSize houtNe)

theorem skimSafeTransferReturnDataActiveWords_mload292_haw (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    ¬ (⟨292⟩ : UInt256) ≥ skimSafeTransferReturnDataActiveWords out * ⟨32⟩ := by
  intro h
  have hle :
      (skimSafeTransferReturnDataActiveWords out * ⟨32⟩).toNat ≤
        (⟨292⟩ : UInt256).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (skimSafeTransferReturnDataActiveWords_mul32_lt out houtSize),
    show (⟨292⟩ : UInt256).toNat = 292 from by decide] at hle
  have hge := skimSafeTransferReturnDataActiveWords_toNat_ge out houtSize
  omega

theorem skimSafeTransferReturnDataActiveWords_mload292_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
          (⟨292⟩ : UInt256).toNat 32) =
      skimSafeTransferReturnDataActiveWords out := by
  have hM :
      MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
          (⟨292⟩ : UInt256).toNat 32 =
        (skimSafeTransferReturnDataActiveWords out).toNat := by
    rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
    simp [MachineState.M]
    have hge := skimSafeTransferReturnDataActiveWords_toNat_ge out houtSize
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem skimSafeTransferReturnDataMem_mload292
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (if (⟨292⟩ : UInt256).toNat ≥
          (skimSafeTransferReturnDataMem self o toWord value out).size
        ∨ (⟨292⟩ : UInt256) ≥ skimSafeTransferReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferReturnDataMem self o toWord value out).readWithPadding
          (⟨292⟩ : UInt256).toNat 32))) =
      UInt256.ofNat out.size := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨292⟩ : UInt256)) (aw := skimSafeTransferReturnDataActiveWords out)
    (v := UInt256.ofNat out.size)
    (by
      rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
      unfold skimSafeTransferReturnDataMem
      by_cases hin :
          324 + out.size ≤
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size
      · rw [write_eq_gen out
          (skimSafeTransferReturnDataSizeMem self o toWord value out)
          324 out.size houtNe le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbase :
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size = 388 :=
          skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize
        have hext :
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size <
              324 + out.size := by omega
        rw [write_eq_gen_extend out
          (skimSafeTransferReturnDataSizeMem self o toWord value out)
          324 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)
    (skimSafeTransferReturnDataActiveWords_mload292_haw out houtSize)
    (by
      simpa [show (⟨292⟩ : UInt256).toNat = 292 from by decide] using
        skimSafeTransferReturnDataMem_read292 self toWord value out ho32 hoSize houtNe
          (lt_size_of_lt_sign houtSize))

theorem skimSafeTransferReturnDataMem_mload324
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255) :
    (if (⟨324⟩ : UInt256).toNat ≥
          (skimSafeTransferReturnDataMem self o toWord value out).size
        ∨ (⟨324⟩ : UInt256) ≥ skimSafeTransferReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferReturnDataMem self o toWord value out).readWithPadding
          (⟨324⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨324⟩ : UInt256).toNat = 324 from by decide]
    let base := skimSafeTransferReturnDataSizeMem self o toWord value out
    have hbase : base.size = 388 :=
      skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize
    unfold skimSafeTransferReturnDataMem
    change UInt256.ofNat
        (fromByteArrayBigEndian ((out.write 0 base 324 out.size).readWithPadding 324 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    by_cases hin : 324 + out.size ≤ base.size
    · rw [write_eq_gen out base 324 out.size (by omega) le_rfl hin]
      rw [ByteArray.append_assoc]
      rw [readWithPadding_eq_extract _ 324 (by
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ 324 356 (by
        rw [ByteArray.size_extract]
        omega)]
      rw [show (base.extract 0 324).size = 324 by
        rw [ByteArray.size_extract, hbase]
        omega]
      rw [Nat.sub_self, show 356 - 324 = 32 by omega]
      rw [extract_append_left _ _ 0 32 (by
        rw [ByteArray.size_extract]
        omega)]
      rw [extract_prefix _ out.size 0 32 (by omega)]
    · have hext : base.size < 324 + out.size := by omega
      rw [write_eq_gen_extend out base 324 out.size (by omega) le_rfl (by rw [hbase]; omega)
          hext]
      rw [readWithPadding_eq_extract _ 324 (by
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ 324 356 (by
        rw [ByteArray.size_extract, hbase]
        omega)]
      rw [show (base.extract 0 324).size = 324 by
        rw [ByteArray.size_extract, hbase]
        omega]
      rw [Nat.sub_self, show 356 - 324 = 32 by omega]
      rw [extract_prefix _ out.size 0 32 (by omega)]
  · rw [not_or]
    constructor
    · rw [show (⟨324⟩ : UInt256).toNat = 324 from by decide]
      unfold skimSafeTransferReturnDataMem
      by_cases hin :
          324 + out.size ≤
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size
      · rw [write_eq_gen out (skimSafeTransferReturnDataSizeMem self o toWord value out)
          324 out.size (by omega) le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbase :
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size = 388 :=
          skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize
        have hext :
            (skimSafeTransferReturnDataSizeMem self o toWord value out).size <
              324 + out.size := by omega
        rw [write_eq_gen_extend out
          (skimSafeTransferReturnDataSizeMem self o toWord value out)
          324 out.size (by omega) le_rfl (by rw [hbase]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega
    · intro h
      have hle :
          (skimSafeTransferReturnDataActiveWords out * ⟨32⟩).toNat ≤
            (⟨324⟩ : UInt256).toNat := h
      rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt (skimSafeTransferReturnDataActiveWords_mul32_lt out houtSize),
        show (⟨324⟩ : UInt256).toNat = 324 from by decide] at hle
      unfold skimSafeTransferReturnDataActiveWords at hle
      have hMlt : MachineState.M (UInt256.ofNat 13).toNat 324 out.size < UInt256.size := by
        have hmul := skimSafeTransferReturnDataActiveWords_M_mul32_lt out houtSize
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

theorem skimSafeTransferReturnDataActiveWords_mload324_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
          (⟨324⟩ : UInt256).toNat 32) =
      skimSafeTransferReturnDataActiveWords out := by
  have hM :
      MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
          (⟨324⟩ : UInt256).toNat 32 =
        (skimSafeTransferReturnDataActiveWords out).toNat := by
    rw [show (⟨324⟩ : UInt256).toNat = 324 from by decide]
    simp [MachineState.M]
    have hge := skimSafeTransferReturnDataActiveWords_toNat_ge out houtSize
    omega
  rw [hM]
  exact u256_ofNat_toNat _

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferReturnNonemptyReturnToCheck {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {status callRetOffset maskedToken value toWord token ret dataPtr finalAw : UInt256}
    {R : List UInt256} {mem0 memFinal out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw0 : UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: callRetOffset :: maskedToken :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R) mem0 aw0 out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (hloadPtr :
      (if (⟨64⟩ : UInt256).toNat ≥ mem0.size ∨ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem0.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      dataPtr)
    (haw64 : UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32) = aw0)
    (hawDataPtr : UInt256.ofNat (MachineState.M aw0.toNat dataPtr.toNat 32) = aw0)
    (hmemFinal :
      out.write 0
        ((UInt256.toByteArray (UInt256.ofNat out.size)).write 0
          ((UInt256.toByteArray
            (dataPtr +
              (UInt256.land (UInt256.ofNat out.size + ⟨63⟩)
                (UInt256.lnot ⟨31⟩)))).write 0 mem0 64 32)
          dataPtr.toNat 32)
        ((dataPtr + ⟨32⟩).toNat) out.size =
      memFinal)
    (hawFinal :
      UInt256.ofNat
        (MachineState.M aw0.toNat ((dataPtr + ⟨32⟩).toNat) out.size) =
      finalAw)
    (hR : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (dataPtr :: status :: value :: toWord :: token :: ret :: R)
      memFinal finalAw out acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    dsimp [rdsz]
    exact UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro hzero
    have hnat : rdsz.toNat = 0 := by rw [hzero]; rfl
    rw [hrdsz_toNat] at hnat
    exact houtNe hnat
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6608 := rd6607
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat out.size = rdsz from rfl, heq0] at rd6608
  have rd6610 := evm_run rd6608 with [jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd6611 := RD.mload 0 dataPtr aw0 rd6610 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw64])
    hloadPtr haw64
    (by simp only [List.length_cons]; omega)
  let rounded : UInt256 := UInt256.land (rdsz + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray := (UInt256.toByteArray (dataPtr + rounded)).write 0
    mem0 64 32
  have rd6625 := evm_run rd6611 with [
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and,
    dup3, add, push1 ⟨64⟩]
  have rd6626 := RD.mstore 0 mem2 aw0 rd6625 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw64])
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    haw64
    (by simp only [List.length_cons]; omega)
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 dataPtr.toNat 32
  have rd6628 := evm_run rd6626 with [returndatasize, dup3]
  have rd6629 := RD.mstore 0 mem3 aw0 rd6628 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawDataPtr])
    (by dsimp [mem3])
    hawDataPtr
    (by simp only [List.length_cons]; omega)
  have rd6636 := evm_run rd6629 with [returndatasize, push1 ⟨0⟩, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := dataPtr + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat out.size
  have hcopyLen_toNat : copyLen.toNat = out.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)
  let mem4 : ByteArray := out.write 0 mem3 copyDest.toNat copyLen.toNat
  have hmem4 : mem4 = memFinal := by
    simpa [mem4, mem3, mem2, copyDest, copyLen, rdsz, rounded, hcopyLen_toNat]
      using hmemFinal
  have haw4 :
      UInt256.ofNat (MachineState.M aw0.toNat copyDest.toNat copyLen.toNat) =
        finalAw := by
    simpa [copyDest, copyLen, hcopyLen_toNat] using hawFinal
  have haw4' :
      UInt256.ofNat (MachineState.M aw0.toNat (dataPtr + ⟨32⟩).toNat out.size) =
        finalAw := by
    simpa [copyDest, copyLen, hcopyLen_toNat] using haw4
  have rd6637 := RD.returndatacopy (Cₘ finalAw - Cₘ aw0) mem4 finalAw
    rd6636 (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize), haw4'])
    (by rfl)
    haw4
    (by evm_ov)
  have rd6646 := evm_run rd6637 with [push2 ⟨6646⟩, jump (by jump_dest), jumpdest]
  have rd6652 := evm_run rd6646 with [pop, swap2, pop, swap2, pop]
  rw [hmem4] at rd6652
  exact ⟨_, _, by simpa using rd6652⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyReturnToCheck {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel status : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (⟨292⟩ :: status :: value :: toWord :: token :: ret :: token1 :: token :: toWord ::
        ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out acc k' C' := by
  exact RD.uniswapSafeTransferReturnNonemptyReturnToCheck
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
    h houtNe houtSize
    (skimSafeTransferCallMem2_mload64 self toWord value ho32 hoSize)
    (by native_decide)
    (by native_decide)
    (by
      rw [
        show (UInt256.ofNat out.size + ⟨63⟩) =
          UInt256.add (UInt256.ofNat out.size) ⟨63⟩ from rfl,
        show (⟨292⟩ : UInt256).toNat = 292 from by decide,
        show ((⟨292⟩ : UInt256) + ⟨32⟩).toNat = 324 from by decide]
      rfl)
    (by
      rw [show ((⟨292⟩ : UInt256) + ⟨32⟩).toNat = 324 from by decide]
      rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferEmptyFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
    (hout : out.size = 0)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6607' := rd6607
  rw [hout] at rd6607'
  have rd6641 := evm_run rd6607' with [jumpiT (by native_decide) (by jump_dest)]
  have rd6652 := evm_run rd6641 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap2, pop, swap2, pop]
  have rd6692 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  have rd6701 := evm_run rd6697 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost (skimSafeTransferCallMem2_mload64 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov)]
  have rd6705 := rd6701.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by native_decide) (by native_decide) (by evm_ov)
  have rd6708 := evm_run rd6705 with [push1 ⟨229⟩, shl, dup2]
  have rd6710 := evm_run rd6708 with [
    raw mstore 0 (skimSafeTransferFailedMem0 self o toWord value) (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferFailedMem0; rfl) (by native_decide) (by evm_ov)]
  have rd6716 := evm_run rd6710 with [push1 ⟨32⟩, push1 ⟨4⟩, dup3, add]
  have rd6717 := evm_run rd6716 with [
    raw mstore 0 (skimSafeTransferFailedMem1 self o toWord value) (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferFailedMem1; rfl) (by native_decide) (by evm_ov)]
  have rd6723 := evm_run rd6717 with [push1 ⟨26⟩, push1 ⟨36⟩, dup3, add]
  have rd6724 := evm_run rd6723 with [
    raw mstore 0 (skimSafeTransferFailedMem2 self o toWord value) (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferFailedMem2; rfl) (by native_decide) (by evm_ov)]
  have rd6757 := rd6724.pushConst uniswapSafeTransferFailedStringWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd6757 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 0 (skimSafeTransferFailedMem3 self o toWord value) (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSafeTransferFailedMem3; rfl) (by native_decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost (skimSafeTransferFailedMem3_mload64 self toWord value ho32 hoSize)
      (by native_decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferEmptyReturnToRet {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
    (hout : out.size = 0)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k' C' := by
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6607' := rd6607
  rw [hout] at rd6607'
  have rd6641 := evm_run rd6607' with [jumpiT (by native_decide) (by jump_dest)]
  have rd6652 := evm_run rd6641 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap2, pop, swap2, pop]
  have rd6658 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiNT (by native_decide)]
  have rd6668 := evm_run rd6658 with [
    pop, dup1,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; native_decide)
        (by native_decide)
        (skimSafeTransferCallMem2_read96_zero self toWord value ho32 hoSize))
      (by native_decide) (by evm_ov),
    iszero, dup1, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6773 := evm_run rd6668 with [jumpdest, push2 ⟨6773⟩,
    jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferEmptyReturnTo5330 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 sel : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ⟨5330⟩ :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
    (hout : out.size = 0) (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5330⟩
      (token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k' C' := by
  exact RD.uniswapSkimSafeTransferEmptyReturnToRet h hout ho32 hoSize (by jump_dest)

end UniswapV2Pair
