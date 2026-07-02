import Examples.UniswapV2Pair.SkimSecondRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` second `_safeTransfer` runtime tail -/

noncomputable def skimSecondSafeTransferMem0
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (⟨356⟩ : UInt256)).write 0
    (skimSecondBalanceStaticcallMem self o toWord prevValue out2) 64 32

noncomputable def skimSecondSafeTransferMem1
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0
    (skimSecondSafeTransferMem0 self o toWord prevValue out2) 292 32

noncomputable def skimSecondSafeTransferMem2
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray skimSafeTransferSignatureWord).write 0
    (skimSecondSafeTransferMem1 self o toWord prevValue out2) 324 32

noncomputable def skimSecondSafeTransferMem3
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).write 0
    (skimSecondSafeTransferMem2 self o toWord prevValue out2) 392 32

noncomputable def skimSecondSafeTransferMem4
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0
    (skimSecondSafeTransferMem3 self o toWord prevValue out2) 424 32

noncomputable def skimSecondSafeTransferMem5
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨68⟩ : UInt256)).write 0
    (skimSecondSafeTransferMem4 self o toWord prevValue out2 value) 356 32

noncomputable def skimSecondSafeTransferMem5WritesAfter64
    (toWord value : UInt256) : List (Nat × UInt256) :=
  [(292, (⟨25⟩ : UInt256)),
   (324, skimSafeTransferSignatureWord),
   (392, UInt256.land solcAddrMask toWord),
   (424, value),
   (356, (⟨68⟩ : UInt256))]

noncomputable def skimSecondSafeTransferMem5Writes
    (toWord value : UInt256) : List (Nat × UInt256) :=
  (64, (⟨356⟩ : UInt256)) :: skimSecondSafeTransferMem5WritesAfter64 toWord value

theorem skimSecondSafeTransferMem5_eq_writeCascade
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) :
    skimSecondSafeTransferMem5 self o toWord prevValue out2 value =
      writeCascade (skimSecondBalanceStaticcallMem self o toWord prevValue out2)
        (skimSecondSafeTransferMem5Writes toWord value) := by
  rfl

theorem skimSecondSafeTransferMem5Writes_size (toWord value : UInt256) :
    writeCascadeSize 388 (skimSecondSafeTransferMem5Writes toWord value) = 456 := by
  rfl

theorem skimSecondSafeTransferMem5Writes_gaps (toWord value : UInt256) :
    WriteGapsOk 388 (skimSecondSafeTransferMem5Writes toWord value) := by
  simp [WriteGapsOk, skimSecondSafeTransferMem5Writes,
    skimSecondSafeTransferMem5WritesAfter64]
  exact lt_usize 4 (by norm_num)

theorem skimSecondSafeTransferMem5WritesAfter64_disjoint64 (toWord value : UInt256) :
    WindowDisjointFromWrites 388 64 32
      (skimSecondSafeTransferMem5WritesAfter64 toWord value) := by
  simp [WindowDisjointFromWrites, skimSecondSafeTransferMem5WritesAfter64]
  exact lt_usize 4 (by norm_num)

noncomputable def skimSecondSafeTransferMem6
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨456⟩ : UInt256)).write 0
    (skimSecondSafeTransferMem5 self o toWord prevValue out2 value) 64 32

noncomputable def skimSecondSafeTransferWord388
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSecondSafeTransferMem6 self o toWord prevValue out2 value).readWithPadding 388 32))

noncomputable def skimSecondSafeTransferPatchedSelectorWord
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft transferSelectorWord ⟨224⟩)
    (UInt256.land skimSafeTransferSelectorPatchMask
      (skimSecondSafeTransferWord388 self o toWord prevValue out2 value))

noncomputable def skimSecondSafeTransferMem7
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value)).write 0
    (skimSecondSafeTransferMem6 self o toWord prevValue out2 value) 388 32

theorem skimSecondSafeTransferMem0_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem0 self o toWord prevValue out2).size = 388 := by
  unfold skimSecondSafeTransferMem0
  exact toByteArray_write32_size_of_le _ _ 64 388 388
    (skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
      ho32 hoSize hout32 houtSize)
    (by
      rw [skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
        ho32 hoSize hout32 houtSize]
      omega)
    (by norm_num)

theorem skimSecondSafeTransferMem1_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem1 self o toWord prevValue out2).size = 388 := by
  unfold skimSecondSafeTransferMem1
  exact toByteArray_write32_size_of_le _ _ 292 388 388
    (skimSecondSafeTransferMem0_size self toWord prevValue ho32 hoSize hout32 houtSize)
    (by
      rw [skimSecondSafeTransferMem0_size self toWord prevValue ho32 hoSize hout32 houtSize]
      omega)
    (by norm_num)

theorem skimSecondSafeTransferMem2_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem2 self o toWord prevValue out2).size = 388 := by
  unfold skimSecondSafeTransferMem2
  exact toByteArray_write32_size_of_le _ _ 324 388 388
    (skimSecondSafeTransferMem1_size self toWord prevValue ho32 hoSize hout32 houtSize)
    (by
      rw [skimSecondSafeTransferMem1_size self toWord prevValue ho32 hoSize hout32 houtSize]
      omega)
    (by norm_num)

theorem skimSecondSafeTransferMem3_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem3 self o toWord prevValue out2).size = 424 := by
  unfold skimSecondSafeTransferMem3
  exact toByteArray_write32_size_of_ge _ _ 392 388 424
    (skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize hout32 houtSize)
    (by norm_num) (lt_usize 4 (by norm_num)) (by norm_num)

theorem skimSecondSafeTransferMem4_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem4 self o toWord prevValue out2 value).size = 456 := by
  unfold skimSecondSafeTransferMem4
  exact toByteArray_write32_size_of_ge _ _ 424 424 456
    (skimSecondSafeTransferMem3_size self toWord prevValue ho32 hoSize hout32 houtSize)
    (by norm_num) (lt_usize 0 (by norm_num)) (by norm_num)

theorem skimSecondSafeTransferMem5_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem5 self o toWord prevValue out2 value).size = 456 := by
  rw [skimSecondSafeTransferMem5_eq_writeCascade]
  exact safeTransferCalldata_writeCascade_size _ _ 388 456
    (skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
      ho32 hoSize hout32 houtSize)
    (by
      rw [skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
        ho32 hoSize hout32 houtSize]
      exact skimSecondSafeTransferMem5Writes_gaps toWord value)
    (skimSecondSafeTransferMem5Writes_size toWord value)

theorem skimSecondSafeTransferMem6_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem6 self o toWord prevValue out2 value).size = 456 := by
  unfold skimSecondSafeTransferMem6
  exact toByteArray_write32_size_of_le _ _ 64 456 456
    (skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize)
    (by
      rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize]
      omega)
    (by norm_num)

theorem skimSecondSafeTransferMem7_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).size = 456 := by
  unfold skimSecondSafeTransferMem7
  exact toByteArray_write32_size_of_le _ _ 388 456 456
    (skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize)
    (by
      rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]
      omega)
    (by norm_num)

theorem skimSecondSafeTransferMem2_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem2 self o toWord prevValue out2).readWithPadding 64 32 =
      UInt256.toByteArray (⟨356⟩ : UInt256) := by
  unfold skimSecondSafeTransferMem2 skimSecondSafeTransferMem1 skimSecondSafeTransferMem0
  simpa [writeCascade, Reasoning.Theory.writeWord] using
    writeCascade_read_word_of_head_of_base
      (skimSecondBalanceStaticcallMem self o toWord prevValue out2)
      (base := 388) (off := 64) (⟨356⟩ : UInt256)
      [(292, (⟨25⟩ : UInt256)), (324, skimSafeTransferSignatureWord)]
      (skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
        ho32 hoSize hout32 houtSize)
      (lt_usize 0 (by norm_num))
      (by simp [WindowDisjointFromWrites])

theorem skimSecondSafeTransferMem2_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferMem2 self o toWord prevValue out2).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferMem2 self o toWord prevValue out2).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨356⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize hout32 houtSize]
      native_decide)
    (by native_decide)
    (skimSecondSafeTransferMem2_read64 self toWord prevValue ho32 hoSize hout32 houtSize)

theorem skimSecondSafeTransferMem4_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem4 self o toWord prevValue out2 value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨356⟩ : UInt256) := by
  unfold skimSecondSafeTransferMem4 skimSecondSafeTransferMem3
  change (writeCascade (skimSecondSafeTransferMem2 self o toWord prevValue out2)
      [(392, UInt256.land solcAddrMask toWord), (424, value)]).readWithPadding 64 32 =
    UInt256.toByteArray (⟨356⟩ : UInt256)
  rw [writeCascade_read_preserved_len]
  · exact skimSecondSafeTransferMem2_read64 self toWord prevValue ho32 hoSize hout32 houtSize
  · rw [skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize hout32 houtSize]
    simp [WindowDisjointFromWrites]
    exact lt_usize 4 (by norm_num)
  · norm_num
  · norm_num

theorem skimSecondSafeTransferMem4_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferMem4 self o toWord prevValue out2 value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferMem4 self o toWord prevValue out2 value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨356⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondSafeTransferMem4_size self toWord prevValue value ho32 hoSize
        hout32 houtSize]
      native_decide)
    (by native_decide)
    (skimSecondSafeTransferMem4_read64 self toWord prevValue value ho32 hoSize
      hout32 houtSize)

theorem skimSecondSafeTransferMem5_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem5 self o toWord prevValue out2 value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨356⟩ : UInt256) := by
  rw [skimSecondSafeTransferMem5_eq_writeCascade]
  simpa [skimSecondSafeTransferMem5Writes] using
    writeCascade_read_word_of_head_of_base
      (skimSecondBalanceStaticcallMem self o toWord prevValue out2)
      (base := 388) (off := 64) (⟨356⟩ : UInt256)
      (skimSecondSafeTransferMem5WritesAfter64 toWord value)
      (skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
        ho32 hoSize hout32 houtSize)
      (lt_usize 0 (by norm_num))
      (skimSecondSafeTransferMem5WritesAfter64_disjoint64 toWord value)

theorem skimSecondSafeTransferMem5_read356
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem5 self o toWord prevValue out2 value).readWithPadding 356 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold skimSecondSafeTransferMem5
  exact toByteArray_write32_read_back _ _ 356
    (by
      rw [skimSecondSafeTransferMem4_size self toWord prevValue value ho32 hoSize hout32 houtSize]
      omega)

theorem skimSecondSafeTransferMem6_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem6 self o toWord prevValue out2 value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨456⟩ : UInt256) := by
  unfold skimSecondSafeTransferMem6
  exact toByteArray_write32_read_back _ _ 64
    (by
      rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize]
      omega)

theorem skimSecondSafeTransferMem7_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨456⟩ : UInt256) := by
  unfold skimSecondSafeTransferMem7
  rw [write32_read_below _ _ 388 64 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        omega)
      (by omega)]
  exact skimSecondSafeTransferMem6_read64 self toWord prevValue value ho32 hoSize
    hout32 houtSize

theorem skimSecondSafeTransferMem7_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferMem7 self o toWord prevValue out2 value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨456⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize
        hout32 houtSize]
      native_decide)
    (by native_decide)
    (skimSecondSafeTransferMem7_read64 self toWord prevValue value ho32 hoSize
      hout32 houtSize)

theorem skimSecondSafeTransferMem7_read356
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).readWithPadding 356 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold skimSecondSafeTransferMem7 skimSecondSafeTransferMem6
  change ByteArray.readWithPadding
      (writeCascade (skimSecondSafeTransferMem5 self o toWord prevValue out2 value)
        [(64, (⟨456⟩ : UInt256)),
          (388, skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value)])
      356 32 = UInt256.toByteArray (⟨68⟩ : UInt256)
  rw [writeCascade_read_preserved_len]
  · exact skimSecondSafeTransferMem5_read356 self toWord prevValue value ho32 hoSize
      hout32 houtSize
  · rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize]
    simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num

theorem skimSecondSafeTransferMem7_mload356
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨356⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).size
        ∨ (⟨356⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferMem7 self o toWord prevValue out2 value).readWithPadding
          (⟨356⟩ : UInt256).toNat 32)))
      = ⟨68⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize
        hout32 houtSize]
      native_decide)
    (by native_decide)
    (skimSecondSafeTransferMem7_read356 self toWord prevValue value ho32 hoSize
      hout32 houtSize)

theorem skimSecondSafeTransferMem6_mload388
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨388⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferMem6 self o toWord prevValue out2 value).size
        ∨ (⟨388⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferMem6 self o toWord prevValue out2 value).readWithPadding
          (⟨388⟩ : UInt256).toNat 32)))
      = skimSecondSafeTransferWord388 self o toWord prevValue out2 value := by
  unfold skimSecondSafeTransferWord388
  exact mloadValue_eq_readWithPadding_of_lt_size _ (UInt256.ofNat 15) ⟨388⟩ 456
    (skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize)
    (by native_decide) (by native_decide)

theorem skimSecondSafeTransferMem7_read388
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).readWithPadding 388 32 =
      UInt256.toByteArray
        (skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value) := by
  unfold skimSecondSafeTransferMem7
  exact toByteArray_write32_read_back _ _ 388
    (by
      rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]
      omega)

theorem skimSecondSafeTransferMem7_mload388
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨388⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).size
        ∨ (⟨388⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferMem7 self o toWord prevValue out2 value).readWithPadding
          (⟨388⟩ : UInt256).toNat 32)))
      = skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize
        hout32 houtSize]
      native_decide)
    (by native_decide)
    (skimSecondSafeTransferMem7_read388 self toWord prevValue value ho32 hoSize
      hout32 houtSize)

noncomputable def skimSecondSafeTransferCallMem0
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value)).write 0
    (skimSecondSafeTransferMem7 self o toWord prevValue out2 value) 456 32

noncomputable def skimSecondSafeTransferCopyWord1
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value)
        |>.readWithPadding 420 32))

noncomputable def skimSecondSafeTransferCallMem1
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value)).write 0
    (skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value) 488 32

noncomputable def skimSecondSafeTransferTailSourceWord
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value)
        |>.readWithPadding 452 32))

noncomputable def skimSecondSafeTransferTailWord
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (skimSecondSafeTransferTailSourceWord self o toWord prevValue out2 value)
      (UInt256.lnot skimSafeTransferTailMask))
    (UInt256.land ⟨0⟩ skimSafeTransferTailMask)

noncomputable def skimSecondSafeTransferCallMem2
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferTailWord self o toWord prevValue out2 value)).write 0
    (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value) 520 32

noncomputable def skimSecondSafeTransferCallMem2Writes
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) : List (Nat × UInt256) :=
  [(456, skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value),
   (488, skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value),
   (520, skimSecondSafeTransferTailWord self o toWord prevValue out2 value)]

theorem skimSecondSafeTransferCallMem2_eq_writeCascade
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) :
    skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value =
      writeCascade (skimSecondSafeTransferMem7 self o toWord prevValue out2 value)
        (skimSecondSafeTransferCallMem2Writes self o toWord prevValue out2 value) := by
  rfl

theorem skimSecondSafeTransferCallMem2Writes_size
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) :
    writeCascadeSize 456
      (skimSecondSafeTransferCallMem2Writes self o toWord prevValue out2 value) = 552 := by
  rfl

theorem skimSecondSafeTransferCallMem2Writes_gaps
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) :
    WriteGapsOk 456
      (skimSecondSafeTransferCallMem2Writes self o toWord prevValue out2 value) := by
  simp [WriteGapsOk, skimSecondSafeTransferCallMem2Writes]

theorem skimSecondSafeTransferCallMem2Writes_disjoint64
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) :
    WindowDisjointFromWrites 456 64 32
      (skimSecondSafeTransferCallMem2Writes self o toWord prevValue out2 value) := by
  simp [WindowDisjointFromWrites, skimSecondSafeTransferCallMem2Writes]

theorem skimSecondSafeTransferCallMem0_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value).size = 488 := by
  unfold skimSecondSafeTransferCallMem0
  rw [toByteArray_write_eq _ _ 456
      (by
        rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize
          hout32 houtSize])
      (by
        rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize hout32 houtSize,
    ByteArray_zeroes_size,
    show (USize.ofNat (456 - 456)).toNat = 0 from
      USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem skimSecondSafeTransferCallMem1_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).size = 520 := by
  unfold skimSecondSafeTransferCallMem1
  rw [toByteArray_write_eq _ _ 488
      (by
        rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize
          hout32 houtSize])
      (by
        rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        change 0 < USize.size
        exact lt_usize 0 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize
      hout32 houtSize,
    ByteArray_zeroes_size,
    show (USize.ofNat (488 - 488)).toNat = 0 from
      USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem skimSecondSafeTransferCallMem2_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).size = 552 := by
  have hbase :
      (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).size = 456 :=
    skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize hout32 houtSize
  have hgaps :
      WriteGapsOk (skimSecondSafeTransferMem7 self o toWord prevValue out2 value).size
        (skimSecondSafeTransferCallMem2Writes self o toWord prevValue out2 value) := by
    rw [hbase]
    exact skimSecondSafeTransferCallMem2Writes_gaps self o toWord prevValue out2 value
  have hcascade :=
    writeCascade_size (skimSecondSafeTransferMem7 self o toWord prevValue out2 value)
      (skimSecondSafeTransferCallMem2Writes self o toWord prevValue out2 value) hgaps
  rw [skimSecondSafeTransferCallMem2_eq_writeCascade, hcascade, hbase]
  exact skimSecondSafeTransferCallMem2Writes_size self o toWord prevValue out2 value

theorem skimSecondSafeTransferCallMem0_mload420
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨420⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value).size
        ∨ (⟨420⟩ : UInt256) ≥ UInt256.ofNat 16 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value).readWithPadding
          (⟨420⟩ : UInt256).toNat 32)))
      = skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value := by
  have hguard :
      ¬((⟨420⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value).size
        ∨ (⟨420⟩ : UInt256) ≥ UInt256.ofNat 16 * ⟨32⟩) := by
    exact not_or.mpr ⟨by
      rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize
        hout32 houtSize]
      native_decide, by native_decide⟩
  rw [if_neg hguard]
  rfl

theorem skimSecondSafeTransferCallMem1_mload452
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨452⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).size
        ∨ (⟨452⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).readWithPadding
          (⟨452⟩ : UInt256).toNat 32)))
      = skimSecondSafeTransferTailSourceWord self o toWord prevValue out2 value := by
  have hguard :
      ¬((⟨452⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).size
        ∨ (⟨452⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩) := by
    exact not_or.mpr ⟨by
      rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize
        hout32 houtSize]
      native_decide, by native_decide⟩
  rw [if_neg hguard]
  rfl

theorem skimSecondSafeTransferCallMem1_mload520
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨520⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).size
        ∨ (⟨520⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).readWithPadding
          (⟨520⟩ : UInt256).toNat 32)))
      = ⟨0⟩ := by
  have hguard :
      (⟨520⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).size
        ∨ (⟨520⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ := by
    left
    rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize
      hout32 houtSize]
    native_decide
  rw [if_pos hguard]

theorem skimSecondSafeTransferCallMem2_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨456⟩ : UInt256) := by
  rw [skimSecondSafeTransferCallMem2_eq_writeCascade]
  rw [writeCascade_read_preserved]
  · exact skimSecondSafeTransferMem7_read64 self toWord prevValue value ho32 hoSize
      hout32 houtSize
  · rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize
      hout32 houtSize]
    exact skimSecondSafeTransferCallMem2Writes_disjoint64 self o toWord prevValue out2 value

theorem skimSecondSafeTransferCallMem2_read96_zero
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSecondSafeTransferCallMem2
  rw [write32_read_below _ _ 520 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize
          hout32 houtSize])
      (by omega)]
  unfold skimSecondSafeTransferCallMem1
  rw [write32_read_below _ _ 488 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize
          hout32 houtSize])
      (by omega)]
  unfold skimSecondSafeTransferCallMem0
  rw [write32_read_below _ _ 456 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize
          hout32 houtSize])
      (by omega)]
  unfold skimSecondSafeTransferMem7
  rw [write32_read_below _ _ 388 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        omega)
      (by omega)]
  unfold skimSecondSafeTransferMem6
  rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        omega)
      (by omega)
      (by
        rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        omega)]
  unfold skimSecondSafeTransferMem5
  rw [write32_read_below _ _ 356 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem4_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        omega)
      (by omega)]
  unfold skimSecondSafeTransferMem4
  rw [write32_read_below _ _ 424 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem3_size self toWord prevValue ho32 hoSize
          hout32 houtSize])
      (by omega)]
  unfold skimSecondSafeTransferMem3
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask toWord)
      (skimSecondSafeTransferMem2 self o toWord prevValue out2) 392 96
      (by
        rw [skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize
          hout32 houtSize]
        omega)
      (by omega)
      (by
        rw [skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize
          hout32 houtSize]
        exact lt_usize _ (by norm_num))]
  unfold skimSecondSafeTransferMem2
  rw [write32_read_below _ _ 324 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem1_size self toWord prevValue ho32 hoSize
          hout32 houtSize]
        omega)
      (by omega)]
  unfold skimSecondSafeTransferMem1
  rw [write32_read_below _ _ 292 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferMem0_size self toWord prevValue ho32 hoSize
          hout32 houtSize]
        omega)
      (by omega)]
  unfold skimSecondSafeTransferMem0
  rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])
      (by
        rw [skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
          ho32 hoSize hout32 houtSize]
        omega)
      (by omega)
      (by
        rw [skimSecondBalanceStaticcallMem_size_of_size_ge self toWord prevValue out2
          ho32 hoSize hout32 houtSize]
        omega)]
  unfold skimSecondBalanceStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out2 hout32 houtSize]
  rw [write_read_below_gen out2 (skimSecondBalanceCalldataMem self o toWord prevValue)
      292 32 96 (by decide) hout32
      (by rw [skimSecondBalanceCalldataMem_size self toWord prevValue ho32 hoSize]; omega)
      (by omega)]
  unfold skimSecondBalanceCalldataMem
  rw [write32_read_below _ _ 296 96 (by rw [toByteArray_size])
      (by rw [skimSecondBalanceSelectorMem_size self toWord prevValue ho32 hoSize]; omega)
      (by omega)]
  unfold skimSecondBalanceSelectorMem
  rw [write32_read_below _ _ 292 96 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord prevValue ho32 hoSize]; omega)
      (by omega)]
  exact skimSafeTransferCallMem2_read96_zero self toWord prevValue ho32 hoSize

theorem skimSecondSafeTransferCallMem2_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨456⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondSafeTransferCallMem2_size self toWord prevValue value ho32 hoSize
        hout32 houtSize]
      native_decide)
    (by native_decide)
    (skimSecondSafeTransferCallMem2_read64 self toWord prevValue value ho32 hoSize
      hout32 houtSize)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimExcessSuccessToSafeTransferEntry {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {balance reserve toWord token safeRet : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (reserve :: balance :: ⟨5325⟩ :: toWord :: token :: safeRet :: R)
      mem aw rdata acc k C)
    (hle : reserve.toNat ≤ balance.toNat)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6370⟩
      (UInt256.sub balance reserve :: toWord :: token :: safeRet :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5325⟩ :=
    RD.uniswapSafeMathSubSuccess h hle (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have rd6370ret := evm_run rd5325 with [jumpdest, push2 ⟨6370⟩]
  have rd6370 := rd6370ret.jump (by decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd6370⟩

theorem skimSecondSafeTransferMem6_read392_28
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem6 self o toWord prevValue out2 value).readWithPadding 392 28 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28 := by
  unfold skimSecondSafeTransferMem6 skimSecondSafeTransferMem5 skimSecondSafeTransferMem4
    skimSecondSafeTransferMem3
  change ByteArray.readWithPadding (writeCascade
      (skimSecondSafeTransferMem2 self o toWord prevValue out2)
      [(392, UInt256.land solcAddrMask toWord), (424, value), (356, (⟨68⟩ : UInt256)),
        (64, (⟨456⟩ : UInt256))]) 392 28 =
    (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28
  simpa using
    writeCascade_read_window_of_head
      (skimSecondSafeTransferMem2 self o toWord prevValue out2) 392 0 28
      (UInt256.land solcAddrMask toWord)
      [(424, value), (356, (⟨68⟩ : UInt256)), (64, (⟨456⟩ : UInt256))]
      (by
        rw [skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize hout32 houtSize]
        exact lt_usize 4 (by norm_num))
      (by
        rw [skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize hout32 houtSize]
        simp [WindowDisjointFromWrites])
      (by norm_num) (by norm_num) (by norm_num)

theorem skimSecondSafeTransferWord388_extract4_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (UInt256.toByteArray (skimSecondSafeTransferWord388 self o toWord prevValue out2 value)).extract 4 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 0 28 := by
  unfold skimSecondSafeTransferWord388
  have hreadSize :
      ((skimSecondSafeTransferMem6 self o toWord prevValue out2 value).readWithPadding 388 32).size = 32 := by
    rw [readWithPadding_eq_extract' _ 388 32 (by norm_num) (by norm_num)
      (by rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
    rw [ByteArray.size_extract]
    rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]
    omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize]
  rw [readWithPadding_eq_extract' _ 388 32 (by norm_num) (by norm_num)
    (by rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
  rw [extract_extract_BA]
  rw [show 388 + 4 = 392 by omega, show min (388 + 32) (388 + 32) = 420 by omega]
  rw [← readWithPadding_eq_extract' _ 392 28 (by norm_num) (by norm_num)
    (by rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
  exact skimSecondSafeTransferMem6_read392_28 self toWord prevValue value ho32 hoSize hout32 houtSize

theorem skimSecondSafeTransferMem3_read420_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem3 self o toWord prevValue out2).readWithPadding 420 4 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 := by
  unfold skimSecondSafeTransferMem3
  exact toByteArray_write_read_window_of_gap (UInt256.land solcAddrMask toWord) _ 392 28 4
    (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [skimSecondSafeTransferMem2_size self toWord prevValue ho32 hoSize hout32 houtSize]
      exact lt_usize _ (by norm_num))

theorem skimSecondSafeTransferMem4_read420_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem4 self o toWord prevValue out2 value).readWithPadding 420 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold skimSecondSafeTransferMem4
  exact safeTransferCalldata_read_boundary_word _ _ _ 424 (by norm_num)
    (skimSecondSafeTransferMem3_size self toWord prevValue ho32 hoSize hout32 houtSize)
    (skimSecondSafeTransferMem3_read420_4 self toWord prevValue ho32 hoSize hout32 houtSize)

theorem skimSecondSafeTransferCallMem0_read420_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value).readWithPadding 420 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold skimSecondSafeTransferCallMem0
  rw [write32_read_below _ _ 456 420 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize hout32 houtSize]) (by omega)]
  unfold skimSecondSafeTransferMem7
  rw [write32_read_above _ _ 388 420 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)
      (by omega)
      (by rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
  unfold skimSecondSafeTransferMem6
  rw [write32_read_above _ _ 64 420 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)
      (by omega)
      (by rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
  unfold skimSecondSafeTransferMem5
  rw [write32_read_above _ _ 356 420 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem4_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)
      (by omega)
      (by rw [skimSecondSafeTransferMem4_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
  exact skimSecondSafeTransferMem4_read420_32 self toWord prevValue value ho32 hoSize hout32 houtSize

theorem skimSecondSafeTransferCopyWord1_toByteArray
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    UInt256.toByteArray (skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value) =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold skimSecondSafeTransferCopyWord1
  rw [skimSecondSafeTransferCallMem0_read420_32 self toWord prevValue value ho32 hoSize hout32 houtSize]
  apply toByteArray_ofNat_fromByteArrayBigEndian_of_size
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    toByteArray_size]
  norm_num

theorem skimSecondSafeTransferMem4_read452_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferMem4 self o toWord prevValue out2 value).readWithPadding 452 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold skimSecondSafeTransferMem4
  exact toByteArray_write_read_window_of_gap value _ 424 28 4
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [skimSecondSafeTransferMem3_size self toWord prevValue ho32 hoSize hout32 houtSize]; exact lt_usize _ (by norm_num))

theorem skimSecondSafeTransferCallMem1_read452_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).readWithPadding 452 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold skimSecondSafeTransferCallMem1
  rw [write32_read_below_len _ _ 488 452 4 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize hout32 houtSize])
      (by omega)
      (by rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)
      (by norm_num) (by norm_num)]
  unfold skimSecondSafeTransferCallMem0
  rw [write32_read_below_len _ _ 456 452 4 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize hout32 houtSize])
      (by omega)
      (by rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize hout32 houtSize])
      (by norm_num) (by norm_num)]
  unfold skimSecondSafeTransferMem7
  rw [write32_read_above_len _ _ 388 452 4 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)
      (by omega)
      (by rw [skimSecondSafeTransferMem6_size self toWord prevValue value ho32 hoSize hout32 houtSize])
      (by norm_num) (by norm_num)]
  unfold skimSecondSafeTransferMem6
  rw [write32_read_above_len _ _ 64 452 4 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)
      (by omega)
      (by rw [skimSecondSafeTransferMem5_size self toWord prevValue value ho32 hoSize hout32 houtSize])
      (by norm_num) (by norm_num)]
  unfold skimSecondSafeTransferMem5
  rw [write32_read_above_len _ _ 356 452 4 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferMem4_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)
      (by omega)
      (by rw [skimSecondSafeTransferMem4_size self toWord prevValue value ho32 hoSize hout32 houtSize])
      (by norm_num) (by norm_num)]
  exact skimSecondSafeTransferMem4_read452_4 self toWord prevValue value ho32 hoSize hout32 houtSize

theorem skimSecondSafeTransferTailSourceWord_extract0_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (UInt256.toByteArray (skimSecondSafeTransferTailSourceWord self o toWord prevValue out2 value)).extract 0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold skimSecondSafeTransferTailSourceWord
  have hreadSize :
      ((skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value).readWithPadding 452 32).size = 32 := by
    rw [readWithPadding_eq_extract' _ 452 32 (by norm_num) (by norm_num)
      (by rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
    rw [ByteArray.size_extract]
    rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize hout32 houtSize]
    omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize]
  rw [readWithPadding_eq_extract' _ 452 32 (by norm_num) (by norm_num)
    (by rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
  rw [extract_extract_BA]
  rw [show 452 + 0 = 452 by omega, show min (452 + 4) (452 + 32) = 456 by omega]
  rw [← readWithPadding_eq_extract' _ 452 4 (by norm_num) (by norm_num)
    (by rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize hout32 houtSize]; omega)]
  exact skimSecondSafeTransferCallMem1_read452_4 self toWord prevValue value ho32 hoSize hout32 houtSize

theorem skimSecondSafeTransferTailWord_extract0_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (UInt256.toByteArray (skimSecondSafeTransferTailWord self o toWord prevValue out2 value)).extract 0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  rw [skimSecondSafeTransferTailWord]
  rw [skimSafeTransferTailWord_extract0_4_of_source]
  exact skimSecondSafeTransferTailSourceWord_extract0_4 self toWord prevValue value ho32 hoSize hout32 houtSize

theorem skimSecondSafeTransferCallMem2_read456_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding 456 32 =
      UInt256.toByteArray (skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value) := by
  unfold skimSecondSafeTransferCallMem2
  rw [write32_read_below _ _ 520 456 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize hout32 houtSize]) (by omega)]
  unfold skimSecondSafeTransferCallMem1
  rw [write32_read_below _ _ 488 456 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize hout32 houtSize]) (by omega)]
  unfold skimSecondSafeTransferCallMem0
  exact toByteArray_write_read_back_of_gap
    (skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value) _ 456
    (by rw [skimSecondSafeTransferMem7_size self toWord prevValue value ho32 hoSize hout32 houtSize]; norm_num)

theorem skimSecondSafeTransferCallMem2_read488_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding 488 32 =
      UInt256.toByteArray (skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value) := by
  unfold skimSecondSafeTransferCallMem2
  rw [write32_read_below _ _ 520 488 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize hout32 houtSize]) (by omega)]
  unfold skimSecondSafeTransferCallMem1
  exact toByteArray_write_read_back_of_gap
    (skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value) _ 488
    (by rw [skimSecondSafeTransferCallMem0_size self toWord prevValue value ho32 hoSize hout32 houtSize]; norm_num)

theorem skimSecondSafeTransferCallMem2_read520_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding 520 4 =
      (UInt256.toByteArray (skimSecondSafeTransferTailWord self o toWord prevValue out2 value)).extract 0 4 := by
  unfold skimSecondSafeTransferCallMem2
  rw [write32_read_prefix_len _ _ 520 4 (by rw [toByteArray_size])
      (by rw [skimSecondSafeTransferCallMem1_size self toWord prevValue value ho32 hoSize hout32 houtSize])
      (by norm_num) (by norm_num) (by norm_num)]

theorem skimSecondSafeTransferCallMem2_read456_68
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256)
    (_ho32 : 32 ≤ o.size) (_hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding 456 68 =
      (transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68 := by
  rw [transferCalldataMem_read128_68]
  rw [byteArray_readWithPadding_split _ 456 32 36 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [skimSecondSafeTransferCallMem2_size self toWord prevValue value _ho32 _hoSize hout32 houtSize]; norm_num)]
  rw [byteArray_readWithPadding_split _ 488 32 4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [skimSecondSafeTransferCallMem2_size self toWord prevValue value _ho32 _hoSize hout32 houtSize]; norm_num)]
  rw [skimSecondSafeTransferCallMem2_read456_32 self toWord prevValue value _ho32 _hoSize hout32 houtSize,
    skimSecondSafeTransferCallMem2_read488_32 self toWord prevValue value _ho32 _hoSize hout32 houtSize]
  change UInt256.toByteArray (skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value) ++
      (UInt256.toByteArray (skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value) ++
        (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value).readWithPadding 520 4) =
    transferSelector ++ (UInt256.land solcAddrMask toWord).toByteArray ++ value.toByteArray
  rw [skimSecondSafeTransferCallMem2_read520_4 self toWord prevValue value _ho32 _hoSize hout32 houtSize]
  rw [skimSecondSafeTransferPatchedSelectorWord, skimSafeTransferPatchedSelector_toByteArray]
  rw [skimSecondSafeTransferWord388_extract4_32 self toWord prevValue value _ho32 _hoSize hout32 houtSize,
    skimSecondSafeTransferCopyWord1_toByteArray self toWord prevValue value _ho32 _hoSize hout32 houtSize,
    skimSecondSafeTransferTailWord_extract0_4 self toWord prevValue value _ho32 _hoSize hout32 houtSize]
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
theorem RD.uniswapSkimSecondSafeTransferEntryToCallMade {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6370⟩
      (value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondBalanceStaticcallMem self o toWord prevValue out2) (UInt256.ofNat 13) out2
      (cA, σ) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size)
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
            ((skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value)
              |>.readWithPadding 456 68)
            (ee.depth + 1) ee.header ee.perm)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨524⟩ ::
            UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
            value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
            sel :: [])
          (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value)
          (UInt256.ofNat 18) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  have rd6375 := evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (skimSecondBalanceStaticcallMem_mload64_of_size_ge self toWord prevValue out2
        ho32 hoSize hout32 houtSize)
      (by native_decide) (by evm_ov)]
  have rd6380 := evm_run rd6375 with [
    dup1, dup3, add, dup3,
    raw mstore 0 (skimSecondSafeTransferMem0 self o toWord prevValue out2)
      (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSecondSafeTransferMem0; rfl) (by native_decide) (by evm_ov)]
  have rd6384 := evm_run rd6380 with [
    push1 ⟨25⟩, dup2,
    raw mstore 0 (skimSecondSafeTransferMem1 self o toWord prevValue out2)
      (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSecondSafeTransferMem1; rfl) (by native_decide) (by evm_ov)]
  have rd6417 := rd6384.pushConst skimSafeTransferSignatureWord (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd6423 := evm_run rd6417 with [
    push1 ⟨32⟩, swap2, dup3, add,
    raw mstore 0 (skimSecondSafeTransferMem2 self o toWord prevValue out2)
      (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (by unfold skimSecondSafeTransferMem2; rfl) (by native_decide) (by evm_ov)]
  have rd6425 := evm_run rd6423 with [
    dup2,
    raw mload 0 ⟨356⟩ (UInt256.ofNat 13)
      (by native_decide) mem_cost
      (skimSecondSafeTransferMem2_mload64 self toWord prevValue ho32 hoSize
        hout32 houtSize)
      (by native_decide) (by evm_ov)]
  have rd6441 := evm_run rd6425 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, dup2, and,
    push1 ⟨36⟩, dup4, add,
    raw mstore 3 (skimSecondSafeTransferMem3 self o toWord prevValue out2)
      (UInt256.ofNat 14)
      (by native_decide) mem_cost
      (by
        rw [show (⟨356⟩ : UInt256) + ⟨36⟩ = ⟨392⟩ by native_decide]
        unfold skimSecondSafeTransferMem3
        rfl)
      (by native_decide) (by evm_ov)]
  have rd6449 := evm_run rd6441 with [
    push1 ⟨68⟩, dup1, dup4, add, dup7, swap1,
    raw mstore 3 (skimSecondSafeTransferMem4 self o toWord prevValue out2 value)
      (UInt256.ofNat 15)
      (by native_decide) mem_cost
      (by
        rw [show (⟨356⟩ : UInt256) + ⟨68⟩ = ⟨424⟩ by native_decide]
        unfold skimSecondSafeTransferMem4
        rfl)
      (by native_decide) (by evm_ov)]
  have rd6451 := evm_run rd6449 with [
    dup5,
    raw mload 0 ⟨356⟩ (UInt256.ofNat 15)
      (by native_decide) mem_cost
      (skimSecondSafeTransferMem4_mload64 self toWord prevValue value ho32 hoSize
        hout32 houtSize)
      (by native_decide) (by evm_ov)]
  have rd6459 := evm_run rd6451 with [
    dup1, dup5, sub, swap1, swap2, add, dup2,
    raw mstore 0 (skimSecondSafeTransferMem5 self o toWord prevValue out2 value)
      (UInt256.ofNat 15)
      (by native_decide) mem_cost
      (by unfold skimSecondSafeTransferMem5; rfl) (by native_decide) (by evm_ov)]
  have rd6466 := evm_run rd6459 with [
    push1 ⟨100⟩, swap1, swap3, add, dup5,
    raw mstore 0 (skimSecondSafeTransferMem6 self o toWord prevValue out2 value)
      (UInt256.ofNat 15)
      (by native_decide) mem_cost
      (by unfold skimSecondSafeTransferMem6; rfl) (by native_decide) (by evm_ov)]
  have rd6471 := evm_run rd6466 with [
    swap2, dup2, add, dup1,
    raw mload 0 (skimSecondSafeTransferWord388 self o toWord prevValue out2 value)
      (UInt256.ofNat 15)
      (by native_decide) mem_cost
      (skimSecondSafeTransferMem6_mload388 self toWord prevValue value ho32 hoSize
        hout32 houtSize)
      (by native_decide) (by evm_ov)]
  have rd6480 := evm_run rd6471 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and]
  have rd6485 := rd6480.pushConst transferSelectorWord (width := 4) (op := .PUSH4)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd6491 := evm_run rd6485 with [
    push1 ⟨224⟩, shl, lor, dup2,
    raw mstore 0 (skimSecondSafeTransferMem7 self o toWord prevValue out2 value)
      (UInt256.ofNat 15)
      (by native_decide) mem_cost
      (by
        unfold skimSecondSafeTransferMem7 skimSecondSafeTransferPatchedSelectorWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd6512 := evm_run rd6491 with [
    swap3,
    raw mload 0 ⟨456⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (skimSecondSafeTransferMem7_mload64 self toWord prevValue value
        ho32 hoSize hout32 houtSize)
      (by native_decide) (by evm_ov),
    dup2,
    raw mload 0 ⟨68⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost (skimSecondSafeTransferMem7_mload356 self toWord prevValue value
        ho32 hoSize hout32 houtSize)
      (by native_decide) (by evm_ov),
    push1 ⟨0⟩, swap5, push1 ⟨96⟩, swap5, dup10, and,
    swap4, swap3, swap2, dup3, swap2, swap1, dup1, dup4, dup4]
  have rd6521a := evm_run rd6512 with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539a := evm_run rd6521a with [
    dup1,
    raw mload 0
      (skimSecondSafeTransferPatchedSelectorWord self o toWord prevValue out2 value)
      (UInt256.ofNat 15) (by native_decide)
      mem_cost
      (skimSecondSafeTransferMem7_mload388 self toWord prevValue value ho32 hoSize
        hout32 houtSize)
      (by native_decide) (by evm_ov),
    dup3,
    raw mstore 3 (skimSecondSafeTransferCallMem0 self o toWord prevValue out2 value)
      (UInt256.ofNat 16)
      (by native_decide) mem_cost
      (by unfold skimSecondSafeTransferCallMem0; rfl) (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512a := rd6539a.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + (⟨356⟩ + ⟨32⟩) = ⟨420⟩ by native_decide,
    show (⟨32⟩ : UInt256) + ⟨456⟩ = ⟨488⟩ by native_decide,
    show (⟨68⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨36⟩ by native_decide]
    at rd6512a
  have rd6521b := evm_run rd6512a with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539b := evm_run rd6521b with [
    dup1,
    raw mload 0 (skimSecondSafeTransferCopyWord1 self o toWord prevValue out2 value)
      (UInt256.ofNat 16) (by native_decide)
      mem_cost (skimSecondSafeTransferCallMem0_mload420 self toWord prevValue value
        ho32 hoSize hout32 houtSize)
      (by native_decide) (by evm_ov),
    dup3,
    raw mstore 3 (skimSecondSafeTransferCallMem1 self o toWord prevValue out2 value)
      (UInt256.ofNat 17)
      (by native_decide) mem_cost
      (by unfold skimSecondSafeTransferCallMem1; rfl) (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512b := rd6539b.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨420⟩ = ⟨452⟩ by native_decide,
    show (⟨32⟩ : UInt256) + ⟨488⟩ = ⟨520⟩ by native_decide,
    show (⟨36⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨4⟩ by native_decide]
    at rd6512b
  have rd6543 := evm_run rd6512b with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd6575 := evm_run rd6543 with [
    jumpdest, push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub,
    dup1, not, dup3,
    raw mload 0 (skimSecondSafeTransferTailSourceWord self o toWord prevValue out2 value)
      (UInt256.ofNat 17) (by native_decide)
      mem_cost (skimSecondSafeTransferCallMem1_mload452 self toWord prevValue value
        ho32 hoSize hout32 houtSize)
      (by native_decide) (by evm_ov),
    and, dup2, dup5,
    raw mload 3 ⟨0⟩ (UInt256.ofNat 18) (by native_decide)
      mem_cost (skimSecondSafeTransferCallMem1_mload520 self toWord prevValue value
        ho32 hoSize hout32 houtSize)
      (by native_decide) (by evm_ov),
    and, dup1, dup3, lor, dup6,
    raw mstore 0 (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value)
      (UInt256.ofNat 18)
      (by native_decide) mem_cost
      (by
        unfold skimSecondSafeTransferCallMem2 skimSecondSafeTransferTailWord
          skimSafeTransferTailMask
        rfl)
      (by native_decide) (by evm_ov),
    pop, pop, pop, pop, pop, pop]
  have rd6593 := evm_run rd6575 with [
    swap1, pop, add, swap2, pop, pop, push1 ⟨0⟩, push1 ⟨64⟩,
    raw mload 0 ⟨456⟩ (UInt256.ofNat 18) (by native_decide)
      mem_cost (skimSecondSafeTransferCallMem2_mload64 self toWord prevValue value
        ho32 hoSize hout32 houtSize)
      (by native_decide) (by evm_ov),
    dup1, dup4, sub, dup2, push1 ⟨0⟩, dup7]
  obtain ⟨gasArg, rd6594⟩ := rd6593.gas (by native_decide) (by evm_ov)
  rw [show (⟨68⟩ : UInt256) + ⟨456⟩ = ⟨524⟩ by native_decide,
    show UInt256.sub (⟨524⟩ : UInt256) ⟨456⟩ = ⟨68⟩ by native_decide]
    at rd6594
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘ, rd6595, houtSize'⟩ :=
    rd6594.call (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, A_in, callGas, gasArg, k', C', ?_, ?_, houtSize'⟩
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
            (MachineState.M (UInt256.ofNat 18).toNat (⟨456⟩ : UInt256).toNat
              (⟨68⟩ : UInt256).toNat)
            (⟨456⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
          UInt256.ofNat 18 := by
      native_decide
    rw [hlen, byteArray_write_len_zero, haw] at rd6595
    exact rd6595

def skimSecondSafeTransferReturnDataPtr (out : ByteArray) : UInt256 :=
  (⟨456⟩ : UInt256) + skimSafeTransferReturnDataRounded out

noncomputable def skimSecondSafeTransferReturnDataPtrMem
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (skimSecondSafeTransferReturnDataPtr out)).write 0
    (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) 64 32

noncomputable def skimSecondSafeTransferReturnDataSizeMem
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat out.size)).write 0
    (skimSecondSafeTransferReturnDataPtrMem self o toWord prevValue out2 value out) 456 32

noncomputable def skimSecondSafeTransferReturnDataMem
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out2 : ByteArray)
    (value : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
    488 out.size

def skimSecondSafeTransferReturnDataActiveWords (out : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (UInt256.ofNat 18).toNat 488 out.size)

theorem skimSecondSafeTransferReturnDataPtrMem_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferReturnDataPtrMem self o toWord prevValue out2 value out).size =
      552 := by
  unfold skimSecondSafeTransferReturnDataPtrMem
  rw [write32_eq _ _ 64 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferCallMem2_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSecondSafeTransferCallMem2_size self toWord prevValue value ho32 hoSize
      hout32 houtSize,
    toByteArray_size]
  omega

theorem skimSecondSafeTransferReturnDataSizeMem_size
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size =
      552 := by
  unfold skimSecondSafeTransferReturnDataSizeMem
  rw [write32_eq _ _ 456 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferReturnDataPtrMem_size self toWord prevValue value out
          ho32 hoSize hout32 houtSize]
        omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSecondSafeTransferReturnDataPtrMem_size self toWord prevValue value out
      ho32 hoSize hout32 houtSize,
    toByteArray_size]
  omega

theorem skimSecondSafeTransferReturnDataPtrMem_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferReturnDataPtrMem self o toWord prevValue out2 value out).readWithPadding
      64 32 =
      UInt256.toByteArray (skimSecondSafeTransferReturnDataPtr out) := by
  unfold skimSecondSafeTransferReturnDataPtrMem
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferCallMem2_size self toWord prevValue value ho32 hoSize
          hout32 houtSize]
        omega)]
  rw [show (UInt256.toByteArray (skimSecondSafeTransferReturnDataPtr out)).extract 0 32 =
      UInt256.toByteArray (skimSecondSafeTransferReturnDataPtr out) by
    rw [show 32 = (UInt256.toByteArray (skimSecondSafeTransferReturnDataPtr out)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSecondSafeTransferReturnDataSizeMem_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).readWithPadding
      64 32 =
      UInt256.toByteArray (skimSecondSafeTransferReturnDataPtr out) := by
  unfold skimSecondSafeTransferReturnDataSizeMem
  rw [write32_read_below _ _ 456 64 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferReturnDataPtrMem_size self toWord prevValue value out
          ho32 hoSize hout32 houtSize]
        omega)
      (by omega)]
  exact skimSecondSafeTransferReturnDataPtrMem_read64 self toWord prevValue value out
    ho32 hoSize hout32 houtSize

theorem skimSecondSafeTransferReturnDataSizeMem_read456
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size)
    (houtRetSize : out.size < UInt256.size) :
    (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).readWithPadding
      456 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) := by
  unfold skimSecondSafeTransferReturnDataSizeMem
  rw [write32_read_back _ _ 456 (by rw [toByteArray_size])
      (by
        rw [skimSecondSafeTransferReturnDataPtrMem_size self toWord prevValue value out
          ho32 hoSize hout32 houtSize]
        omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat out.size)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat out.size)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSecondSafeTransferReturnDataMem_read456
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtRetSize : out.size < UInt256.size) :
    (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).readWithPadding
      456 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) := by
  unfold skimSecondSafeTransferReturnDataMem
  by_cases hin :
      488 + out.size ≤
        (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size
  · rw [write_read_below_gen out
      (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
      488 out.size 456 houtNe le_rfl hin (by omega)]
    exact skimSecondSafeTransferReturnDataSizeMem_read456 self toWord prevValue value out
      ho32 hoSize hout32 houtSize houtRetSize
  · have hbase :
        (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size =
          552 :=
      skimSecondSafeTransferReturnDataSizeMem_size self toWord prevValue value out
        ho32 hoSize hout32 houtSize
    have hext :
        (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size <
          488 + out.size := by omega
    rw [write_eq_gen_extend out
      (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
      488 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
    rw [readWithPadding_eq_extract _ 456 (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ 456 488 (by rw [ByteArray.size_extract]; omega)]
    rw [extract_prefix _ 488 456 488 (by omega)]
    rw [← readWithPadding_eq_extract
      (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
      456 (by rw [hbase]; omega)]
    exact skimSecondSafeTransferReturnDataSizeMem_read456 self toWord prevValue value out
      ho32 hoSize hout32 houtSize houtRetSize

theorem skimSecondSafeTransferReturnDataMem_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size)
    (houtNe : out.size ≠ 0) :
    (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).readWithPadding
      64 32 =
      UInt256.toByteArray (skimSecondSafeTransferReturnDataPtr out) := by
  unfold skimSecondSafeTransferReturnDataMem
  by_cases hin :
      488 + out.size ≤
        (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size
  · rw [write_read_below_gen out
      (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
      488 out.size 64 houtNe le_rfl hin (by omega)]
    exact skimSecondSafeTransferReturnDataSizeMem_read64 self toWord prevValue value out
      ho32 hoSize hout32 houtSize
  · have hbase :
        (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size =
          552 :=
      skimSecondSafeTransferReturnDataSizeMem_size self toWord prevValue value out
        ho32 hoSize hout32 houtSize
    have hext :
        (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size <
          488 + out.size := by omega
    rw [write_eq_gen_extend out
      (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
      488 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
    rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ 64 96 (by rw [ByteArray.size_extract]; omega)]
    rw [extract_prefix _ 488 64 96 (by omega)]
    rw [← readWithPadding_eq_extract
      (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
      64 (by rw [hbase]; omega)]
    exact skimSecondSafeTransferReturnDataSizeMem_read64 self toWord prevValue value out
      ho32 hoSize hout32 houtSize


end UniswapV2Pair
