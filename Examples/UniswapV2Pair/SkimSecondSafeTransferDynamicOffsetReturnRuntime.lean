import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicOffsetRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dynamic-offset second `_safeTransfer` return-data tails -/

theorem write_read_below_gen_extend (src base : ByteArray) (destAddr len readAddr : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hbelow : readAddr + 32 ≤ destAddr) :
    (src.write 0 base destAddr len).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  by_cases hin : destAddr + len ≤ base.size
  · exact write_read_below_gen src base destAddr len readAddr hlen hsrc hin hbelow
  · have hext : base.size < destAddr + len := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend src base destAddr len hlen hsrc hdest hext]
    have hbasePrefix : (base.extract 0 destAddr).size = destAddr := by
      rw [ByteArray.size_extract]
      omega
    have hsrcPrefix : (src.extract 0 len).size = len := by
      rw [ByteArray.size_extract]
      omega
    rw [readWithPadding_eq_extract _ readAddr (by
      rw [ByteArray.size_append, hbasePrefix, hsrcPrefix]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [hbasePrefix]; omega)]
    rw [extract_prefix _ destAddr readAddr (readAddr + 32) hbelow]
    rw [← readWithPadding_eq_extract base readAddr (by omega)]

theorem skimSafeTransferReturnDataMem_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) :
    (skimSafeTransferReturnDataMem self o toWord value out).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold skimSafeTransferReturnDataMem
  rw [write_read_below_gen_extend out
      (skimSafeTransferReturnDataSizeMem self o toWord value out) 324 out.size 96
      houtNe le_rfl
      (by
        rw [skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize]
        omega)
      (by omega)]
  unfold skimSafeTransferReturnDataSizeMem
  rw [write32_read_below _ _ 292 96 (by rw [toByteArray_size])
      (by
        rw [skimSafeTransferReturnDataPtrMem_size self toWord value out ho32 hoSize]
        omega)
      (by omega)]
  unfold skimSafeTransferReturnDataPtrMem
  rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])
      (by
        rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]
        omega)
      (by omega)
      (by
        rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]
        omega)]
  exact skimSafeTransferCallMem2_read96_zero self toWord value ho32 hoSize

theorem skimSecondBalanceDynamicStaticcallMem_read96_zero
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
        96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  have hptr128 : 96 + 32 ≤ (skimSafeTransferReturnDataPtr out1).toNat := by
    unfold skimSafeTransferReturnDataPtr
    rw [uadd_toNat]
    have hroundLe := skimSafeTransferReturnDataRounded_le out1 hout1Size
    have hlt :
        (⟨292⟩ : UInt256).toNat + (skimSafeTransferReturnDataRounded out1).toNat <
          UInt256.size := by
      have hpow : 2 ^ 255 + 355 < UInt256.size := by norm_num [UInt256.size]
      rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
      omega
    rw [Nat.mod_eq_of_lt hlt]
    rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
    have hround64 := skimSafeTransferReturnDataRounded_nonempty_ge64 out1 hout1Ne hout1Size
    omega
  have hselector :
      (skimSecondBalanceDynamicSelectorMem self o toWord value out1).readWithPadding 96 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    unfold skimSecondBalanceDynamicSelectorMem
    rw [toByteArray_write_read_below_of_gap _ _ (skimSafeTransferReturnDataPtr out1).toNat 96
        (by
          have hsz := skimSafeTransferReturnDataMem_size_of_nonempty self toWord value
            ho32 hoSize hout1Ne
          rw [hsz]
          split <;> omega)
        (by
          exact hptr128)
        (skimSafeTransferReturnDataPtr_gap self toWord value ho32 hoSize hout1Ne
          hout1Size)]
    exact skimSafeTransferReturnDataMem_read96_zero self toWord value ho32 hoSize hout1Ne
  have hcalldata :
      (skimSecondBalanceDynamicCalldataMem self o toWord value out1).readWithPadding 96 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    unfold skimSecondBalanceDynamicCalldataMem
    rw [write32_read_below _ _
        ((skimSafeTransferReturnDataPtr out1 + ⟨4⟩).toNat) 96 (by rw [toByteArray_size])
        (by
          have hsz := skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
            ho32 hoSize hout1Ne hout1Size
          have hptr4 :
              (skimSafeTransferReturnDataPtr out1 + (⟨4⟩ : UInt256)).toNat =
                (skimSafeTransferReturnDataPtr out1).toNat + 4 := by
            simpa using skimSafeTransferReturnDataPtr_add4_toNat out1 hout1Size
          rw [hptr4]
          omega)
        (by
          have hptr4 :
              (skimSafeTransferReturnDataPtr out1 + (⟨4⟩ : UInt256)).toNat =
                (skimSafeTransferReturnDataPtr out1).toNat + 4 := by
            simpa using skimSafeTransferReturnDataPtr_add4_toNat out1 hout1Size
          rw [hptr4]
          omega)]
    exact hselector
  unfold skimSecondBalanceDynamicStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out2 hout2_32 hout2Size]
  rw [write_read_below_gen out2
      (skimSecondBalanceDynamicCalldataMem self o toWord value out1)
      (skimSafeTransferReturnDataPtr out1).toNat 32 96 (by decide) hout2_32
      (by
        have hsz := skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
          ho32 hoSize hout1Ne hout1Size
        omega)
      (by
        exact hptr128)]
  exact hcalldata

def skimSecondSafeTransferDynamicReturnDataPtr (out1 out : ByteArray) : UInt256 :=
  skimSecondSafeTransferDynamicCallPtr out1 + skimSafeTransferReturnDataRounded out

noncomputable def skimSecondSafeTransferDynamicReturnDataPtrMem
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out1 out2 : ByteArray)
    (value : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (skimSecondSafeTransferDynamicReturnDataPtr out1 out)).write 0
    (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value) 64 32

noncomputable def skimSecondSafeTransferDynamicReturnDataSizeMem
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out1 out2 : ByteArray)
    (value : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat out.size)).write 0
    (skimSecondSafeTransferDynamicReturnDataPtrMem self o toWord prevValue out1 out2 value out)
    (skimSecondSafeTransferDynamicCallPtr out1).toNat 32

noncomputable def skimSecondSafeTransferDynamicReturnDataMem
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256) (out1 out2 : ByteArray)
    (value : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0
    (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out)
    (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size

def skimSecondSafeTransferDynamicReturnDataActiveWords (out1 out : ByteArray) : UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (UInt256.ofNat
        (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out1).toNat
          (skimSecondSafeTransferDynamicCallPtr out1).toNat 32)).toNat
      (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size)

theorem skimSecondSafeTransferDynamicRetPtr_window_lt_small
    (out1 out : ByteArray)
    (hout1Small : out1.size < 2 ^ 138) (houtSmall : out.size < 2 ^ 138) :
    (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size + 31 < UInt256.size := by
  have hout1Size : out1.size < 2 ^ 255 := by
    have hpow : 2 ^ 138 < 2 ^ 255 := by norm_num
    omega
  rw [skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
  have hbase := skimSecondSafeTransferDynamicBasePtr_toNat_le out1 hout1Size
  have hcap : 2 ^ 138 + 2 ^ 138 + 582 < UInt256.size := by
    norm_num [UInt256.size]
  omega

theorem skimSecondSafeTransferDynamicReturnDataActiveWords_mul32_lt
    (out1 out : ByteArray)
    (hout1Small : out1.size < 2 ^ 138) (houtSmall : out.size < 2 ^ 138) :
    (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out).toNat * 32 <
      UInt256.size := by
  have hout1Size : out1.size < 2 ^ 255 := by
    have hpow : 2 ^ 138 < 2 ^ 255 := by norm_num
    omega
  let awSize : UInt256 :=
    UInt256.ofNat
      (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out1).toNat
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 32)
  have hawSize : awSize.toNat * 32 < UInt256.size := by
    dsimp [awSize]
    exact UInt256_ofNat_M_mul32_lt _ _
      (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
      (by
        simpa [skimSecondSafeTransferDynamicCallPtr] using
          skimSecondSafeTransferDynamicBasePtr_window_lt out1 164 32
            hout1Size (by norm_num) (by norm_num))
  have hret :=
    skimSecondSafeTransferDynamicRetPtr_window_lt_small out1 out hout1Small houtSmall
  unfold skimSecondSafeTransferDynamicReturnDataActiveWords
  change
      (UInt256.ofNat
        (MachineState.M awSize.toNat (skimSecondSafeTransferDynamicRetPtr out1).toNat
          out.size)).toNat * 32 < UInt256.size
  have hMmul :=
    MachineState_M_mul32_lt_of_bounds hawSize hret
  have hMlt :
      MachineState.M awSize.toNat (skimSecondSafeTransferDynamicRetPtr out1).toNat
        out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hMmul

theorem skimSecondSafeTransferDynamicReturnDataActiveWords_cover_callPtr
    (out1 out : ByteArray)
    (hout1Small : out1.size < 2 ^ 138) (houtSmall : out.size < 2 ^ 138) :
    (skimSecondSafeTransferDynamicCallPtr out1).toNat + 32 ≤
      (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out).toNat * 32 := by
  have hout1Size : out1.size < 2 ^ 255 := by
    have hpow : 2 ^ 138 < 2 ^ 255 := by norm_num
    omega
  let awSize : UInt256 :=
    UInt256.ofNat
      (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out1).toNat
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 32)
  have hawSize : awSize.toNat * 32 < UInt256.size := by
    dsimp [awSize]
    exact UInt256_ofNat_M_mul32_lt _ _
      (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
      (by
        simpa [skimSecondSafeTransferDynamicCallPtr] using
          skimSecondSafeTransferDynamicBasePtr_window_lt out1 164 32
            hout1Size (by norm_num) (by norm_num))
  have hcoverSize :
      (skimSecondSafeTransferDynamicCallPtr out1).toNat + 32 ≤ awSize.toNat * 32 := by
    dsimp [awSize]
    exact UInt256_ofNat_M_covers _ _
      (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
      (by
        simpa [skimSecondSafeTransferDynamicCallPtr] using
          skimSecondSafeTransferDynamicBasePtr_window_lt out1 164 32
            hout1Size (by norm_num) (by norm_num))
  have hret :=
    skimSecondSafeTransferDynamicRetPtr_window_lt_small out1 out hout1Small houtSmall
  unfold skimSecondSafeTransferDynamicReturnDataActiveWords
  change
      (skimSecondSafeTransferDynamicCallPtr out1).toNat + 32 ≤
        (UInt256.ofNat
          (MachineState.M awSize.toNat (skimSecondSafeTransferDynamicRetPtr out1).toNat
            out.size)).toNat * 32
  have hMmul :=
    MachineState_M_mul32_lt_of_bounds hawSize hret
  have hMlt :
      MachineState.M awSize.toNat (skimSecondSafeTransferDynamicRetPtr out1).toNat
        out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact le_trans hcoverSize
    (Nat.mul_le_mul_right 32
      (MachineState_M_ge_left awSize.toNat
        (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size))

theorem skimSecondSafeTransferDynamicReturnDataActiveWords_cover_retPtr
    (out1 out : ByteArray)
    (hout1Small : out1.size < 2 ^ 138) (houtSmall : out.size < 2 ^ 138)
    (hout32 : 32 ≤ out.size) :
    (skimSecondSafeTransferDynamicRetPtr out1).toNat + 32 ≤
      (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out).toNat * 32 := by
  have hout1Size : out1.size < 2 ^ 255 := by
    have hpow : 2 ^ 138 < 2 ^ 255 := by norm_num
    omega
  let awSize : UInt256 :=
    UInt256.ofNat
      (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out1).toNat
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 32)
  have hawSize : awSize.toNat * 32 < UInt256.size := by
    dsimp [awSize]
    exact UInt256_ofNat_M_mul32_lt _ _
      (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
      (by
        simpa [skimSecondSafeTransferDynamicCallPtr] using
          skimSecondSafeTransferDynamicBasePtr_window_lt out1 164 32
            hout1Size (by norm_num) (by norm_num))
  have hret :=
    skimSecondSafeTransferDynamicRetPtr_window_lt_small out1 out hout1Small houtSmall
  unfold skimSecondSafeTransferDynamicReturnDataActiveWords
  change
      (skimSecondSafeTransferDynamicRetPtr out1).toNat + 32 ≤
        (UInt256.ofNat
          (MachineState.M awSize.toNat (skimSecondSafeTransferDynamicRetPtr out1).toNat
            out.size)).toNat * 32
  have hMmul :=
    MachineState_M_mul32_lt_of_bounds hawSize hret
  have hMlt :
      MachineState.M awSize.toNat (skimSecondSafeTransferDynamicRetPtr out1).toNat
        out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  have hcover :
      (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size ≤
        MachineState.M awSize.toNat (skimSecondSafeTransferDynamicRetPtr out1).toNat
            out.size * 32 := by
    unfold MachineState.M
    split
    · omega
    · have hceil :
          (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size ≤
            (((skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size + 31) / 32) * 32 := by
        have hmod := Nat.mod_lt
          ((skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size + 31)
          (by norm_num : 0 < 32)
        have hdm := Nat.div_add_mod
          ((skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size + 31) 32
        omega
      exact le_trans hceil
        (Nat.mul_le_mul_right 32 (Nat.le_max_right _ _))
  omega

theorem skimSecondSafeTransferDynamicReturnDataActiveWords_mloadCallPtr_same
    (out1 out : ByteArray)
    (hout1Small : out1.size < 2 ^ 138) (houtSmall : out.size < 2 ^ 138) :
    UInt256.ofNat
        (MachineState.M (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out).toNat
          (skimSecondSafeTransferDynamicCallPtr out1).toNat 32) =
      skimSecondSafeTransferDynamicReturnDataActiveWords out1 out :=
  UInt256_M_same_of_cover _ _
    (skimSecondSafeTransferDynamicReturnDataActiveWords_mul32_lt
      out1 out hout1Small houtSmall)
    (skimSecondSafeTransferDynamicReturnDataActiveWords_cover_callPtr
      out1 out hout1Small houtSmall)

theorem skimSecondSafeTransferDynamicReturnDataActiveWords_mloadRetPtr_same
    (out1 out : ByteArray)
    (hout1Small : out1.size < 2 ^ 138) (houtSmall : out.size < 2 ^ 138)
    (hout32 : 32 ≤ out.size) :
    UInt256.ofNat
        (MachineState.M (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out).toNat
          (skimSecondSafeTransferDynamicRetPtr out1).toNat 32) =
      skimSecondSafeTransferDynamicReturnDataActiveWords out1 out :=
  UInt256_M_same_of_cover _ _
    (skimSecondSafeTransferDynamicReturnDataActiveWords_mul32_lt
      out1 out hout1Small houtSmall)
    (skimSecondSafeTransferDynamicReturnDataActiveWords_cover_retPtr
      out1 out hout1Small houtSmall hout32)

theorem skimSecondSafeTransferDynamicCallMem2_size_ge_retEnd
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicRetEnd out1).toNat ≤
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).size := by
  unfold skimSecondSafeTransferDynamicCallMem2
  have h228 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size (by norm_num)
  rw [h228]
  have hge :=
    toByteArray_write_size_ge_off_add32
      (skimSecondSafeTransferDynamicTailWord self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
      ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 228)
      (by
        have hmem1 :=
          skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228 self toWord
            prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        exact lt_usize _ (by omega))
  rw [skimSecondSafeTransferDynamicRetEnd_toNat out1 hout1Size]
  omega

theorem skimSecondSafeTransferDynamicBasePtr_toNat_ge128 (out : ByteArray)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    128 ≤ (skimSecondSafeTransferDynamicBasePtr out).toNat := by
  unfold skimSecondSafeTransferDynamicBasePtr skimSafeTransferReturnDataPtr
  rw [uadd_toNat]
  have hround64 := skimSafeTransferReturnDataRounded_nonempty_ge64 out houtNe houtSize
  have hroundLe := skimSafeTransferReturnDataRounded_le out houtSize
  have hlt :
      (⟨292⟩ : UInt256).toNat + (skimSafeTransferReturnDataRounded out).toNat <
        UInt256.size := by
    have hpow : 2 ^ 255 + 355 < UInt256.size := by norm_num [UInt256.size]
    rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
    omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide]
  omega

theorem skimSecondSafeTransferDynamicMem1_size_ge_base_add32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
      (skimSecondSafeTransferDynamicMem1 self o toWord prevValue out1 out2).size := by
  unfold skimSecondSafeTransferDynamicMem1
  exact toByteArray_write_size_ge_off_add32 (⟨25⟩ : UInt256)
    (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2)
    (skimSecondSafeTransferDynamicBasePtr out1).toNat
    (by
      have hbase :=
        skimSecondSafeTransferDynamicMem0_size_ge_base_add32 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      exact lt_usize _ (by omega))

theorem skimSecondSafeTransferDynamicCallMem2_read96_zero
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
        |>.readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  have hbase128 := skimSecondSafeTransferDynamicBasePtr_toNat_ge128 out1 hout1Ne hout1Size
  unfold skimSecondSafeTransferDynamicCallMem2
  rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat
      96 (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicCallMem1
    rw [write32_read_below _ _ (skimSecondSafeTransferDynamicRetPtr out1).toNat
        96 (by rw [toByteArray_size])]
    · unfold skimSecondSafeTransferDynamicCallMem0
      rw [write32_read_below _ _ (skimSecondSafeTransferDynamicCallPtr out1).toNat
          96 (by rw [toByteArray_size])]
      · unfold skimSecondSafeTransferDynamicMem7
        rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat
            96 (by rw [toByteArray_size])]
        · unfold skimSecondSafeTransferDynamicMem6
          rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])]
          · unfold skimSecondSafeTransferDynamicMem5
            rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat
                96 (by rw [toByteArray_size])]
            · unfold skimSecondSafeTransferDynamicMem4
              rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat
                  96 (by rw [toByteArray_size])]
              · unfold skimSecondSafeTransferDynamicMem3
                rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat
                    96 (by rw [toByteArray_size])]
                · unfold skimSecondSafeTransferDynamicMem2
                  rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨32⟩).toNat
                      96 (by rw [toByteArray_size])]
                  · unfold skimSecondSafeTransferDynamicMem1
                    rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1).toNat
                        96 (by rw [toByteArray_size])]
                    · unfold skimSecondSafeTransferDynamicMem0
                      rw [write32_read_above _ _ 64 96 (by rw [toByteArray_size])]
                      · exact skimSecondBalanceDynamicStaticcallMem_read96_zero
                          self toWord prevValue ho32 hoSize hout1Ne hout1Size
                          hout2_32 hout2Size
                      · have hsize :=
                          skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
                            self toWord prevValue ho32 hoSize hout1Ne hout1Size
                            hout2_32 hout2Size
                        have hsize' :
                            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
                              (skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2).size := by
                          simpa [skimSecondSafeTransferDynamicBasePtr] using hsize
                        omega
                      · omega
                      · have hsize :=
                          skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
                            self toWord prevValue ho32 hoSize hout1Ne hout1Size
                            hout2_32 hout2Size
                        have hsize' :
                            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
                              (skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2).size := by
                          simpa [skimSecondSafeTransferDynamicBasePtr] using hsize
                        omega
                    · exact skimSecondSafeTransferDynamicMem0_size_ge_base_add32
                        self toWord prevValue ho32 hoSize hout1Ne hout1Size
                        hout2_32 hout2Size
                    · omega
                  · exact skimSecondSafeTransferDynamicMem1_size_ge_base_add32
                      self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
                  · have h32 :
                        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨32⟩ : UInt256)).toNat =
                          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 := by
                      simpa using
                        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 32 hout1Size
                          (by norm_num)
                    rw [h32]
                    omega
                · exact skimSecondSafeTransferDynamicMem2_size_ge_base_add64
                    self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
                · have h100 :
                      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨100⟩ : UInt256)).toNat =
                        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 100 := by
                    simpa using
                      skimSecondSafeTransferDynamicBasePtr_add_toNat out1 100 hout1Size
                        (by norm_num)
                  rw [h100]
                  omega
              · exact skimSecondSafeTransferDynamicMem3_size_ge_base_add132
                  self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
              · have h132 :
                    (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
                      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
                  simpa using
                    skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size
                      (by norm_num)
                rw [h132]
                omega
            · exact skimSecondSafeTransferDynamicMem4_size_ge_base_add164
                self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
            · have h64 :
                  (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
                    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
                simpa using
                  skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size
                    (by norm_num)
              rw [h64]
              omega
          · exact skimSecondSafeTransferDynamicMem5_size_ge_base_add164
              self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
          · omega
          · exact by
              have hsize :=
                skimSecondSafeTransferDynamicMem5_size_ge_base_add164 self toWord prevValue value
                  ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
              have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
              omega
        · exact skimSecondSafeTransferDynamicMem6_size_ge_base_add164
            self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        · have h96 :
              (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
                (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
            simpa using
              skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size
                (by norm_num)
          rw [h96]
          omega
      · exact skimSecondSafeTransferDynamicMem7_size_ge_base_add164
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      · rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size]
        omega
    · exact skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    · rw [skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
      omega
  · have h228 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size (by norm_num)
    rw [h228]
    exact skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228
      self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · have h228 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size (by norm_num)
    rw [h228]
    omega

theorem skimSecondSafeTransferDynamicCallMem2_mload96_zero
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (⟨96⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).size
        ∨ (⟨96⟩ : UInt256) ≥ skimSecondSafeTransferDynamicWordsCall2 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
          |>.readWithPadding (⟨96⟩ : UInt256).toNat 32))) =
      ⟨0⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨96⟩ : UInt256)) (aw := skimSecondSafeTransferDynamicWordsCall2 out1)
    (v := (⟨0⟩ : UInt256))
    (by
      have hsize :=
        skimSecondSafeTransferDynamicCallMem2_size_ge_retEnd self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      have hret := skimSecondSafeTransferDynamicRetEnd_toNat out1 hout1Size
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      change 96 < (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).size
      omega)
    (UInt256_mload_haw_of_cover _ _
      (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
      (by
        have hge := skimSecondSafeTransferDynamicWordsCall2_toNat_ge13 out1 hout1Size
        rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide]
        omega))
    (by
      simpa [show (⟨96⟩ : UInt256).toNat = 96 from rfl] using
        skimSecondSafeTransferDynamicCallMem2_read96_zero self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

theorem skimSecondSafeTransferDynamicReturnDataPtrMem_size_ge_retEnd
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 out : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicRetEnd out1).toNat ≤
      (skimSecondSafeTransferDynamicReturnDataPtrMem self o toWord prevValue out1 out2 value out).size := by
  unfold skimSecondSafeTransferDynamicReturnDataPtrMem
  rw [write32_eq _ _ 64 (by rw [toByteArray_size])]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    have hbase :=
      skimSecondSafeTransferDynamicCallMem2_size_ge_retEnd self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega
  · have hbase :=
      skimSecondSafeTransferDynamicCallMem2_size_ge_retEnd self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega

theorem skimSecondSafeTransferDynamicReturnDataSizeMem_size_ge_retPtr
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 out : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicRetPtr out1).toNat ≤
      (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out).size := by
  unfold skimSecondSafeTransferDynamicReturnDataSizeMem
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size
  have hret := skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size
  have hge :=
    toByteArray_write_size_ge_off_add32 (UInt256.ofNat out.size)
      (skimSecondSafeTransferDynamicReturnDataPtrMem self o toWord prevValue out1 out2 value out)
      (skimSecondSafeTransferDynamicCallPtr out1).toNat
      (by
        have hptrMem :=
          skimSecondSafeTransferDynamicReturnDataPtrMem_size_ge_retEnd self toWord
            prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
            (out := out)
        rw [hcall, skimSecondSafeTransferDynamicRetEnd_toNat out1 hout1Size] at hptrMem
        exact lt_usize _ (by omega))
  omega

theorem skimSecondSafeTransferDynamicReturnDataMem_read_callPtr
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 out : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (houtNe : out.size ≠ 0) :
    (skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out)
        |>.readWithPadding (skimSecondSafeTransferDynamicCallPtr out1).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat out.size) := by
  unfold skimSecondSafeTransferDynamicReturnDataMem
  rw [write_read_below_gen_extend out
      (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out)
      (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size
      (skimSecondSafeTransferDynamicCallPtr out1).toNat
      houtNe le_rfl
      (skimSecondSafeTransferDynamicReturnDataSizeMem_size_ge_retPtr self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (by
        rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size,
          skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
        omega)]
  unfold skimSecondSafeTransferDynamicReturnDataSizeMem
  rw [write32_read_back _ _ (skimSecondSafeTransferDynamicCallPtr out1).toNat
      (by rw [toByteArray_size])]
  · rw [show (UInt256.toByteArray (UInt256.ofNat out.size)).extract 0 32 =
        UInt256.toByteArray (UInt256.ofNat out.size) by
      rw [show 32 = (UInt256.toByteArray (UInt256.ofNat out.size)).size by
        rw [toByteArray_size]]
      exact byteArray_extract_self _]
  · have hptrMem :=
      skimSecondSafeTransferDynamicReturnDataPtrMem_size_ge_retEnd self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        (out := out)
    rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size,
      skimSecondSafeTransferDynamicRetEnd_toNat out1 hout1Size] at hptrMem
    omega

theorem skimSecondSafeTransferDynamicReturnDataMem_mloadCallPtr
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 out : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout1Small : out1.size < 2 ^ 138)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSmall : out.size < 2 ^ 138) :
    (if (skimSecondSafeTransferDynamicCallPtr out1).toNat ≥
          (skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out).size
        ∨ skimSecondSafeTransferDynamicCallPtr out1 ≥
          skimSecondSafeTransferDynamicReturnDataActiveWords out1 out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out)
          |>.readWithPadding (skimSecondSafeTransferDynamicCallPtr out1).toNat 32))) =
      UInt256.ofNat out.size := by
  exact mloadWordValue_of_readWithPadding
    (off := skimSecondSafeTransferDynamicCallPtr out1)
    (aw := skimSecondSafeTransferDynamicReturnDataActiveWords out1 out)
    (v := UInt256.ofNat out.size)
    (by
      unfold skimSecondSafeTransferDynamicReturnDataMem
      by_cases hin :
          (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size ≤
            (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out).size
      · rw [write_eq_gen out
          (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out)
          (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size houtNe le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size,
          skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
        omega
      · have hbase :=
          skimSecondSafeTransferDynamicReturnDataSizeMem_size_ge_retPtr self toWord
            prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
            (out := out)
        have hext :
            (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out).size <
              (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size := by
          omega
        rw [write_eq_gen_extend out
          (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out)
          (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size houtNe le_rfl
          hbase hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size,
          skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
        omega)
    (UInt256_mload_haw_of_cover _ _
      (skimSecondSafeTransferDynamicReturnDataActiveWords_mul32_lt
        out1 out hout1Small houtSmall)
      (skimSecondSafeTransferDynamicReturnDataActiveWords_cover_callPtr
        out1 out hout1Small houtSmall))
    (by
      simpa using
        skimSecondSafeTransferDynamicReturnDataMem_read_callPtr self toWord prevValue
          value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size houtNe)

theorem skimSecondSafeTransferDynamicReturnDataMem_mloadRetPtr
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 out : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout1Small : out1.size < 2 ^ 138)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSmall : out.size < 2 ^ 138) :
    (if (skimSecondSafeTransferDynamicRetPtr out1).toNat ≥
          (skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out).size
        ∨ skimSecondSafeTransferDynamicRetPtr out1 ≥
          skimSecondSafeTransferDynamicReturnDataActiveWords out1 out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out)
          |>.readWithPadding (skimSecondSafeTransferDynamicRetPtr out1).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  rw [if_neg]
  · unfold skimSecondSafeTransferDynamicReturnDataMem
    let base :=
      skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out
    change UInt256.ofNat
        (fromByteArrayBigEndian
          ((out.write 0 base (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size)
            |>.readWithPadding (skimSecondSafeTransferDynamicRetPtr out1).toNat 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    have hbase :
        (skimSecondSafeTransferDynamicRetPtr out1).toNat ≤ base.size := by
      exact skimSecondSafeTransferDynamicReturnDataSizeMem_size_ge_retPtr self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    by_cases hin : (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size ≤ base.size
    · rw [write_eq_gen out base (skimSecondSafeTransferDynamicRetPtr out1).toNat
        out.size (by omega) le_rfl hin]
      rw [ByteArray.append_assoc]
      rw [readWithPadding_eq_extract _ (skimSecondSafeTransferDynamicRetPtr out1).toNat (by
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ (skimSecondSafeTransferDynamicRetPtr out1).toNat
        ((skimSecondSafeTransferDynamicRetPtr out1).toNat + 32) (by
          rw [ByteArray.size_extract]
          omega)]
      rw [show (base.extract 0 (skimSecondSafeTransferDynamicRetPtr out1).toNat).size =
          (skimSecondSafeTransferDynamicRetPtr out1).toNat by
        rw [ByteArray.size_extract]
        omega]
      rw [Nat.sub_self,
        show (skimSecondSafeTransferDynamicRetPtr out1).toNat + 32 -
            (skimSecondSafeTransferDynamicRetPtr out1).toNat = 32 by omega]
      rw [extract_append_left _ _ 0 32 (by
        rw [ByteArray.size_extract]
        omega)]
      rw [extract_prefix _ out.size 0 32 (by omega)]
    · have hext : base.size < (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size := by
        omega
      rw [write_eq_gen_extend out base (skimSecondSafeTransferDynamicRetPtr out1).toNat
        out.size (by omega) le_rfl hbase hext]
      rw [readWithPadding_eq_extract _ (skimSecondSafeTransferDynamicRetPtr out1).toNat (by
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ (skimSecondSafeTransferDynamicRetPtr out1).toNat
        ((skimSecondSafeTransferDynamicRetPtr out1).toNat + 32) (by
          rw [ByteArray.size_extract]
          omega)]
      rw [show (base.extract 0 (skimSecondSafeTransferDynamicRetPtr out1).toNat).size =
          (skimSecondSafeTransferDynamicRetPtr out1).toNat by
        rw [ByteArray.size_extract]
        omega]
      rw [Nat.sub_self,
        show (skimSecondSafeTransferDynamicRetPtr out1).toNat + 32 -
            (skimSecondSafeTransferDynamicRetPtr out1).toNat = 32 by omega]
      rw [extract_prefix _ out.size 0 32 (by omega)]
  · rw [not_or]
    constructor
    · unfold skimSecondSafeTransferDynamicReturnDataMem
      by_cases hin :
          (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size ≤
            (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out).size
      · rw [write_eq_gen out
          (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out)
          (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size (by omega) le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbase :=
          skimSecondSafeTransferDynamicReturnDataSizeMem_size_ge_retPtr self toWord
            prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
            (out := out)
        have hext :
            (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out).size <
              (skimSecondSafeTransferDynamicRetPtr out1).toNat + out.size := by
          omega
        rw [write_eq_gen_extend out
          (skimSecondSafeTransferDynamicReturnDataSizeMem self o toWord prevValue out1 out2 value out)
          (skimSecondSafeTransferDynamicRetPtr out1).toNat out.size (by omega) le_rfl
          hbase hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega
    · exact UInt256_mload_haw_of_cover _ _
        (skimSecondSafeTransferDynamicReturnDataActiveWords_mul32_lt
          out1 out hout1Small houtSmall)
        (skimSecondSafeTransferDynamicReturnDataActiveWords_cover_retPtr
          out1 out hout1Small houtSmall hout32)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyReturnToCheck_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel status : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (skimSecondSafeTransferDynamicCallPtr out1 :: status :: value :: toWord :: token :: ret ::
        token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out)
      (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out) out acc k' C' := by
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
  let aw0 := skimSecondSafeTransferDynamicWordsCall2 out1
  let awLoad64 : UInt256 :=
    UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad64 : awLoad64 = aw0 := by
    simpa [awLoad64, aw0] using
      UInt256_mload64_same_of_toNat_ge13 (skimSecondSafeTransferDynamicWordsCall2 out1)
        (skimSecondSafeTransferDynamicWordsCall2_toNat_ge13 out1 hout1Size)
  have rd6611₀ := RD.mload
    (Cₘ awLoad64 - Cₘ aw0) (skimSecondSafeTransferDynamicCallPtr out1) awLoad64
    rd6610 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad64, aw0])
    (by
      simpa [aw0] using
        skimSecondSafeTransferDynamicCallMem2_mload64 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
    (by simpa [awLoad64, aw0] using hawLoad64)
    (by evm_ov)
  have rd6611 := by
    simpa [awLoad64, aw0, hawLoad64] using rd6611₀
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1 + rounded)).write 0
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value) 64 32
  have rd6626pre := evm_run rd6611 with [
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and,
    dup3, add, push1 ⟨64⟩]
  have rd6626₀ := RD.mstore
    (Cₘ awLoad64 - Cₘ aw0) mem2 awLoad64 rd6626pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad64, aw0])
    (by unfold mem2 rounded rdsz; rfl)
    (by simpa [awLoad64, aw0] using hawLoad64)
    (by evm_ov)
  have rd6626 := by
    simpa [awLoad64, aw0, hawLoad64] using rd6626₀
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2
    (skimSecondSafeTransferDynamicCallPtr out1).toNat 32
  let awSize : UInt256 :=
    UInt256.ofNat
      (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out1).toNat
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 32)
  have rd6629 := evm_run rd6626 with [
    returndatasize, dup3,
    raw mstore
      (Cₘ awSize - Cₘ (skimSecondSafeTransferDynamicWordsCall2 out1))
      mem3 awSize
      (by native_decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, awSize])
      (by rfl) (by rfl) (by evm_ov)]
  have rd6636 := evm_run rd6629 with [returndatasize, push1 ⟨0⟩, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := skimSecondSafeTransferDynamicCallPtr out1 + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat out.size
  have hcopyDest_eq : copyDest = skimSecondSafeTransferDynamicRetPtr out1 := by
    simp only [copyDest]
    rw [u256_add_comm]
    exact skimSecondSafeTransferDynamicCallPtr_add32 out1
  have hcopyLen_toNat : copyLen.toNat = out.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)
  let mem4 : ByteArray := out.write 0 mem3 copyDest.toNat copyLen.toNat
  have hmem4 :
      mem4 =
        skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out := by
    simp [mem4, mem3, mem2, copyDest, copyLen, rdsz, rounded,
      skimSecondSafeTransferDynamicReturnDataMem,
      skimSecondSafeTransferDynamicReturnDataSizeMem,
      skimSecondSafeTransferDynamicReturnDataPtrMem,
      skimSecondSafeTransferDynamicReturnDataPtr,
      skimSafeTransferReturnDataRounded, hcopyDest_eq, hcopyLen_toNat]
  have haw4 :
      UInt256.ofNat
          (MachineState.M awSize.toNat copyDest.toNat copyLen.toNat) =
        skimSecondSafeTransferDynamicReturnDataActiveWords out1 out := by
    simp [skimSecondSafeTransferDynamicReturnDataActiveWords, copyDest, copyLen, awSize,
      hcopyDest_eq, hcopyLen_toNat]
  have rd6637 := RD.returndatacopy
    (Cₘ (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out) -
      Cₘ awSize)
    mem4
    (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out)
    rd6636 (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        skimSecondSafeTransferDynamicReturnDataActiveWords, awSize, hcopyDest_eq,
        hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd6646 := evm_run rd6637 with [push2 ⟨6646⟩, jump (by jump_dest), jumpdest]
  have rd6652 := evm_run rd6646 with [pop, swap2, pop, swap2, pop]
  rw [hmem4] at rd6652
  exact ⟨_, _, by simpa using rd6652⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (houtSmall : out.size < 2 ^ 138)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout1Small : out1.size < 2 ^ 138)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: skimSecondSafeTransferDynamicRetPtr out1 ::
        skimSecondSafeTransferDynamicCallPtr out1 :: ⟨1⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out)
      (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out) out acc k' C' := by
  obtain ⟨k6652, C6652, rd6652⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyReturnToCheck_dynamic_offset
      (self := self) (value := value) (toWord := toWord) (prevValue := prevValue)
      (token := token) (token0 := token0) (ret := ret) (sel := sel)
      (status := (⟨1⟩ : UInt256))
      h houtNe houtSize ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have hsizeNe : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro hzero
    have hnat : (UInt256.ofNat out.size).toNat = 0 := by
      rw [hzero]
      rfl
    rw [UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)] at hnat
    exact houtNe hnat
  have hsizeIsZero : UInt256.isZero (UInt256.ofNat out.size) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hsizeNe
  have hloadCall :=
    skimSecondSafeTransferDynamicReturnDataMem_mloadCallPtr self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout1Small hout2_32 hout2Size houtNe houtSmall
  have hawCall :=
    skimSecondSafeTransferDynamicReturnDataActiveWords_mloadCallPtr_same
      out1 out hout1Small houtSmall
  have rd6661 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiNT (by native_decide), pop, dup1]
  have rd6662 := RD.mload
    0 (UInt256.ofNat out.size) (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out)
    rd6661 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawCall])
    hloadCall hawCall
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6675 := evm_run rd6662 with [
    iszero, dup1, push2 ⟨6692⟩, jumpiNT hsizeIsZero, pop, dup1, dup1,
    push1 ⟨32⟩, add, swap1]
  have rd6676 := RD.mload
    0 (UInt256.ofNat out.size) (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out)
    rd6675 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawCall])
    hloadCall hawCall
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [skimSecondSafeTransferDynamicCallPtr_add32 out1] using rd6676⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyShortReverts_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (houtNe : out.size ≠ 0) (hshort : out.size < 32) (houtSize : out.size < 2 ^ 255)
    (houtSmall : out.size < 2 ^ 138)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout1Small : out1.size < 2 ^ 138)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded_dynamic_offset
      h houtNe houtSize houtSmall ho32 hoSize hout1Ne hout1Size hout1Small
      hout2_32 hout2Size
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hshort
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6684
  have rd6685 := evm_run rd6684 with [jumpiNT (by native_decide)]
  exact RD.uniswapPush1Dup1Revert0 rd6685 (by native_decide)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (houtSmall : out.size < 2 ^ 138)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout1Small : out1.size < 2 ^ 138)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded_dynamic_offset
      h houtNe houtSize houtSmall ho32 hoSize hout1Ne hout1Size hout1Small
      hout2_32 hout2Size
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have hawRet :=
    skimSecondSafeTransferDynamicReturnDataActiveWords_mloadRetPtr_same
      out1 out hout1Small houtSmall hout32
  have rd6692₀ := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out) rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawRet])
    (skimSecondSafeTransferDynamicReturnDataMem_mloadRetPtr self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout1Small hout2_32 hout2Size hout32 houtSmall)
    hawRet
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6692 := rd6692₀
  rw [hword] at rd6692
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  obtain ⟨k6697, C6697, rd6697'⟩ : ∃ k' C',
      RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
        (skimSecondSafeTransferDynamicCallPtr out1 :: ⟨1⟩ :: value :: toWord ::
          token :: ret :: token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
        (skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out)
        (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out) out acc k' C' := by
    exact ⟨_, _, by simpa using rd6697⟩
  exact RD.uniswapSkimSecondSafeTransferFailureMessageFrom6697Reverts_generic rd6697'

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (houtSmall : out.size < 2 ^ 138)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout1Small : out1.size < 2 ^ 138)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferDynamicReturnDataMem self o toWord prevValue out1 out2 value out)
      (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out) out acc k' C' := by
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded_dynamic_offset
      h houtNe houtSize houtSmall ho32 hoSize hout1Ne hout1Size hout1Small
      hout2_32 hout2Size
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have hawRet :=
    skimSecondSafeTransferDynamicReturnDataActiveWords_mloadRetPtr_same
      out1 out hout1Small houtSmall hout32
  have rd6692₀ := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (skimSecondSafeTransferDynamicReturnDataActiveWords out1 out) rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawRet])
    (skimSecondSafeTransferDynamicReturnDataMem_mloadRetPtr self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout1Small hout2_32 hout2Size hout32 houtSmall)
    hawRet
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6692 := rd6692₀
  have rd6773 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiT hword (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferEmptyReturnToRet_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (hout : out.size = 0)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k' C' := by
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6607' := rd6607
  rw [hout] at rd6607'
  have rd6641 := evm_run rd6607' with [jumpiT (by native_decide) (by jump_dest)]
  have rd6652 := evm_run rd6641 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap2, pop, swap2, pop]
  have rd6658 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiNT (by native_decide)]
  have haw96 :
      UInt256.ofNat
          (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out1).toNat
            (⟨96⟩ : UInt256).toNat 32) =
        skimSecondSafeTransferDynamicWordsCall2 out1 := by
    exact UInt256_M_same_of_cover _ _
      (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
      (by
        have hge := skimSecondSafeTransferDynamicWordsCall2_toNat_ge13 out1 hout1Size
        rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide]
        omega)
  have rd6668 := evm_run rd6658 with [
    pop, dup1,
    raw mload 0 ⟨0⟩ (skimSecondSafeTransferDynamicWordsCall2 out1) (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw96])
      (skimSecondSafeTransferDynamicCallMem2_mload96_zero self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      haw96 (by evm_ov),
    iszero, dup1, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6773 := evm_run rd6668 with [jumpdest, push2 ⟨6773⟩,
    jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ⟨5433⟩ :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (hout : out.size = 0)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5433⟩
      (token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k' C' := by
  exact RD.uniswapSkimSecondSafeTransferEmptyReturnToRet_dynamic_offset
    h hout ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size (by jump_dest)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferFailureMessageFrom6697Reverts_generic
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {value toWord token token0 ret sel status retDataPtr : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
      (retDataPtr :: status :: value :: toWord :: token :: ret :: token :: token0 :: toWord ::
        ⟨570⟩ :: sel :: [])
      mem aw out acc k C) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let fp0 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))
  let aw1 : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6701 := evm_run h with [push1 ⟨64⟩, dup1]
  have rd6701' := RD.mload
    (Cₘ aw1 - Cₘ aw) fp0 aw1 rd6701 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6705 := rd6701'.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by native_decide) (by native_decide) (by evm_ov)
  have rd6708 := evm_run rd6705 with [push1 ⟨229⟩, shl, dup2]
  let err0 : ByteArray := (UInt256.toByteArray uniswapErrorStringSelector).write 0 mem fp0.toNat 32
  let aw2 : UInt256 := UInt256.ofNat (MachineState.M aw1.toNat fp0.toNat 32)
  have rd6710 := RD.mstore
    (Cₘ aw2 - Cₘ aw1) err0 aw2 rd6708 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, aw2])
    (by simp [err0, uniswapErrorStringSelector])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6716 := evm_run rd6710 with [push1 ⟨32⟩, push1 ⟨4⟩, dup3, add]
  let off1 : UInt256 := fp0 + ⟨4⟩
  let err1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 err0 off1.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat off1.toNat 32)
  have rd6717 := RD.mstore
    (Cₘ aw3 - Cₘ aw2) err1 aw3 rd6716 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, aw3, off1])
    (by simp [err1, off1])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6723 := evm_run rd6717 with [push1 ⟨26⟩, push1 ⟨36⟩, dup3, add]
  let off2 : UInt256 := fp0 + ⟨36⟩
  let err2 : ByteArray := (UInt256.toByteArray (⟨26⟩ : UInt256)).write 0 err1 off2.toNat 32
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat off2.toNat 32)
  have rd6724 := RD.mstore
    (Cₘ aw4 - Cₘ aw3) err2 aw4 rd6723 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3, aw4, off2])
    (by simp [err2, off2])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6757 := rd6724.pushConst uniswapSafeTransferFailedStringWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd6760 := evm_run rd6757 with [push1 ⟨68⟩, dup3, add]
  let off3 : UInt256 := fp0 + ⟨68⟩
  let err3 : ByteArray := (UInt256.toByteArray uniswapSafeTransferFailedStringWord).write 0
    err2 off3.toNat 32
  let aw5 : UInt256 := UInt256.ofNat (MachineState.M aw4.toNat off3.toNat 32)
  have rd6762 := RD.mstore
    (Cₘ aw5 - Cₘ aw4) err3 aw5 rd6760 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw4, aw5, off3])
    (by simp [err3, off3])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6763 := evm_run rd6762 with [swap1]
  let fp1 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ err3.size ∨ (⟨64⟩ : UInt256) ≥ aw5 * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (err3.readWithPadding 64 32))
  let aw6 : UInt256 := UInt256.ofNat (MachineState.M aw5.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6764 := RD.mload
    (Cₘ aw6 - Cₘ aw5) fp1 aw6 rd6763 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw5, aw6])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6772 := evm_run rd6764 with [
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat
      (MachineState.M aw6.toNat fp1.toNat ((⟨100⟩ : UInt256) + fp0.sub fp1).toNat)) -
      Cₘ aw6)
    rd6772 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨k6652, C6652, rd6652⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyReturnToCheck_dynamic_offset
      (self := self) (value := value) (toWord := toWord) (prevValue := prevValue)
      (token := token) (token0 := token0) (ret := ret) (sel := sel)
      (status := (⟨0⟩ : UInt256))
      h houtNe houtSize ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have rd6692 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  exact RD.uniswapSkimSecondSafeTransferFailureMessageFrom6697Reverts_generic rd6697

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferEmptyFailureReverts_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1) out acc k C)
    (hout : out.size = 0) :
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
  exact RD.uniswapSkimSecondSafeTransferFailureMessageFrom6697Reverts_generic rd6697

end UniswapV2Pair
