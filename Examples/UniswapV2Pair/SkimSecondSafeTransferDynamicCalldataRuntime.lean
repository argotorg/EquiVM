import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicOffsetReturnRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace UniswapV2Pair

theorem skimSecondSafeTransferDynamicMem3_read_base128_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 4 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 := by
  have h100 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨100⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 100 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 100 hout1Size
      (by norm_num)
  have h128 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨128⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 128 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 128 hout1Size
      (by norm_num)
  unfold skimSecondSafeTransferDynamicMem3
  have hread := toByteArray_write_read_window_of_gap (UInt256.land solcAddrMask toWord)
    (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2)
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat 28 4
    (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [h100]
      have hmem2 := skimSecondSafeTransferDynamicMem2_size_ge_base_add64
        self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      exact lt_usize _ (by omega))
  rw [show
    ((UInt256.toByteArray (UInt256.land solcAddrMask toWord)).write 0
        (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2)
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat 32).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 4 =
      ((UInt256.toByteArray (UInt256.land solcAddrMask toWord)).write 0
        (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2)
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat 32).readWithPadding
        ((skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat + 28) 4 by
    rw [h100, h128]]
  rw [hread]

theorem skimSecondSafeTransferDynamicMem4_read_base128_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 4 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 := by
  have h128 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨128⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 128 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 128 hout1Size
      (by norm_num)
  have h132 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size
      (by norm_num)
  unfold skimSecondSafeTransferDynamicMem4
  rw [write32_read_below_len _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 4
      (by rw [toByteArray_size])]
  · exact skimSecondSafeTransferDynamicMem3_read_base128_4 self toWord prevValue
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · rw [h132]
    exact skimSecondSafeTransferDynamicMem3_size_ge_base_add132 self toWord prevValue
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · rw [h128, h132]
  · rw [h128]
    have hmem3 := skimSecondSafeTransferDynamicMem3_size_ge_base_add132
      self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega
  · norm_num
  · norm_num

set_option maxHeartbeats 1000000 in
theorem skimSecondSafeTransferDynamicMem4_read_base132_28
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat 28 =
      (UInt256.toByteArray value).extract 0 28 := by
  have h132 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size
      (by norm_num)
  unfold skimSecondSafeTransferDynamicMem4
  let mem3 := skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2
  let off := (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat
  have hgap : off - mem3.size < USize.size := by
    dsimp [off, mem3]
    rw [h132]
    have hmem3 := skimSecondSafeTransferDynamicMem3_size_ge_base_add132
      self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    exact lt_usize _ (by omega)
  simpa [off, mem3] using toByteArray_write_read_window_of_gap value mem3 off 0 28
    (by norm_num) (by norm_num) (by norm_num) hgap

theorem skimSecondSafeTransferDynamicMem4_read_base128_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  have h128 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨128⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 128 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 128 hout1Size
      (by norm_num)
  have h132 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size
      (by norm_num)
  rw [byteArray_readWithPadding_split _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat
      4 28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · rw [show (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat + 4 =
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat by
      rw [h128, h132]]
    rw [skimSecondSafeTransferDynamicMem4_read_base128_4 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
    rw [skimSecondSafeTransferDynamicMem4_read_base132_28 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
  · rw [h128]
    have hmem4 := skimSecondSafeTransferDynamicMem4_size_ge_base_add164
      self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega

theorem skimSecondSafeTransferDynamicCallMem0_read_base128_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 32 =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  have h64 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size
      (by norm_num)
  have h96 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size
      (by norm_num)
  have h128 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨128⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 128 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 128 hout1Size
      (by norm_num)
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size
  unfold skimSecondSafeTransferDynamicCallMem0
  rw [write32_read_below _ _
      (skimSecondSafeTransferDynamicCallPtr out1).toNat
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat
      (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicMem7
    rw [write32_read_above _ _
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat
        (by rw [toByteArray_size])]
    · unfold skimSecondSafeTransferDynamicMem6
      rw [write32_read_above _ _ 64
          (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat
          (by rw [toByteArray_size])]
      · unfold skimSecondSafeTransferDynamicMem5
        rw [write32_read_above _ _
            (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat
            (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat
            (by rw [toByteArray_size])]
        · exact skimSecondSafeTransferDynamicMem4_read_base128_32 self toWord prevValue value
            ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        · rw [h64]
          have hmem4 := skimSecondSafeTransferDynamicMem4_size_ge_base_add164
            self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
          omega
        · rw [h64, h128]
          omega
        · rw [h128]
          have hmem4 := skimSecondSafeTransferDynamicMem4_size_ge_base_add164
            self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
          omega
      · have hmem5 := skimSecondSafeTransferDynamicMem5_size_ge_base_add164
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
        omega
      · rw [h128]
        have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
        omega
      · rw [h128]
        have hmem5 := skimSecondSafeTransferDynamicMem5_size_ge_base_add164
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        omega
    · rw [h96]
      have hmem6 := skimSecondSafeTransferDynamicMem6_size_ge_base_add164
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
    · rw [h96, h128]
    · rw [h128]
      have hmem6 := skimSecondSafeTransferDynamicMem6_size_ge_base_add164
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
  · rw [hcall]
    exact skimSecondSafeTransferDynamicMem7_size_ge_base_add164 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · rw [h128, hcall]
    omega

theorem skimSecondSafeTransferDynamicCopyWord1_toByteArray
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    UInt256.toByteArray
        (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value) =
      (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).extract 28 32 ++
        (UInt256.toByteArray value).extract 0 28 := by
  unfold skimSecondSafeTransferDynamicCopyWord1
  rw [skimSecondSafeTransferDynamicCallMem0_read_base128_32 self toWord prevValue value
    ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
  apply toByteArray_ofNat_fromByteArrayBigEndian_of_size
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    toByteArray_size]
  norm_num

theorem skimSecondSafeTransferDynamicMem4_read_base160_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  have h132 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size
      (by norm_num)
  have h160 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨160⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 160 hout1Size
      (by norm_num)
  unfold skimSecondSafeTransferDynamicMem4
  let mem3 := skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2
  let off := (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat
  have hgap : off - mem3.size < USize.size := by
    dsimp [off, mem3]
    rw [h132]
    have hmem3 := skimSecondSafeTransferDynamicMem3_size_ge_base_add132
      self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    exact lt_usize _ (by omega)
  rw [show (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat = off + 28 by
    dsimp [off]
    rw [h132, h160]]
  simpa [off, mem3] using toByteArray_write_read_window_of_gap value mem3 off 28 4
    (by norm_num) (by norm_num) (by norm_num) hgap

theorem skimSecondSafeTransferDynamicCallMem1_read_base160_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  have h64 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size
      (by norm_num)
  have h96 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size
      (by norm_num)
  have h160 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨160⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 160 hout1Size
      (by norm_num)
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size
  have hret := skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size
  unfold skimSecondSafeTransferDynamicCallMem1
  rw [write32_read_below_len _ _
      (skimSecondSafeTransferDynamicRetPtr out1).toNat
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 4
      (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicCallMem0
    rw [write32_read_below_len _ _
        (skimSecondSafeTransferDynamicCallPtr out1).toNat
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 4
        (by rw [toByteArray_size])]
    · unfold skimSecondSafeTransferDynamicMem7
      rw [write32_read_above_len _ _
          (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat
          (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 4
          (by rw [toByteArray_size])]
      · unfold skimSecondSafeTransferDynamicMem6
        rw [write32_read_above_len _ _ 64
            (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 4
            (by rw [toByteArray_size])]
        · unfold skimSecondSafeTransferDynamicMem5
          rw [write32_read_above_len _ _
              (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat
              (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 4
              (by rw [toByteArray_size])]
          · exact skimSecondSafeTransferDynamicMem4_read_base160_4 self toWord prevValue value
              ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
          · rw [h64]
            have hmem4 := skimSecondSafeTransferDynamicMem4_size_ge_base_add164
              self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
            omega
          · rw [h64, h160]
            omega
          · rw [h160]
            have hmem4 := skimSecondSafeTransferDynamicMem4_size_ge_base_add164
              self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
            omega
          · norm_num
          · norm_num
        · have hmem5 := skimSecondSafeTransferDynamicMem5_size_ge_base_add164
            self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
          have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
          omega
        · rw [h160]
          have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
          omega
        · rw [h160]
          have hmem5 := skimSecondSafeTransferDynamicMem5_size_ge_base_add164
            self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
          omega
        · norm_num
        · norm_num
      · rw [h96]
        have hmem6 := skimSecondSafeTransferDynamicMem6_size_ge_base_add164
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        omega
      · rw [h96, h160]
        omega
      · rw [h160]
        have hmem6 := skimSecondSafeTransferDynamicMem6_size_ge_base_add164
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        omega
      · norm_num
      · norm_num
    · rw [hcall]
      exact skimSecondSafeTransferDynamicMem7_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    · rw [h160, hcall]
    · rw [h160]
      have hmem7 := skimSecondSafeTransferDynamicMem7_size_ge_base_add164
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
    · norm_num
    · norm_num
  · rw [hret]
    exact skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · rw [h160, hret]
    omega
  · rw [h160]
    have hmem0 := skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196
      self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega
  · norm_num
  · norm_num

theorem skimSecondSafeTransferDynamicTailSourceWord_extract0_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (UInt256.toByteArray
        (skimSecondSafeTransferDynamicTailSourceWord self o toWord prevValue out1 out2 value)).extract
        0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  unfold skimSecondSafeTransferDynamicTailSourceWord
  have h160 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨160⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 160 hout1Size
      (by norm_num)
  have hreadSize :
      ((skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
          |>.readWithPadding (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat
            32).size = 32 := by
    rw [readWithPadding_eq_extract' _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat
        32 (by norm_num) (by norm_num)]
    · rw [ByteArray.size_extract]
      have hmem1 := skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      rw [h160]
      omega
    · rw [h160]
      have hmem1 := skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize]
  rw [readWithPadding_eq_extract' _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat
      32 (by norm_num) (by norm_num)]
  · rw [extract_extract_BA]
    rw [h160]
    rw [show (skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 + 0 =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 by omega]
    rw [show min ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 + 4)
        ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 + 32) =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 by omega]
    rw [← h160]
    rw [show (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 =
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨160⟩ : UInt256)).toNat + 4 by
      rw [h160]]
    rw [← readWithPadding_eq_extract' _
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat
        4 (by norm_num) (by norm_num)]
    exact skimSecondSafeTransferDynamicCallMem1_read_base160_4
      self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    · rw [h160]
      have hmem1 := skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
  · rw [h160]
    have hmem1 := skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228
      self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega

theorem skimSecondSafeTransferDynamicTailWord_extract0_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (UInt256.toByteArray
        (skimSecondSafeTransferDynamicTailWord self o toWord prevValue out1 out2 value)).extract
        0 4 =
      (UInt256.toByteArray value).extract 28 32 := by
  rw [skimSecondSafeTransferDynamicTailWord]
  rw [skimSafeTransferTailWord_extract0_4_of_source]
  exact skimSecondSafeTransferDynamicTailSourceWord_extract0_4
    self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size

theorem skimSecondSafeTransferDynamicCallMem2_read_callPtr_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 32 =
      UInt256.toByteArray
        (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value) := by
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size
  have hret := skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size
  have h228 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
      (by norm_num)
  unfold skimSecondSafeTransferDynamicCallMem2
  rw [write32_read_below _ _
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat
      (skimSecondSafeTransferDynamicCallPtr out1).toNat
      (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicCallMem1
    rw [write32_read_below _ _
        (skimSecondSafeTransferDynamicRetPtr out1).toNat
        (skimSecondSafeTransferDynamicCallPtr out1).toNat
        (by rw [toByteArray_size])]
    · unfold skimSecondSafeTransferDynamicCallMem0
      exact toByteArray_write_read_back_of_gap
        (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value)
        _ (skimSecondSafeTransferDynamicCallPtr out1).toNat
        (by
          rw [hcall]
          have hmem7 := skimSecondSafeTransferDynamicMem7_size_ge_base_add164
            self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
          exact lt_usize _ (by omega))
    · rw [hret]
      exact skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    · rw [hcall, hret]
  · rw [h228]
    exact skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · rw [hcall, h228]
    omega

theorem skimSecondSafeTransferDynamicCallMem2_read_retPtr_32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicRetPtr out1).toNat 32 =
      UInt256.toByteArray
        (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value) := by
  have hret := skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size
  have h228 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
      (by norm_num)
  unfold skimSecondSafeTransferDynamicCallMem2
  rw [write32_read_below _ _
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat
      (skimSecondSafeTransferDynamicRetPtr out1).toNat
      (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicCallMem1
    exact toByteArray_write_read_back_of_gap
      (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value)
      _ (skimSecondSafeTransferDynamicRetPtr out1).toNat
      (by
        rw [hret]
        have hmem0 := skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        exact lt_usize _ (by omega))
  · rw [h228]
    exact skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · rw [hret, h228]

theorem skimSecondSafeTransferDynamicCallMem2_read_base228_4
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat 4 =
      (UInt256.toByteArray
        (skimSecondSafeTransferDynamicTailWord self o toWord prevValue out1 out2 value)).extract
        0 4 := by
  have h228 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
      (by norm_num)
  unfold skimSecondSafeTransferDynamicCallMem2
  rw [write32_read_prefix_len _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat
      4 (by rw [toByteArray_size])]
  · rw [h228]
    exact skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · norm_num
  · norm_num
  · norm_num

theorem skimSecondSafeTransferDynamicCallMem2_read_callPtr_68
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 68 =
      (transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68 := by
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size
  have hret := skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size
  have hretEnd := skimSecondSafeTransferDynamicRetEnd_toNat out1 hout1Size
  have h228 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
      (by norm_num)
  rw [transferCalldataMem_read128_68]
  rw [byteArray_readWithPadding_split _
      (skimSecondSafeTransferDynamicCallPtr out1).toNat 32 36
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · rw [show (skimSecondSafeTransferDynamicCallPtr out1).toNat + 32 =
        (skimSecondSafeTransferDynamicRetPtr out1).toNat by
      rw [hcall, hret]]
    rw [byteArray_readWithPadding_split _
        (skimSecondSafeTransferDynamicRetPtr out1).toNat 32 4
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    · rw [
        skimSecondSafeTransferDynamicCallMem2_read_callPtr_32
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size,
        skimSecondSafeTransferDynamicCallMem2_read_retPtr_32
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
      change UInt256.toByteArray
            (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2
              value) ++
          (UInt256.toByteArray
              (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value) ++
            (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).readWithPadding
              ((skimSecondSafeTransferDynamicRetPtr out1).toNat + 32) 4) =
        transferSelector ++ (UInt256.land solcAddrMask toWord).toByteArray ++ value.toByteArray
      rw [show (skimSecondSafeTransferDynamicRetPtr out1).toNat + 32 =
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat by
        rw [hret, h228]]
      rw [skimSecondSafeTransferDynamicCallMem2_read_base228_4
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
      rw [skimSecondSafeTransferDynamicPatchedSelectorWord,
        skimSafeTransferPatchedSelector_toByteArray]
      rw [
        skimSecondSafeTransferDynamicWord96_extract4_32
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size,
        skimSecondSafeTransferDynamicCopyWord1_toByteArray
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size,
        skimSecondSafeTransferDynamicTailWord_extract0_4
          self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
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
          ((addrBytes.extract 28 32 ++ valueBytes.extract 0 28) ++
            valueBytes.extract 28 32) =
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
    · rw [hret]
      have hsize := skimSecondSafeTransferDynamicCallMem2_size_ge_retEnd
        self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      rw [hretEnd] at hsize
      omega
  · rw [hcall]
    have hsize := skimSecondSafeTransferDynamicCallMem2_size_ge_retEnd
      self toWord prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    rw [hretEnd] at hsize
    omega

end UniswapV2Pair
