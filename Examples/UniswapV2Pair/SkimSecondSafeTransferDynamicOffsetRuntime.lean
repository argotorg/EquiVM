import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicOffsetMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem MachineState_M_same_of_cover_len (s f l : Nat) (hcover : f + l ≤ s * 32) :
    MachineState.M s f l = s := by
  unfold MachineState.M
  cases l with
  | zero => rfl
  | succ l =>
      change max s ((f + (l + 1) + 31) / 32) = s
      rw [Nat.max_eq_left]
      have hdivlt : (f + (l + 1) + 31) / 32 < s + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 32)]
        omega
      omega

theorem skimSecondSafeTransferDynamicWordsCall0_cover_base128 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicBasePtr out + (⟨128⟩ : UInt256)).toNat + 32 ≤
      (skimSecondSafeTransferDynamicWordsCall0 out).toNat * 32 := by
  have hcover := UInt256_ofNat_M_covers
    (skimSecondSafeTransferDynamicWordsMem4 out)
    (skimSecondSafeTransferDynamicCallPtr out)
    (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out houtSize)
    (by
      simpa [skimSecondSafeTransferDynamicCallPtr] using
        skimSecondSafeTransferDynamicBasePtr_window_lt out 164 32
          houtSize (by norm_num) (by norm_num))
  unfold skimSecondSafeTransferDynamicWordsCall0 at hcover
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out houtSize
  have h128 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨128⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out).toNat + 128 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out 128 houtSize (by norm_num)
  rw [hcall] at hcover
  have htarget :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨128⟩ : UInt256)).toNat + 32 ≤
        (UInt256.ofNat
          (MachineState.M (skimSecondSafeTransferDynamicWordsMem4 out).toNat
            ((skimSecondSafeTransferDynamicBasePtr out).toNat + 164) 32)).toNat * 32 := by
    rw [h128]
    omega
  simpa [skimSecondSafeTransferDynamicWordsCall0, hcall] using htarget

theorem skimSecondSafeTransferDynamicWordsCall1_cover_base160 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicBasePtr out + (⟨160⟩ : UInt256)).toNat + 32 ≤
      (skimSecondSafeTransferDynamicWordsCall1 out).toNat * 32 := by
  have hcover := UInt256_ofNat_M_covers
    (skimSecondSafeTransferDynamicWordsCall0 out)
    (skimSecondSafeTransferDynamicRetPtr out)
    (skimSecondSafeTransferDynamicWordsCall0_mul32_lt out houtSize)
    (by
      simpa [skimSecondSafeTransferDynamicRetPtr] using
        skimSecondSafeTransferDynamicBasePtr_window_lt out 196 32
          houtSize (by norm_num) (by norm_num))
  unfold skimSecondSafeTransferDynamicWordsCall1 at hcover
  have hret := skimSecondSafeTransferDynamicRetPtr_toNat out houtSize
  have h160 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨160⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out).toNat + 160 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out 160 houtSize (by norm_num)
  rw [hret] at hcover
  have htarget :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨160⟩ : UInt256)).toNat + 32 ≤
        (UInt256.ofNat
          (MachineState.M (skimSecondSafeTransferDynamicWordsCall0 out).toNat
            ((skimSecondSafeTransferDynamicBasePtr out).toNat + 196) 32)).toNat * 32 := by
    rw [h160]
    omega
  simpa [skimSecondSafeTransferDynamicWordsCall1, hret] using htarget

theorem skimSecondSafeTransferDynamicWordsCall2_cover_callPtr68 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicCallPtr out).toNat + 68 ≤
      (skimSecondSafeTransferDynamicWordsCall2 out).toNat * 32 := by
  have hcover := UInt256_ofNat_M_covers
    (skimSecondSafeTransferDynamicWordsCall1 out)
    (skimSecondSafeTransferDynamicBasePtr out + ⟨228⟩)
    (skimSecondSafeTransferDynamicWordsCall1_mul32_lt out houtSize)
    (by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_window_lt out 228 32
          houtSize (by norm_num) (by norm_num))
  unfold skimSecondSafeTransferDynamicWordsCall2 at hcover
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out houtSize
  have h228 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨228⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out).toNat + 228 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out 228 houtSize (by norm_num)
  rw [h228] at hcover
  have htarget :
      (skimSecondSafeTransferDynamicCallPtr out).toNat + 68 ≤
        (UInt256.ofNat
          (MachineState.M (skimSecondSafeTransferDynamicWordsCall1 out).toNat
            ((skimSecondSafeTransferDynamicBasePtr out).toNat + 228) 32)).toNat * 32 := by
    rw [hcall]
    omega
  simpa [skimSecondSafeTransferDynamicWordsCall2, h228] using htarget

theorem skimSecondSafeTransferDynamicWordsCall2_cover_base228 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicBasePtr out + (⟨228⟩ : UInt256)).toNat + 32 ≤
      (skimSecondSafeTransferDynamicWordsCall2 out).toNat * 32 := by
  have hcover := UInt256_ofNat_M_covers
    (skimSecondSafeTransferDynamicWordsCall1 out)
    (skimSecondSafeTransferDynamicBasePtr out + ⟨228⟩)
    (skimSecondSafeTransferDynamicWordsCall1_mul32_lt out houtSize)
    (by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_window_lt out 228 32
          houtSize (by norm_num) (by norm_num))
  simpa [skimSecondSafeTransferDynamicWordsCall2] using hcover

theorem skimSecondSafeTransferDynamicWordsCall2_callOutputSame (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M
          (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out).toNat
            (skimSecondSafeTransferDynamicCallPtr out).toNat 68)
          (skimSecondSafeTransferDynamicCallPtr out).toNat 0) =
      skimSecondSafeTransferDynamicWordsCall2 out := by
  have hinner :
      MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out).toNat
          (skimSecondSafeTransferDynamicCallPtr out).toNat 68 =
        (skimSecondSafeTransferDynamicWordsCall2 out).toNat := by
    exact MachineState_M_same_of_cover_len _ _ _
      (skimSecondSafeTransferDynamicWordsCall2_cover_callPtr68 out houtSize)
  rw [hinner]
  simpa [MachineState.M] using u256_ofNat_toNat (skimSecondSafeTransferDynamicWordsCall2 out)

theorem skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 196 ≤
      (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value).size := by
  unfold skimSecondSafeTransferDynamicCallMem0
  rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size]
  exact toByteArray_write_size_ge_off_add32
    (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value)
    (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value)
    ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 164)
    (by
      have hmem7 :=
        skimSecondSafeTransferDynamicMem7_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      exact lt_usize _ (by omega))

theorem skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 ≤
      (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value).size := by
  unfold skimSecondSafeTransferDynamicCallMem1
  rw [skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
  exact toByteArray_write_size_ge_off_add32
    (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value)
    (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value)
    ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 196)
    (by
      have hmem0 :=
        skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      exact lt_usize _ (by omega))

theorem skimSecondSafeTransferDynamicCallMem0_mload_base128
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat ≥
          (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩) ≥
          skimSecondSafeTransferDynamicWordsCall0 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
       ((skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value)
        |>.readWithPadding (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 32))) =
      skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value := by
  have hguard :
      ¬((skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat ≥
          (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩) ≥
          skimSecondSafeTransferDynamicWordsCall0 out1 * ⟨32⟩) := by
    rw [not_or]
    constructor
    · have h128 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨128⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 128 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 128 hout1Size (by norm_num)
      rw [h128]
      have hsize :=
        skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
    · exact UInt256_mload_haw_of_cover _ _
        (skimSecondSafeTransferDynamicWordsCall0_mul32_lt out1 hout1Size)
        (skimSecondSafeTransferDynamicWordsCall0_cover_base128 out1 hout1Size)
  rw [if_neg hguard]
  rfl

theorem skimSecondSafeTransferDynamicCallMem1_mload_base160
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat ≥
          (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩) ≥
          skimSecondSafeTransferDynamicWordsCall1 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
       ((skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
        |>.readWithPadding (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 32))) =
      skimSecondSafeTransferDynamicTailSourceWord self o toWord prevValue out1 out2 value := by
  have hguard :
      ¬((skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat ≥
          (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩) ≥
          skimSecondSafeTransferDynamicWordsCall1 out1 * ⟨32⟩) := by
    rw [not_or]
    constructor
    · have h160 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨160⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 160 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 160 hout1Size (by norm_num)
      rw [h160]
      have hsize :=
        skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
    · exact UInt256_mload_haw_of_cover _ _
        (skimSecondSafeTransferDynamicWordsCall1_mul32_lt out1 hout1Size)
        (skimSecondSafeTransferDynamicWordsCall1_cover_base160 out1 hout1Size)
  rw [if_neg hguard]
  rfl

theorem skimSecondSafeTransferDynamicCallMem2_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    ((skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
        |>.readWithPadding 64 32) =
      UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1) := by
  unfold skimSecondSafeTransferDynamicCallMem2
  rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat
      64 (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicCallMem1
    rw [write32_read_below _ _ (skimSecondSafeTransferDynamicRetPtr out1).toNat
        64 (by rw [toByteArray_size])]
    · unfold skimSecondSafeTransferDynamicCallMem0
      rw [write32_read_below _ _ (skimSecondSafeTransferDynamicCallPtr out1).toNat
          64 (by rw [toByteArray_size])]
      · exact skimSecondSafeTransferDynamicMem7_read64 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      · rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size]
        exact skimSecondSafeTransferDynamicMem7_size_ge_base_add164 self toWord
          prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      · rw [skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size]
        have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
        omega
    · rw [skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
      exact skimSecondSafeTransferDynamicCallMem0_size_ge_base_add196 self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    · rw [skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size]
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      omega
  · have h228 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
      simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
        (by norm_num)
    rw [h228]
    exact skimSecondSafeTransferDynamicCallMem1_size_ge_base_add228 self toWord
      prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · have h228 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
      simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
        (by norm_num)
    rw [h228]
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega

theorem skimSecondSafeTransferDynamicCallMem2_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondSafeTransferDynamicWordsCall2 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      skimSecondSafeTransferDynamicCallPtr out1 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondSafeTransferDynamicWordsCall2 out1)
    (v := skimSecondSafeTransferDynamicCallPtr out1)
    (by
      unfold skimSecondSafeTransferDynamicCallMem2
      have h228 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
        simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
          (by norm_num)
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
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      change 64 <
        ((UInt256.toByteArray
          (skimSecondSafeTransferDynamicTailWord self o toWord prevValue out1 out2 value)).write
            0 (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
            ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 228) 32).size
      omega)
    (UInt256_mload64_haw_of_toNat_ge13 _
      (skimSecondSafeTransferDynamicWordsCall2_toNat_ge13 out1 hout1Size)
      (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size))
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from rfl] using
        skimSecondSafeTransferDynamicCallMem2_read64 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

theorem skimSecondBalanceDynamicSelectorMem_size_le_base_add32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255) :
    (skimSecondBalanceDynamicSelectorMem self o toWord value out1).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 := by
  unfold skimSecondBalanceDynamicSelectorMem
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray balanceOfSelectorShifted)
    (destination := skimSafeTransferReturnDataMem self o toWord value out1)
    (sourceOffset := 0) (destinationOffset := (skimSafeTransferReturnDataPtr out1).toNat)
    (length := 32)
  have hbase := skimSafeTransferReturnDataMem_size_le_ptr_add32 self toWord value
    ho32 hoSize hout1Ne hout1Size
  simpa [skimSecondSafeTransferDynamicBasePtr, toByteArray_size] using
    le_trans hwrite (by omega)

theorem skimSecondBalanceDynamicCalldataMem_size_le_base_add36
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255) :
    (skimSecondBalanceDynamicCalldataMem self o toWord value out1).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 36 := by
  unfold skimSecondBalanceDynamicCalldataMem
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray self)
    (destination := skimSecondBalanceDynamicSelectorMem self o toWord value out1)
    (sourceOffset := 0)
    (destinationOffset := (skimSafeTransferReturnDataPtr out1 + ⟨4⟩).toNat)
    (length := 32)
  have hsel :=
    skimSecondBalanceDynamicSelectorMem_size_le_base_add32 self toWord value
      ho32 hoSize hout1Ne hout1Size
  have h4 :
      (skimSafeTransferReturnDataPtr out1 + (⟨4⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 4 := by
    simpa [skimSecondSafeTransferDynamicBasePtr] using
      skimSafeTransferReturnDataPtr_add_ofNat_toNat out1 4 hout1Size (by norm_num)
  simpa [toByteArray_size, h4] using le_trans hwrite (by omega)

theorem skimSecondBalanceDynamicStaticcallMem_size_le_base_add36_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 36 := by
  unfold skimSecondBalanceDynamicStaticcallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out2.size)).toNat = 32 := by
    simpa using
      umin_ofNat_right_toNat_of_ge (c := 32) (n := out2.size) (by decide)
        hout2_32 hout2Size
  have hwrite := byteArray_write_size_le
    (source := out2)
    (destination := skimSecondBalanceDynamicCalldataMem self o toWord value out1)
    (sourceOffset := 0) (destinationOffset := (skimSafeTransferReturnDataPtr out1).toNat)
    (length := (min (⟨32⟩ : UInt256) (UInt256.ofNat out2.size)).toNat)
  have hcalldata :=
    skimSecondBalanceDynamicCalldataMem_size_le_base_add36 self toWord value
      ho32 hoSize hout1Ne hout1Size
  have hptr :
      (skimSafeTransferReturnDataPtr out1).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat := by
    rfl
  have hmax :
      max (skimSecondBalanceDynamicCalldataMem self o toWord value out1).size
          ((skimSafeTransferReturnDataPtr out1).toNat +
            (min (⟨32⟩ : UInt256) (UInt256.ofNat out2.size)).toNat) ≤
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 36 := by
    rw [hlen, hptr]
    omega
  exact le_trans hwrite hmax

theorem skimSecondSafeTransferDynamicMem0_size_le_base_add64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
  unfold skimSecondSafeTransferDynamicMem0
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩))
    (destination := skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2)
    (sourceOffset := 0) (destinationOffset := 64) (length := 32)
  have hbase :=
    skimSecondBalanceDynamicStaticcallMem_size_le_base_add36_of_size_ge self toWord prevValue
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
  simpa [toByteArray_size] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicMem1_size_le_base_add64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem1 self o toWord prevValue out1 out2).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
  unfold skimSecondSafeTransferDynamicMem1
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray (⟨25⟩ : UInt256))
    (destination := skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2)
    (sourceOffset := 0)
    (destinationOffset := (skimSecondSafeTransferDynamicBasePtr out1).toNat)
    (length := 32)
  have hmem0 := skimSecondSafeTransferDynamicMem0_size_le_base_add64 self toWord prevValue
    ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  simpa [toByteArray_size] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicMem2_size_le_base_add64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
  unfold skimSecondSafeTransferDynamicMem2
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray skimSafeTransferSignatureWord)
    (destination := skimSecondSafeTransferDynamicMem1 self o toWord prevValue out1 out2)
    (sourceOffset := 0)
    (destinationOffset := (skimSecondSafeTransferDynamicBasePtr out1 + ⟨32⟩).toNat)
    (length := 32)
  have hmem1 := skimSecondSafeTransferDynamicMem1_size_le_base_add64 self toWord prevValue
    ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have h32 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨32⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 32 hout1Size
      (by norm_num)
  simpa [toByteArray_size, h32] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicMem3_size_le_base_add132
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
  unfold skimSecondSafeTransferDynamicMem3
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray (UInt256.land solcAddrMask toWord))
    (destination := skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2)
    (sourceOffset := 0)
    (destinationOffset := (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat)
    (length := 32)
  have hmem2 := skimSecondSafeTransferDynamicMem2_size_le_base_add64 self toWord prevValue
    ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have h100 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨100⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 100 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 100 hout1Size
      (by norm_num)
  simpa [toByteArray_size, h100] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicMem4_size_le_base_add164
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 := by
  unfold skimSecondSafeTransferDynamicMem4
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray value)
    (destination := skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2)
    (sourceOffset := 0)
    (destinationOffset := (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat)
    (length := 32)
  have hmem3 := skimSecondSafeTransferDynamicMem3_size_le_base_add132 self toWord prevValue
    ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have h132 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size
      (by norm_num)
  simpa [toByteArray_size, h132] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicMem7_size_le_base_add164
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 := by
  unfold skimSecondSafeTransferDynamicMem7
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray
      (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value))
    (destination := skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value)
    (sourceOffset := 0)
    (destinationOffset := (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat)
    (length := 32)
  have hmem6 : (skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 := by
    unfold skimSecondSafeTransferDynamicMem6
    have hwrite6 := byteArray_write_size_le
      (source := UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1))
      (destination := skimSecondSafeTransferDynamicMem5 self o toWord prevValue out1 out2 value)
      (sourceOffset := 0) (destinationOffset := 64) (length := 32)
    have hmem5 : (skimSecondSafeTransferDynamicMem5 self o toWord prevValue out1 out2 value).size ≤
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 := by
      unfold skimSecondSafeTransferDynamicMem5
      have hwrite5 := byteArray_write_size_le
        (source := UInt256.toByteArray (⟨68⟩ : UInt256))
        (destination := skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value)
        (sourceOffset := 0)
        (destinationOffset := (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat)
        (length := 32)
      have hmem4 := skimSecondSafeTransferDynamicMem4_size_le_base_add164 self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      have h64 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
        simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size
          (by norm_num)
      simpa [toByteArray_size, h64] using le_trans hwrite5 (by omega)
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    simpa [toByteArray_size] using le_trans hwrite6 (by omega)
  have h96 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size
      (by norm_num)
  simpa [toByteArray_size, h96] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicCallMem0_size_le_base_add196
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 196 := by
  unfold skimSecondSafeTransferDynamicCallMem0
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray
      (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value))
    (destination := skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value)
    (sourceOffset := 0)
    (destinationOffset := (skimSecondSafeTransferDynamicCallPtr out1).toNat)
    (length := 32)
  have hmem7 := skimSecondSafeTransferDynamicMem7_size_le_base_add164 self toWord
    prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have hcall := skimSecondSafeTransferDynamicCallPtr_toNat out1 hout1Size
  simpa [toByteArray_size, hcall] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicCallMem1_size_le_base_add228
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value).size ≤
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
  unfold skimSecondSafeTransferDynamicCallMem1
  have hwrite := byteArray_write_size_le
    (source := UInt256.toByteArray
      (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value))
    (destination := skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value)
    (sourceOffset := 0)
    (destinationOffset := (skimSecondSafeTransferDynamicRetPtr out1).toNat)
    (length := 32)
  have hmem0 := skimSecondSafeTransferDynamicCallMem0_size_le_base_add196 self toWord
    prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have hret := skimSecondSafeTransferDynamicRetPtr_toNat out1 hout1Size
  simpa [toByteArray_size, hret] using le_trans hwrite (by omega)

theorem skimSecondSafeTransferDynamicCallMem1_mload_base228
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat ≥
          (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩) ≥
          skimSecondSafeTransferDynamicWordsCall1 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
       ((skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
        |>.readWithPadding (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat 32))) =
      ⟨0⟩ := by
  rw [if_pos]
  left
  have hsize := skimSecondSafeTransferDynamicCallMem1_size_le_base_add228 self toWord
    prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have h228 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨228⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 228 := by
    simpa using skimSecondSafeTransferDynamicBasePtr_add_toNat out1 228 hout1Size
      (by norm_num)
  rw [h228]
  exact hsize

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferEntryToCallMade_dynamic_offset
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out1 out2 : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6370⟩
      (value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2)
      (skimSecondBalanceDynamicStaticcallWords out1) out2 (cA, σ) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
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
            ((skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
              |>.readWithPadding (skimSecondSafeTransferDynamicCallPtr out1).toNat 68)
            (ee.depth + 1) ee.header ee.perm)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: skimSecondSafeTransferDynamicRetEnd out1 ::
            UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
            value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
            sel :: [])
          (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
          (skimSecondSafeTransferDynamicWordsCall2 out1) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  have rd6375 := evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 (skimSafeTransferReturnDataPtr out1)
      (skimSecondSafeTransferDynamicWords0 out1) (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size]
        exact Nat.sub_self _)
      (skimSecondBalanceDynamicStaticcallMem_mload64_of_size_ge self toWord prevValue
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (by
        simpa [skimSecondSafeTransferDynamicWords0] using
          skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size)
      (by evm_ov)]
  have rd6380 := evm_run rd6375 with [
    dup1, dup3, add, dup3,
    raw mstore 0 (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2)
      (skimSecondSafeTransferDynamicWords0 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size,
            skimSecondSafeTransferDynamicWords0]
        exact Nat.sub_self _)
      (by
        rw [u256_add_comm (⟨64⟩ : UInt256) (skimSafeTransferReturnDataPtr out1)]
        unfold skimSecondSafeTransferDynamicMem0 skimSecondSafeTransferDynamicBasePtr
        rfl)
      (by
        simpa [skimSecondSafeTransferDynamicWords0] using
          skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size)
      (by evm_ov)]
  have rd6384 := evm_run rd6380 with [
    push1 ⟨25⟩, dup2,
    raw mstore 0 (skimSecondSafeTransferDynamicMem1 self o toWord prevValue out1 out2)
      (skimSecondSafeTransferDynamicWords0 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondBalanceDynamicStaticcallWords_ptr_same out1 hout1Size,
            skimSecondSafeTransferDynamicWords0]
        exact Nat.sub_self _)
      (by unfold skimSecondSafeTransferDynamicMem1 skimSecondSafeTransferDynamicBasePtr; rfl)
      (by
        simpa [skimSecondSafeTransferDynamicWords0] using
          skimSecondBalanceDynamicStaticcallWords_ptr_same out1 hout1Size)
      (by evm_ov)]
  have rd6417 := rd6384.pushConst skimSafeTransferSignatureWord (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd6423 := evm_run rd6417 with [
    push1 ⟨32⟩, swap2, dup3, add,
    raw mstore
      (Cₘ (skimSecondSafeTransferDynamicWordsMem2 out1) -
        Cₘ (skimSecondSafeTransferDynamicWords0 out1))
      (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2)
      (skimSecondSafeTransferDynamicWordsMem2 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [u256_add_comm (⟨32⟩ : UInt256) (skimSafeTransferReturnDataPtr out1)]
        unfold skimSecondSafeTransferDynamicWordsMem2 skimSecondSafeTransferDynamicBasePtr
        rfl)
      (by
        rw [u256_add_comm (⟨32⟩ : UInt256) (skimSafeTransferReturnDataPtr out1)]
        unfold skimSecondSafeTransferDynamicMem2 skimSecondSafeTransferDynamicBasePtr
        rfl)
      (by
        rw [u256_add_comm (⟨32⟩ : UInt256) (skimSafeTransferReturnDataPtr out1)]
        unfold skimSecondSafeTransferDynamicWordsMem2 skimSecondSafeTransferDynamicBasePtr
        rfl)
      (by evm_ov)]
  have rd6425 := evm_run rd6423 with [
    dup2,
    raw mload 0 (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩)
      (skimSecondSafeTransferDynamicWordsMem2 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondSafeTransferDynamicWordsMem2_mload64_same out1 hout1Size]
        exact Nat.sub_self _)
      (skimSecondSafeTransferDynamicMem2_mload64 self toWord prevValue
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (skimSecondSafeTransferDynamicWordsMem2_mload64_same out1 hout1Size)
      (by evm_ov)]
  have rd6441 := evm_run rd6425 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, dup2, and,
    push1 ⟨36⟩, dup4, add,
    raw mstore
      (Cₘ (skimSecondSafeTransferDynamicWordsMem3 out1) -
        Cₘ (skimSecondSafeTransferDynamicWordsMem2 out1))
      (skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2)
      (skimSecondSafeTransferDynamicWordsMem3 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [skimSecondSafeTransferDynamicBasePtr_add64_add36 out1]
        unfold skimSecondSafeTransferDynamicWordsMem3
        rfl)
      (by
        rw [skimSecondSafeTransferDynamicBasePtr_add64_add36 out1]
        unfold skimSecondSafeTransferDynamicMem3
        rfl)
      (by
        rw [skimSecondSafeTransferDynamicBasePtr_add64_add36 out1]
        unfold skimSecondSafeTransferDynamicWordsMem3
        rfl)
      (by evm_ov)]
  have rd6449 := evm_run rd6441 with [
    push1 ⟨68⟩, dup1, dup4, add, dup7, swap1,
    raw mstore
      (Cₘ (skimSecondSafeTransferDynamicWordsMem4 out1) -
        Cₘ (skimSecondSafeTransferDynamicWordsMem3 out1))
      (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsMem4 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [skimSecondSafeTransferDynamicBasePtr_add64_add68 out1]
        unfold skimSecondSafeTransferDynamicWordsMem4
        rfl)
      (by
        rw [skimSecondSafeTransferDynamicBasePtr_add64_add68 out1]
        unfold skimSecondSafeTransferDynamicMem4
        rfl)
      (by
        rw [skimSecondSafeTransferDynamicBasePtr_add64_add68 out1]
        unfold skimSecondSafeTransferDynamicWordsMem4
        rfl)
      (by evm_ov)]
  have rd6451 := evm_run rd6449 with [
    dup5,
    raw mload 0 (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩)
      (skimSecondSafeTransferDynamicWordsMem4 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondSafeTransferDynamicWordsMem4_mload64_same out1 hout1Size]
        exact Nat.sub_self _)
      (skimSecondSafeTransferDynamicMem4_mload64 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (skimSecondSafeTransferDynamicWordsMem4_mload64_same out1 hout1Size)
      (by evm_ov)]
  have rd6459 := evm_run rd6451 with [
    dup1, dup5, sub, swap1, swap2, add, dup2,
    raw mstore 0 (skimSecondSafeTransferDynamicMem5 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsMem4 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondSafeTransferDynamicWordsMem4_mload_base64_same out1 hout1Size]
        exact Nat.sub_self _)
      (by
        unfold skimSecondSafeTransferDynamicMem5
        rw [u256_sub_self,
          show (⟨68⟩ : UInt256) + ⟨0⟩ = ⟨68⟩ by native_decide])
      (skimSecondSafeTransferDynamicWordsMem4_mload_base64_same out1 hout1Size)
      (by evm_ov)]
  have rd6466 := evm_run rd6459 with [
    push1 ⟨100⟩, swap1, swap3, add, dup5,
    raw mstore 0 (skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsMem4 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondSafeTransferDynamicWordsMem4_mload64_same out1 hout1Size]
        exact Nat.sub_self _)
      (by
        unfold skimSecondSafeTransferDynamicMem6 skimSecondSafeTransferDynamicCallPtr
        rw [u256_add_assoc]
        rw [show (⟨64⟩ : UInt256) + ⟨100⟩ = ⟨164⟩ by native_decide]
        rfl)
      (skimSecondSafeTransferDynamicWordsMem4_mload64_same out1 hout1Size)
      (by evm_ov)]
  have rd6471 := evm_run rd6466 with [
    swap2, dup2, add, dup1,
    raw mload 0
      (skimSecondSafeTransferDynamicWord96 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsMem4 out1)
      (by native_decide)
      (fun s haws hstks => by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ, hptr,
            skimSecondSafeTransferDynamicWordsMem4_mload_base96_same out1 hout1Size]
        exact Nat.sub_self _)
      (by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        rw [hptr]
        exact skimSecondSafeTransferDynamicMem6_mload_base96 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        rw [hptr]
        exact skimSecondSafeTransferDynamicWordsMem4_mload_base96_same out1 hout1Size)
      (by evm_ov)]
  have rd6480 := evm_run rd6471 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and]
  have rd6485 := rd6480.pushConst transferSelectorWord (width := 4) (op := .PUSH4)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd6491 := evm_run rd6485 with [
    push1 ⟨224⟩, shl, or, dup2,
    raw mstore 0 (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsMem4 out1)
      (by native_decide)
      (fun s haws hstks => by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ, hptr,
            skimSecondSafeTransferDynamicWordsMem4_mload_base96_same out1 hout1Size]
        exact Nat.sub_self _)
      (by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        rw [hptr]
        unfold skimSecondSafeTransferDynamicMem7
          skimSecondSafeTransferDynamicPatchedSelectorWord
        rfl)
      (by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        rw [hptr]
        exact skimSecondSafeTransferDynamicWordsMem4_mload_base96_same out1 hout1Size)
      (by evm_ov)]
  have rd6512 := evm_run rd6491 with [
    swap3,
    raw mload 0 (skimSecondSafeTransferDynamicCallPtr out1)
      (skimSecondSafeTransferDynamicWordsMem4 out1) (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondSafeTransferDynamicWordsMem4_mload64_same out1 hout1Size]
        exact Nat.sub_self _)
      (skimSecondSafeTransferDynamicMem7_mload64 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (skimSecondSafeTransferDynamicWordsMem4_mload64_same out1 hout1Size)
      (by evm_ov),
    dup2,
    raw mload 0 (⟨68⟩ : UInt256)
      (skimSecondSafeTransferDynamicWordsMem4 out1) (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            skimSecondSafeTransferDynamicWordsMem4_mload_base64_same out1 hout1Size]
        exact Nat.sub_self _)
      (skimSecondSafeTransferDynamicMem7_mload_base64 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (skimSecondSafeTransferDynamicWordsMem4_mload_base64_same out1 hout1Size)
      (by evm_ov),
    push1 ⟨0⟩, swap5, push1 ⟨96⟩, swap5, dup10, and,
    swap4, swap3, swap2, dup3, swap2, swap1, dup1, dup4, dup4]
  have rd6521a := evm_run rd6512 with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539a := evm_run rd6521a with [
    dup1,
    raw mload 0
      (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsMem4 out1) (by native_decide)
      (fun s haws hstks => by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ, hptr,
            skimSecondSafeTransferDynamicWordsMem4_mload_base96_same out1 hout1Size]
        exact Nat.sub_self _)
      (by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        rw [hptr]
        exact skimSecondSafeTransferDynamicMem7_mload_base96 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (by
        have hptr :
            skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
              skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
          rw [u256_add_assoc]
          rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
        rw [hptr]
        exact skimSecondSafeTransferDynamicWordsMem4_mload_base96_same out1 hout1Size)
      (by evm_ov),
    dup3,
    raw mstore
      (Cₘ (skimSecondSafeTransferDynamicWordsCall0 out1) -
        Cₘ (skimSecondSafeTransferDynamicWordsMem4 out1))
      (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall0 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        unfold skimSecondSafeTransferDynamicWordsCall0
        rfl)
      (by unfold skimSecondSafeTransferDynamicCallMem0; rfl)
      (by unfold skimSecondSafeTransferDynamicWordsCall0; rfl) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512a := rd6539a.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hbase96 :
      skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256) + ⟨32⟩ =
        skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩ := by
    rw [u256_add_assoc]
    rw [show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
  rw [hbase96, skimSecondSafeTransferDynamicBasePtr_add96_add32 out1,
    skimSecondSafeTransferDynamicCallPtr_add32 out1,
    show (⟨68⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨36⟩ by native_decide]
    at rd6512a
  have rd6521b := evm_run rd6512a with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩, jumpiNT (by native_decide)]
  have rd6539b := evm_run rd6521b with [
    dup1,
    raw mload 0
      (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall0 out1) (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            UInt256_M_same_of_cover _ _
              (skimSecondSafeTransferDynamicWordsCall0_mul32_lt out1 hout1Size)
              (skimSecondSafeTransferDynamicWordsCall0_cover_base128 out1 hout1Size)]
        exact Nat.sub_self _)
      (skimSecondSafeTransferDynamicCallMem0_mload_base128 self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (UInt256_M_same_of_cover _ _
        (skimSecondSafeTransferDynamicWordsCall0_mul32_lt out1 hout1Size)
        (skimSecondSafeTransferDynamicWordsCall0_cover_base128 out1 hout1Size))
      (by evm_ov),
    dup3,
    raw mstore
      (Cₘ (skimSecondSafeTransferDynamicWordsCall1 out1) -
        Cₘ (skimSecondSafeTransferDynamicWordsCall0 out1))
      (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall1 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        unfold skimSecondSafeTransferDynamicWordsCall1
        rfl)
      (by unfold skimSecondSafeTransferDynamicCallMem1; rfl)
      (by unfold skimSecondSafeTransferDynamicWordsCall1; rfl) (by evm_ov),
    push1 ⟨31⟩, not, swap1, swap3, add, swap2,
    push1 ⟨32⟩, swap2, dup3, add, swap2, add, push2 ⟨6512⟩]
  have rd6512b := rd6539b.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [skimSecondSafeTransferDynamicBasePtr_add128_add32 out1,
    skimSecondSafeTransferDynamicRetPtr_add32 out1,
    show (⟨36⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨4⟩ by native_decide]
    at rd6512b
  have rd6543 := evm_run rd6512b with [
    jumpdest, push1 ⟨32⟩, dup4, lt, push2 ⟨6543⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd6575 := evm_run rd6543 with [
    jumpdest, push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub,
    dup1, not, dup3,
    raw mload 0
      (skimSecondSafeTransferDynamicTailSourceWord self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall1 out1) (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            UInt256_M_same_of_cover _ _
              (skimSecondSafeTransferDynamicWordsCall1_mul32_lt out1 hout1Size)
              (skimSecondSafeTransferDynamicWordsCall1_cover_base160 out1 hout1Size)]
        exact Nat.sub_self _)
      (skimSecondSafeTransferDynamicCallMem1_mload_base160 self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (UInt256_M_same_of_cover _ _
        (skimSecondSafeTransferDynamicWordsCall1_mul32_lt out1 hout1Size)
        (skimSecondSafeTransferDynamicWordsCall1_cover_base160 out1 hout1Size))
      (by evm_ov),
    and, dup2, dup5,
    raw mload
      (Cₘ (skimSecondSafeTransferDynamicWordsCall2 out1) -
        Cₘ (skimSecondSafeTransferDynamicWordsCall1 out1))
      ⟨0⟩ (skimSecondSafeTransferDynamicWordsCall2 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        unfold skimSecondSafeTransferDynamicWordsCall2
        rfl)
      (skimSecondSafeTransferDynamicCallMem1_mload_base228 self toWord
        prevValue value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (by unfold skimSecondSafeTransferDynamicWordsCall2; rfl)
      (by evm_ov),
    and, dup1, dup3, or, dup6,
    raw mstore 0
      (skimSecondSafeTransferDynamicCallMem2 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicWordsCall2 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            UInt256_M_same_of_cover _ _
              (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
              (skimSecondSafeTransferDynamicWordsCall2_cover_base228 out1 hout1Size)]
        exact Nat.sub_self _)
      (by
        unfold skimSecondSafeTransferDynamicCallMem2 skimSecondSafeTransferDynamicTailWord
          skimSafeTransferTailMask
        rfl)
      (UInt256_M_same_of_cover _ _
        (skimSecondSafeTransferDynamicWordsCall2_mul32_lt out1 hout1Size)
        (skimSecondSafeTransferDynamicWordsCall2_cover_base228 out1 hout1Size))
      (by evm_ov),
    pop, pop, pop, pop, pop, pop]
  have rd6593 := evm_run rd6575 with [
    swap1, pop, add, swap2, pop, pop, push1 ⟨0⟩, push1 ⟨64⟩,
    raw mload 0 (skimSecondSafeTransferDynamicCallPtr out1)
      (skimSecondSafeTransferDynamicWordsCall2 out1)
      (by native_decide)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ,
            UInt256_mload64_same_of_toNat_ge13 _
              (skimSecondSafeTransferDynamicWordsCall2_toNat_ge13 out1 hout1Size)]
        exact Nat.sub_self _)
      (skimSecondSafeTransferDynamicCallMem2_mload64 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
      (UInt256_mload64_same_of_toNat_ge13 _
        (skimSecondSafeTransferDynamicWordsCall2_toNat_ge13 out1 hout1Size))
      (by evm_ov),
    dup1, dup4, sub, dup2, push1 ⟨0⟩, dup7]
  obtain ⟨gasArg, rd6594⟩ := rd6593.gas (by native_decide) (by evm_ov)
  rw [skimSecondSafeTransferDynamicCallPtr_add68 out1,
    skimSecondSafeTransferDynamicRetEnd_sub_callPtr out1 hout1Size]
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
            (MachineState.M (skimSecondSafeTransferDynamicWordsCall2 out1).toNat
              (skimSecondSafeTransferDynamicCallPtr out1).toNat (⟨68⟩ : UInt256).toNat)
            (skimSecondSafeTransferDynamicCallPtr out1).toNat (⟨0⟩ : UInt256).toNat) =
          skimSecondSafeTransferDynamicWordsCall2 out1 := by
      simpa using skimSecondSafeTransferDynamicWordsCall2_callOutputSame out1 hout1Size
    rw [hlen, byteArray_write_len_zero, haw] at rd6595
    exact rd6595

end UniswapV2Pair
