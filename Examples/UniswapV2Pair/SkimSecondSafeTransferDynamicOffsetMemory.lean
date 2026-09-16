import Examples.UniswapV2Pair.MemorySteps
import Examples.UniswapV2Pair.SkimDynamicSecondRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dynamic-offset second `_safeTransfer` after nonempty first returndata -/

def skimSecondSafeTransferDynamicBasePtr (out1 : ByteArray) : UInt256 :=
  skimSafeTransferReturnDataPtr out1

def skimSecondSafeTransferDynamicCallPtr (out1 : ByteArray) : UInt256 :=
  skimSecondSafeTransferDynamicBasePtr out1 + ⟨164⟩

def skimSecondSafeTransferDynamicRetPtr (out1 : ByteArray) : UInt256 :=
  skimSecondSafeTransferDynamicBasePtr out1 + ⟨196⟩

def skimSecondSafeTransferDynamicRetEnd (out1 : ByteArray) : UInt256 :=
  skimSecondSafeTransferDynamicBasePtr out1 + ⟨232⟩

theorem skimSecondSafeTransferDynamicBasePtr_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    96 ≤ (skimSecondSafeTransferDynamicBasePtr out).toNat := by
  simpa [skimSecondSafeTransferDynamicBasePtr] using
    skimSafeTransferReturnDataPtr_toNat_ge out houtSize

theorem skimSecondSafeTransferDynamicBasePtr_toNat_le (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicBasePtr out).toNat ≤ 355 + out.size := by
  simpa [skimSecondSafeTransferDynamicBasePtr] using
    skimSafeTransferReturnDataPtr_toNat_le out houtSize

theorem skimSecondSafeTransferDynamicBasePtr_add_toNat (out : ByteArray) (n : ℕ)
    (houtSize : out.size < 2 ^ 255) (hn : n ≤ 512) :
    (skimSecondSafeTransferDynamicBasePtr out + UInt256.ofNat n).toNat =
      (skimSecondSafeTransferDynamicBasePtr out).toNat + n := by
  simpa [skimSecondSafeTransferDynamicBasePtr] using
    skimSafeTransferReturnDataPtr_add_ofNat_toNat out n houtSize hn

theorem skimSecondSafeTransferDynamicCallPtr_toNat (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicCallPtr out).toNat =
      (skimSecondSafeTransferDynamicBasePtr out).toNat + 164 := by
  simpa [skimSecondSafeTransferDynamicCallPtr] using
    skimSecondSafeTransferDynamicBasePtr_add_toNat out 164 houtSize (by norm_num)

theorem skimSecondSafeTransferDynamicRetPtr_toNat (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicRetPtr out).toNat =
      (skimSecondSafeTransferDynamicBasePtr out).toNat + 196 := by
  simpa [skimSecondSafeTransferDynamicRetPtr] using
    skimSecondSafeTransferDynamicBasePtr_add_toNat out 196 houtSize (by norm_num)

theorem skimSecondSafeTransferDynamicRetEnd_toNat (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicRetEnd out).toNat =
      (skimSecondSafeTransferDynamicBasePtr out).toNat + 232 := by
  simpa [skimSecondSafeTransferDynamicRetEnd] using
    skimSecondSafeTransferDynamicBasePtr_add_toNat out 232 houtSize (by norm_num)

theorem skimSecondSafeTransferDynamicBasePtr_add64_add36 (out : ByteArray) :
    skimSecondSafeTransferDynamicBasePtr out + (⟨64⟩ : UInt256) + ⟨36⟩ =
      skimSecondSafeTransferDynamicBasePtr out + ⟨100⟩ := by
  rw [u256_add_assoc]
  rw [show (⟨64⟩ : UInt256) + ⟨36⟩ = ⟨100⟩ by native_decide]

theorem skimSecondSafeTransferDynamicBasePtr_add64_add68 (out : ByteArray) :
    skimSecondSafeTransferDynamicBasePtr out + (⟨64⟩ : UInt256) + ⟨68⟩ =
      skimSecondSafeTransferDynamicBasePtr out + ⟨132⟩ := by
  rw [u256_add_assoc]
  rw [show (⟨64⟩ : UInt256) + ⟨68⟩ = ⟨132⟩ by native_decide]

theorem skimSecondSafeTransferDynamicBasePtr_add96_add32 (out : ByteArray) :
    (⟨32⟩ : UInt256) + (skimSecondSafeTransferDynamicBasePtr out + ⟨96⟩) =
      skimSecondSafeTransferDynamicBasePtr out + ⟨128⟩ := by
  rw [u256_add_comm (⟨32⟩ : UInt256) _]
  rw [u256_add_assoc]
  rw [show (⟨96⟩ : UInt256) + ⟨32⟩ = ⟨128⟩ by native_decide]

theorem skimSecondSafeTransferDynamicBasePtr_add128_add32 (out : ByteArray) :
    (⟨32⟩ : UInt256) + (skimSecondSafeTransferDynamicBasePtr out + ⟨128⟩) =
      skimSecondSafeTransferDynamicBasePtr out + ⟨160⟩ := by
  rw [u256_add_comm (⟨32⟩ : UInt256) _]
  rw [u256_add_assoc]
  rw [show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ by native_decide]

theorem skimSecondSafeTransferDynamicCallPtr_add32 (out : ByteArray) :
    (⟨32⟩ : UInt256) + skimSecondSafeTransferDynamicCallPtr out =
      skimSecondSafeTransferDynamicRetPtr out := by
  rw [skimSecondSafeTransferDynamicCallPtr, skimSecondSafeTransferDynamicRetPtr]
  rw [u256_add_comm (⟨32⟩ : UInt256) _]
  rw [u256_add_assoc]
  rw [show (⟨164⟩ : UInt256) + ⟨32⟩ = ⟨196⟩ by native_decide]

theorem skimSecondSafeTransferDynamicRetPtr_add32 (out : ByteArray) :
    (⟨32⟩ : UInt256) + skimSecondSafeTransferDynamicRetPtr out =
      skimSecondSafeTransferDynamicBasePtr out + ⟨228⟩ := by
  rw [skimSecondSafeTransferDynamicRetPtr]
  rw [u256_add_comm (⟨32⟩ : UInt256) _]
  rw [u256_add_assoc]
  rw [show (⟨196⟩ : UInt256) + ⟨32⟩ = ⟨228⟩ by native_decide]

theorem skimSecondSafeTransferDynamicCallPtr_add68 (out : ByteArray) :
    (⟨68⟩ : UInt256) + skimSecondSafeTransferDynamicCallPtr out =
      skimSecondSafeTransferDynamicRetEnd out := by
  rw [skimSecondSafeTransferDynamicCallPtr, skimSecondSafeTransferDynamicRetEnd]
  rw [u256_add_comm (⟨68⟩ : UInt256) _]
  rw [u256_add_assoc]
  rw [show (⟨164⟩ : UInt256) + ⟨68⟩ = ⟨232⟩ by native_decide]

theorem skimSecondSafeTransferDynamicRetEnd_sub_callPtr (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
      UInt256.sub (skimSecondSafeTransferDynamicRetEnd out)
        (skimSecondSafeTransferDynamicCallPtr out) =
      ⟨68⟩ := by
  apply u256_inj
  rw [usub_toNat]
  · rw [skimSecondSafeTransferDynamicRetEnd_toNat out houtSize,
      skimSecondSafeTransferDynamicCallPtr_toNat out houtSize]
    rw [show (⟨68⟩ : UInt256).toNat = 68 from rfl]
    omega
  · rw [skimSecondSafeTransferDynamicRetEnd_toNat out houtSize,
      skimSecondSafeTransferDynamicCallPtr_toNat out houtSize]
    omega

def skimSecondSafeTransferDynamicWords0 (out1 : ByteArray) : UInt256 :=
  skimSecondBalanceDynamicStaticcallWords out1

def skimSecondSafeTransferDynamicWordsMem2 (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWords0 out1).toNat
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨32⟩).toNat 32)

def skimSecondSafeTransferDynamicWordsMem3 (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsMem2 out1).toNat
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat 32)

def skimSecondSafeTransferDynamicWordsMem4 (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsMem3 out1).toNat
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat 32)

def skimSecondSafeTransferDynamicWordsCall0 (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsMem4 out1).toNat
    (skimSecondSafeTransferDynamicCallPtr out1).toNat 32)

def skimSecondSafeTransferDynamicWordsCall1 (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsCall0 out1).toNat
    (skimSecondSafeTransferDynamicRetPtr out1).toNat 32)

def skimSecondSafeTransferDynamicWordsCall2 (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsCall1 out1).toNat
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat 32)



theorem skimSecondSafeTransferDynamicBasePtr_window_lt (out : ByteArray)
    (n len : Nat) (houtSize : out.size < 2 ^ 255) (hn : n ≤ 512)
    (hlen : len ≤ 512) :
    (skimSecondSafeTransferDynamicBasePtr out + UInt256.ofNat n).toNat + len + 31 <
      UInt256.size := by
  rw [skimSecondSafeTransferDynamicBasePtr_add_toNat out n houtSize hn]
  have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_le out houtSize
  have hcap : 2 ^ 255 + 1410 < UInt256.size := by norm_num [UInt256.size]
  omega






theorem skimSecondBalanceDynamicStaticcallWords_mload64_ptr_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat
              (MachineState.M (skimSecondBalanceDynamicStaticcallWords out).toNat
                (⟨64⟩ : UInt256).toNat 32)).toNat
          (skimSafeTransferReturnDataPtr out).toNat 32) =
      skimSecondBalanceDynamicStaticcallWords out := by
  rw [skimSecondBalanceDynamicStaticcallWords_mload64_same out houtSize]
  apply UInt256_M_same_of_cover
  · exact skimSecondBalanceDynamicStaticcallWords_mul32_lt out houtSize
  · unfold skimSecondBalanceDynamicStaticcallWords
    have hmul := skimSecondBalanceDynamicStaticcallWords_M_mul32_lt out houtSize
    have hMlt :
        MachineState.M
            (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
              (skimSafeTransferReturnDataPtr out).toNat 36)
            (skimSafeTransferReturnDataPtr out).toNat 32 < UInt256.size := by
      have hnonneg :
          MachineState.M
              (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
                (skimSafeTransferReturnDataPtr out).toNat 36)
              (skimSafeTransferReturnDataPtr out).toNat 32 ≤
            MachineState.M
                (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
                  (skimSafeTransferReturnDataPtr out).toNat 36)
                (skimSafeTransferReturnDataPtr out).toNat 32 * 32 := by
        omega
      omega
    rw [UInt256.toNat_ofNat_of_lt hMlt]
    unfold MachineState.M
    have hceil :
        (skimSafeTransferReturnDataPtr out).toNat + 32 ≤
          (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32) * 32 := by
      have hmod := Nat.mod_lt ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31)
        (by norm_num : 0 < 32)
      have hdm := Nat.div_add_mod ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) 32
      omega
    have hleq :
        ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32 ≤
          max
            (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
              (skimSafeTransferReturnDataPtr out).toNat 36)
            (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32) :=
      Nat.le_max_right _ _
    exact le_trans hceil (Nat.mul_le_mul_right 32 hleq)

theorem skimSecondBalanceDynamicStaticcallWords_ptr_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M (skimSecondBalanceDynamicStaticcallWords out).toNat
          (skimSafeTransferReturnDataPtr out).toNat 32) =
      skimSecondBalanceDynamicStaticcallWords out := by
  have h := skimSecondBalanceDynamicStaticcallWords_mload64_ptr_same out houtSize
  rw [skimSecondBalanceDynamicStaticcallWords_mload64_same out houtSize] at h
  exact h

theorem skimSafeTransferReturnDataRounded_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    out.size ≤ (skimSafeTransferReturnDataRounded out).toNat := by
  unfold skimSafeTransferReturnDataRounded UInt256.land UInt256.toNat
  have hsum : (UInt256.ofNat out.size + ⟨63⟩ : UInt256).toNat =
      out.size + 63 := by
    rw [uadd_toNat]
    have hof : (UInt256.ofNat out.size).toNat = out.size := by
      exact UInt256.toNat_ofNat_of_lt (by
        have hpow : 2 ^ 255 < UInt256.size := by norm_num [UInt256.size]
        omega)
    rw [hof]
    have hlt : out.size + 63 < UInt256.size := by
      have hpow : 2 ^ 255 + 63 < UInt256.size := by norm_num [UInt256.size]
      omega
    exact Nat.mod_eq_of_lt hlt
  change out.size ≤ (Fin.land ((UInt256.ofNat out.size + ⟨63⟩ : UInt256).val)
      (UInt256.lnot ⟨31⟩).val).val
  rw [Fin.land]
  change out.size ≤
    (Nat.land (UInt256.ofNat out.size + ⟨63⟩ : UInt256).toNat
      (UInt256.lnot ⟨31⟩).toNat) % UInt256.size
  rw [hsum]
  have hlnot : (UInt256.lnot ⟨31⟩).toNat = 2 ^ 256 - 2 ^ 5 := by
    native_decide
  change out.size ≤ (Nat.land (out.size + 63) (UInt256.lnot ⟨31⟩).toNat) %
    UInt256.size
  rw [hlnot]
  rw [natLandClearLow (out.size + 63) 5 (by norm_num)]
  · have hltmod : ((out.size + 63) / 2 ^ 5) * 2 ^ 5 < UInt256.size := by
      have hle : ((out.size + 63) / 2 ^ 5) * 2 ^ 5 ≤ out.size + 63 :=
        Nat.div_mul_le_self _ _
      have hpow : 2 ^ 255 + 63 < UInt256.size := by norm_num [UInt256.size]
      omega
    rw [Nat.mod_eq_of_lt hltmod]
    have hdiv : out.size ≤ ((out.size + 63) / 32) * 32 := by
      have hmod := Nat.mod_lt (out.size + 63) (by norm_num : 0 < 32)
      have hdm := Nat.div_add_mod (out.size + 63) 32
      omega
    simpa [show 2 ^ 5 = 32 by norm_num] using hdiv
  · have hpow : 2 ^ 255 + 63 < 2 ^ 256 := by norm_num
    omega

theorem skimSafeTransferReturnDataRounded_nonempty_ge64 (out : ByteArray)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    64 ≤ (skimSafeTransferReturnDataRounded out).toNat := by
  unfold skimSafeTransferReturnDataRounded UInt256.land UInt256.toNat
  have hsum : (UInt256.ofNat out.size + ⟨63⟩ : UInt256).toNat =
      out.size + 63 := by
    rw [uadd_toNat]
    have hof : (UInt256.ofNat out.size).toNat = out.size := by
      exact UInt256.toNat_ofNat_of_lt (by
        have hpow : 2 ^ 255 < UInt256.size := by norm_num [UInt256.size]
        omega)
    rw [hof]
    have hlt : out.size + 63 < UInt256.size := by
      have hpow : 2 ^ 255 + 63 < UInt256.size := by norm_num [UInt256.size]
      omega
    exact Nat.mod_eq_of_lt hlt
  change 64 ≤ (Fin.land ((UInt256.ofNat out.size + ⟨63⟩ : UInt256).val)
      (UInt256.lnot ⟨31⟩).val).val
  rw [Fin.land]
  change 64 ≤
    (Nat.land (UInt256.ofNat out.size + ⟨63⟩ : UInt256).toNat
      (UInt256.lnot ⟨31⟩).toNat) % UInt256.size
  rw [hsum]
  have hlnot : (UInt256.lnot ⟨31⟩).toNat = 2 ^ 256 - 2 ^ 5 := by
    native_decide
  change 64 ≤ (Nat.land (out.size + 63) (UInt256.lnot ⟨31⟩).toNat) %
    UInt256.size
  rw [hlnot]
  rw [natLandClearLow (out.size + 63) 5 (by norm_num)]
  · have hltmod : ((out.size + 63) / 2 ^ 5) * 2 ^ 5 < UInt256.size := by
      have hle : ((out.size + 63) / 2 ^ 5) * 2 ^ 5 ≤ out.size + 63 :=
        Nat.div_mul_le_self _ _
      have hpow : 2 ^ 255 + 63 < UInt256.size := by norm_num [UInt256.size]
      omega
    rw [Nat.mod_eq_of_lt hltmod]
    have hpos : 1 ≤ out.size := Nat.pos_of_ne_zero houtNe
    have hdiv : 64 ≤ ((out.size + 63) / 32) * 32 := by
      have hle : 64 ≤ out.size + 63 := by omega
      have hq : 2 ≤ (out.size + 63) / 32 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 32)]
        exact hle
      omega
    simpa [show 2 ^ 5 = 32 by norm_num] using hdiv
  · have hpow : 2 ^ 255 + 63 < 2 ^ 256 := by norm_num
    omega

theorem skimSafeTransferReturnDataMem_size_le_ptr_add32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataMem self o toWord value out).size ≤
      (skimSafeTransferReturnDataPtr out).toNat + 32 := by
  rw [skimSafeTransferReturnDataMem_size_of_nonempty self toWord value
    ho32 hoSize houtNe]
  have hroundGe := skimSafeTransferReturnDataRounded_ge out houtSize
  have hround64 := skimSafeTransferReturnDataRounded_nonempty_ge64 out houtNe houtSize
  have hroundLe := skimSafeTransferReturnDataRounded_le out houtSize
  have hptr : (skimSafeTransferReturnDataPtr out).toNat =
      292 + (skimSafeTransferReturnDataRounded out).toNat := by
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
  split
  · rw [hptr]
    omega
  · rw [hptr]
    omega

private theorem byteArray_zeroes_size_le (n : Nat) :
    (ffi.ByteArray.zeroes n).size ≤ n :=
  (ByteArray_zeroes_size n).le

private theorem byteArray_copySlice_size_le
    (source destination : ByteArray) (sourceOffset destinationOffset length : Nat) :
    (source.copySlice sourceOffset destination destinationOffset length).size ≤
      max destination.size (destinationOffset + length) := by
  rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  rw [show source.data.size = source.size from rfl,
    show destination.data.size = destination.size from rfl]
  omega

theorem byteArray_write_size_le
    (source destination : ByteArray) (sourceOffset destinationOffset length : Nat) :
    (source.write sourceOffset destination destinationOffset length).size ≤
      max destination.size (destinationOffset + length) := by
  unfold ByteArray.write
  by_cases hlen : length = 0
  · simp [hlen]
  · simp [hlen]
    by_cases hsrc : sourceOffset ≥ source.size
    · simp [hsrc]
      have hcopy := byteArray_copySlice_size_le
        (ffi.ByteArray.zeroes
          (min length (destination.size - destinationOffset)))
        destination 0 (min destinationOffset destination.size)
        (min length (destination.size - destinationOffset))
      have hbound :
          max destination.size
              (min destinationOffset destination.size +
                min length (destination.size - destinationOffset)) ≤
            max destination.size (destinationOffset + length) := by
        omega
      exact le_max_iff.mp (le_trans hcopy hbound)
    · simp [hsrc]
      have hpad :
          (ffi.ByteArray.zeroes
              (destinationOffset - destination.size)).size ≤
            destinationOffset - destination.size :=
        byteArray_zeroes_size_le _
      have hdest :
          (destination ++ ffi.ByteArray.zeroes
              (destinationOffset - destination.size)).size ≤
            max destination.size (destinationOffset + length) := by
        rw [ByteArray.size_append]
        omega
      have hcopy := byteArray_copySlice_size_le
        (source ++ ffi.ByteArray.zeroes
          (min destination.size (destinationOffset + length) -
            (destinationOffset + min length (source.size - sourceOffset))))
        (destination ++ ffi.ByteArray.zeroes
          (destinationOffset - destination.size))
        sourceOffset destinationOffset
        (min length (source.size - sourceOffset) +
          (min destination.size (destinationOffset + length) -
            (destinationOffset + min length (source.size - sourceOffset))))
      have hwriteEnd :
          destinationOffset +
              (min length (source.size - sourceOffset) +
                (min destination.size (destinationOffset + length) -
                  (destinationOffset + min length (source.size - sourceOffset)))) ≤
            max destination.size (destinationOffset + length) := by
        omega
      exact le_max_iff.mp (le_trans hcopy (max_le hdest hwriteEnd))

theorem skimSecondSafeTransferDynamicWords0_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicWords0 out).toNat * 32 < UInt256.size := by
  simpa [skimSecondSafeTransferDynamicWords0] using
    skimSecondBalanceDynamicStaticcallWords_mul32_lt out houtSize

theorem skimSecondSafeTransferDynamicWords0_toNat_ge13 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondSafeTransferDynamicWords0 out).toNat := by
  simpa [skimSecondSafeTransferDynamicWords0] using
    skimSecondBalanceDynamicStaticcallWords_toNat_ge out houtSize

theorem skimSecondSafeTransferDynamicWordsMem2_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicWordsMem2 out).toNat * 32 < UInt256.size := by
  unfold skimSecondSafeTransferDynamicWordsMem2
  exact UInt256_ofNat_M_mul32_lt _ _
    (skimSecondSafeTransferDynamicWords0_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 32 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsMem2_toNat_ge13 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondSafeTransferDynamicWordsMem2 out).toNat := by
  unfold skimSecondSafeTransferDynamicWordsMem2
  exact UInt256_ofNat_M_toNat_ge _ _
    (skimSecondSafeTransferDynamicWords0_toNat_ge13 out houtSize)
    (skimSecondSafeTransferDynamicWords0_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 32 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsMem3_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicWordsMem3 out).toNat * 32 < UInt256.size := by
  unfold skimSecondSafeTransferDynamicWordsMem3
  exact UInt256_ofNat_M_mul32_lt _ _
    (skimSecondSafeTransferDynamicWordsMem2_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 100 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsMem3_toNat_ge13 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondSafeTransferDynamicWordsMem3 out).toNat := by
  unfold skimSecondSafeTransferDynamicWordsMem3
  exact UInt256_ofNat_M_toNat_ge _ _
    (skimSecondSafeTransferDynamicWordsMem2_toNat_ge13 out houtSize)
    (skimSecondSafeTransferDynamicWordsMem2_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 100 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsMem4_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicWordsMem4 out).toNat * 32 < UInt256.size := by
  unfold skimSecondSafeTransferDynamicWordsMem4
  exact UInt256_ofNat_M_mul32_lt _ _
    (skimSecondSafeTransferDynamicWordsMem3_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 132 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsMem4_toNat_ge13 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondSafeTransferDynamicWordsMem4 out).toNat := by
  unfold skimSecondSafeTransferDynamicWordsMem4
  exact UInt256_ofNat_M_toNat_ge _ _
    (skimSecondSafeTransferDynamicWordsMem3_toNat_ge13 out houtSize)
    (skimSecondSafeTransferDynamicWordsMem3_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 132 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsCall0_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicWordsCall0 out).toNat * 32 < UInt256.size := by
  unfold skimSecondSafeTransferDynamicWordsCall0 skimSecondSafeTransferDynamicCallPtr
  exact UInt256_ofNat_M_mul32_lt _ _
    (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 164 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsCall0_toNat_ge13 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondSafeTransferDynamicWordsCall0 out).toNat := by
  unfold skimSecondSafeTransferDynamicWordsCall0 skimSecondSafeTransferDynamicCallPtr
  exact UInt256_ofNat_M_toNat_ge _ _
    (skimSecondSafeTransferDynamicWordsMem4_toNat_ge13 out houtSize)
    (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 164 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsCall1_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicWordsCall1 out).toNat * 32 < UInt256.size := by
  unfold skimSecondSafeTransferDynamicWordsCall1 skimSecondSafeTransferDynamicRetPtr
  exact UInt256_ofNat_M_mul32_lt _ _
    (skimSecondSafeTransferDynamicWordsCall0_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 196 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsCall1_toNat_ge13 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondSafeTransferDynamicWordsCall1 out).toNat := by
  unfold skimSecondSafeTransferDynamicWordsCall1 skimSecondSafeTransferDynamicRetPtr
  exact UInt256_ofNat_M_toNat_ge _ _
    (skimSecondSafeTransferDynamicWordsCall0_toNat_ge13 out houtSize)
    (skimSecondSafeTransferDynamicWordsCall0_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 196 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsCall2_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicWordsCall2 out).toNat * 32 < UInt256.size := by
  unfold skimSecondSafeTransferDynamicWordsCall2
  exact UInt256_ofNat_M_mul32_lt _ _
    (skimSecondSafeTransferDynamicWordsCall1_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 228 32
        houtSize (by norm_num) (by norm_num))

theorem skimSecondSafeTransferDynamicWordsCall2_toNat_ge13 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondSafeTransferDynamicWordsCall2 out).toNat := by
  unfold skimSecondSafeTransferDynamicWordsCall2
  exact UInt256_ofNat_M_toNat_ge _ _
    (skimSecondSafeTransferDynamicWordsCall1_toNat_ge13 out houtSize)
    (skimSecondSafeTransferDynamicWordsCall1_mul32_lt out houtSize)
    (by
      simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 228 32
        houtSize (by norm_num) (by norm_num))

noncomputable def skimSecondSafeTransferDynamicMem0
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩)).write 0
    (skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2) 64 32

theorem skimSecondSafeTransferDynamicMem0_size_ge_base_add32
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
      (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2).size := by
  unfold skimSecondSafeTransferDynamicMem0
  rw [write32_eq _ _ 64 (by rw [toByteArray_size])
      (by
        have hsize :=
          skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
            self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        have hsize' :
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
              (skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2).size := by
          simpa [skimSecondSafeTransferDynamicBasePtr] using hsize
        have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
        omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  have hsize :=
    skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
      self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  have hsize' :
      (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
        (skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2).size := by
    simpa [skimSecondSafeTransferDynamicBasePtr] using hsize
  have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
  omega

theorem skimSecondSafeTransferDynamicMem0_size_ge96
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    96 ≤ (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2).size := by
  have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
  have hsize :=
    skimSecondSafeTransferDynamicMem0_size_ge_base_add32 self toWord prevValue
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  omega

theorem skimSecondSafeTransferDynamicMem0_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2).readWithPadding
        64 32 =
      UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩) := by
  unfold skimSecondSafeTransferDynamicMem0
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
      (by
        have hsize :=
          skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
            self toWord prevValue ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        have hsize' :
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
              (skimSecondBalanceDynamicStaticcallMem self o toWord prevValue out1 out2).size := by
          simpa [skimSecondSafeTransferDynamicBasePtr] using hsize
        have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
        omega)]
  rw [show (UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩)).extract
      0 32 =
      UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩) by
    rw [show 32 =
      (UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

noncomputable def skimSecondSafeTransferDynamicMem1
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0
    (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2)
    (skimSecondSafeTransferDynamicBasePtr out1).toNat 32

noncomputable def skimSecondSafeTransferDynamicMem2
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray skimSafeTransferSignatureWord).write 0
    (skimSecondSafeTransferDynamicMem1 self o toWord prevValue out1 out2)
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨32⟩).toNat 32

theorem skimSecondSafeTransferDynamicMem2_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2).readWithPadding
        64 32 =
      UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩) := by
  unfold skimSecondSafeTransferDynamicMem2
  rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨32⟩).toNat
      64 (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicMem1
    rw [write32_read_below _ _ (skimSecondSafeTransferDynamicBasePtr out1).toNat
        64 (by rw [toByteArray_size])]
    · exact skimSecondSafeTransferDynamicMem0_read64 self toWord prevValue
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    · have hbase :=
        skimSecondSafeTransferDynamicMem0_size_ge_base_add32 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
    · have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      omega
  · unfold skimSecondSafeTransferDynamicMem1
    have hptr32 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨32⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 32 hout1Size (by norm_num)
    rw [hptr32]
    exact toByteArray_write_size_ge_off_add32 (⟨25⟩ : UInt256)
      (skimSecondSafeTransferDynamicMem0 self o toWord prevValue out1 out2)
      (skimSecondSafeTransferDynamicBasePtr out1).toNat
      (by
        have hbase :=
          skimSecondSafeTransferDynamicMem0_size_ge_base_add32 self toWord prevValue
            ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        exact lt_usize _ (by omega))
  · have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    have hptr32 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨32⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 32 hout1Size (by norm_num)
    rw [hptr32]
    omega

theorem skimSecondSafeTransferDynamicMem2_size_ge_base_add64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 ≤
      (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2).size := by
  unfold skimSecondSafeTransferDynamicMem2
  have hptr32 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨32⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out1 32 hout1Size (by norm_num)
  rw [hptr32]
  exact toByteArray_write_size_ge_off_add32 skimSafeTransferSignatureWord
    (skimSecondSafeTransferDynamicMem1 self o toWord prevValue out1 out2)
    ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 32)
    (by
      have hmem1 : (skimSecondSafeTransferDynamicBasePtr out1).toNat + 32 ≤
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
      exact lt_usize _ (by omega))

theorem skimSecondSafeTransferDynamicWordsMem2_mload64_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsMem2 out).toNat
      (⟨64⟩ : UInt256).toNat 32) =
      skimSecondSafeTransferDynamicWordsMem2 out :=
  UInt256_mload64_same_of_toNat_ge13 _
    (skimSecondSafeTransferDynamicWordsMem2_toNat_ge13 out houtSize)

theorem skimSecondSafeTransferDynamicMem2_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondSafeTransferDynamicWordsMem2 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondSafeTransferDynamicWordsMem2 out1)
    (v := skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩)
    (by
      have hsize :=
        skimSecondSafeTransferDynamicMem2_size_ge_base_add64 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      change 64 < (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2).size
      omega)
    (UInt256_mload64_haw_of_toNat_ge13 _
      (skimSecondSafeTransferDynamicWordsMem2_toNat_ge13 out1 hout1Size)
      (skimSecondSafeTransferDynamicWordsMem2_mul32_lt out1 hout1Size))
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from rfl] using
        skimSecondSafeTransferDynamicMem2_read64 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

noncomputable def skimSecondSafeTransferDynamicMem3
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).write 0
    (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2)
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat 32

noncomputable def skimSecondSafeTransferDynamicMem4
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0
    (skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2)
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat 32

theorem skimSecondSafeTransferDynamicMem3_size_ge_base_add132
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 ≤
      (skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2).size := by
  unfold skimSecondSafeTransferDynamicMem3
  have h100 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨100⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 100 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out1 100 hout1Size (by norm_num)
  rw [h100]
  exact toByteArray_write_size_ge_off_add32 (UInt256.land solcAddrMask toWord)
    (skimSecondSafeTransferDynamicMem2 self o toWord prevValue out1 out2)
    ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 100)
    (by
      have hmem2 :=
        skimSecondSafeTransferDynamicMem2_size_ge_base_add64 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      exact lt_usize _ (by omega))

theorem skimSecondSafeTransferDynamicMem4_size_ge_base_add164
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 ≤
      (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).size := by
  unfold skimSecondSafeTransferDynamicMem4
  have h132 :
      (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size (by norm_num)
  rw [h132]
  exact toByteArray_write_size_ge_off_add32 value
    (skimSecondSafeTransferDynamicMem3 self o toWord prevValue out1 out2)
    ((skimSecondSafeTransferDynamicBasePtr out1).toNat + 132)
    (by
      have hmem3 :=
        skimSecondSafeTransferDynamicMem3_size_ge_base_add132 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      exact lt_usize _ (by omega))

theorem skimSecondSafeTransferDynamicMem4_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).readWithPadding
        64 32 =
      UInt256.toByteArray (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩) := by
  unfold skimSecondSafeTransferDynamicMem4
  rw [toByteArray_write_read_below_of_gap value _
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨132⟩).toNat 64]
  · unfold skimSecondSafeTransferDynamicMem3
    rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask toWord) _
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨100⟩).toNat 64]
    · exact skimSecondSafeTransferDynamicMem2_read64 self toWord prevValue
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    · have hsize :=
        skimSecondSafeTransferDynamicMem2_size_ge_base_add64 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      omega
    · have h100 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨100⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 100 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 100 hout1Size (by norm_num)
      rw [h100]
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      omega
    · have h100 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨100⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 100 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 100 hout1Size (by norm_num)
      rw [h100]
      have hsize :=
        skimSecondSafeTransferDynamicMem2_size_ge_base_add64 self toWord prevValue
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      exact lt_usize _ (by omega)
  · have hsize :=
      skimSecondSafeTransferDynamicMem3_size_ge_base_add132 self toWord prevValue
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega
  · have h132 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size (by norm_num)
    rw [h132]
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega
  · have h132 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨132⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 132 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 132 hout1Size (by norm_num)
    rw [h132]
    have hsize :=
      skimSecondSafeTransferDynamicMem3_size_ge_base_add132 self toWord prevValue
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    exact lt_usize _ (by omega)

theorem skimSecondSafeTransferDynamicWordsMem4_mload64_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsMem4 out).toNat
      (⟨64⟩ : UInt256).toNat 32) =
      skimSecondSafeTransferDynamicWordsMem4 out :=
  UInt256_mload64_same_of_toNat_ge13 _
    (skimSecondSafeTransferDynamicWordsMem4_toNat_ge13 out houtSize)

theorem skimSecondSafeTransferDynamicMem4_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondSafeTransferDynamicWordsMem4 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondSafeTransferDynamicWordsMem4 out1)
    (v := skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩)
    (by
      have hsize :=
        skimSecondSafeTransferDynamicMem4_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      change 64 < (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value).size
      omega)
    (UInt256_mload64_haw_of_toNat_ge13 _
      (skimSecondSafeTransferDynamicWordsMem4_toNat_ge13 out1 hout1Size)
      (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out1 hout1Size))
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from rfl] using
        skimSecondSafeTransferDynamicMem4_read64 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

noncomputable def skimSecondSafeTransferDynamicMem5
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨68⟩ : UInt256)).write 0
    (skimSecondSafeTransferDynamicMem4 self o toWord prevValue out1 out2 value)
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat 32

noncomputable def skimSecondSafeTransferDynamicMem6
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : ByteArray :=
  (UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1)).write 0
    (skimSecondSafeTransferDynamicMem5 self o toWord prevValue out1 out2 value) 64 32

theorem skimSecondSafeTransferDynamicMem5_size_ge_base_add164
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 ≤
      (skimSecondSafeTransferDynamicMem5 self o toWord prevValue out1 out2 value).size := by
  unfold skimSecondSafeTransferDynamicMem5
  rw [write32_eq _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat
      (by rw [toByteArray_size])]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    have hmem4 :=
      skimSecondSafeTransferDynamicMem4_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega
  · have h64 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size (by norm_num)
    rw [h64]
    have hmem4 :=
      skimSecondSafeTransferDynamicMem4_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega

theorem skimSecondSafeTransferDynamicMem6_size_ge_base_add164
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 ≤
      (skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value).size := by
  unfold skimSecondSafeTransferDynamicMem6
  rw [write32_eq _ _ 64 (by rw [toByteArray_size])]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    have hmem5 :=
      skimSecondSafeTransferDynamicMem5_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    rw [Nat.min_eq_left (by omega : 64 ≤
        (skimSecondSafeTransferDynamicMem5 self o toWord prevValue out1 out2 value).size)]
    rw [Nat.min_eq_left (by norm_num : 32 ≤ 32)]
    rw [Nat.min_self]
    omega
  · have hmem5 :=
      skimSecondSafeTransferDynamicMem5_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega

theorem skimSecondSafeTransferDynamicWordsMem4_cover_base96 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicBasePtr out + (⟨96⟩ : UInt256)).toNat + 32 ≤
      (skimSecondSafeTransferDynamicWordsMem4 out).toNat * 32 := by
  have hcover132 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨132⟩ : UInt256)).toNat + 32 ≤
        (skimSecondSafeTransferDynamicWordsMem4 out).toNat * 32 := by
    unfold skimSecondSafeTransferDynamicWordsMem4
    exact UInt256_ofNat_M_covers _ _
      (skimSecondSafeTransferDynamicWordsMem3_mul32_lt out houtSize)
      (by
        simpa using skimSecondSafeTransferDynamicBasePtr_window_lt out 132 32
          houtSize (by norm_num) (by norm_num))
  have h96 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨96⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out).toNat + 96 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out 96 houtSize (by norm_num)
  have h132 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨132⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out).toNat + 132 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out 132 houtSize (by norm_num)
  rw [h96]
  rw [h132] at hcover132
  omega

theorem skimSecondSafeTransferDynamicWordsMem4_mload_base96_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsMem4 out).toNat
      (skimSecondSafeTransferDynamicBasePtr out + ⟨96⟩).toNat 32) =
      skimSecondSafeTransferDynamicWordsMem4 out :=
  UInt256_M_same_of_cover _ _
    (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out houtSize)
    (skimSecondSafeTransferDynamicWordsMem4_cover_base96 out houtSize)

noncomputable def skimSecondSafeTransferDynamicWord96
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value)
        |>.readWithPadding (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat 32))

theorem skimSecondSafeTransferDynamicMem6_mload_base96
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat ≥
          (skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩) ≥
          skimSecondSafeTransferDynamicWordsMem4 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value).readWithPadding
          (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat 32))) =
      skimSecondSafeTransferDynamicWord96 self o toWord prevValue out1 out2 value := by
  rw [if_neg]
  · rfl
  · rw [not_or]
    constructor
    · have h96 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
      rw [h96]
      have hsize :=
        skimSecondSafeTransferDynamicMem6_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
    · exact UInt256_mload_haw_of_cover _ _
        (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out1 hout1Size)
        (skimSecondSafeTransferDynamicWordsMem4_cover_base96 out1 hout1Size)

theorem skimSecondSafeTransferDynamicMem6_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value).readWithPadding
        64 32 =
      UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1) := by
  unfold skimSecondSafeTransferDynamicMem6
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])]
  · rw [show (UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1)).extract 0 32 =
        UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1) by
      rw [show 32 = (UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1)).size by
        rw [toByteArray_size]]
      exact byteArray_extract_self _]
  · have hmem5 :=
      skimSecondSafeTransferDynamicMem5_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega

noncomputable def skimSecondSafeTransferDynamicPatchedSelectorWord
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft transferSelectorWord ⟨224⟩)
    (UInt256.land skimSafeTransferSelectorPatchMask
      (skimSecondSafeTransferDynamicWord96 self o toWord prevValue out1 out2 value))

noncomputable def skimSecondSafeTransferDynamicMem7
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value))
    |>.write 0
      (skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat 32

theorem skimSecondSafeTransferDynamicWordsMem4_cover_base64 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferDynamicBasePtr out + (⟨64⟩ : UInt256)).toNat + 32 ≤
      (skimSecondSafeTransferDynamicWordsMem4 out).toNat * 32 := by
  have hcover := skimSecondSafeTransferDynamicWordsMem4_cover_base96 out houtSize
  have h64 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨64⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out).toNat + 64 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out 64 houtSize (by norm_num)
  have h96 :
      (skimSecondSafeTransferDynamicBasePtr out + (⟨96⟩ : UInt256)).toNat =
        (skimSecondSafeTransferDynamicBasePtr out).toNat + 96 := by
    simpa using
      skimSecondSafeTransferDynamicBasePtr_add_toNat out 96 houtSize (by norm_num)
  rw [h64]
  rw [h96] at hcover
  omega

theorem skimSecondSafeTransferDynamicWordsMem4_mload_base64_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (skimSecondSafeTransferDynamicWordsMem4 out).toNat
      (skimSecondSafeTransferDynamicBasePtr out + ⟨64⟩).toNat 32) =
      skimSecondSafeTransferDynamicWordsMem4 out :=
  UInt256_M_same_of_cover _ _
    (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out houtSize)
    (skimSecondSafeTransferDynamicWordsMem4_cover_base64 out houtSize)

theorem skimSecondSafeTransferDynamicMem7_size_ge_base_add164
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicBasePtr out1).toNat + 164 ≤
      (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size := by
  unfold skimSecondSafeTransferDynamicMem7
  rw [write32_eq _ _ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat
      (by rw [toByteArray_size])]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    have hmem6 :=
      skimSecondSafeTransferDynamicMem6_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    have h96 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
    rw [h96]
    rw [Nat.min_eq_left (by omega : (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 ≤
        (skimSecondSafeTransferDynamicMem6 self o toWord prevValue out1 out2 value).size)]
    rw [Nat.min_eq_left (by norm_num : 32 ≤ 32)]
    rw [Nat.min_self]
    omega
  · have h96 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
    rw [h96]
    have hmem6 :=
      skimSecondSafeTransferDynamicMem6_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega

theorem skimSecondSafeTransferDynamicMem7_read64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).readWithPadding
        64 32 =
      UInt256.toByteArray (skimSecondSafeTransferDynamicCallPtr out1) := by
  unfold skimSecondSafeTransferDynamicMem7
  rw [write32_read_below _ _
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat 64
      (by rw [toByteArray_size])]
  · exact skimSecondSafeTransferDynamicMem6_read64 self toWord prevValue value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
  · have h96 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
    rw [h96]
    have hmem6 :=
      skimSecondSafeTransferDynamicMem6_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega
  · have h96 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
    rw [h96]
    have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
    omega

theorem skimSecondSafeTransferDynamicMem7_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondSafeTransferDynamicWordsMem4 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSecondSafeTransferDynamicCallPtr out1 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondSafeTransferDynamicWordsMem4 out1)
    (v := skimSecondSafeTransferDynamicCallPtr out1)
    (by
      have hsize :=
        skimSecondSafeTransferDynamicMem7_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      change 64 < (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size
      omega)
    (UInt256_mload64_haw_of_toNat_ge13 _
      (skimSecondSafeTransferDynamicWordsMem4_toNat_ge13 out1 hout1Size)
      (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out1 hout1Size))
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from rfl] using
        skimSecondSafeTransferDynamicMem7_read64 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

theorem skimSecondSafeTransferDynamicMem7_read_base64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat 32 =
      UInt256.toByteArray (⟨68⟩ : UInt256) := by
  unfold skimSecondSafeTransferDynamicMem7
  rw [write32_read_below _ _
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat
      (by rw [toByteArray_size])]
  · unfold skimSecondSafeTransferDynamicMem6
    rw [write32_read_above _ _ 64
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat
        (by rw [toByteArray_size])]
    · unfold skimSecondSafeTransferDynamicMem5
      rw [write32_read_back _ _
          (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat
          (by rw [toByteArray_size])]
      · rw [show (UInt256.toByteArray (⟨68⟩ : UInt256)).extract 0 32 =
            UInt256.toByteArray (⟨68⟩ : UInt256) by
          rw [show 32 = (UInt256.toByteArray (⟨68⟩ : UInt256)).size by
            rw [toByteArray_size]]
          exact byteArray_extract_self _]
      · have h64 :
            (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
              (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
          simpa using
            skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size (by norm_num)
        rw [h64]
        have hmem4 :=
          skimSecondSafeTransferDynamicMem4_size_ge_base_add164 self toWord prevValue value
            ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
        omega
    · have hmem5 :=
        skimSecondSafeTransferDynamicMem5_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      omega
    · have h64 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size (by norm_num)
      rw [h64]
      have hptr := skimSecondSafeTransferDynamicBasePtr_toNat_ge out1 hout1Size
      omega
    · have h64 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size (by norm_num)
      rw [h64]
      have hmem5 :=
        skimSecondSafeTransferDynamicMem5_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
  · have h96 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
    rw [h96]
    have hmem6 :=
      skimSecondSafeTransferDynamicMem6_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega
  · have h64 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size (by norm_num)
    have h96 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
    rw [h64, h96]

theorem skimSecondSafeTransferDynamicMem7_mload_base64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat ≥
          (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩) ≥
          skimSecondSafeTransferDynamicWordsMem4 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).readWithPadding
          (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩).toNat 32))) =
      ⟨68⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (skimSecondSafeTransferDynamicBasePtr out1 + ⟨64⟩))
    (aw := skimSecondSafeTransferDynamicWordsMem4 out1) (v := (⟨68⟩ : UInt256))
    (by
      have h64 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨64⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 64 hout1Size (by norm_num)
      rw [h64]
      have hsize :=
        skimSecondSafeTransferDynamicMem7_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      change (skimSecondSafeTransferDynamicBasePtr out1).toNat + 64 <
        (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size
      omega)
    (UInt256_mload_haw_of_cover _ _
      (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out1 hout1Size)
      (skimSecondSafeTransferDynamicWordsMem4_cover_base64 out1 hout1Size))
    (by
      exact skimSecondSafeTransferDynamicMem7_read_base64
        (self := self) (o := o) (toWord := toWord) (prevValue := prevValue)
        (out1 := out1) (out2 := out2) (value := value)
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

theorem skimSecondSafeTransferDynamicMem7_read_base96
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).readWithPadding
        (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat 32 =
      UInt256.toByteArray
        (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value) := by
  unfold skimSecondSafeTransferDynamicMem7
  rw [write32_read_back _ _
      (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat
      (by rw [toByteArray_size])]
  · rw [show (UInt256.toByteArray
          (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value)).extract
          0 32 =
        UInt256.toByteArray
          (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value) by
      rw [show 32 =
          (UInt256.toByteArray
            (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value)).size by
        rw [toByteArray_size]]
      exact byteArray_extract_self _]
  · have h96 :
        (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
          (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
      simpa using
        skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
    rw [h96]
    have hmem6 :=
      skimSecondSafeTransferDynamicMem6_size_ge_base_add164 self toWord prevValue value
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega

theorem skimSecondSafeTransferDynamicMem7_mload_base96
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out1 out2 : ByteArray}
    (value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat ≥
          (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size
        ∨ (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩) ≥
          skimSecondSafeTransferDynamicWordsMem4 out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
       ((skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).readWithPadding
         (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩).toNat 32))) =
      skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value := by
  exact mloadWordValue_of_readWithPadding
    (off := (skimSecondSafeTransferDynamicBasePtr out1 + ⟨96⟩))
    (aw := skimSecondSafeTransferDynamicWordsMem4 out1)
    (v := skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value)
    (by
      have h96 :
          (skimSecondSafeTransferDynamicBasePtr out1 + (⟨96⟩ : UInt256)).toNat =
            (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 := by
        simpa using
          skimSecondSafeTransferDynamicBasePtr_add_toNat out1 96 hout1Size (by norm_num)
      rw [h96]
      have hsize :=
        skimSecondSafeTransferDynamicMem7_size_ge_base_add164 self toWord prevValue value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      change (skimSecondSafeTransferDynamicBasePtr out1).toNat + 96 <
        (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value).size
      omega)
    (UInt256_mload_haw_of_cover _ _
      (skimSecondSafeTransferDynamicWordsMem4_mul32_lt out1 hout1Size)
      (skimSecondSafeTransferDynamicWordsMem4_cover_base96 out1 hout1Size))
    (by
      exact skimSecondSafeTransferDynamicMem7_read_base96
        (self := self) (o := o) (toWord := toWord) (prevValue := prevValue)
        (out1 := out1) (out2 := out2) (value := value)
        ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

noncomputable def skimSecondSafeTransferDynamicCallMem0
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferDynamicPatchedSelectorWord self o toWord prevValue out1 out2 value))
    |>.write 0
      (skimSecondSafeTransferDynamicMem7 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicCallPtr out1).toNat 32

noncomputable def skimSecondSafeTransferDynamicCopyWord1
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value)
        |>.readWithPadding (skimSecondSafeTransferDynamicBasePtr out1 + ⟨128⟩).toNat 32))

noncomputable def skimSecondSafeTransferDynamicCallMem1
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferDynamicCopyWord1 self o toWord prevValue out1 out2 value))
    |>.write 0
      (skimSecondSafeTransferDynamicCallMem0 self o toWord prevValue out1 out2 value)
      (skimSecondSafeTransferDynamicRetPtr out1).toNat 32

noncomputable def skimSecondSafeTransferDynamicTailSourceWord
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      ((skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
        |>.readWithPadding (skimSecondSafeTransferDynamicBasePtr out1 + ⟨160⟩).toNat 32))

noncomputable def skimSecondSafeTransferDynamicTailWord
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land
      (skimSecondSafeTransferDynamicTailSourceWord self o toWord prevValue out1 out2 value)
      (UInt256.lnot skimSafeTransferTailMask))
    (UInt256.land ⟨0⟩ skimSafeTransferTailMask)

noncomputable def skimSecondSafeTransferDynamicCallMem2
    (self : UInt256) (o : ByteArray) (toWord prevValue : UInt256)
    (out1 out2 : ByteArray) (value : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (skimSecondSafeTransferDynamicTailWord self o toWord prevValue out1 out2 value)).write 0
    (skimSecondSafeTransferDynamicCallMem1 self o toWord prevValue out1 out2 value)
    (skimSecondSafeTransferDynamicBasePtr out1 + ⟨228⟩).toNat 32

end UniswapV2Pair
