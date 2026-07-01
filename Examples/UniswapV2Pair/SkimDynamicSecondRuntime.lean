import Examples.UniswapV2Pair.SkimSafeTransferDynamicRuntime
import Examples.UniswapV2Pair.SkimSecondRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` second `balanceOf` after nonempty first `_safeTransfer` returndata -/

noncomputable def skimSecondBalanceDynamicSelectorMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out1 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray balanceOfSelectorShifted).write 0
    (skimSafeTransferReturnDataMem self o toWord value out1)
    (skimSafeTransferReturnDataPtr out1).toNat 32

noncomputable def skimSecondBalanceDynamicCalldataMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out1 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray self).write 0
    (skimSecondBalanceDynamicSelectorMem self o toWord value out1)
    ((skimSafeTransferReturnDataPtr out1) + ⟨4⟩).toNat 32

noncomputable def skimSecondBalanceDynamicStaticcallMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out1 out2 : ByteArray) :
    ByteArray :=
  out2.write 0 (skimSecondBalanceDynamicCalldataMem self o toWord value out1)
    (skimSafeTransferReturnDataPtr out1).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out2.size)).toNat

def skimSecondBalanceDynamicSelectorWords (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSafeTransferReturnDataActiveWords out1).toNat
    (skimSafeTransferReturnDataPtr out1).toNat 32)

def skimSecondBalanceDynamicCalldataWords (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (skimSecondBalanceDynamicSelectorWords out1).toNat
    ((skimSafeTransferReturnDataPtr out1) + ⟨4⟩).toNat 32)

def skimSecondBalanceDynamicStaticcallWords (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M (skimSecondBalanceDynamicCalldataWords out1).toNat
      (skimSafeTransferReturnDataPtr out1).toNat 36)
    (skimSafeTransferReturnDataPtr out1).toNat 32)

theorem skimSafeTransferReturnDataActiveWords_mload64_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
      (⟨64⟩ : UInt256).toNat 32) =
      skimSafeTransferReturnDataActiveWords out := by
  have hM :
      MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
          (⟨64⟩ : UInt256).toNat 32 =
        (skimSafeTransferReturnDataActiveWords out).toNat := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    simp [MachineState.M]
    have hge := skimSafeTransferReturnDataActiveWords_toNat_ge out houtSize
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem skimSafeTransferReturnDataMem_size_of_nonempty
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) (houtNe : out.size ≠ 0) :
    (skimSafeTransferReturnDataMem self o toWord value out).size =
      if 324 + out.size ≤ 388 then 388 else 324 + out.size := by
  unfold skimSafeTransferReturnDataMem
  have hbase :
      (skimSafeTransferReturnDataSizeMem self o toWord value out).size = 388 :=
    skimSafeTransferReturnDataSizeMem_size self toWord value out ho32 hoSize
  by_cases hin : 324 + out.size ≤ 388
  · rw [if_pos hin]
    have hin' :
        324 + out.size ≤
          (skimSafeTransferReturnDataSizeMem self o toWord value out).size := by
      rw [hbase]
      exact hin
    rw [write_eq_gen out
      (skimSafeTransferReturnDataSizeMem self o toWord value out)
      324 out.size houtNe le_rfl hin']
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega
  · rw [if_neg hin]
    have hext :
        (skimSafeTransferReturnDataSizeMem self o toWord value out).size <
          324 + out.size := by
      rw [hbase]
      omega
    rw [write_eq_gen_extend out
      (skimSafeTransferReturnDataSizeMem self o toWord value out)
      324 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
    omega

theorem skimSafeTransferReturnDataMem_size_ge96
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) (houtNe : out.size ≠ 0) :
    96 ≤ (skimSafeTransferReturnDataMem self o toWord value out).size := by
  rw [skimSafeTransferReturnDataMem_size_of_nonempty self toWord value ho32 hoSize houtNe]
  split <;> omega

theorem skimSafeTransferReturnDataPtr_gap
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataPtr out).toNat -
        (skimSafeTransferReturnDataMem self o toWord value out).size <
      USize.size := by
  have hptrLe := skimSafeTransferReturnDataPtr_toNat_le out houtSize
  have hsize := skimSafeTransferReturnDataMem_size_of_nonempty self toWord value
    ho32 hoSize houtNe
  rw [hsize]
  split
  · exact lt_usize _ (by omega)
  · exact lt_usize _ (by omega)

theorem skimSafeTransferReturnDataPtr_add4_toNat (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat =
      (skimSafeTransferReturnDataPtr out).toNat + 4 := by
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
  rw [Nat.mod_eq_of_lt]
  have hptrLe := skimSafeTransferReturnDataPtr_toNat_le out houtSize
  have hcap : 2 ^ 255 + 359 < UInt256.size := by norm_num [UInt256.size]
  omega

theorem skimSafeTransferReturnDataPtr_add_ofNat_toNat (out : ByteArray) (n : ℕ)
    (houtSize : out.size < 2 ^ 255) (hn : n ≤ 512) :
    ((skimSafeTransferReturnDataPtr out) + UInt256.ofNat n).toNat =
      (skimSafeTransferReturnDataPtr out).toNat + n := by
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by
    have hcap : 512 < UInt256.size := by norm_num [UInt256.size]
    omega)]
  rw [Nat.mod_eq_of_lt]
  have hptrLe := skimSafeTransferReturnDataPtr_toNat_le out houtSize
  have hcap : 2 ^ 255 + 867 < UInt256.size := by norm_num [UInt256.size]
  omega

theorem skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataPtr out).toNat + 32 ≤
      (skimSecondBalanceDynamicSelectorMem self o toWord value out).size := by
  unfold skimSecondBalanceDynamicSelectorMem
  exact toByteArray_write_size_ge_off_add32 balanceOfSelectorShifted
    (skimSafeTransferReturnDataMem self o toWord value out)
    (skimSafeTransferReturnDataPtr out).toNat
    (skimSafeTransferReturnDataPtr_gap self toWord value ho32 hoSize houtNe houtSize)

theorem skimSecondBalanceDynamicSelectorMem_size_ge96
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    96 ≤ (skimSecondBalanceDynamicSelectorMem self o toWord value out).size := by
  have hptr := skimSafeTransferReturnDataPtr_toNat_ge out houtSize
  have hsize :=
    skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
      ho32 hoSize houtNe houtSize
  omega

theorem skimSecondBalanceDynamicSelectorMem_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicSelectorMem self o toWord value out).readWithPadding 64 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out) := by
  unfold skimSecondBalanceDynamicSelectorMem
  rw [toByteArray_write_read_below_of_gap balanceOfSelectorShifted
    (skimSafeTransferReturnDataMem self o toWord value out)
    (skimSafeTransferReturnDataPtr out).toNat 64
    (skimSafeTransferReturnDataMem_size_ge96 self toWord value ho32 hoSize houtNe)
    (by
      have hptr := skimSafeTransferReturnDataPtr_toNat_ge out houtSize
      omega)
    (skimSafeTransferReturnDataPtr_gap self toWord value ho32 hoSize houtNe houtSize)]
  exact skimSafeTransferReturnDataMem_read64 self toWord value out ho32 hoSize houtNe

theorem skimSecondBalanceDynamicCalldataMem_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicCalldataMem self o toWord value out).readWithPadding 64 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out) := by
  unfold skimSecondBalanceDynamicCalldataMem
  rw [write32_read_below _ _
    ((skimSafeTransferReturnDataPtr out + ⟨4⟩).toNat) 64
    (by rw [toByteArray_size])
    (by
      rw [skimSafeTransferReturnDataPtr_add4_toNat out houtSize]
      have hsize :=
        skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
          ho32 hoSize houtNe houtSize
      omega)
    (by
      rw [skimSafeTransferReturnDataPtr_add4_toNat out houtSize]
      have hptr := skimSafeTransferReturnDataPtr_toNat_ge out houtSize
      omega)]
  exact skimSecondBalanceDynamicSelectorMem_read64 self toWord value ho32 hoSize houtNe
    houtSize

theorem skimSecondBalanceDynamicCalldataMem_size_ge96
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    96 ≤ (skimSecondBalanceDynamicCalldataMem self o toWord value out).size := by
  unfold skimSecondBalanceDynamicCalldataMem
  rw [skimSafeTransferReturnDataPtr_add4_toNat out houtSize]
  have hptr := skimSafeTransferReturnDataPtr_toNat_ge out houtSize
  have hbase :=
    skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
      ho32 hoSize houtNe houtSize
  have hwrite := toByteArray_write_size_ge_off_add32 self
    (skimSecondBalanceDynamicSelectorMem self o toWord value out)
    ((skimSafeTransferReturnDataPtr out).toNat + 4)
    (by
      exact lt_usize _ (by omega))
  omega

theorem skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataPtr out).toNat + 36 ≤
      (skimSecondBalanceDynamicCalldataMem self o toWord value out).size := by
  unfold skimSecondBalanceDynamicCalldataMem
  rw [skimSafeTransferReturnDataPtr_add4_toNat out houtSize]
  have hbase :=
    skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
      ho32 hoSize houtNe houtSize
  have hwrite := toByteArray_write_size_ge_off_add32 self
    (skimSecondBalanceDynamicSelectorMem self o toWord value out)
    ((skimSafeTransferReturnDataPtr out).toNat + 4)
    (lt_usize _ (by omega))
  omega

theorem skimSecondBalanceDynamicSelectorMem_read_ptr_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicSelectorMem self o toWord value out).readWithPadding
        (skimSafeTransferReturnDataPtr out).toNat 4 =
      balanceOfSelector := by
  unfold skimSecondBalanceDynamicSelectorMem
  have hread := toByteArray_write_read_window_of_gap balanceOfSelectorShifted
    (skimSafeTransferReturnDataMem self o toWord value out)
    (skimSafeTransferReturnDataPtr out).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
    (skimSafeTransferReturnDataPtr_gap self toWord value ho32 hoSize houtNe houtSize)
  rw [show
    (balanceOfSelectorShifted.toByteArray.write 0
        (skimSafeTransferReturnDataMem self o toWord value out)
        (skimSafeTransferReturnDataPtr out).toNat 32).readWithPadding
        (skimSafeTransferReturnDataPtr out).toNat 4 =
      (balanceOfSelectorShifted.toByteArray.write 0
        (skimSafeTransferReturnDataMem self o toWord value out)
        (skimSafeTransferReturnDataPtr out).toNat 32).readWithPadding
        ((skimSafeTransferReturnDataPtr out).toNat + 0) 4 by
      rw [Nat.add_zero]]
  rw [hread]
  native_decide

theorem skimSecondBalanceDynamicCalldataMem_read_ptr_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicCalldataMem self o toWord value out).readWithPadding
        (skimSafeTransferReturnDataPtr out).toNat 4 =
      balanceOfSelector := by
  unfold skimSecondBalanceDynamicCalldataMem
  rw [write32_read_below_len _ _
    ((skimSafeTransferReturnDataPtr out + ⟨4⟩).toNat)
    (skimSafeTransferReturnDataPtr out).toNat 4
    (by rw [toByteArray_size])
    (by
      rw [skimSafeTransferReturnDataPtr_add4_toNat out houtSize]
      have hbase :=
        skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
          ho32 hoSize houtNe houtSize
      omega)
    (by rw [skimSafeTransferReturnDataPtr_add4_toNat out houtSize])
    (by
      have hbase :=
        skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
          ho32 hoSize houtNe houtSize
      omega)
    (by norm_num) (by norm_num)]
  exact skimSecondBalanceDynamicSelectorMem_read_ptr_4 self toWord value
    ho32 hoSize houtNe houtSize

theorem skimSecondBalanceDynamicCalldataMem_read_ptr_add4_32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicCalldataMem self o toWord value out).readWithPadding
        ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 =
      UInt256.toByteArray self := by
  unfold skimSecondBalanceDynamicCalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by
      rw [skimSafeTransferReturnDataPtr_add4_toNat out houtSize]
      have hbase :=
        skimSecondBalanceDynamicSelectorMem_size_ge_ptr_add32 self toWord value
          ho32 hoSize houtNe houtSize
      omega)]
  rw [show (UInt256.toByteArray self).extract 0 32 = UInt256.toByteArray self by
    rw [show 32 = (UInt256.toByteArray self).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSecondBalanceDynamicCalldataMem_read_ptr_36
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicCalldataMem self o toWord value out).readWithPadding
        (skimSafeTransferReturnDataPtr out).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray self := by
  rw [byteArray_readWithPadding_split _ (skimSafeTransferReturnDataPtr out).toNat 4 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        have hsize :=
          skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
            ho32 hoSize houtNe houtSize
        omega)]
  rw [skimSecondBalanceDynamicCalldataMem_read_ptr_4 self toWord value
      ho32 hoSize houtNe houtSize]
  rw [show (skimSafeTransferReturnDataPtr out).toNat + 4 =
      ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat from
        (skimSafeTransferReturnDataPtr_add4_toNat out houtSize).symm]
  rw [skimSecondBalanceDynamicCalldataMem_read_ptr_add4_32 self toWord value
      ho32 hoSize houtNe houtSize]

theorem skimSecondBalanceDynamicCalldataMem_encode
    (self : AccountAddress) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    config.externalABI.encode? "balanceOf" [.address self] =
      some ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat self.val) o toWord value out)
        |>.readWithPadding (skimSafeTransferReturnDataPtr out).toNat 36) := by
  rw [skimSecondBalanceDynamicCalldataMem_read_ptr_36 _ _ _ ho32 hoSize houtNe houtSize]
  have h := balanceOfThisCalldataMem_encode self
  rw [balanceOfThisCalldataMem_read128_36] at h
  exact h

theorem UInt256_mload64_same_of_toNat_ge13 (aw : UInt256) (haw : 13 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
  have hM : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 = aw.toNat := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    simp [MachineState.M]
    omega
  rw [hM]
  exact u256_ofNat_toNat aw

theorem UInt256_mload64_haw_of_toNat_ge13 (aw : UInt256)
    (hge : 13 ≤ aw.toNat) (hmul : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  intro h
  have hle : (aw * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
  omega

theorem skimSecondBalanceDynamicSelectorWords_M_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
        (skimSafeTransferReturnDataPtr out).toNat 32 * 32 < UInt256.size := by
  have hactive := skimSafeTransferReturnDataActiveWords_mul32_lt out houtSize
  have hptrLe := skimSafeTransferReturnDataPtr_toNat_le out houtSize
  unfold MachineState.M
  split
  · exact hactive
  · by_cases hle :
        (skimSafeTransferReturnDataActiveWords out).toNat ≤
          ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv :
          (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32) * 32 ≤
            (skimSafeTransferReturnDataPtr out).toNat + 32 + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 418 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      exact hactive

theorem skimSecondBalanceDynamicSelectorWords_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondBalanceDynamicSelectorWords out).toNat := by
  unfold skimSecondBalanceDynamicSelectorWords
  have hMmul := skimSecondBalanceDynamicSelectorWords_M_mul32_lt out houtSize
  have hMlt :
      MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
          (skimSafeTransferReturnDataPtr out).toNat 32 < UInt256.size := by
    have hnonneg :
        MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
            (skimSafeTransferReturnDataPtr out).toNat 32 ≤
          MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
            (skimSafeTransferReturnDataPtr out).toNat 32 * 32 := by
      omega
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  have hactive := skimSafeTransferReturnDataActiveWords_toNat_ge out houtSize
  unfold MachineState.M
  split
  · exact hactive
  · exact le_trans hactive (Nat.le_max_left _ _)

theorem skimSecondBalanceDynamicSelectorWords_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicSelectorWords out).toNat * 32 < UInt256.size := by
  unfold skimSecondBalanceDynamicSelectorWords
  have hMmul := skimSecondBalanceDynamicSelectorWords_M_mul32_lt out houtSize
  have hMlt :
      MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
          (skimSafeTransferReturnDataPtr out).toNat 32 < UInt256.size := by
    have hnonneg :
        MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
            (skimSafeTransferReturnDataPtr out).toNat 32 ≤
          MachineState.M (skimSafeTransferReturnDataActiveWords out).toNat
            (skimSafeTransferReturnDataPtr out).toNat 32 * 32 := by
      omega
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hMmul

theorem skimSecondBalanceDynamicCalldataWords_M_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    MachineState.M (skimSecondBalanceDynamicSelectorWords out).toNat
        ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 * 32 <
      UInt256.size := by
  have hactive := skimSecondBalanceDynamicSelectorWords_mul32_lt out houtSize
  have hptrLe := skimSafeTransferReturnDataPtr_toNat_le out houtSize
  have hoff : ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat =
      (skimSafeTransferReturnDataPtr out).toNat + 4 :=
    skimSafeTransferReturnDataPtr_add4_toNat out houtSize
  unfold MachineState.M
  split
  · exact hactive
  · by_cases hle :
        (skimSecondBalanceDynamicSelectorWords out).toNat ≤
          (((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat + 32 + 31) / 32
    · rw [Nat.max_eq_right hle]
      rw [hoff]
      have hdiv :
          (((skimSafeTransferReturnDataPtr out).toNat + 4 + 32 + 31) / 32) * 32 ≤
            (skimSafeTransferReturnDataPtr out).toNat + 4 + 32 + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 422 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      exact hactive

theorem skimSecondBalanceDynamicCalldataWords_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondBalanceDynamicCalldataWords out).toNat := by
  unfold skimSecondBalanceDynamicCalldataWords
  have hMmul := skimSecondBalanceDynamicCalldataWords_M_mul32_lt out houtSize
  have hMlt :
      MachineState.M (skimSecondBalanceDynamicSelectorWords out).toNat
          ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 < UInt256.size := by
    have hnonneg :
        MachineState.M (skimSecondBalanceDynamicSelectorWords out).toNat
            ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 ≤
          MachineState.M (skimSecondBalanceDynamicSelectorWords out).toNat
            ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 * 32 := by
      omega
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  have hactive := skimSecondBalanceDynamicSelectorWords_toNat_ge out houtSize
  unfold MachineState.M
  split
  · exact hactive
  · exact le_trans hactive (Nat.le_max_left _ _)

theorem skimSecondBalanceDynamicCalldataWords_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicCalldataWords out).toNat * 32 < UInt256.size := by
  unfold skimSecondBalanceDynamicCalldataWords
  have hMmul := skimSecondBalanceDynamicCalldataWords_M_mul32_lt out houtSize
  have hMlt :
      MachineState.M (skimSecondBalanceDynamicSelectorWords out).toNat
          ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 < UInt256.size := by
    have hnonneg :
        MachineState.M (skimSecondBalanceDynamicSelectorWords out).toNat
            ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 ≤
          MachineState.M (skimSecondBalanceDynamicSelectorWords out).toNat
            ((skimSafeTransferReturnDataPtr out) + ⟨4⟩).toNat 32 * 32 := by
      omega
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hMmul

theorem skimSecondBalanceDynamicCalldataWords_mload64_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
      (⟨64⟩ : UInt256).toNat 32) =
      skimSecondBalanceDynamicCalldataWords out :=
  UInt256_mload64_same_of_toNat_ge13 _
    (skimSecondBalanceDynamicCalldataWords_toNat_ge out houtSize)

theorem skimSecondBalanceDynamicStaticcallWords_M_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    MachineState.M
        (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
          (skimSafeTransferReturnDataPtr out).toNat 36)
        (skimSafeTransferReturnDataPtr out).toNat 32 * 32 <
      UInt256.size := by
  have hcalldata := skimSecondBalanceDynamicCalldataWords_mul32_lt out houtSize
  have hptrLe := skimSafeTransferReturnDataPtr_toNat_le out houtSize
  have hinner :
      MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
          (skimSafeTransferReturnDataPtr out).toNat 36 * 32 < UInt256.size := by
    unfold MachineState.M
    split
    · exact hcalldata
    · by_cases hle :
          (skimSecondBalanceDynamicCalldataWords out).toNat ≤
            ((skimSafeTransferReturnDataPtr out).toNat + 36 + 31) / 32
      · rw [Nat.max_eq_right hle]
        have hdiv :
            (((skimSafeTransferReturnDataPtr out).toNat + 36 + 31) / 32) * 32 ≤
              (skimSafeTransferReturnDataPtr out).toNat + 36 + 31 :=
          Nat.div_mul_le_self _ _
        have hcap : 2 ^ 255 + 422 < UInt256.size := by norm_num [UInt256.size]
        omega
      · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
        exact hcalldata
  unfold MachineState.M
  split
  · exact hinner
  · by_cases hle :
        MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
            (skimSafeTransferReturnDataPtr out).toNat 36 ≤
          ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32
    · change
        max
            (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
              (skimSafeTransferReturnDataPtr out).toNat 36)
            (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32) *
          32 <
        UInt256.size
      rw [Nat.max_eq_right hle]
      have hdiv :
          (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32) * 32 ≤
            (skimSafeTransferReturnDataPtr out).toNat + 32 + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 418 < UInt256.size := by norm_num [UInt256.size]
      omega
    · change
        max
            (MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
              (skimSafeTransferReturnDataPtr out).toNat 36)
            (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32) *
          32 <
        UInt256.size
      rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      exact hinner

theorem skimSecondBalanceDynamicStaticcallWords_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    13 ≤ (skimSecondBalanceDynamicStaticcallWords out).toNat := by
  unfold skimSecondBalanceDynamicStaticcallWords
  have hMmul := skimSecondBalanceDynamicStaticcallWords_M_mul32_lt out houtSize
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
  have hcalldata := skimSecondBalanceDynamicCalldataWords_toNat_ge out houtSize
  have hinnerGe :
      13 ≤ MachineState.M (skimSecondBalanceDynamicCalldataWords out).toNat
        (skimSafeTransferReturnDataPtr out).toNat 36 := by
    unfold MachineState.M
    split
    · exact hcalldata
    · exact le_trans hcalldata (Nat.le_max_left _ _)
  unfold MachineState.M
  split
  · exact hinnerGe
  · exact le_trans hinnerGe (Nat.le_max_left _ _)

theorem skimSecondBalanceDynamicStaticcallWords_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondBalanceDynamicStaticcallWords out).toNat * 32 < UInt256.size := by
  unfold skimSecondBalanceDynamicStaticcallWords
  have hMmul := skimSecondBalanceDynamicStaticcallWords_M_mul32_lt out houtSize
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
  exact hMmul

theorem skimSecondBalanceDynamicStaticcallWords_mload64_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (skimSecondBalanceDynamicStaticcallWords out).toNat
      (⟨64⟩ : UInt256).toNat 32) =
      skimSecondBalanceDynamicStaticcallWords out :=
  UInt256_mload64_same_of_toNat_ge13 _
    (skimSecondBalanceDynamicStaticcallWords_toNat_ge out houtSize)

theorem skimSecondBalanceDynamicStaticcallMem_read64_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
        64 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out1) := by
  unfold skimSecondBalanceDynamicStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out2 hout2_32 hout2Size]
  rw [write32_read_below _ _ (skimSafeTransferReturnDataPtr out1).toNat 64 hout2_32
    (by
      have hsize :=
        skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
          ho32 hoSize hout1Ne hout1Size
      omega)
    (by
      have hptr := skimSafeTransferReturnDataPtr_toNat_ge out1 hout1Size
      omega)]
  exact skimSecondBalanceDynamicCalldataMem_read64 self toWord value
    ho32 hoSize hout1Ne hout1Size

theorem skimSecondBalanceDynamicStaticcallMem_mload64_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondBalanceDynamicStaticcallWords out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSafeTransferReturnDataPtr out1 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondBalanceDynamicStaticcallWords out1)
    (v := skimSafeTransferReturnDataPtr out1)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold skimSecondBalanceDynamicStaticcallMem
      rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out2 hout2_32 hout2Size]
      have hbase :=
        skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
          ho32 hoSize hout1Ne hout1Size
      rw [write32_eq out2 _ _ hout2_32 (by omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract]
      rw [Nat.min_eq_left (by omega : (skimSafeTransferReturnDataPtr out1).toNat ≤
          (skimSecondBalanceDynamicCalldataMem self o toWord value out1).size),
        Nat.min_eq_left hout2_32]
      have hptr := skimSafeTransferReturnDataPtr_toNat_ge out1 hout1Size
      omega)
    (UInt256_mload64_haw_of_toNat_ge13 _
      (skimSecondBalanceDynamicStaticcallWords_toNat_ge out1 hout1Size)
      (skimSecondBalanceDynamicStaticcallWords_mul32_lt out1 hout1Size))
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        skimSecondBalanceDynamicStaticcallMem_read64_of_size_ge self toWord value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)

theorem skimSecondBalanceDynamicStaticcallMem_read64_of_size_lt
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hshort : out2.size < 32) (hout2Size : out2.size < UInt256.size) :
    (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
        64 32 =
      UInt256.toByteArray (skimSafeTransferReturnDataPtr out1) := by
  unfold skimSecondBalanceDynamicStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_lt out2 hshort hout2Size]
  by_cases hzero : out2.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact skimSecondBalanceDynamicCalldataMem_read64 self toWord value
      ho32 hoSize hout1Ne hout1Size
  · rw [write_read_below_gen out2
      (skimSecondBalanceDynamicCalldataMem self o toWord value out1)
      (skimSafeTransferReturnDataPtr out1).toNat out2.size 64 hzero le_rfl
      (by
        have hbase :=
          skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
            ho32 hoSize hout1Ne hout1Size
        omega)
      (by
        have hptr := skimSafeTransferReturnDataPtr_toNat_ge out1 hout1Size
        omega)]
    exact skimSecondBalanceDynamicCalldataMem_read64 self toWord value
      ho32 hoSize hout1Ne hout1Size

theorem skimSecondBalanceDynamicStaticcallMem_mload64_of_size_lt
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hshort : out2.size < 32) (hout2Size : out2.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondBalanceDynamicStaticcallWords out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSafeTransferReturnDataPtr out1 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondBalanceDynamicStaticcallWords out1)
    (v := skimSafeTransferReturnDataPtr out1)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold skimSecondBalanceDynamicStaticcallMem
      rw [skimSecondBalanceStaticcallWriteLen_of_size_lt out2 hshort hout2Size]
      by_cases hzero : out2.size = 0
      · rw [hzero, byteArray_write_len_zero]
        have hsize :=
          skimSecondBalanceDynamicCalldataMem_size_ge96 self toWord value
            ho32 hoSize hout1Ne hout1Size
        omega
      · have hbase :=
          skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
            ho32 hoSize hout1Ne hout1Size
        rw [write_eq_gen out2
          (skimSecondBalanceDynamicCalldataMem self o toWord value out1)
          (skimSafeTransferReturnDataPtr out1).toNat out2.size hzero le_rfl
          (by omega)]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        rw [Nat.min_eq_left (by omega : (skimSafeTransferReturnDataPtr out1).toNat ≤
            (skimSecondBalanceDynamicCalldataMem self o toWord value out1).size),
          Nat.min_eq_left le_rfl]
        have hptr := skimSafeTransferReturnDataPtr_toNat_ge out1 hout1Size
        omega)
    (UInt256_mload64_haw_of_toNat_ge13 _
      (skimSecondBalanceDynamicStaticcallWords_toNat_ge out1 hout1Size)
      (skimSecondBalanceDynamicStaticcallWords_mul32_lt out1 hout1Size))
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        skimSecondBalanceDynamicStaticcallMem_read64_of_size_lt self toWord value
          ho32 hoSize hout1Ne hout1Size hshort hout2Size)

theorem skimSecondBalanceDynamicStaticcallWords_ptr_lt_mul32 (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSafeTransferReturnDataPtr out).toNat <
      (skimSecondBalanceDynamicStaticcallWords out).toNat * 32 := by
  unfold skimSecondBalanceDynamicStaticcallWords
  have hMmul := skimSecondBalanceDynamicStaticcallWords_M_mul32_lt out houtSize
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
  simp [MachineState.M]
  have hceil :
      (skimSafeTransferReturnDataPtr out).toNat <
        (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32) * 32 := by
    have hmod := Nat.mod_lt ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31)
      (by norm_num : 0 < 32)
    have hdm := Nat.div_add_mod ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) 32
    omega
  have hleq :
      ((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32 ≤
        max (skimSecondBalanceDynamicCalldataWords out).toNat
          (max (((skimSafeTransferReturnDataPtr out).toNat + 36 + 31) / 32)
            (((skimSafeTransferReturnDataPtr out).toNat + 32 + 31) / 32)) := by
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact lt_of_lt_of_le hceil (Nat.mul_le_mul_right 32 hleq)

theorem skimSecondBalanceDynamicStaticcallWords_ptr_haw (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    ¬ skimSafeTransferReturnDataPtr out ≥
      skimSecondBalanceDynamicStaticcallWords out * ⟨32⟩ := by
  intro h
  have hle :
      (skimSecondBalanceDynamicStaticcallWords out * ⟨32⟩).toNat ≤
        (skimSafeTransferReturnDataPtr out).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (skimSecondBalanceDynamicStaticcallWords_mul32_lt out houtSize)] at hle
  have hlt := skimSecondBalanceDynamicStaticcallWords_ptr_lt_mul32 out houtSize
  omega

theorem skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSafeTransferReturnDataPtr out1).toNat + 32 ≤
      (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).size := by
  unfold skimSecondBalanceDynamicStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out2 hout2_32 hout2Size]
  have hbase :=
    skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
      ho32 hoSize hout1Ne hout1Size
  rw [write32_eq out2 _ _ hout2_32 (by omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract]
  rw [Nat.min_eq_left (by omega : (skimSafeTransferReturnDataPtr out1).toNat ≤
      (skimSecondBalanceDynamicCalldataMem self o toWord value out1).size),
    Nat.min_eq_left hout2_32]
  omega

theorem skimSecondBalanceDynamicStaticcallMem_read_ptr_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
        (skimSafeTransferReturnDataPtr out1).toNat 32 =
      out2.extract 0 32 := by
  unfold skimSecondBalanceDynamicStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out2 hout2_32 hout2Size]
  exact write32_read_back out2
    (skimSecondBalanceDynamicCalldataMem self o toWord value out1)
    (skimSafeTransferReturnDataPtr out1).toNat hout2_32
    (by
      have hbase :=
        skimSecondBalanceDynamicCalldataMem_size_ge_ptr_add36 self toWord value
          ho32 hoSize hout1Ne hout1Size
      omega)

theorem skimSecondBalanceDynamicStaticcallMem_mload_ptr_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out1 out2 : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    (if (skimSafeTransferReturnDataPtr out1).toNat ≥
          (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).size
        ∨ skimSafeTransferReturnDataPtr out1 ≥
            skimSecondBalanceDynamicStaticcallWords out1 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
          (skimSafeTransferReturnDataPtr out1).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32)) := by
  rw [if_neg]
  · rw [skimSecondBalanceDynamicStaticcallMem_read_ptr_of_size_ge self toWord value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
  · rw [not_or]
    constructor
    · have hsize :=
        skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
          self toWord value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
      omega
    · exact skimSecondBalanceDynamicStaticcallWords_ptr_haw out1 hout1Size

theorem skimSecondBalanceDynamicCalldataMem_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondBalanceDynamicCalldataMem self o toWord value out).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondBalanceDynamicCalldataWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicCalldataMem self o toWord value out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSafeTransferReturnDataPtr out := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondBalanceDynamicCalldataWords out)
    (v := skimSafeTransferReturnDataPtr out)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hsize :=
        skimSecondBalanceDynamicCalldataMem_size_ge96 self toWord value
          ho32 hoSize houtNe houtSize
      omega)
    (UInt256_mload64_haw_of_toNat_ge13 _
      (skimSecondBalanceDynamicCalldataWords_toNat_ge out houtSize)
      (skimSecondBalanceDynamicCalldataWords_mul32_lt out houtSize))
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        skimSecondBalanceDynamicCalldataMem_read64 self toWord value
          ho32 hoSize houtNe houtSize)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceOfStaticcallMade_dynamic {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord token0 token1 sel : UInt256}
    {o out1 : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5330⟩
      (token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem (UInt256.ofNat ee.codeOwner.val) o toWord value out1)
      (skimSafeTransferReturnDataActiveWords out1) out1 (cA, σ) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hdepth : ee.depth.val < 1024)
    (htoken1Code : uniswapExtCodeSizeWord σ (UInt256.land token1 solcAddrMask) ≠ ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out2 : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out2) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
          (toExecute σ (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat ee.codeOwner.val) o
              toWord value out1)
            |>.readWithPadding (skimSafeTransferReturnDataPtr out1).toNat 36)
          (ee.depth + 1) ee.header false)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5273⟩
          ((if z then (⟨1⟩ : UInt256) else ⟨0⟩) ::
            (skimSafeTransferReturnDataPtr out1 + ⟨36⟩) ::
            balanceOfSelectorWord :: UInt256.land token1 solcAddrMask ::
            UInt256.land reserve112Mask (UInt256.div (uniswapSlotWord ⟨8⟩ σ ee) reserve112Shift) ::
            ⟨5325⟩ :: toWord :: token1 :: ⟨5433⟩ ::
            token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
          (skimSecondBalanceDynamicStaticcallMem (UInt256.ofNat ee.codeOwner.val) o
            toWord value out1 out2)
          (skimSecondBalanceDynamicStaticcallWords out1) out2 (cA', σ') k' C'
      ∧ out2.size < UInt256.size := by
  let packedWord := uniswapSlotWord ⟨8⟩ σ ee
  let token1Clean := UInt256.land token1 solcAddrMask
  let reserve1Word := UInt256.land reserve112Mask (UInt256.div packedWord reserve112Shift)
  let fp := skimSafeTransferReturnDataPtr out1
  have rd5333 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨k5334, C5334, rd5334₀⟩ := rd5333.sload (by native_decide) (by evm_ov)
  have rd5334 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5334⟩
      (packedWord :: token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem (UInt256.ofNat ee.codeOwner.val) o toWord value out1)
      (skimSafeTransferReturnDataActiveWords out1) out1 (cA, σ) k5334 C5334 := by
    simpa [packedWord, uniswapSlotWord] using rd5334₀
  let aw0 := skimSafeTransferReturnDataActiveWords out1
  let awLoad0 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad0 : awLoad0 = aw0 := by
    simpa [awLoad0, aw0] using skimSafeTransferReturnDataActiveWords_mload64_same out1 hout1Size
  have rd5342 := evm_run rd5334 with [push1 ⟨64⟩, dup1]
  have rd5343₀ := RD.mload
    (Cₘ awLoad0 - Cₘ aw0) fp awLoad0 rd5342 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad0, aw0])
    (by
      simpa [fp, aw0] using
        skimSafeTransferReturnDataMem_mload64 (UInt256.ofNat ee.codeOwner.val)
          toWord value out1 ho32 hoSize hout1Ne hout1Size)
    (by simpa [awLoad0, aw0] using hawLoad0)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5343 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5338⟩
      (fp :: ⟨64⟩ :: packedWord :: token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem (UInt256.ofNat ee.codeOwner.val) o toWord value out1)
      aw0 out1 (cA, σ) (k5334 + 1 + 1 + 1) (C5334 + 3 + 3 + 3) := by
    simpa [hawLoad0] using rd5343₀
  have rd5347 := evm_run rd5343 with [
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  let awSel := skimSecondBalanceDynamicSelectorWords out1
  have rd5348 := RD.mstore
    (Cₘ awSel - Cₘ aw0)
    (skimSecondBalanceDynamicSelectorMem (UInt256.ofNat ee.codeOwner.val) o
      toWord value out1)
    awSel rd5347 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awSel, aw0, fp,
        skimSecondBalanceDynamicSelectorWords])
    (by unfold skimSecondBalanceDynamicSelectorMem fp; rfl)
    (by simp [awSel, aw0, fp, skimSecondBalanceDynamicSelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5353 := evm_run rd5348 with [uniswapAddress, push1 ⟨4⟩, dup3, add]
  let awCalldata := skimSecondBalanceDynamicCalldataWords out1
  have rd5354 := RD.mstore
    (Cₘ awCalldata - Cₘ awSel)
    (skimSecondBalanceDynamicCalldataMem (UInt256.ofNat ee.codeOwner.val) o
      toWord value out1)
    awCalldata rd5353 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCalldata, awSel, fp,
        skimSecondBalanceDynamicCalldataWords])
    (by unfold skimSecondBalanceDynamicCalldataMem fp; rfl)
    (by simp [awCalldata, awSel, fp, skimSecondBalanceDynamicCalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  let awLoad1 : UInt256 :=
    UInt256.ofNat (MachineState.M awCalldata.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad1 : awLoad1 = awCalldata := by
    simpa [awLoad1, awCalldata] using
      skimSecondBalanceDynamicCalldataWords_mload64_same out1 hout1Size
  have rd5355 := evm_run rd5354 with [swap1]
  have rd5356₀ := RD.mload
    (Cₘ awLoad1 - Cₘ awCalldata) fp awLoad1 rd5355 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad1, awCalldata])
    (by
      simpa [fp, awCalldata] using
        skimSecondBalanceDynamicCalldataMem_mload64 (UInt256.ofNat ee.codeOwner.val)
          toWord value ho32 hoSize hout1Ne hout1Size)
    (by simpa [awLoad1, awCalldata] using hawLoad1)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5356pre := by
    simpa [hawLoad1] using rd5356₀
  have rd5356 := evm_run rd5356pre with [
    push2 ⟨5433⟩, swap3, dup5, swap3, dup8, swap3, push2 ⟨5325⟩, swap3]
  have rd5384₀ := evm_run rd5356 with [
    push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5384 := rd5384₀
  rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from rfl,
    show UInt256.sub reserve112Shift ⟨1⟩ = reserve112Mask from rfl] at rd5384
  have rd5395₀ := evm_run rd5384 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, swap2]
  have rd5395 := rd5395₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5395
  have rd5421₀ := evm_run rd5395 with [
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup3, add,
    swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3, swap1, sub, add,
    dup2, dup7, dup1]
  have rd5421 := rd5421₀
  rw [show UInt256.sub fp fp = ⟨0⟩ from u256_sub_self fp,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5421
  obtain ⟨gasWord, _, _, rd5272⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨5269⟩) rd5421 htoken1Code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA', σ', z, out2, A_in, callGas, k', C', hΘ, rd5273, hout2Size⟩ :=
    RD.uniswapStaticcall rd5272 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA', σ', z, out2, A_in, callGas, k', C', ?_, ?_, hout2Size⟩
  · simpa [token1Clean, skimSecondBalanceDynamicStaticcallMem, fp] using hΘ
  · simpa [packedWord, token1Clean, reserve1Word, reserve112Shift, reserve112Mask,
      skimSecondBalanceDynamicStaticcallMem, skimSecondBalanceDynamicStaticcallWords, fp]
      using rd5273

theorem RD.uniswapSkimSecondBalanceCallFailureReverts_dynamic {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5273⟩
      (status :: R) mem aw out acc k C)
    (hstatus : status = ⟨0⟩) (houtSize : out.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (okPc := ⟨5289⟩) h hstatus
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) houtSize hov

theorem RD.uniswapSkimSecondBalanceCallSuccessToDecode_dynamic {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5273⟩
      (status :: R) mem aw out acc k C)
    (hstatus : status ≠ ⟨0⟩) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩
      R mem aw out acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (okPc := ⟨5289⟩) h hstatus
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts_dynamic
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord : UInt256} {o out1 out2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩
      (d0 :: d1 :: d2 :: R)
      (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2)
      (skimSecondBalanceDynamicStaticcallWords out1) out2 acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hshort : out2.size < 32) (hout2Size : out2.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let aw0 := skimSecondBalanceDynamicStaticcallWords out1
  let awLoad64 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad64 : awLoad64 = aw0 := by
    simpa [awLoad64, aw0] using
      skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size
  have rdPop0 := RD.pop h (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide) (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload
    (Cₘ awLoad64 - Cₘ aw0) (skimSafeTransferReturnDataPtr out1) awLoad64
    rdPush64 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk,
        awLoad64, aw0])
    (by
      simpa [aw0] using
        skimSecondBalanceDynamicStaticcallMem_mload64_of_size_lt self toWord value
          ho32 hoSize hout1Ne hout1Size hshort hout2Size)
    (by simpa [awLoad64, aw0] using hawLoad64)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out2.size hout2Size]
    exact hshort
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨5311⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by native_decide) hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough (by native_decide)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceReturnWordDecodeOk_dynamic
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord : UInt256} {o out1 out2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩
      (d0 :: d1 :: d2 :: R)
      (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2)
      (skimSecondBalanceDynamicStaticcallWords out1) out2 acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5314⟩
      (UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32)) :: R)
      (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2)
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat
            (MachineState.M (skimSecondBalanceDynamicStaticcallWords out1).toNat
              (⟨64⟩ : UInt256).toNat 32)).toNat
          (skimSafeTransferReturnDataPtr out1).toNat 32))
      out2 acc k' C' := by
  let aw0 := skimSecondBalanceDynamicStaticcallWords out1
  let fp := skimSafeTransferReturnDataPtr out1
  let awLoad64 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoadRet : UInt256 := UInt256.ofNat (MachineState.M awLoad64.toNat fp.toNat 32)
  have hawLoad64 : awLoad64 = aw0 := by
    simpa [awLoad64, aw0] using
      skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size
  have rdPop0 := RD.pop h (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide) (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload
    (Cₘ awLoad64 - Cₘ aw0) fp awLoad64 rdPush64 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk,
        awLoad64, aw0])
    (by
      simpa [fp, aw0] using
        skimSecondBalanceDynamicStaticcallMem_mload64_of_size_ge self toWord value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
    (by simpa [awLoad64, aw0] using hawLoad64)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out2.size hout2Size]
    exact hout2_32
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨5311⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdMloadRet := RD.mload
    (Cₘ awLoadRet - Cₘ awLoad64)
    (UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))) awLoadRet
    rdPopLen (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk,
        awLoadRet, awLoad64, aw0, fp])
    (by
      simpa [fp, aw0, hawLoad64] using
        skimSecondBalanceDynamicStaticcallMem_mload_ptr_of_size_ge self toWord value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
    (by simpa [awLoadRet, awLoad64, aw0, fp, hawLoad64])
    (by omega)
  exact ⟨_, _, by simpa [awLoadRet, awLoad64, aw0, fp] using rdMloadRet⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceOfNoCodeReverts_dynamic {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord token0 token1 sel : UInt256}
    {o out1 : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5330⟩
      (token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem (UInt256.ofNat ee.codeOwner.val) o toWord value out1)
      (skimSafeTransferReturnDataActiveWords out1) out1 (cA, σ) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (htoken1NoCode : uniswapExtCodeSizeWord σ (UInt256.land token1 solcAddrMask) = ⟨0⟩) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let packedWord := uniswapSlotWord ⟨8⟩ σ ee
  let token1Clean := UInt256.land token1 solcAddrMask
  let reserve1Word := UInt256.land reserve112Mask (UInt256.div packedWord reserve112Shift)
  let fp := skimSafeTransferReturnDataPtr out1
  have rd5333 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨k5334, C5334, rd5334₀⟩ := rd5333.sload (by native_decide) (by evm_ov)
  have rd5334 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5334⟩
      (packedWord :: token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem (UInt256.ofNat ee.codeOwner.val) o toWord value out1)
      (skimSafeTransferReturnDataActiveWords out1) out1 (cA, σ) k5334 C5334 := by
    simpa [packedWord, uniswapSlotWord] using rd5334₀
  let aw0 := skimSafeTransferReturnDataActiveWords out1
  let awLoad0 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad0 : awLoad0 = aw0 := by
    simpa [awLoad0, aw0] using skimSafeTransferReturnDataActiveWords_mload64_same out1 hout1Size
  have rd5342 := evm_run rd5334 with [push1 ⟨64⟩, dup1]
  have rd5343₀ := RD.mload
    (Cₘ awLoad0 - Cₘ aw0) fp awLoad0 rd5342 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad0, aw0])
    (by
      simpa [fp, aw0] using
        skimSafeTransferReturnDataMem_mload64 (UInt256.ofNat ee.codeOwner.val)
          toWord value out1 ho32 hoSize hout1Ne hout1Size)
    (by simpa [awLoad0, aw0] using hawLoad0)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5343 := by
    simpa [hawLoad0] using rd5343₀
  let awSel := skimSecondBalanceDynamicSelectorWords out1
  have rd5348 := RD.mstore
    (Cₘ awSel - Cₘ aw0)
    (skimSecondBalanceDynamicSelectorMem (UInt256.ofNat ee.codeOwner.val) o
      toWord value out1)
    awSel (evm_run rd5343 with [push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2])
    (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awSel, aw0, fp,
        skimSecondBalanceDynamicSelectorWords])
    (by unfold skimSecondBalanceDynamicSelectorMem fp; rfl)
    (by simp [awSel, aw0, fp, skimSecondBalanceDynamicSelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5353 := evm_run rd5348 with [uniswapAddress, push1 ⟨4⟩, dup3, add]
  let awCalldata := skimSecondBalanceDynamicCalldataWords out1
  have rd5354 := RD.mstore
    (Cₘ awCalldata - Cₘ awSel)
    (skimSecondBalanceDynamicCalldataMem (UInt256.ofNat ee.codeOwner.val) o
      toWord value out1)
    awCalldata rd5353 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCalldata, awSel,
        fp, skimSecondBalanceDynamicCalldataWords])
    (by unfold skimSecondBalanceDynamicCalldataMem fp; rfl)
    (by simp [awCalldata, awSel, fp, skimSecondBalanceDynamicCalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  let awLoad1 : UInt256 :=
    UInt256.ofNat (MachineState.M awCalldata.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad1 : awLoad1 = awCalldata := by
    simpa [awLoad1, awCalldata] using
      skimSecondBalanceDynamicCalldataWords_mload64_same out1 hout1Size
  have rd5355 := evm_run rd5354 with [swap1]
  have rd5356₀ := RD.mload
    (Cₘ awLoad1 - Cₘ awCalldata) fp awLoad1 rd5355 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad1, awCalldata])
    (by
      simpa [fp, awCalldata] using
        skimSecondBalanceDynamicCalldataMem_mload64 (UInt256.ofNat ee.codeOwner.val)
          toWord value ho32 hoSize hout1Ne hout1Size)
    (by simpa [awLoad1, awCalldata] using hawLoad1)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5356 := by
    simpa [hawLoad1] using rd5356₀
  have rd5384₀ := evm_run rd5356 with [
    push2 ⟨5433⟩, swap3, dup5, swap3, dup8, swap3, push2 ⟨5325⟩, swap3,
    push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5384 := rd5384₀
  rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from rfl,
    show UInt256.sub reserve112Shift ⟨1⟩ = reserve112Mask from rfl] at rd5384
  have rd5395₀ := evm_run rd5384 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, swap2]
  have rd5395 := rd5395₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5395
  have rd5421₀ := evm_run rd5395 with [
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup3, add,
    swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3, swap1, sub, add,
    dup2, dup7, dup1]
  have rd5421 := rd5421₀
  rw [show UInt256.sub fp fp = ⟨0⟩ from u256_sub_self fp,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5421
  exact RD.uniswapExtcodesizeGuardMissing (okPc := ⟨5269⟩) rd5421 htoken1NoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubUnderflow_dynamic {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hlt : a.toNat < b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6886 := evm_run h with [jumpdest, dup1, dup3, sub, dup3, dup2]
  have rd6887₀ := evm_run rd6886 with [gt]
  have rd6887 := rd6887₀
  rw [hgt] at rd6887
  have rd6888₀ := evm_run rd6887 with [iszero]
  have rd6888 := rd6888₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6888
  have rd6891 := evm_run rd6888 with [
    push2 ⟨2911⟩, jumpiNT (by decide)]
  let fp0 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))
  let aw1 : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6895a := evm_run rd6891 with [push1 ⟨64⟩, dup1]
  have rd6895 := RD.mload
    (Cₘ aw1 - Cₘ aw) fp0 aw1 rd6895a (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6899 := rd6895.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd6918a := evm_run rd6899 with [push1 ⟨229⟩, shl, dup2]
  let mem0 : ByteArray := (UInt256.toByteArray uniswapErrorStringSelector).write 0 mem fp0.toNat 32
  let aw2 : UInt256 := UInt256.ofNat (MachineState.M aw1.toNat fp0.toNat 32)
  have rd6918a' := RD.mstore
    (Cₘ aw2 - Cₘ aw1) mem0 aw2 rd6918a (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, aw2])
    (by simp [mem0, uniswapErrorStringSelector])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6918b0 := evm_run rd6918a' with [push1 ⟨32⟩, push1 ⟨4⟩, dup3, add]
  let off1 : UInt256 := fp0 + ⟨4⟩
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 off1.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat off1.toNat 32)
  have rd6918b := RD.mstore
    (Cₘ aw3 - Cₘ aw2) mem1 aw3 rd6918b0 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, aw3, off1])
    (by simp [mem1, off1])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6918c0 := evm_run rd6918b with [push1 ⟨21⟩, push1 ⟨36⟩, dup3, add]
  let off2 : UInt256 := fp0 + ⟨36⟩
  let mem2 : ByteArray := (UInt256.toByteArray (⟨21⟩ : UInt256)).write 0 mem1 off2.toNat 32
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat off2.toNat 32)
  have rd6918 := RD.mstore
    (Cₘ aw4 - Cₘ aw3) mem2 aw4 rd6918c0 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3, aw4, off2])
    (by simp [mem2, off2])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6940 := rd6918.pushConst
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by decide) (by evm_ov)
  have rd6944 := evm_run rd6940 with [push1 ⟨88⟩, shl, push1 ⟨68⟩, dup3, add]
  let off3 : UInt256 := fp0 + ⟨68⟩
  let mem3 : ByteArray :=
    (UInt256.toByteArray uniswapSafeMathSubUnderflowStringWord).write 0 mem2 off3.toNat 32
  let aw5 : UInt256 := UInt256.ofNat (MachineState.M aw4.toNat off3.toNat 32)
  have rd6944' := RD.mstore
    (Cₘ aw5 - Cₘ aw4) mem3 aw5 rd6944 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw4, aw5, off3])
    (by simp [mem3, off3, uniswapSafeMathSubUnderflowStringWord])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6945 := evm_run rd6944' with [swap1]
  let fp1 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem3.size ∨ (⟨64⟩ : UInt256) ≥ aw5 * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem3.readWithPadding 64 32))
  let aw6 : UInt256 := UInt256.ofNat (MachineState.M aw5.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6946 := RD.mload
    (Cₘ aw6 - Cₘ aw5) fp1 aw6 rd6945 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw5, aw6])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6954 := evm_run rd6946 with [
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat
      (MachineState.M aw6.toNat fp1.toNat ((⟨100⟩ : UInt256) + fp0.sub fp1).toNat)) -
      Cₘ aw6)
    rd6954 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
    (by simp only [List.length_cons, List.length_nil]; omega)

end UniswapV2Pair
