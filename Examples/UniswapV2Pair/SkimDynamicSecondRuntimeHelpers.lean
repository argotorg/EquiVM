import Examples.UniswapV2Pair.SkimSafeTransferDynamicRuntime
import Examples.UniswapV2Pair.SkimSecondRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` second `balanceOf` after nonempty first `_safeTransfer` returndata -/

def skimSecondBalanceDynamicSelectorMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out1 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray balanceOfSelectorShifted).write 0
    (skimSafeTransferReturnDataMem self o toWord value out1)
    (skimSafeTransferReturnDataPtr out1).toNat 32

def skimSecondBalanceDynamicCalldataMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out1 : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray self).write 0
    (skimSecondBalanceDynamicSelectorMem self o toWord value out1)
    ((skimSafeTransferReturnDataPtr out1) + ⟨4⟩).toNat 32

def skimSecondBalanceDynamicStaticcallMem
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
 then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSafeTransferReturnDataPtr out1 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256))
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
 then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSafeTransferReturnDataPtr out1 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256))
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
          (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).size then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2).readWithPadding
          (skimSafeTransferReturnDataPtr out1).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32)) := by
  rw [if_neg]
  · rw [skimSecondBalanceDynamicStaticcallMem_read_ptr_of_size_ge self toWord value
      ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size]
  · have hsize :=
      skimSecondBalanceDynamicStaticcallMem_size_ge_ptr_add32_of_size_ge
        self toWord value ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size
    omega

theorem skimSecondBalanceDynamicCalldataMem_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) {out : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondBalanceDynamicCalldataMem self o toWord value out).size
 then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceDynamicCalldataMem self o toWord value out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSafeTransferReturnDataPtr out := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256))
    (v := skimSafeTransferReturnDataPtr out)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hsize :=
        skimSecondBalanceDynamicCalldataMem_size_ge96 self toWord value
          ho32 hoSize houtNe houtSize
      omega)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        skimSecondBalanceDynamicCalldataMem_read64 self toWord value
          ho32 hoSize houtNe houtSize)


end UniswapV2Pair
