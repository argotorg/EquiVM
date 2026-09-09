import Benchmarks.Dss.Flipper.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Shared storage helpers for packed `Bid` fields -/

def uint48Divisor20 : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩

def uint48Divisor26 : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩

abbrev flipperUint48Offset20Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (UInt256.div (flipperSlotWord slot σ I) uint48Divisor20) uint48Mask

abbrev flipperUint48Offset26Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (UInt256.div (flipperSlotWord slot σ I) uint48Divisor26) uint48Mask

abbrev bidBaseOfWord (id : UInt256) : UInt256 :=
  solcMappingSlot ⟨1⟩ id

abbrev bidPackedSlotOfWord (id : UInt256) : UInt256 :=
  bidBaseOfWord id + ⟨2⟩

theorem bidsBase_intOfNatWord (id : UInt256) :
    bidsBase (.int (Int.ofNat id.toNat)) = bidBaseOfWord id := by
  unfold bidsBase mapSlot bidBaseOfWord solcMappingSlot
  rw [keyValueToWord_uint256]

theorem keyValueToWord_uint256_natCast (w : UInt256) :
    keyValueToWord (.int ((w.toNat : Nat) : Int)) = w := by
  simpa using keyValueToWord_uint256 w

theorem flipperStorageLocLoad_uint48_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨20, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          uint48Divisor20) uint48Mask).toNat) := by
  have h := storageLocLoad_uint_offset (evm := evm) (slot := slot)
    (offset := ⟨20, by decide⟩) (size := (⟨6, by decide⟩ : Fin 33))
    (width := (⟨48, by decide⟩ : ABI.BitWidth)) (hbound := by decide)
    (hoff := by decide) (hsize := by decide)
  have hmask : UInt256.ofNat (256 ^ (⟨6, by decide⟩ : Fin 33).val - 1) =
      uint48Mask := by
    decide +native
  have hdiv : UInt256.ofNat (256 ^ (⟨20, by decide⟩ : Fin 32).val) =
      uint48Divisor20 := by
    decide +native
  simpa [uint48Loc, uint48Int, hmask, hdiv] using h

theorem flipperStorageLocLoad_uint48_offset26 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨26, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          uint48Divisor26) uint48Mask).toNat) := by
  have h := storageLocLoad_uint_offset (evm := evm) (slot := slot)
    (offset := ⟨26, by decide⟩) (size := (⟨6, by decide⟩ : Fin 33))
    (width := (⟨48, by decide⟩ : ABI.BitWidth)) (hbound := by decide)
    (hoff := by decide) (hsize := by decide)
  have hmask : UInt256.ofNat (256 ^ (⟨6, by decide⟩ : Fin 33).val - 1) =
      uint48Mask := by
    decide +native
  have hdiv : UInt256.ofNat (256 ^ (⟨26, by decide⟩ : Fin 32).val) =
      uint48Divisor26 := by
    decide +native
  simpa [uint48Loc, uint48Int, hmask, hdiv] using h

theorem natLandClearMiddle160_208 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1) =
      n % 2 ^ 160 + (n / 2 ^ 208) * 2 ^ 208 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1)).testBit i =
    (n % 2 ^ 160 + n / 2 ^ 208 * 2 ^ 208).testBit i
  have hmask :
      (2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1 =
        Nat.lor (2 ^ 160 - 1) ((2 ^ 48 - 1) <<< 208) := by
    rw [Nat.shiftLeft_eq]
    rw [nat_lor_shift_add (2 ^ 160 - 1) (2 ^ 48 - 1) 208]
    · norm_num [Nat.pow_add]
    · norm_num
  have hrhs :
      n % 2 ^ 160 + n / 2 ^ 208 * 2 ^ 208 =
        Nat.lor (n % 2 ^ 160) ((n / 2 ^ 208) * 2 ^ 208) := by
    rw [nat_lor_shift_add (n % 2 ^ 160) (n / 2 ^ 208) 208]
    · exact (Nat.mod_lt _ (by positivity : 0 < 2 ^ 160)).trans_le (by norm_num)
  rw [hmask, hrhs]
  rw [Nat.testBit_and]
  change (n.testBit i && (((2 ^ 160 - 1) ||| ((2 ^ 48 - 1) <<< 208)).testBit i)) =
    (((n % 2 ^ 160) ||| (n / 2 ^ 208 * 2 ^ 208)).testBit i)
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 208) * 2 ^ 208 = (n / 2 ^ 208) <<< 208 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  by_cases hi160 : i < 160
  · have hi208 : i < 208 := by omega
    simp [hi160, hi208]
  · have hnot160 : ¬ i < 160 := hi160
    by_cases hi208 : i < 208
    · simp [hnot160, hi208]
    · have h208le : 208 ≤ i := Nat.le_of_not_gt hi208
      by_cases hi256 : i < 256
      · have hlt48 : i - 208 < 48 := by omega
        have hmaskBit :
            Nat.testBit 281474976710655 (i - 208) = true := by
          change Nat.testBit (2 ^ 48 - 1) (i - 208) = true
          rw [Nat.testBit_two_pow_sub_one]
          simp [hlt48]
        simp [hnot160, hi208, hmaskBit]
        exact (divPow_testBit n 208 i h208le).symm
      · have hnot48 : ¬ i - 208 < 48 := by omega
        have hmaskBit :
            Nat.testBit 281474976710655 (i - 208) = false := by
          change Nat.testBit (2 ^ 48 - 1) (i - 208) = false
          rw [Nat.testBit_two_pow_sub_one]
          simp [hnot48]
        simp [hnot160, hi208, hmaskBit]
        have hq : n / 2 ^ 208 < 2 ^ 48 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by
            rw [← Nat.pow_add]]
          exact hn
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))

abbrev setUint48Offset20Word (old val : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
    (UInt256.shiftLeft (UInt256.land val uint48Mask) ⟨160⟩)

theorem setUint48Offset20Word_toNat (old val : UInt256) (hval : val.toNat < 2 ^ 48) :
    (setUint48Offset20Word old val).toNat =
      old.toNat % 2 ^ 160 + val.toNat * 2 ^ 160 +
        (old.toNat / 2 ^ 208) * 2 ^ 208 := by
  unfold setUint48Offset20Word
  have hclearMask :
      UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩) =
        UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1) := by
    decide +native
  have hvalLow : (UInt256.land val uint48Mask).toNat = val.toNat := by
    rw [u256_land_toNat]
    change Nat.land val.toNat (2 ^ 48 - 1) % UInt256.size = val.toNat
    rw [nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt hval]
    exact Nat.mod_eq_of_lt val.val.isLt
  have hshiftToNat :
      (UInt256.shiftLeft (UInt256.land val uint48Mask) ⟨160⟩).toNat =
        val.toNat * 2 ^ 160 := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide : ¬ ((⟨160⟩ : UInt256).val ≥ 256))]
    change (((UInt256.land val uint48Mask).toNat <<< 160) % UInt256.size) =
      val.toNat * 2 ^ 160
    rw [hvalLow, Nat.shiftLeft_eq]
    have hlt : val.toNat * 2 ^ 160 < UInt256.size := by
      calc
        val.toNat * 2 ^ 160 < 2 ^ 48 * 2 ^ 160 :=
          Nat.mul_lt_mul_of_pos_right hval (by norm_num)
        _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
    exact Nat.mod_eq_of_lt hlt
  have hclearToNat :
      (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩))).toNat =
        old.toNat % 2 ^ 160 + (old.toNat / 2 ^ 208) * 2 ^ 208 := by
    rw [hclearMask, u256_land_toNat]
    have hmaskLt :
        (2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1 < UInt256.size := by
      norm_num [UInt256.size]
    rw [ulit_toNat' _ hmaskLt]
    rw [natLandClearMiddle160_208 old.toNat old.val.isLt]
    have hlt :
        old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 < UInt256.size := by
      have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by positivity)
      have hq : old.toNat / 2 ^ 208 < 2 ^ 48 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
        exact old.val.isLt
      have hlowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
      have hqLe : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hq
      have hhighLe : old.toNat / 2 ^ 208 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
        Nat.mul_le_mul_right _ hqLe
      norm_num [UInt256.size, Nat.pow_add] at hlowLe hhighLe ⊢
      omega
    rw [Nat.mod_eq_of_lt hlt]
  rw [u256_lor_toNat, hclearToNat, hshiftToNat]
  let low := old.toNat % 2 ^ 160
  let mid := val.toNat * 2 ^ 160
  let high := old.toNat / 2 ^ 208 * 2 ^ 208
  have hlowLt : low < 2 ^ 160 := by
    exact Nat.mod_lt _ (by positivity)
  have hlowLt208 : low < 2 ^ 208 := lt_of_lt_of_le hlowLt (by norm_num)
  have hmidLt208 : mid < 2 ^ 208 := by
    calc
      mid = val.toNat * 2 ^ 160 := rfl
      _ < 2 ^ 48 * 2 ^ 160 := Nat.mul_lt_mul_of_pos_right hval (by norm_num)
      _ = 2 ^ 208 := by norm_num [Nat.pow_add]
  have hclearLor : low + high = Nat.lor low high := by
    rw [nat_lor_shift_add low (old.toNat / 2 ^ 208) 208 hlowLt208]
  have hmidHighLor : Nat.lor mid high = mid + high := by
    rw [nat_lor_shift_add mid (old.toNat / 2 ^ 208) 208 hmidLt208]
  have hlor :
      Nat.lor (low + high) mid = low + mid + high := by
    rw [hclearLor]
    change ((low ||| high) ||| mid) = low + mid + high
    rw [Nat.lor_assoc]
    rw [show high ||| mid = mid ||| high from nat_lor_comm high mid]
    rw [show mid ||| high = mid + high from hmidHighLor]
    have hfactor : mid + high =
        (val.toNat + old.toNat / 2 ^ 208 * 2 ^ 48) * 2 ^ 160 := by
      dsimp [mid, high]
      ring
    rw [hfactor]
    rw [show low ||| ((val.toNat + old.toNat / 2 ^ 208 * 2 ^ 48) * 2 ^ 160) =
        low + ((val.toNat + old.toNat / 2 ^ 208 * 2 ^ 48) * 2 ^ 160) from
      nat_lor_shift_add low (val.toNat + old.toNat / 2 ^ 208 * 2 ^ 48) 160 hlowLt]
    rw [← hfactor]
    ring
  rw [show old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 = low + high from rfl]
  rw [show val.toNat * 2 ^ 160 = mid from rfl]
  rw [hlor]
  have hlt : low + mid + high < UInt256.size := by
    have hq : old.toNat / 2 ^ 208 < 2 ^ 48 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      exact old.val.isLt
    have hlowLe : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlowLt
    have hvalLe : val.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hval
    have hqLe : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hq
    have hmidLe : mid ≤ (2 ^ 48 - 1) * 2 ^ 160 :=
      Nat.mul_le_mul_right _ hvalLe
    have hhighLe : high ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hqLe
    dsimp [low, mid, high] at hlowLe hmidLe hhighLe ⊢
    norm_num [UInt256.size, Nat.pow_add] at hlowLe hmidLe hhighLe ⊢
    omega
  rw [Nat.mod_eq_of_lt hlt]

theorem flipperStorageLocStore_uint48_offset20 (evm : EVM.State) (slot val : UInt256)
    (hval : val.toNat < 2 ^ 48) :
    storageLocStore evm (uint48Loc slot ⟨20, by decide⟩ (by decide))
      (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset20Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          val)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (6 : Fin 33).val _
        ++ List.drop ((20 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset20Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        val).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_take_wordLE,
    fromBytes'_drop_wordLE]
  have hwordToNat :=
    setUint48Offset20Word_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val hval
  rw [hwordToNat]
  rw [show 256 ^ 20 = (2 : Nat) ^ 160 by norm_num [Nat.pow_add]]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num [Nat.pow_add]]
  rw [Nat.mod_eq_of_lt hval]
  rw [List.length_append]
  rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
  rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
  rw [show 256 ^ (20 + 6) = (2 : Nat) ^ 208 by norm_num [Nat.pow_add]]
  norm_num [UInt256.size, Nat.pow_add]
  ring

abbrev setUint48Offset26Word (old val : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨208⟩)))
    (UInt256.shiftLeft (UInt256.land val uint48Mask) ⟨208⟩)

theorem uint48MulDivisor26_eq_shiftLeft (w : UInt256) :
    UInt256.mul w uint48Divisor26 = UInt256.shiftLeft w ⟨208⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨208⟩ : UInt256).val ≥ 256))]
  change w.toNat * uint48Divisor26.toNat % UInt256.size =
    (w.toNat <<< 208) % UInt256.size
  rw [show uint48Divisor26.toNat = 2 ^ 208 by decide +native]
  rw [Nat.shiftLeft_eq]

theorem setUint48Offset26RuntimeWord (old data : UInt256) :
    UInt256.lor
        (UInt256.land old (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
        (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor26) =
      setUint48Offset26Word old (UInt256.land data uint48Mask) := by
  have hlow :
      UInt256.land (UInt256.land data uint48Mask) uint48Mask =
        UInt256.land data uint48Mask := by
    exact uint48Mask_clean (uint48Mask_bound data)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩ =
        UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨208⟩) := by
    decide +native
  have hshift :
      UInt256.mul (UInt256.land data uint48Mask) uint48Divisor26 =
        UInt256.shiftLeft (UInt256.land data uint48Mask) ⟨208⟩ := by
    exact uint48MulDivisor26_eq_shiftLeft (UInt256.land data uint48Mask)
  calc
    UInt256.lor
        (UInt256.land old (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
        (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor26) =
        UInt256.lor
          (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨208⟩)))
          (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor26) := by
          rw [hmask]
    _ = UInt256.lor
          (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨208⟩)))
          (UInt256.shiftLeft (UInt256.land data uint48Mask) ⟨208⟩) := by
          rw [hshift]
    _ = setUint48Offset26Word old (UInt256.land data uint48Mask) := by
          unfold setUint48Offset26Word
          rw [hlow]

theorem setUint48Offset26Word_toNat (old val : UInt256) (hval : val.toNat < 2 ^ 48) :
    (setUint48Offset26Word old val).toNat =
      old.toNat % 2 ^ 208 + val.toNat * 2 ^ 208 := by
  unfold setUint48Offset26Word
  have hclearMask :
      UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨208⟩) =
        UInt256.ofNat ((2 : Nat) ^ 208 - 1) := by
    decide +native
  have hvalLow : (UInt256.land val uint48Mask).toNat = val.toNat := by
    rw [u256_land_toNat]
    change Nat.land val.toNat (2 ^ 48 - 1) % UInt256.size = val.toNat
    rw [nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt hval]
    exact Nat.mod_eq_of_lt val.val.isLt
  have hshiftToNat :
      (UInt256.shiftLeft (UInt256.land val uint48Mask) ⟨208⟩).toNat =
        val.toNat * 2 ^ 208 := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide : ¬ ((⟨208⟩ : UInt256).val ≥ 256))]
    change (((UInt256.land val uint48Mask).toNat <<< 208) % UInt256.size) =
      val.toNat * 2 ^ 208
    rw [hvalLow, Nat.shiftLeft_eq]
    have hlt : val.toNat * 2 ^ 208 < UInt256.size := by
      calc
        val.toNat * 2 ^ 208 < 2 ^ 48 * 2 ^ 208 :=
          Nat.mul_lt_mul_of_pos_right hval (by norm_num)
        _ = UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
    exact Nat.mod_eq_of_lt hlt
  have hclearToNat :
      (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨208⟩))).toNat =
        old.toNat % 2 ^ 208 := by
    rw [hclearMask, u256_land_toNat]
    have hmaskLt : (2 : Nat) ^ 208 - 1 < UInt256.size := by
      norm_num [UInt256.size]
    rw [ulit_toNat' _ hmaskLt]
    rw [nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt
      (lt_trans (Nat.mod_lt _ (by positivity : 0 < 2 ^ 208))
        (by norm_num [UInt256.size]))
  rw [u256_lor_toNat, hclearToNat, hshiftToNat]
  rw [nat_lor_shift_add (old.toNat % 2 ^ 208) val.toNat 208
    (Nat.mod_lt _ (by positivity : 0 < 2 ^ 208))]
  have hlt :
      old.toNat % 2 ^ 208 + val.toNat * 2 ^ 208 < UInt256.size := by
    have hlow : old.toNat % 2 ^ 208 < 2 ^ 208 := Nat.mod_lt _ (by positivity)
    have hlowLe : old.toNat % 2 ^ 208 ≤ 2 ^ 208 - 1 := Nat.le_pred_of_lt hlow
    have hvalLe : val.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hval
    have hhighLe : val.toNat * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hvalLe
    norm_num [UInt256.size, Nat.pow_add] at hlowLe hhighLe ⊢
    omega
  exact Nat.mod_eq_of_lt hlt

theorem flipperStorageLocStore_uint48_offset26 (evm : EVM.State) (slot val : UInt256)
    (hval : val.toNat < 2 ^ 48) :
    storageLocStore evm (uint48Loc slot ⟨26, by decide⟩ (by decide))
      (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset26Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          val)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (26 : Fin 32).val _ ++ List.take (6 : Fin 33).val _
        ++ List.drop ((26 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset26Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        val).toNat
  rw [show (26 : Fin 32).val = 26 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_take_wordLE,
    fromBytes'_drop_wordLE]
  have hwordToNat :=
    setUint48Offset26Word_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val hval
  rw [hwordToNat]
  rw [show 256 ^ 26 = (2 : Nat) ^ 208 by norm_num [Nat.pow_add]]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num [Nat.pow_add]]
  rw [Nat.mod_eq_of_lt hval]
  rw [List.length_append]
  rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
  rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
  rw [show 256 ^ (26 + 6) = UInt256.size by norm_num [UInt256.size, Nat.pow_add]]
  have hdiv0 :
      UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) /
          UInt256.size = 0 :=
    Nat.div_eq_of_lt (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
  rw [hdiv0]
  norm_num [UInt256.size, Nat.pow_add]
  ring

end Benchmarks.Dss.Flipper
