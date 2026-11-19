import Benchmarks.Midnight.PackedWrites

/-! The packed continuous-fee field at byte offset 14 of a market word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

abbrev uint32Offset14Mask : UInt256 :=
  UInt256.ofNat ((2 : Nat) ^ 144 - 2 ^ 112)

def setUint32Offset14Word (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint32Offset14Mask))
    (UInt256.mul (UInt256.land data uint32Mask) (UInt256.ofNat (2 ^ 112)))

theorem natLandKeepLow112High144 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (Nat.lor (2 ^ 112 - 1) (((2 : Nat) ^ (256 - 144) - 1) <<< 144)) =
      Nat.lor (n % 2 ^ 112) ((n / 2 ^ 144) * 2 ^ 144) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 ^ 112 - 1) ||| (((2 : Nat) ^ (256 - 144) - 1) <<< 144))).testBit i =
    ((n % 2 ^ 112) ||| ((n / 2 ^ 144) * 2 ^ 144)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 144) * 2 ^ 144 = (n / 2 ^ 144) <<< 144 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hi112 : i < 112
  · have hnot144 : ¬ 144 ≤ i := by omega
    simp [hi112, hnot144]
  · by_cases hi144 : i < 144
    · simp [hi112, hi144]
    · have h144le : 144 ≤ i := Nat.le_of_not_gt hi144
      by_cases hi256 : i < 256
      · have hlt : i - 144 < 256 - 144 := by omega
        simp [hi112, hi144, hlt]
        exact (divPow_testBit n 144 i h144le).symm
      · have hnlt : ¬ i - 144 < 256 - 144 := by omega
        simp [hi112, hi144, hnlt]
        have hq : n / 2 ^ 144 < 2 ^ (256 - 144) := by
          apply Nat.div_lt_of_lt_mul
          norm_num
          exact hn
        have hpow : n / 2 ^ 144 < 2 ^ (i - 144) := by
          exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact Nat.testBit_lt_two_pow hpow

theorem setUint32Offset14Word_toNat (old data : UInt256) :
    (setUint32Offset14Word old data).toNat =
      old.toNat % 2 ^ 112 +
        (UInt256.land data uint32Mask).toNat * 2 ^ 112 +
        (old.toNat / 2 ^ 144) * 2 ^ 144 := by
  unfold setUint32Offset14Word
  rw [u256_lor_toNat]
  have hnot : UInt256.lnot uint32Offset14Mask =
      UInt256.ofNat (Nat.lor (2 ^ 112 - 1) (((2 : Nat) ^ (256 - 144) - 1) <<< 144)) := by
    decide
  have hcleared : (UInt256.land old (UInt256.lnot uint32Offset14Mask)).toNat =
      Nat.lor (old.toNat % 2 ^ 112) ((old.toNat / 2 ^ 144) * 2 ^ 144) := by
    rw [hnot, u256_land_toNat]
    change Nat.land old.toNat
        (Nat.lor (2 ^ 112 - 1) (((2 : Nat) ^ (256 - 144) - 1) <<< 144)) %
        UInt256.size = _
    have hmaskLt :
        Nat.lor (2 ^ 112 - 1) (((2 : Nat) ^ (256 - 144) - 1) <<< 144) <
          UInt256.size := by
      decide
    have hlandLt : Nat.land old.toNat
        (Nat.lor (2 ^ 112 - 1) (((2 : Nat) ^ (256 - 144) - 1) <<< 144)) <
          UInt256.size :=
      lt_of_le_of_lt (nat_land_le_right _ _) hmaskLt
    rw [natLandKeepLow112High144 old.toNat (by
      change old.val.val < UInt256.size
      exact old.val.isLt)] at hlandLt ⊢
    exact Nat.mod_eq_of_lt hlandLt
  rw [hcleared]
  have hdataMul : (UInt256.mul (UInt256.land data uint32Mask)
      (UInt256.ofNat (2 ^ 112))).toNat =
      (UInt256.land data uint32Mask).toNat * 2 ^ 112 := by
    rw [u256_mul_toNat]
    rw [show (UInt256.ofNat (2 ^ 112)).toNat = 2 ^ 112 by decide]
    apply Nat.mod_eq_of_lt
    have hlow : (UInt256.land data uint32Mask).toNat < 2 ^ 32 := by
      exact u256LandMaskToNatLtOfToNat data _ (by decide)
    exact lt_trans (Nat.mul_lt_mul_of_pos_right hlow (by norm_num))
      (by norm_num [UInt256.size])
  rw [hdataMul]
  let low := old.toNat % 2 ^ 112
  let mid := (UInt256.land data uint32Mask).toNat
  let high := old.toNat / 2 ^ 144
  change Nat.lor (Nat.lor low (high * 2 ^ 144)) (mid * 2 ^ 112) % UInt256.size =
    low + mid * 2 ^ 112 + high * 2 ^ 144
  have hlowLt : low < 2 ^ 112 :=
    Nat.mod_lt _ (by norm_num)
  have hmidLt : mid < 2 ^ 32 := by
    exact u256LandMaskToNatLtOfToNat data _ (by decide)
  have hlowMidLt : low + mid * 2 ^ 112 < 2 ^ 144 := by
    have hlowLe : low ≤ 2 ^ 112 - 1 := Nat.le_pred_of_lt hlowLt
    have hmidLe : mid ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hmidLt
    have hmidTerm : mid * 2 ^ 112 ≤ (2 ^ 32 - 1) * 2 ^ 112 :=
      Nat.mul_le_mul_right _ hmidLe
    have hmax : (2 ^ 112 - 1) + (2 ^ 32 - 1) * 2 ^ 112 < 2 ^ 144 := by
      norm_num [Nat.pow_add]
    omega
  have hhighLt : high < 2 ^ 112 := by
    apply Nat.div_lt_of_lt_mul
    norm_num [high]
    change old.val.val < UInt256.size
    exact old.val.isLt
  have hsumLt : low + mid * 2 ^ 112 + high * 2 ^ 144 < UInt256.size := by
    have hlowMidLe : low + mid * 2 ^ 112 ≤ 2 ^ 144 - 1 := Nat.le_pred_of_lt hlowMidLt
    have hhighLe : high ≤ 2 ^ 112 - 1 := Nat.le_pred_of_lt hhighLt
    have hhighTerm : high * 2 ^ 144 ≤ (2 ^ 112 - 1) * 2 ^ 144 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax : (2 ^ 144 - 1) + (2 ^ 112 - 1) * 2 ^ 144 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have hlorReorder : Nat.lor (Nat.lor low (high * 2 ^ 144)) (mid * 2 ^ 112) =
      Nat.lor low (Nat.lor (mid * 2 ^ 112) (high * 2 ^ 144)) := by
    calc
      Nat.lor (Nat.lor low (high * 2 ^ 144)) (mid * 2 ^ 112) =
          Nat.lor low (Nat.lor (high * 2 ^ 144) (mid * 2 ^ 112)) := by
            exact Nat.lor_assoc low (high * 2 ^ 144) (mid * 2 ^ 112)
      _ = Nat.lor low (Nat.lor (mid * 2 ^ 112) (high * 2 ^ 144)) := by
            exact congrArg (Nat.lor low) (Nat.lor_comm (high * 2 ^ 144) (mid * 2 ^ 112))
  rw [hlorReorder]
  rw [show Nat.lor low (Nat.lor (mid * 2 ^ 112) (high * 2 ^ 144)) =
      Nat.lor (Nat.lor low (mid * 2 ^ 112)) (high * 2 ^ 144) by
        exact (Nat.lor_assoc low (mid * 2 ^ 112) (high * 2 ^ 144)).symm]
  rw [nat_lor_shift_add low mid 112 hlowLt]
  rw [nat_lor_shift_add (low + mid * 2 ^ 112) high 144 hlowMidLt]
  exact Nat.mod_eq_of_lt hsumLt


theorem storageLocStore_uint32_offset14_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (packedUInt32Loc slot ⟨14, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt32Modulus)) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint32Offset14Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord packedUInt32Loc
  simp only [valueToWord, wordOfInt_emod_uint32, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (14 : Fin 32).val _ ++ List.take (4 : Fin 33).val _ ++
        List.drop ((14 : Fin 32).val + (4 : Fin 33).val) _) =
      (setUint32Offset14Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        data).toNat
  rw [show (14 : Fin 32).val = 14 from rfl, show (4 : Fin 33).val = 4 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 4 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld6 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 14).length = 14 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  have hlenVal6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint32Mask)).1.take 4).length =
        4 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint32Mask)).2]
    norm_num
  rw [List.length_append, hlenOld6, hlenVal6]
  rw [show 2 ^ (8 * 4) = (2 : Nat) ^ 32 by norm_num]
  rw [show 256 ^ 14 = (2 : Nat) ^ 112 by norm_num]
  rw [show 256 ^ 18 = (2 : Nat) ^ 144 by norm_num]
  rw [setUint32Offset14Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint32Mask)
      (UInt256.ofNat (2 ^ 32 - 1)) = UInt256.land data uint32Mask := by
    exact maskTwice data _
  rw [hclean]
  ring

theorem setUint32Offset14Word_solc (old value : UInt256) (hvalue : value.toNat < 2 ^ 32) :
    UInt256.lor
      (UInt256.land (UInt256.shiftLeft ⟨4294967295⟩ ⟨112⟩) (UInt256.shiftLeft value ⟨112⟩))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨4294967295⟩ ⟨112⟩)) old) =
      setUint32Offset14Word old value := by
  have hm : UInt256.shiftLeft ⟨4294967295⟩ ⟨112⟩ = uint32Offset14Mask := by decide
  have hc : UInt256.land value uint32Mask = value :=
    u256LandMaskCleanOfToNat _ _ (by decide) hvalue
  have hfit : value.toNat * 2 ^ 112 < UInt256.size :=
    lt_trans (Nat.mul_lt_mul_of_pos_right hvalue (by decide)) (by decide)
  have hs : UInt256.shiftLeft value ⟨112⟩ = UInt256.mul value (UInt256.ofNat (2 ^ 112)) := by
    apply u256_inj
    rw [shiftLeft_toNat_of_noOverflow _ _ (by decide) hfit, u256_mul_toNat]
    change value.toNat * 2 ^ 112 = value.toNat * 2 ^ 112 % UInt256.size
    exact (Nat.mod_eq_of_lt hfit).symm
  have hclean : UInt256.land (UInt256.shiftLeft value ⟨112⟩) uint32Offset14Mask =
      UInt256.shiftLeft value ⟨112⟩ :=
    shiftLeft_land_mask value 32 112 (by decide) (by decide) hvalue
  rw [hm, u256_land_comm uint32Offset14Mask, hclean, hs]
  simp only [setUint32Offset14Word, hc, u256_lor_comm, u256_land_comm]

end Benchmarks.Midnight
