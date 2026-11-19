import Benchmarks.Midnight.PackedWrites

/-! The tick-spacing byte at offset 18 of a market word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def packedUInt8Int : IntType := .uint ⟨8, by decide⟩
def packedUInt8Modulus : Int := (2 : Int) ^ 8
def packedUInt8Loc (slot : UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int packedUInt8Int }
abbrev uint8Mask : UInt256 := ⟨255⟩

theorem wordOfInt_emod_uint8 (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat % packedUInt8Modulus) =
      UInt256.land w uint8Mask := by
  have hnonneg : 0 ≤ Int.ofNat w.toNat % packedUInt8Modulus := by
    exact Int.emod_nonneg _ (by norm_num [packedUInt8Modulus])
  have hcast : ((w.toNat % 2 ^ 8 : Nat) : Int) =
      Int.ofNat w.toNat % packedUInt8Modulus := by
    norm_num [packedUInt8Modulus, Int.natCast_mod]
  have htoNat : (Int.ofNat w.toNat % packedUInt8Modulus).toNat = w.toNat % 2 ^ 8 := by
    have h := congrArg Int.toNat hcast
    simpa using h.symm
  rw [wordOfInt_nonneg _ hnonneg]
  apply u256_inj
  change (Int.ofNat w.toNat % packedUInt8Modulus).toNat % EVM.twoPow 256 =
    (UInt256.land w uint8Mask).toNat
  rw [htoNat]
  rw [u256_land_toNat]
  change w.toNat % 2 ^ 8 % EVM.twoPow 256 =
    Nat.land w.toNat (2 ^ 8 - 1) % UInt256.size
  rw [nat_land_mask_eq_mod]
  simp [EVM.twoPow, UInt256.size]

abbrev uint8Offset18Mask : UInt256 :=
  UInt256.ofNat ((2 : Nat) ^ 152 - 2 ^ 144)

def setUint8Offset18Word (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint8Offset18Mask))
    (UInt256.mul (UInt256.land data uint8Mask) (UInt256.ofNat (2 ^ 144)))

theorem natLandKeepLow144High152 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (Nat.lor (2 ^ 144 - 1) (((2 : Nat) ^ (256 - 152) - 1) <<< 152)) =
      Nat.lor (n % 2 ^ 144) ((n / 2 ^ 152) * 2 ^ 152) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 ^ 144 - 1) ||| (((2 : Nat) ^ (256 - 152) - 1) <<< 152))).testBit i =
    ((n % 2 ^ 144) ||| ((n / 2 ^ 152) * 2 ^ 152)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 152) * 2 ^ 152 = (n / 2 ^ 152) <<< 152 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hi144 : i < 144
  · have hnot144 : ¬ 152 ≤ i := by omega
    simp [hi144, hnot144]
  · by_cases hi152 : i < 152
    · simp [hi144, hi152]
    · have h152le : 152 ≤ i := Nat.le_of_not_gt hi152
      by_cases hi256 : i < 256
      · have hlt : i - 152 < 256 - 152 := by omega
        simp [hi144, hi152, hlt]
        exact (divPow_testBit n 152 i h152le).symm
      · have hnlt : ¬ i - 152 < 256 - 152 := by omega
        simp [hi144, hi152, hnlt]
        have hq : n / 2 ^ 152 < 2 ^ (256 - 152) := by
          apply Nat.div_lt_of_lt_mul
          norm_num
          exact hn
        have hpow : n / 2 ^ 152 < 2 ^ (i - 152) := by
          exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact Nat.testBit_lt_two_pow hpow

theorem setUint8Offset18Word_toNat (old data : UInt256) :
    (setUint8Offset18Word old data).toNat =
      old.toNat % 2 ^ 144 +
        (UInt256.land data uint8Mask).toNat * 2 ^ 144 +
        (old.toNat / 2 ^ 152) * 2 ^ 152 := by
  unfold setUint8Offset18Word
  rw [u256_lor_toNat]
  have hnot : UInt256.lnot uint8Offset18Mask =
      UInt256.ofNat (Nat.lor (2 ^ 144 - 1) (((2 : Nat) ^ (256 - 152) - 1) <<< 152)) := by
    decide
  have hcleared : (UInt256.land old (UInt256.lnot uint8Offset18Mask)).toNat =
      Nat.lor (old.toNat % 2 ^ 144) ((old.toNat / 2 ^ 152) * 2 ^ 152) := by
    rw [hnot, u256_land_toNat]
    change Nat.land old.toNat
        (Nat.lor (2 ^ 144 - 1) (((2 : Nat) ^ (256 - 152) - 1) <<< 152)) %
        UInt256.size = _
    have hmaskLt :
        Nat.lor (2 ^ 144 - 1) (((2 : Nat) ^ (256 - 152) - 1) <<< 152) <
          UInt256.size := by
      decide
    have hlandLt : Nat.land old.toNat
        (Nat.lor (2 ^ 144 - 1) (((2 : Nat) ^ (256 - 152) - 1) <<< 152)) <
          UInt256.size :=
      lt_of_le_of_lt (nat_land_le_right _ _) hmaskLt
    rw [natLandKeepLow144High152 old.toNat (by
      change old.val.val < UInt256.size
      exact old.val.isLt)] at hlandLt ⊢
    exact Nat.mod_eq_of_lt hlandLt
  rw [hcleared]
  have hdataMul : (UInt256.mul (UInt256.land data uint8Mask)
      (UInt256.ofNat (2 ^ 144))).toNat =
      (UInt256.land data uint8Mask).toNat * 2 ^ 144 := by
    rw [u256_mul_toNat]
    rw [show (UInt256.ofNat (2 ^ 144)).toNat = 2 ^ 144 by decide]
    apply Nat.mod_eq_of_lt
    have hlow : (UInt256.land data uint8Mask).toNat < 2 ^ 8 := by
      exact u256LandMaskToNatLtOfToNat data _ (by decide)
    exact lt_trans (Nat.mul_lt_mul_of_pos_right hlow (by norm_num))
      (by norm_num [UInt256.size])
  rw [hdataMul]
  let low := old.toNat % 2 ^ 144
  let mid := (UInt256.land data uint8Mask).toNat
  let high := old.toNat / 2 ^ 152
  change Nat.lor (Nat.lor low (high * 2 ^ 152)) (mid * 2 ^ 144) % UInt256.size =
    low + mid * 2 ^ 144 + high * 2 ^ 152
  have hlowLt : low < 2 ^ 144 :=
    Nat.mod_lt _ (by norm_num)
  have hmidLt : mid < 2 ^ 8 := by
    exact u256LandMaskToNatLtOfToNat data _ (by decide)
  have hlowMidLt : low + mid * 2 ^ 144 < 2 ^ 152 := by
    have hlowLe : low ≤ 2 ^ 144 - 1 := Nat.le_pred_of_lt hlowLt
    have hmidLe : mid ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hmidLt
    have hmidTerm : mid * 2 ^ 144 ≤ (2 ^ 8 - 1) * 2 ^ 144 :=
      Nat.mul_le_mul_right _ hmidLe
    have hmax : (2 ^ 144 - 1) + (2 ^ 8 - 1) * 2 ^ 144 < 2 ^ 152 := by
      norm_num [Nat.pow_add]
    omega
  have hhighLt : high < 2 ^ 104 := by
    apply Nat.div_lt_of_lt_mul
    norm_num [high]
    change old.val.val < UInt256.size
    exact old.val.isLt
  have hsumLt : low + mid * 2 ^ 144 + high * 2 ^ 152 < UInt256.size := by
    have hlowMidLe : low + mid * 2 ^ 144 ≤ 2 ^ 152 - 1 := Nat.le_pred_of_lt hlowMidLt
    have hhighLe : high ≤ 2 ^ 104 - 1 := Nat.le_pred_of_lt hhighLt
    have hhighTerm : high * 2 ^ 152 ≤ (2 ^ 104 - 1) * 2 ^ 152 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax : (2 ^ 152 - 1) + (2 ^ 104 - 1) * 2 ^ 152 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have hlorReorder : Nat.lor (Nat.lor low (high * 2 ^ 152)) (mid * 2 ^ 144) =
      Nat.lor low (Nat.lor (mid * 2 ^ 144) (high * 2 ^ 152)) := by
    calc
      Nat.lor (Nat.lor low (high * 2 ^ 152)) (mid * 2 ^ 144) =
          Nat.lor low (Nat.lor (high * 2 ^ 152) (mid * 2 ^ 144)) := by
            exact Nat.lor_assoc low (high * 2 ^ 152) (mid * 2 ^ 144)
      _ = Nat.lor low (Nat.lor (mid * 2 ^ 144) (high * 2 ^ 152)) := by
            exact congrArg (Nat.lor low) (Nat.lor_comm (high * 2 ^ 152) (mid * 2 ^ 144))
  rw [hlorReorder]
  rw [show Nat.lor low (Nat.lor (mid * 2 ^ 144) (high * 2 ^ 152)) =
      Nat.lor (Nat.lor low (mid * 2 ^ 144)) (high * 2 ^ 152) by
        exact (Nat.lor_assoc low (mid * 2 ^ 144) (high * 2 ^ 152)).symm]
  rw [nat_lor_shift_add low mid 144 hlowLt]
  rw [nat_lor_shift_add (low + mid * 2 ^ 144) high 152 hlowMidLt]
  exact Nat.mod_eq_of_lt hsumLt


theorem storageLocStore_uint8_offset18_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (packedUInt8Loc slot ⟨18, by decide⟩)
        (.int (Int.ofNat data.toNat % packedUInt8Modulus)) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint8Offset18Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord packedUInt8Loc
  simp only [valueToWord, wordOfInt_emod_uint8, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (18 : Fin 32).val _ ++ List.take (1 : Fin 33).val _ ++
        List.drop ((18 : Fin 32).val + (1 : Fin 33).val) _) =
      (setUint8Offset18Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        data).toNat
  rw [show (18 : Fin 32).val = 18 from rfl, show (1 : Fin 33).val = 1 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 1 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld18 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 18).length = 18 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  have hlenVal1 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint8Mask)).1.take 1).length =
        1 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint8Mask)).2]
    norm_num
  rw [List.length_append, hlenOld18, hlenVal1]
  rw [show 2 ^ (8 * 1) = (2 : Nat) ^ 8 by norm_num]
  rw [show 256 ^ 18 = (2 : Nat) ^ 144 by norm_num]
  rw [show 256 ^ 19 = (2 : Nat) ^ 152 by norm_num]
  rw [setUint8Offset18Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint8Mask)
      (UInt256.ofNat (2 ^ 8 - 1)) = UInt256.land data uint8Mask := by
    exact maskTwice data _
  rw [hclean]
  ring

theorem setUint8Offset18Word_solc (old value : UInt256) (hvalue : value.toNat < 2 ^ 8) :
    UInt256.lor
      (UInt256.land (UInt256.shiftLeft ⟨255⟩ ⟨144⟩) (UInt256.shiftLeft value ⟨144⟩))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨255⟩ ⟨144⟩)) old) =
      setUint8Offset18Word old value := by
  have hm : UInt256.shiftLeft ⟨255⟩ ⟨144⟩ = uint8Offset18Mask := by decide
  have hc : UInt256.land value uint8Mask = value :=
    u256LandMaskCleanOfToNat _ _ (by decide) hvalue
  have hfit : value.toNat * 2 ^ 144 < UInt256.size :=
    lt_trans (Nat.mul_lt_mul_of_pos_right hvalue (by decide)) (by decide)
  have hs : UInt256.shiftLeft value ⟨144⟩ = UInt256.mul value (UInt256.ofNat (2 ^ 144)) := by
    apply u256_inj
    rw [shiftLeft_toNat_of_noOverflow _ _ (by decide) hfit, u256_mul_toNat]
    change value.toNat * 2 ^ 144 = value.toNat * 2 ^ 144 % UInt256.size
    exact (Nat.mod_eq_of_lt hfit).symm
  have hclean : UInt256.land (UInt256.shiftLeft value ⟨144⟩) uint8Offset18Mask =
      UInt256.shiftLeft value ⟨144⟩ :=
    shiftLeft_land_mask value 8 144 (by decide) (by decide) hvalue
  rw [hm, u256_land_comm uint8Offset18Mask, hclean, hs]
  simp only [setUint8Offset18Word, hc, u256_lor_comm, u256_land_comm]

end Benchmarks.Midnight
