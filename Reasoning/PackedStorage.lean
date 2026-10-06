import Reasoning.Storage

/-!
# Packed storage helpers

Shared uint48 and boolean field updates, including their byte-level storage semantics.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

def packedUInt48Int : IntType := .uint ⟨48, by decide⟩
def packedUInt48Modulus : Int := (2 : Int) ^ 48
def packedUInt48StorageType : StorageType := .elem (.int packedUInt48Int)
def packedUInt256StorageType : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
def packedAddressStorageType : StorageType := .elem .address

def packedUInt48Loc (slot : UInt256) (offset : Fin 32)
    (hbound : offset.val + 6 - 1 < 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 6, hbound := hbound, type := .int packedUInt48Int }

def packedBoolLocAt (slot : UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .bool }

abbrev uint48Mask : UInt256 :=
  ⟨0xffffffffffff⟩

def uint48Offset0Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (solcSlotWordAt slot σ I) uint48Mask

def uint48Offset6Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land uint48Mask
    (UInt256.div (solcSlotWordAt slot σ I) (UInt256.ofNat (256 ^ 6)))

def uint48Offset20Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land uint48Mask
    (UInt256.div (solcSlotWordAt slot σ I) (UInt256.ofNat (256 ^ 20)))

def uint48Offset26Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land uint48Mask
    (UInt256.div (solcSlotWordAt slot σ I) (UInt256.ofNat (256 ^ 26)))

theorem uint48Masked_lt (w : UInt256) :
    (UInt256.land w uint48Mask).toNat < EVM.twoPow 48 := by
  show Nat.land w.toNat uint48Mask.toNat % UInt256.size < EVM.twoPow 48
  have hle := nat_land_le_right w.toNat uint48Mask.toNat
  have hltSize : Nat.land w.toNat uint48Mask.toNat < UInt256.size :=
    lt_of_le_of_lt hle (by decide)
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by decide)

theorem uint48Mask_clean_of_canonical {w : UInt256}
    (h : w.toNat < EVM.twoPow 48) :
    UInt256.land w uint48Mask = w := by
  apply u256_inj
  change Nat.land w.toNat (2 ^ 48 - 1) % UInt256.size = w.toNat
  have h' : w.toNat < 2 ^ 48 := by
    simpa [EVM.twoPow] using h
  rw [nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt h']
  exact Nat.mod_eq_of_lt (lt_trans h (by decide))

theorem uint48Mask_clean (w : UInt256) :
    UInt256.land (UInt256.land w uint48Mask) uint48Mask =
      UInt256.land w uint48Mask :=
  uint48Mask_clean_of_canonical (uint48Masked_lt w)

theorem storageLocLoad_uint48_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (packedUInt48Loc slot ⟨0, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    storageLocLoad_uint_offset0 evm slot ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem storageLocLoad_uint48_offset6 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (packedUInt48Loc slot ⟨6, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 6)))
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    storageLocLoad_uint_offset evm slot ⟨6, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide) (by decide)

theorem storageLocLoad_uint48_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 20)))
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    storageLocLoad_uint_offset evm slot ⟨20, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide) (by decide)

theorem storageLocLoad_uint48_offset26 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 26)))
        uint48Mask).toNat) := by
  simpa [packedUInt48Loc, uint48Mask] using
    storageLocLoad_uint_offset evm slot ⟨26, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide) (by decide)

theorem wordOfInt_emod_uint48 (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat % packedUInt48Modulus) =
      UInt256.land w uint48Mask := by
  have hnonneg : 0 ≤ Int.ofNat w.toNat % packedUInt48Modulus := by
    exact Int.emod_nonneg _ (by norm_num [packedUInt48Modulus])
  have hcast : ((w.toNat % 2 ^ 48 : Nat) : Int) =
      Int.ofNat w.toNat % packedUInt48Modulus := by
    norm_num [packedUInt48Modulus, Int.natCast_mod]
  have htoNat : (Int.ofNat w.toNat % packedUInt48Modulus).toNat = w.toNat % 2 ^ 48 := by
    have h := congrArg Int.toNat hcast
    simpa using h.symm
  rw [wordOfInt_nonneg _ hnonneg]
  apply u256_inj
  change (Int.ofNat w.toNat % packedUInt48Modulus).toNat % EVM.twoPow 256 =
    (UInt256.land w uint48Mask).toNat
  rw [htoNat]
  rw [u256_land_toNat]
  change w.toNat % 2 ^ 48 % EVM.twoPow 256 =
    Nat.land w.toNat (2 ^ 48 - 1) % UInt256.size
  rw [nat_land_mask_eq_mod]
  simp [EVM.twoPow, UInt256.size]

def setUint48Offset0Word (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint48Mask))
    (UInt256.land data uint48Mask)

theorem setUint48Offset0Word_toNat (old data : UInt256) :
    (setUint48Offset0Word old data).toNat =
      (UInt256.land data uint48Mask).toNat + (old.toNat / 2 ^ 48) * 2 ^ 48 := by
  unfold setUint48Offset0Word
  rw [u256_lor_toNat]
  have hhighMask :
      UInt256.lnot uint48Mask = UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 48) := by
    decide
  rw [hhighMask]
  rw [u256_land_comm old (UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 48))]
  rw [u256_land_high_mask_toNat old 48 (by norm_num)]
  rw [nat_lor_comm]
  have hlow : (UInt256.land data uint48Mask).toNat < 2 ^ 48 := by
    simpa [uint48Mask, EVM.twoPow] using uint48Masked_lt data
  rw [nat_lor_shift_add _ _ 48 hlow]
  have hsumLt :
      (UInt256.land data uint48Mask).toNat + old.toNat / 2 ^ 48 * 2 ^ 48 <
        UInt256.size := by
    have hq : old.toNat / 2 ^ 48 < 2 ^ 208 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 48 * 2 ^ 208 = (2 : Nat) ^ 256 by norm_num]
      change old.val.val < 2 ^ 256
      exact old.val.isLt
    have hlowle : (UInt256.land data uint48Mask).toNat ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt hlow
    have hqle : old.toNat / 2 ^ 48 ≤ 2 ^ 208 - 1 := Nat.le_pred_of_lt hq
    have hqterm : old.toNat / 2 ^ 48 * 2 ^ 48 ≤ (2 ^ 208 - 1) * 2 ^ 48 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 48 - 1) + (2 ^ 208 - 1) * 2 ^ 48 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hsumLt]

theorem storageLocStore_uint48_offset0_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (packedUInt48Loc slot ⟨0, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((0 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        data).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (6 : Fin 33).val = 6 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append]
  rw [fromBytes'_take_wordLE_land_mask _ 6 (by norm_num)]
  rw [fromBytes'_drop_wordLE]
  have hlen6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [hlen6]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [setUint48Offset0Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  ring

abbrev uint48Offset6Mask : UInt256 :=
  UInt256.ofNat ((2 : Nat) ^ 96 - 2 ^ 48)

def setUint48Offset6Word (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint48Offset6Mask))
    (UInt256.mul (UInt256.land data uint48Mask) (UInt256.ofNat (2 ^ 48)))

theorem natLandKeepLow48High96 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (Nat.lor (2 ^ 48 - 1) (((2 : Nat) ^ (256 - 96) - 1) <<< 96)) =
      Nat.lor (n % 2 ^ 48) ((n / 2 ^ 96) * 2 ^ 96) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 ^ 48 - 1) ||| (((2 : Nat) ^ (256 - 96) - 1) <<< 96))).testBit i =
    ((n % 2 ^ 48) ||| ((n / 2 ^ 96) * 2 ^ 96)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 96) * 2 ^ 96 = (n / 2 ^ 96) <<< 96 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hi48 : i < 48
  · have hnot96 : ¬ 96 ≤ i := by omega
    simp [hi48, hnot96]
  · by_cases hi96 : i < 96
    · simp [hi48, hi96]
    · have h96le : 96 ≤ i := Nat.le_of_not_gt hi96
      by_cases hi256 : i < 256
      · have hlt : i - 96 < 256 - 96 := by omega
        simp [hi48, hi96, hlt]
        exact (divPow_testBit n 96 i h96le).symm
      · have hnlt : ¬ i - 96 < 256 - 96 := by omega
        simp [hi48, hi96, hnlt]
        have hq : n / 2 ^ 96 < 2 ^ (256 - 96) := by
          apply Nat.div_lt_of_lt_mul
          norm_num
          exact hn
        have hpow : n / 2 ^ 96 < 2 ^ (i - 96) := by
          exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact Nat.testBit_lt_two_pow hpow

theorem setUint48Offset6Word_toNat (old data : UInt256) :
    (setUint48Offset6Word old data).toNat =
      old.toNat % 2 ^ 48 +
        (UInt256.land data uint48Mask).toNat * 2 ^ 48 +
        (old.toNat / 2 ^ 96) * 2 ^ 96 := by
  unfold setUint48Offset6Word
  rw [u256_lor_toNat]
  have hnot : UInt256.lnot uint48Offset6Mask =
      UInt256.ofNat (Nat.lor (2 ^ 48 - 1) (((2 : Nat) ^ (256 - 96) - 1) <<< 96)) := by
    decide
  have hcleared : (UInt256.land old (UInt256.lnot uint48Offset6Mask)).toNat =
      Nat.lor (old.toNat % 2 ^ 48) ((old.toNat / 2 ^ 96) * 2 ^ 96) := by
    rw [hnot, u256_land_toNat]
    change Nat.land old.toNat
        (Nat.lor (2 ^ 48 - 1) (((2 : Nat) ^ (256 - 96) - 1) <<< 96)) %
        UInt256.size = _
    have hmaskLt :
        Nat.lor (2 ^ 48 - 1) (((2 : Nat) ^ (256 - 96) - 1) <<< 96) <
          UInt256.size := by
      decide
    have hlandLt : Nat.land old.toNat
        (Nat.lor (2 ^ 48 - 1) (((2 : Nat) ^ (256 - 96) - 1) <<< 96)) <
          UInt256.size :=
      lt_of_le_of_lt (nat_land_le_right _ _) hmaskLt
    rw [natLandKeepLow48High96 old.toNat (by
      change old.val.val < UInt256.size
      exact old.val.isLt)] at hlandLt ⊢
    exact Nat.mod_eq_of_lt hlandLt
  rw [hcleared]
  have hdataMul : (UInt256.mul (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48))).toNat =
      (UInt256.land data uint48Mask).toNat * 2 ^ 48 := by
    rw [u256_mul_toNat]
    rw [show (UInt256.ofNat (2 ^ 48)).toNat = 2 ^ 48 by decide]
    apply Nat.mod_eq_of_lt
    have hlow : (UInt256.land data uint48Mask).toNat < 2 ^ 48 := by
      simpa [uint48Mask, EVM.twoPow] using uint48Masked_lt data
    exact lt_trans (Nat.mul_lt_mul_of_pos_right hlow (by norm_num))
      (by norm_num [UInt256.size])
  rw [hdataMul]
  let low := old.toNat % 2 ^ 48
  let mid := (UInt256.land data uint48Mask).toNat
  let high := old.toNat / 2 ^ 96
  change Nat.lor (Nat.lor low (high * 2 ^ 96)) (mid * 2 ^ 48) % UInt256.size =
    low + mid * 2 ^ 48 + high * 2 ^ 96
  have hlowLt : low < 2 ^ 48 :=
    Nat.mod_lt _ (by norm_num)
  have hmidLt : mid < 2 ^ 48 := by
    simpa [mid, uint48Mask, EVM.twoPow] using uint48Masked_lt data
  have hlowMidLt : low + mid * 2 ^ 48 < 2 ^ 96 := by
    have hlowLe : low ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlowLt
    have hmidLe : mid ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hmidLt
    have hmidTerm : mid * 2 ^ 48 ≤ (2 ^ 48 - 1) * 2 ^ 48 :=
      Nat.mul_le_mul_right _ hmidLe
    have hmax : (2 ^ 48 - 1) + (2 ^ 48 - 1) * 2 ^ 48 < 2 ^ 96 := by
      norm_num [Nat.pow_add]
    omega
  have hhighLt : high < 2 ^ 160 := by
    apply Nat.div_lt_of_lt_mul
    norm_num [high]
    change old.val.val < UInt256.size
    exact old.val.isLt
  have hsumLt : low + mid * 2 ^ 48 + high * 2 ^ 96 < UInt256.size := by
    have hlowMidLe : low + mid * 2 ^ 48 ≤ 2 ^ 96 - 1 := Nat.le_pred_of_lt hlowMidLt
    have hhighLe : high ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hhighLt
    have hhighTerm : high * 2 ^ 96 ≤ (2 ^ 160 - 1) * 2 ^ 96 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax : (2 ^ 96 - 1) + (2 ^ 160 - 1) * 2 ^ 96 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have hlorReorder : Nat.lor (Nat.lor low (high * 2 ^ 96)) (mid * 2 ^ 48) =
      Nat.lor low (Nat.lor (mid * 2 ^ 48) (high * 2 ^ 96)) := by
    calc
      Nat.lor (Nat.lor low (high * 2 ^ 96)) (mid * 2 ^ 48) =
          Nat.lor low (Nat.lor (high * 2 ^ 96) (mid * 2 ^ 48)) := by
            exact Nat.lor_assoc low (high * 2 ^ 96) (mid * 2 ^ 48)
      _ = Nat.lor low (Nat.lor (mid * 2 ^ 48) (high * 2 ^ 96)) := by
            exact congrArg (Nat.lor low) (Nat.lor_comm (high * 2 ^ 96) (mid * 2 ^ 48))
  rw [hlorReorder]
  rw [show Nat.lor low (Nat.lor (mid * 2 ^ 48) (high * 2 ^ 96)) =
      Nat.lor (Nat.lor low (mid * 2 ^ 48)) (high * 2 ^ 96) by
        exact (Nat.lor_assoc low (mid * 2 ^ 48) (high * 2 ^ 96)).symm]
  rw [nat_lor_shift_add low mid 48 hlowLt]
  rw [nat_lor_shift_add (low + mid * 2 ^ 48) high 96 hlowMidLt]
  exact Nat.mod_eq_of_lt hsumLt

theorem storageLocStore_uint48_offset6_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (packedUInt48Loc slot ⟨6, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (6 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((6 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        data).toNat
  rw [show (6 : Fin 32).val = 6 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 6 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld6 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 6).length = 6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  have hlenVal6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld6, hlenVal6]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 12 = (2 : Nat) ^ 96 by norm_num]
  rw [setUint48Offset6Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  ring

theorem clearStorage_uint256_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : cfg.storage.layout er evm = some (uint256Loc slot)) :
    clearStorage? cfg evm er packedUInt256StorageType =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [packedUInt256StorageType]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (uint256Loc slot) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))) =
    .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩)
  rw [storageLocStore_uint256 evm slot (⟨0⟩ : UInt256)]
  rfl

theorem storageLocStore_addr_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (addressOffset0Loc slot) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) :=
          by
  unfold storageLocStore storageLocWriteWord addressOffset0Loc
  simp only [valueToWord, Reasoning.Theory.wordOfInt_zero, bind, Option.bind]
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (⟨0⟩ : UInt256)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask, fromBytes'_drop_wordLE]
  have hclean : (UInt256.land (⟨0⟩ : UInt256) solcAddrMask).toNat = (0 : Nat) := by
    decide
  rw [hclean]
  have hlen20 :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [setAddressOffset0Word_toNat _ _ (by decide)]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  ring

theorem clearStorage_addr_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : cfg.storage.layout er evm = some (addressOffset0Loc slot)) :
    clearStorage? cfg evm er packedAddressStorageType =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) :=
          by
  rw [Solm.clearStorage?.eq_def]
  simp only [packedAddressStorageType]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (addressOffset0Loc slot) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))) =
    .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩))
  rw [show (Int.ofNat (⟨0⟩ : UInt256).toNat) = 0 from rfl]
  rw [storageLocStore_addr_zero]
  rfl

def clearUint48Offset20Word (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208)

def clearUint48Offset26Word (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 208)

def setUint48Offset26Word (old data : UInt256) : UInt256 :=
  UInt256.ofNat
    (old.toNat % 2 ^ 208 + (UInt256.land data uint48Mask).toNat * 2 ^ 208)

def setUint48Offset20Word (old data : UInt256) : UInt256 :=
  UInt256.ofNat
    (old.toNat % 2 ^ 160 + (UInt256.land data uint48Mask).toNat * 2 ^ 160 +
      old.toNat / 2 ^ 208 * 2 ^ 208)

theorem clearUint48Offset20Word_toNat (old : UInt256) :
    (clearUint48Offset20Word old).toNat =
      old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 := by
  unfold clearUint48Offset20Word
  have hsumLt : old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 < UInt256.size := by
    have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
    have hhigh : old.toNat / 2 ^ 208 < 2 ^ 48 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by norm_num]
      change old.val.val < UInt256.size
      exact old.val.isLt
    have hlowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hhighLe : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hhigh
    have hhighTerm : old.toNat / 2 ^ 208 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax : (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  exact UInt256.toNat_ofNat_of_lt hsumLt

theorem clearUint48Offset26Word_toNat (old : UInt256) :
    (clearUint48Offset26Word old).toNat = old.toNat % 2 ^ 208 := by
  unfold clearUint48Offset26Word
  have hlt : old.toNat % 2 ^ 208 < UInt256.size :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size])
  exact UInt256.toNat_ofNat_of_lt hlt

theorem setUint48Offset26Word_toNat (old data : UInt256) :
    (setUint48Offset26Word old data).toNat =
      old.toNat % 2 ^ 208 + (UInt256.land data uint48Mask).toNat * 2 ^ 208 := by
  unfold setUint48Offset26Word
  have hsumLt :
      old.toNat % 2 ^ 208 + (UInt256.land data uint48Mask).toNat * 2 ^ 208 <
        UInt256.size := by
    have hlow : old.toNat % 2 ^ 208 < 2 ^ 208 := Nat.mod_lt _ (by norm_num)
    have hdata : (UInt256.land data uint48Mask).toNat < 2 ^ 48 := by
      simpa [uint48Mask, EVM.twoPow] using uint48Masked_lt data
    have hlowLe : old.toNat % 2 ^ 208 ≤ 2 ^ 208 - 1 := Nat.le_pred_of_lt hlow
    have hdataLe : (UInt256.land data uint48Mask).toNat ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt hdata
    have hdataTerm :
        (UInt256.land data uint48Mask).toNat * 2 ^ 208 ≤
          (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hdataLe
    have hmax : (2 ^ 208 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  exact UInt256.toNat_ofNat_of_lt hsumLt

theorem setUint48Offset20Word_toNat (old data : UInt256) :
    (setUint48Offset20Word old data).toNat =
      old.toNat % 2 ^ 160 + (UInt256.land data uint48Mask).toNat * 2 ^ 160 +
        old.toNat / 2 ^ 208 * 2 ^ 208 := by
  unfold setUint48Offset20Word
  have hsumLt :
      old.toNat % 2 ^ 160 + (UInt256.land data uint48Mask).toNat * 2 ^ 160 +
          old.toNat / 2 ^ 208 * 2 ^ 208 <
        UInt256.size := by
    have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
    have hdata : (UInt256.land data uint48Mask).toNat < 2 ^ 48 := by
      simpa [uint48Mask, EVM.twoPow] using uint48Masked_lt data
    have hhigh : old.toNat / 2 ^ 208 < 2 ^ 48 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by norm_num]
      change old.val.val < UInt256.size
      exact old.val.isLt
    have hlowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hdataLe : (UInt256.land data uint48Mask).toNat ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt hdata
    have hhighLe : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hhigh
    have hdataTerm :
        (UInt256.land data uint48Mask).toNat * 2 ^ 160 ≤
          (2 ^ 48 - 1) * 2 ^ 160 :=
      Nat.mul_le_mul_right _ hdataLe
    have hhighTerm : old.toNat / 2 ^ 208 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax :
        (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 160 +
            (2 ^ 48 - 1) * 2 ^ 208 <
          UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  exact UInt256.toNat_ofNat_of_lt hsumLt

def setUint48Offset20RawWord (old data : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
    (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
      (UInt256.land uint48Mask data))

theorem natLandKeepLow160High208 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208)) =
      Nat.lor (n % 2 ^ 160) ((n / 2 ^ 208) * 2 ^ 208) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change
    (n &&& ((2 ^ 160 - 1) ||| (((2 : Nat) ^ (256 - 208) - 1) <<< 208))).testBit i =
      ((n % 2 ^ 160) ||| ((n / 2 ^ 208) * 2 ^ 208)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 208) * 2 ^ 208 = (n / 2 ^ 208) <<< 208 by
    rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hi160 : i < 160
  · have hnot208 : ¬ 208 ≤ i := by omega
    simp [hi160, hnot208]
  · by_cases hi208 : i < 208
    · simp [hi160, hi208]
    · have h208le : 208 ≤ i := Nat.le_of_not_gt hi208
      by_cases hi256 : i < 256
      · have hlt : i - 208 < 256 - 208 := by omega
        simp [hi160, hi208, hlt]
        exact (divPow_testBit n 208 i h208le).symm
      · have hnlt : ¬ i - 208 < 256 - 208 := by omega
        simp [hi160, hi208, hnlt]
        have hq : n / 2 ^ 208 < 2 ^ (256 - 208) := by
          apply Nat.div_lt_of_lt_mul
          norm_num
          exact hn
        have hpow : n / 2 ^ 208 < 2 ^ (i - 208) := by
          exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact Nat.testBit_lt_two_pow hpow

theorem setUint48Offset20RawWord_eq_setUint48Offset20Word (old data : UInt256) :
    setUint48Offset20RawWord old data = setUint48Offset20Word old data := by
  apply u256_inj
  rw [setUint48Offset20RawWord]
  rw [u256_lor_toNat]
  have hnot :
      UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩) =
        UInt256.ofNat (Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208)) := by
    decide
  have hcleared :
      (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩))).toNat =
        Nat.lor (old.toNat % 2 ^ 160) ((old.toNat / 2 ^ 208) * 2 ^ 208) := by
    rw [hnot, u256_land_toNat]
    change Nat.land old.toNat
        (Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208)) %
        UInt256.size =
      _
    have hmaskLt :
        Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208) <
          UInt256.size := by
      decide
    have hlandLt :
        Nat.land old.toNat
            (Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208)) <
          UInt256.size :=
      lt_of_le_of_lt (nat_land_le_right _ _) hmaskLt
    rw [natLandKeepLow160High208 old.toNat (by
      change old.val.val < UInt256.size
      exact old.val.isLt)] at hlandLt ⊢
    exact Nat.mod_eq_of_lt hlandLt
  have hshifted :
      (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
          (UInt256.land uint48Mask data)).toNat =
        (UInt256.land data uint48Mask).toNat * 2 ^ 160 := by
    rw [u256_mul_toNat]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩).toNat = 2 ^ 160 by
      decide]
    rw [show (UInt256.land uint48Mask data).toNat =
      (UInt256.land data uint48Mask).toNat by rw [u256_land_comm]]
    rw [Nat.mul_comm (2 ^ 160) (UInt256.land data uint48Mask).toNat]
    apply Nat.mod_eq_of_lt
    have hmid : (UInt256.land data uint48Mask).toNat < 2 ^ 48 := by
      simpa [uint48Mask, EVM.twoPow] using uint48Masked_lt data
    exact lt_trans (Nat.mul_lt_mul_of_pos_right hmid (by norm_num))
      (by norm_num [UInt256.size])
  rw [hcleared, hshifted]
  rw [setUint48Offset20Word_toNat]
  let low := old.toNat % 2 ^ 160
  let mid := (UInt256.land data uint48Mask).toNat
  let high := old.toNat / 2 ^ 208
  change Nat.lor (Nat.lor low (high * 2 ^ 208)) (mid * 2 ^ 160) % UInt256.size =
    low + mid * 2 ^ 160 + high * 2 ^ 208
  have hlowLt : low < 2 ^ 160 :=
    Nat.mod_lt _ (by norm_num)
  have hmidLt : mid < 2 ^ 48 := by
    simpa [mid, uint48Mask, EVM.twoPow] using uint48Masked_lt data
  have hlowMidLt : low + mid * 2 ^ 160 < 2 ^ 208 := by
    have hlowLe : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlowLt
    have hmidLe : mid ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hmidLt
    have hmidTerm : mid * 2 ^ 160 ≤ (2 ^ 48 - 1) * 2 ^ 160 :=
      Nat.mul_le_mul_right _ hmidLe
    have hmax : (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 160 < 2 ^ 208 := by
      norm_num [Nat.pow_add]
    omega
  have hhighLt : high < 2 ^ 48 := by
    apply Nat.div_lt_of_lt_mul
    norm_num [high]
    change old.val.val < UInt256.size
    exact old.val.isLt
  have hsumLt : low + mid * 2 ^ 160 + high * 2 ^ 208 < UInt256.size := by
    have hlowMidLe : low + mid * 2 ^ 160 ≤ 2 ^ 208 - 1 :=
      Nat.le_pred_of_lt hlowMidLt
    have hhighLe : high ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hhighLt
    have hhighTerm : high * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax : (2 ^ 208 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have hlorReorder :
      Nat.lor (Nat.lor low (high * 2 ^ 208)) (mid * 2 ^ 160) =
        Nat.lor low (Nat.lor (mid * 2 ^ 160) (high * 2 ^ 208)) := by
    calc
      Nat.lor (Nat.lor low (high * 2 ^ 208)) (mid * 2 ^ 160) =
          Nat.lor low (Nat.lor (high * 2 ^ 208) (mid * 2 ^ 160)) := by
            exact Nat.lor_assoc low (high * 2 ^ 208) (mid * 2 ^ 160)
      _ = Nat.lor low (Nat.lor (mid * 2 ^ 160) (high * 2 ^ 208)) := by
            exact congrArg (Nat.lor low) (Nat.lor_comm (high * 2 ^ 208) (mid * 2 ^ 160))
  rw [hlorReorder]
  rw [show Nat.lor low (Nat.lor (mid * 2 ^ 160) (high * 2 ^ 208)) =
      Nat.lor (Nat.lor low (mid * 2 ^ 160)) (high * 2 ^ 208) by
        exact (Nat.lor_assoc low (mid * 2 ^ 160) (high * 2 ^ 208)).symm]
  rw [nat_lor_shift_add low mid 160 hlowLt]
  rw [nat_lor_shift_add (low + mid * 2 ^ 160) high 208 hlowMidLt]
  exact Nat.mod_eq_of_lt hsumLt

theorem clearUint48Offset26Word_zero :
    clearUint48Offset26Word ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [clearUint48Offset26Word_toNat]
  rfl

theorem clearUint48Offset26_after_offset20_after_address_zero (old : UInt256) :
    clearUint48Offset26Word
        (clearUint48Offset20Word (setAddressOffset0Word old ⟨0⟩)) =
      ⟨0⟩ := by
  apply u256_inj
  rw [clearUint48Offset26Word_toNat, clearUint48Offset20Word_toNat]
  rw [setAddressOffset0Word_toNat _ _ (by decide)]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  simp

theorem storageLocStore_uint48_offset20_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset20Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, Reasoning.Theory.wordOfInt_zero, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((20 : Fin 32).val + (6 : Fin 33).val) _) =
      (clearUint48Offset20Word old).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlenOld20 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenZero6 :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2]
    norm_num
  rw [List.length_append, hlenOld20, hlenZero6]
  rw [show 256 ^ 20 = (2 : Nat) ^ 160 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [show 256 ^ 26 = (2 : Nat) ^ 208 by norm_num]
  unfold clearUint48Offset20Word
  have hsumLt : old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 < UInt256.size := by
    have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
    have hhigh : old.toNat / 2 ^ 208 < 2 ^ 48 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by norm_num]
      change old.val.val < UInt256.size
      exact old.val.isLt
    have hlowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hhighLe : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hhigh
    have hhighTerm : old.toNat / 2 ^ 208 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hhighLe
    have hmax : (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [UInt256.toNat_ofNat_of_lt hsumLt]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  ring_nf
  rfl

theorem storageLocStore_uint48_offset26_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset26Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, Reasoning.Theory.wordOfInt_zero, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (26 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((26 : Fin 32).val + (6 : Fin 33).val) _) =
      (clearUint48Offset26Word old).toNat
  rw [show (26 : Fin 32).val = 26 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlenOld26 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 26).length = 26 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenZero6 :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2]
    norm_num
  rw [List.length_append, hlenOld26, hlenZero6]
  rw [show 256 ^ 26 = (2 : Nat) ^ 208 by norm_num]
  rw [show 256 ^ 6 = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (26 + 6)) = (2 : Nat) ^ 256 by norm_num]
  rw [show 256 ^ (26 + 6) = (2 : Nat) ^ 256 by norm_num]
  unfold clearUint48Offset26Word
  have hsumLt : old.toNat % 2 ^ 208 < UInt256.size := by
    exact lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size])
  rw [UInt256.toNat_ofNat_of_lt hsumLt]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  have hdiv : old.toNat / 2 ^ 256 = 0 := by
    exact Nat.div_eq_of_lt (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)
  dsimp [old]
  ring_nf
  have hdiv' :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat /
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        0 := by
    simpa [old] using hdiv
  rw [hdiv']
  simp

theorem storageLocStore_uint48_offset26_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset26Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold storageLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (26 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((26 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset26Word old data).toNat
  rw [show (26 : Fin 32).val = 26 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 6 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld26 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 26).length = 26 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenData6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld26, hlenData6]
  rw [show 2 ^ (8 * 26) = (2 : Nat) ^ 208 by norm_num]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (26 + 6)) = (2 : Nat) ^ 256 by norm_num]
  rw [show 256 ^ (26 + 6) = (2 : Nat) ^ 256 by norm_num]
  rw [setUint48Offset26Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  have hdiv : old.toNat / 2 ^ 256 = 0 := by
    exact Nat.div_eq_of_lt (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)
  dsimp [old]
  ring_nf
  have hdiv' :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat /
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        0 := by
    simpa [old] using hdiv
  rw [hdiv']
  simp

theorem storageLocStore_uint48_offset20_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % packedUInt48Modulus)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset20Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold storageLocStore storageLocWriteWord packedUInt48Loc
  simp only [valueToWord, wordOfInt_emod_uint48, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (6 : Fin 33).val _ ++
        List.drop ((20 : Fin 32).val + (6 : Fin 33).val) _) =
      (setUint48Offset20Word old data).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (6 : Fin 33).val = 6 from rfl]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask _ 6 (by norm_num),
    fromBytes'_drop_wordLE]
  have hlenOld20 :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlenData6 :
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data uint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld20, hlenData6]
  rw [show 2 ^ (8 * 20) = (2 : Nat) ^ 160 by norm_num]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (20 + 6)) = (2 : Nat) ^ 208 by norm_num]
  rw [show 256 ^ (20 + 6) = (2 : Nat) ^ 208 by norm_num]
  rw [setUint48Offset20Word_toNat]
  have hclean : UInt256.land (UInt256.land data uint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data uint48Mask := by
    simpa [uint48Mask] using uint48Mask_clean data
  rw [hclean]
  dsimp [old]
  ring_nf

theorem clearStorage_uint48_offset20_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      cfg.storage.layout er evm = some (packedUInt48Loc slot ⟨20, by decide⟩ (by decide))) :
    clearStorage? cfg evm er packedUInt48StorageType =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset20Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [packedUInt48StorageType]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (packedUInt48Loc slot ⟨20, by decide⟩ (by decide)) (.int 0)) =
    .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (clearUint48Offset20Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))
  rw [storageLocStore_uint48_offset20_zero]
  rfl

theorem clearStorage_uint48_offset26_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      cfg.storage.layout er evm = some (packedUInt48Loc slot ⟨26, by decide⟩ (by decide))) :
    clearStorage? cfg evm er packedUInt48StorageType =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset26Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [packedUInt48StorageType]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (packedUInt48Loc slot ⟨26, by decide⟩ (by decide)) (.int 0)) =
    .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (clearUint48Offset26Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))
  rw [storageLocStore_uint48_offset26_zero]
  rfl

def setBoolPairTrueWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨65535⟩)) ⟨257⟩

def clearBoolOffset1Word (old : UInt256) : UInt256 :=
  UInt256.land old (UInt256.lnot ⟨65280⟩)

theorem solcSlotWord_absent {σ : AccountMap} {I : ExecutionEnv}
    (ha : σ.get? I.codeOwner = none) (slot : UInt256) : solcSlotWord σ I slot = ⟨0⟩ := by
  simp [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord, ha, Option.option]

theorem solcSlotWord_sstore_ne (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot value : UInt256) (hne : readSlot ≠ writeSlot) :
    solcSlotWord (sstoreAccountMap I.codeOwner σ writeSlot value) I readSlot =
      solcSlotWord σ I readSlot :=
  sstoreAccountMap_storage_getD_ne σ I.codeOwner readSlot writeSlot value hne

theorem clearLow16Bits_toNat (old : UInt256) :
    (UInt256.land old (UInt256.lnot ⟨65535⟩)).toNat = old.toNat / 65536 * 65536 := by
  rw [u256_land_comm]
  exact u256_land_high_mask_toNat old 16 (by decide)

theorem setBoolPairTrueWord_toNat (old : UInt256) :
    (setBoolPairTrueWord old).toNat = 257 + old.toNat / 65536 * 65536 := by
  rw [setBoolPairTrueWord, u256_lor_toNat_exact, clearLow16Bits_toNat, Nat.or_comm]
  exact nat_lor_shift_add 257 (old.toNat / 65536) 16 (by decide)

theorem clearBoolOffset1Word_toNat (old : UInt256) :
    (clearBoolOffset1Word old).toNat = old.toNat % 256 + old.toNat / 65536 * 65536 := by
  rw [clearBoolOffset1Word, uland_toNat]
  have hm : (UInt256.lnot (⟨65280⟩ : UInt256)).toNat =
      255 ||| (2 ^ 256 - 2 ^ 16) := by decide
  rw [hm, Nat.and_or_distrib_left]
  change Nat.lor (Nat.land old.toNat (2 ^ 8 - 1))
    (Nat.land old.toNat (2 ^ 256 - 2 ^ 16)) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat 16 (by decide) old.val.isLt]
  exact nat_lor_shift_add (old.toNat % 256) (old.toNat / 65536) 16
    (by have := Nat.mod_lt old.toNat (by decide : 0 < 256); omega)

def setBoolOffset1Word (old : UInt256) (value : Bool) : UInt256 :=
  UInt256.ofNat (old.toNat % 256 + 256 * value.toNat + old.toNat / 65536 * 65536)

theorem setBoolOffset1Word_toNat (old : UInt256) (value : Bool) :
    (setBoolOffset1Word old value).toNat =
      old.toNat % 256 + 256 * value.toNat + old.toNat / 65536 * 65536 := by
  apply ulit_toNat'
  have h := old.val.isLt
  have hlow := Nat.mod_lt old.toNat (by decide : 0 < 256)
  cases value <;> change _ < 2 ^ 256 <;> change old.toNat < 2 ^ 256 at h <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] <;> omega

theorem setBoolOffset1Word_false (old : UInt256) :
    setBoolOffset1Word old false = clearBoolOffset1Word old := by
  apply u256_inj
  rw [setBoolOffset1Word_toNat, clearBoolOffset1Word_toNat]
  rfl

theorem setInitializingThenInitialized (old : UInt256) :
    UInt256.lor (UInt256.land (setBoolOffset1Word old true) (UInt256.lnot ⟨255⟩)) ⟨1⟩ =
      setBoolPairTrueWord old := by
  apply u256_inj
  rw [packedSetTrueWord_toNat, setBoolOffset1Word_toNat, setBoolPairTrueWord_toNat]
  have hlow := Nat.mod_lt old.toNat (by decide : 0 < 256)
  simp only [Bool.toNat_true, Nat.mul_one]
  omega

theorem storageLocStore_bool_offset1 (evm : EVM.State) (slot : UInt256) (value : Bool) :
    storageLocStore evm (packedBoolLocAt slot 1) (.bool value) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setBoolOffset1Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value))
          := by
  unfold storageLocStore storageLocWriteWord packedBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof value.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 2) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setBoolOffset1Word_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof value.toUInt256).2]
  cases value <;> simp [Bool.toUInt256, Nat.mul_comm] <;> decide

theorem solcSlotWord_sstore_present (σ : AccountMap) (I : ExecutionEnv)
    {acc : Account} (ha : σ.get? I.codeOwner = some acc) (slot value : UInt256) :
    solcSlotWord (sstoreAccountMap I.codeOwner σ slot value) I slot = value := by
  unfold solcSlotWord sstoreAccountMap
  rw [ha]
  simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self]
  by_cases hz : value = (default : UInt256)
  · subst value
    simp
    rfl
  · simp [hz]

theorem initializingBeginWord (old : UInt256) :
    UInt256.land (UInt256.div (setBoolPairTrueWord old) ⟨256⟩) ⟨255⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uland_toNat]
  change Nat.land ((setBoolPairTrueWord old).toNat / 256) (2 ^ 8 - 1) = 1
  rw [nat_land_mask_eq_mod, setBoolPairTrueWord_toNat]
  omega

def setBoolTrueOffset20Word (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot (UInt256.shiftLeft ⟨255⟩ ⟨160⟩)))
    (UInt256.shiftLeft ⟨1⟩ ⟨160⟩)

theorem setBoolTrueOffset20Word_toNat (old : UInt256) :
    (setBoolTrueOffset20Word old).toNat =
      old.toNat % 2 ^ 160 + 2 ^ 160 + old.toNat / 2 ^ 168 * 2 ^ 168 := by
  have hm : (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨160⟩)).toNat =
      (2 ^ 160 - 1) ||| (2 ^ 256 - 2 ^ 168) := by decide
  have hp : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩).toNat = 2 ^ 160 := by decide
  rw [setBoolTrueOffset20Word, u256_lor_toNat_exact, uland_toNat, hm, hp, Nat.and_or_distrib_left]
  change Nat.lor (Nat.lor (Nat.land old.toNat (2 ^ 160 - 1))
    (Nat.land old.toNat (2 ^ 256 - 2 ^ 168))) (2 ^ 160) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat 168 (by decide) old.val.isLt]
  rw [show Nat.lor (Nat.lor (old.toNat % 2 ^ 160) (old.toNat / 2 ^ 168 * 2 ^ 168))
      (2 ^ 160) = Nat.lor (Nat.lor (old.toNat % 2 ^ 160) (2 ^ 160))
        (old.toNat / 2 ^ 168 * 2 ^ 168) from Nat.or_right_comm _ _ _]
  have hlo : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by decide)
  have hbit : Nat.lor (old.toNat % 2 ^ 160) (2 ^ 160) = old.toNat % 2 ^ 160 + 2 ^ 160 := by
    simpa only [Nat.one_mul] using nat_lor_shift_add _ 1 160 hlo
  rw [hbit]
  exact nat_lor_shift_add _ _ 168 (by omega)

theorem storageLocStore_bool_true_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (packedBoolLocAt slot 20) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setBoolTrueOffset20Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord packedBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20 ++
      (EVM.Word.toBytesLEWithSizeProof true.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 21) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setBoolTrueOffset20Word_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof true.toUInt256).2]
  change _ % 2 ^ 160 + 2 ^ 160 * 1 + 2 ^ 168 * (_ / 2 ^ 168) = _
  omega

theorem setAddressOffset0Word_comm (old bidder : UInt256)
    (hcanon : bidder.toNat < EVM.addressModulus) :
    UInt256.lor (UInt256.land bidder solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old bidder := by
  unfold setAddressOffset0Word
  rw [Reasoning.Theory.u256_land_comm (UInt256.lnot solcAddrMask) old]
  rw [solcAddrMask_clean hcanon]
  exact u256_lor_comm bidder (UInt256.land old (UInt256.lnot solcAddrMask))

end Reasoning.Theory
