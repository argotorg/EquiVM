import Benchmarks.Dss.Flopper.Bids
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! Shared ABI helpers for the auction action entry points. -/

abbrev auctionIdKey (id : UInt256) : KeyValue :=
  .int (Int.ofNat id.toNat)

abbrev auctionBaseSlot (id : UInt256) : UInt256 :=
  bidsBase (auctionIdKey id)

abbrev auctionBidSlot (id : UInt256) : UInt256 :=
  auctionBaseSlot id

abbrev auctionLotSlot (id : UInt256) : UInt256 :=
  auctionBaseSlot id + ⟨1⟩

abbrev auctionPackedSlot (id : UInt256) : UInt256 :=
  auctionBaseSlot id + ⟨2⟩

theorem auctionBaseSlot_eq (id : UInt256) :
    auctionBaseSlot id = solcMappingSlot ⟨1⟩ id := by
  unfold auctionBaseSlot bidsBase auctionIdKey mapSlot solcMappingSlot
  rw [keyValueToWord_uint256]

theorem auctionLotSlot_eq (id : UInt256) :
    auctionLotSlot id = solcMappingSlot ⟨1⟩ id + ⟨1⟩ := by
  simp [auctionLotSlot, auctionBaseSlot_eq]

theorem auctionPackedSlot_eq (id : UInt256) :
    auctionPackedSlot id = solcMappingSlot ⟨1⟩ id + ⟨2⟩ := by
  simp [auctionPackedSlot, auctionBaseSlot_eq]

theorem auctionBidLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "bid"] } evm =
      some (uint256Loc (auctionBidSlot id)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionBidSlot,
    auctionBaseSlot, bidsBase, auctionIdKey, wordLoc, uint256Loc, uint256Int]

theorem auctionLotLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "lot"] } evm =
      some (uint256Loc (auctionLotSlot id)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionLotSlot,
    auctionBaseSlot, bidsBase, auctionIdKey, wordLoc, uint256Loc, uint256Int]

theorem auctionGuyLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "guy"] } evm =
      some (addrLoc (auctionPackedSlot id)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionPackedSlot,
    auctionBaseSlot, bidsBase, auctionIdKey]

theorem auctionTicLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "tic"] } evm =
      some (uint48Loc (auctionPackedSlot id) ⟨20, by decide⟩ (by decide)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionPackedSlot,
    auctionBaseSlot, bidsBase, auctionIdKey]

theorem auctionEndLayout (evm : EVM.State) (id : UInt256) :
    config.storage.layout
        { base := "bids", steps := [.mindex (auctionIdKey id), .field "end"] } evm =
      some (uint48Loc (auctionPackedSlot id) ⟨26, by decide⟩ (by decide)) := by
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, auctionPackedSlot,
    auctionBaseSlot, bidsBase, auctionIdKey]

-- LIBRARY CANDIDATE: scalar `delete` leaf for Solidity `uint256`.
theorem clearStorage_uint256_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : cfg.storage.layout er evm = some (uint256Loc slot)) :
    clearStorage? cfg evm er uint256St =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint256St]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (uint256Loc slot) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))) =
    .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩)
  rw [storageLocStore_uint256 evm slot (⟨0⟩ : UInt256)]
  rfl

-- LIBRARY CANDIDATE: zeroing a Solidity address slot through `delete`.
theorem storageLocStore_addr_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (addrLoc slot) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) := by
  unfold storageLocStore storageLocWriteWord addrLoc
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
    native_decide
  rw [hclean]
  have hlen20 :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [setAddressOffset0Word_toNat _ _ (by native_decide)]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  ring

-- LIBRARY CANDIDATE: scalar `delete` leaf for Solidity `address`.
theorem clearStorage_addr_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc : cfg.storage.layout er evm = some (addrLoc slot)) :
    clearStorage? cfg evm er addrSt =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [addrSt]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (addrLoc slot) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))) =
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
    (old.toNat % 2 ^ 208 + (UInt256.land data flopperUint48Mask).toNat * 2 ^ 208)

def setUint48Offset20Word (old data : UInt256) : UInt256 :=
  UInt256.ofNat
    (old.toNat % 2 ^ 160 + (UInt256.land data flopperUint48Mask).toNat * 2 ^ 160 +
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
      old.toNat % 2 ^ 208 + (UInt256.land data flopperUint48Mask).toNat * 2 ^ 208 := by
  unfold setUint48Offset26Word
  have hsumLt :
      old.toNat % 2 ^ 208 + (UInt256.land data flopperUint48Mask).toNat * 2 ^ 208 <
        UInt256.size := by
    have hlow : old.toNat % 2 ^ 208 < 2 ^ 208 := Nat.mod_lt _ (by norm_num)
    have hdata : (UInt256.land data flopperUint48Mask).toNat < 2 ^ 48 := by
      simpa [flopperUint48Mask, EVM.twoPow] using flopperUint48Masked_lt data
    have hlowLe : old.toNat % 2 ^ 208 ≤ 2 ^ 208 - 1 := Nat.le_pred_of_lt hlow
    have hdataLe : (UInt256.land data flopperUint48Mask).toNat ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt hdata
    have hdataTerm :
        (UInt256.land data flopperUint48Mask).toNat * 2 ^ 208 ≤
          (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hdataLe
    have hmax : (2 ^ 208 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  exact UInt256.toNat_ofNat_of_lt hsumLt

theorem setUint48Offset20Word_toNat (old data : UInt256) :
    (setUint48Offset20Word old data).toNat =
      old.toNat % 2 ^ 160 + (UInt256.land data flopperUint48Mask).toNat * 2 ^ 160 +
        old.toNat / 2 ^ 208 * 2 ^ 208 := by
  unfold setUint48Offset20Word
  have hsumLt :
      old.toNat % 2 ^ 160 + (UInt256.land data flopperUint48Mask).toNat * 2 ^ 160 +
          old.toNat / 2 ^ 208 * 2 ^ 208 <
        UInt256.size := by
    have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
    have hdata : (UInt256.land data flopperUint48Mask).toNat < 2 ^ 48 := by
      simpa [flopperUint48Mask, EVM.twoPow] using flopperUint48Masked_lt data
    have hhigh : old.toNat / 2 ^ 208 < 2 ^ 48 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by norm_num]
      change old.val.val < UInt256.size
      exact old.val.isLt
    have hlowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hdataLe : (UInt256.land data flopperUint48Mask).toNat ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt hdata
    have hhighLe : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hhigh
    have hdataTerm :
        (UInt256.land data flopperUint48Mask).toNat * 2 ^ 160 ≤
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
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft flopperUint48Mask ⟨160⟩)))
    (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
      (UInt256.land flopperUint48Mask data))

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
      UInt256.lnot (UInt256.shiftLeft flopperUint48Mask ⟨160⟩) =
        UInt256.ofNat (Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208)) := by
    native_decide
  have hcleared :
      (UInt256.land old (UInt256.lnot (UInt256.shiftLeft flopperUint48Mask ⟨160⟩))).toNat =
        Nat.lor (old.toNat % 2 ^ 160) ((old.toNat / 2 ^ 208) * 2 ^ 208) := by
    rw [hnot, u256_land_toNat]
    change Nat.land old.toNat
        (Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208)) %
        UInt256.size =
      _
    have hmaskLt :
        Nat.lor (2 ^ 160 - 1) (((2 : Nat) ^ (256 - 208) - 1) <<< 208) <
          UInt256.size := by
      native_decide
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
          (UInt256.land flopperUint48Mask data)).toNat =
        (UInt256.land data flopperUint48Mask).toNat * 2 ^ 160 := by
    rw [u256_mul_toNat]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩).toNat = 2 ^ 160 by
      native_decide]
    rw [show (UInt256.land flopperUint48Mask data).toNat =
      (UInt256.land data flopperUint48Mask).toNat by rw [u256_land_comm]]
    rw [Nat.mul_comm (2 ^ 160) (UInt256.land data flopperUint48Mask).toNat]
    apply Nat.mod_eq_of_lt
    have hmid : (UInt256.land data flopperUint48Mask).toNat < 2 ^ 48 := by
      simpa [flopperUint48Mask, EVM.twoPow] using flopperUint48Masked_lt data
    exact lt_trans (Nat.mul_lt_mul_of_pos_right hmid (by norm_num))
      (by norm_num [UInt256.size])
  rw [hcleared, hshifted]
  rw [setUint48Offset20Word_toNat]
  let low := old.toNat % 2 ^ 160
  let mid := (UInt256.land data flopperUint48Mask).toNat
  let high := old.toNat / 2 ^ 208
  change Nat.lor (Nat.lor low (high * 2 ^ 208)) (mid * 2 ^ 160) % UInt256.size =
    low + mid * 2 ^ 160 + high * 2 ^ 208
  have hlowLt : low < 2 ^ 160 :=
    Nat.mod_lt _ (by norm_num)
  have hmidLt : mid < 2 ^ 48 := by
    simpa [mid, flopperUint48Mask, EVM.twoPow] using flopperUint48Masked_lt data
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
  rw [setAddressOffset0Word_toNat _ _ (by native_decide)]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  simp

-- LIBRARY CANDIDATE: zeroing a packed Solidity uint48 at byte offset 20.
theorem storageLocStore_uint48_offset20_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨20, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset20Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
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

-- LIBRARY CANDIDATE: zeroing a packed Solidity uint48 at byte offset 26.
theorem storageLocStore_uint48_offset26_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨26, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset26Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
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

theorem auctionWordOfInt_emod_uint48 (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat % uint48Modulus) =
      UInt256.land w flopperUint48Mask := by
  have hnonneg : 0 ≤ Int.ofNat w.toNat % uint48Modulus := by
    exact Int.emod_nonneg _ (by norm_num [uint48Modulus])
  have hcast : ((w.toNat % 2 ^ 48 : Nat) : Int) =
      Int.ofNat w.toNat % uint48Modulus := by
    norm_num [uint48Modulus, Int.natCast_mod]
  have htoNat : (Int.ofNat w.toNat % uint48Modulus).toNat = w.toNat % 2 ^ 48 := by
    have h := congrArg Int.toNat hcast
    simpa using h.symm
  rw [wordOfInt_nonneg _ hnonneg]
  apply u256_inj
  change (Int.ofNat w.toNat % uint48Modulus).toNat % EVM.twoPow 256 =
    (UInt256.land w flopperUint48Mask).toNat
  rw [htoNat]
  rw [u256_land_toNat]
  change w.toNat % 2 ^ 48 % EVM.twoPow 256 =
    Nat.land w.toNat (2 ^ 48 - 1) % UInt256.size
  rw [nat_land_mask_eq_mod]
  simp [EVM.twoPow, UInt256.size]

-- LIBRARY CANDIDATE: writing a packed Solidity uint48 at byte offset 26.
theorem storageLocStore_uint48_offset26_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨26, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % uint48Modulus)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset26Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, auctionWordOfInt_emod_uint48, bind, Option.bind]
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
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data flopperUint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data flopperUint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld26, hlenData6]
  rw [show 2 ^ (8 * 26) = (2 : Nat) ^ 208 by norm_num]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (26 + 6)) = (2 : Nat) ^ 256 by norm_num]
  rw [show 256 ^ (26 + 6) = (2 : Nat) ^ 256 by norm_num]
  rw [setUint48Offset26Word_toNat]
  have hclean : UInt256.land (UInt256.land data flopperUint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data flopperUint48Mask := by
    simpa [flopperUint48Mask] using flopperUint48Mask_clean data
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

-- LIBRARY CANDIDATE: writing a packed Solidity uint48 at byte offset 20.
theorem storageLocStore_uint48_offset20_word (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨20, by decide⟩ (by decide))
        (.int (Int.ofNat data.toNat % uint48Modulus)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint48Offset20Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, auctionWordOfInt_emod_uint48, bind, Option.bind]
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
      ((EVM.Word.toBytesLEWithSizeProof (UInt256.land data flopperUint48Mask)).1.take 6).length =
        6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land data flopperUint48Mask)).2]
    norm_num
  rw [List.length_append, hlenOld20, hlenData6]
  rw [show 2 ^ (8 * 20) = (2 : Nat) ^ 160 by norm_num]
  rw [show 2 ^ (8 * 6) = (2 : Nat) ^ 48 by norm_num]
  rw [show 2 ^ (8 * (20 + 6)) = (2 : Nat) ^ 208 by norm_num]
  rw [show 256 ^ (20 + 6) = (2 : Nat) ^ 208 by norm_num]
  rw [setUint48Offset20Word_toNat]
  have hclean : UInt256.land (UInt256.land data flopperUint48Mask)
      (UInt256.ofNat (2 ^ 48 - 1)) = UInt256.land data flopperUint48Mask := by
    simpa [flopperUint48Mask] using flopperUint48Mask_clean data
  rw [hclean]
  dsimp [old]
  ring_nf

theorem clearStorage_uint48_offset20_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      cfg.storage.layout er evm = some (uint48Loc slot ⟨20, by decide⟩ (by decide))) :
    clearStorage? cfg evm er uint48St =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset20Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint48St]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (uint48Loc slot ⟨20, by decide⟩ (by decide)) (.int 0)) =
    .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (clearUint48Offset20Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))
  rw [storageLocStore_uint48_offset20_zero]
  rfl

theorem clearStorage_uint48_offset26_zero {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hloc :
      cfg.storage.layout er evm = some (uint48Loc slot ⟨26, by decide⟩ (by decide))) :
    clearStorage? cfg evm er uint48St =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (clearUint48Offset26Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  rw [Solm.clearStorage?.eq_def]
  simp only [uint48St]
  rw [hloc]
  change EvalResult.ofOption EvalError.storageError
      (storageLocStore evm (uint48Loc slot ⟨26, by decide⟩ (by decide)) (.int 0)) =
    .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (clearUint48Offset26Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))
  rw [storageLocStore_uint48_offset26_zero]
  rfl

theorem evalExpr_auction_id (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "id") =
      .ok (.int (Int.ofNat id.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "id") = _
  rw [hget]
  rfl

theorem evalStorageRef_auction_bid (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm (bidRef (.var "id")) =
      .ok { base := "bids", steps := [.mindex (auctionIdKey id)] } := by
  have hgetElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [bidRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hgetElem,
    auctionIdKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem evalStorageRef_auction_field (evm : EVM.State) (locals : Store) (id : UInt256)
    (field : Ident)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm
        (bidsF (.var "id") field) =
      .ok { base := "bids", steps := [.mindex (auctionIdKey id), .field field] } := by
  have hgetElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [bidsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hgetElem,
    auctionIdKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem resolveStorageRef_auction_bid (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbase : locals.get? "bids" = none) :
    resolveStorageRef? config { contract := contract, locals := locals } evm (bidRef (.var "id")) =
      .ok ({ base := "bids", steps := [.mindex (auctionIdKey id)] }, BidStructTy) := by
  rw [resolveStorageRef?]
  simp only [bidRef]
  rw [hbase]
  rw [show evalStorageRef config { contract := contract, locals := locals } evm
      { base := "bids", steps := [StorageRefStep.mindex (.var "id")] } =
        .ok { base := "bids", steps := [.mindex (auctionIdKey id)] } by
    simpa [bidRef] using evalStorageRef_auction_bid evm locals id hget]
  simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, BidStructTy,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

def auctionDeleteAfterBid (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionBidSlot id) ⟨0⟩

def auctionDeleteAfterLot (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterBid id evm)
    (auctionDeleteAfterBid id evm).executionEnv.codeOwner (auctionLotSlot id) ⟨0⟩

def auctionDeleteAfterGuy (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterLot id evm)
    (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
        (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id))
      ⟨0⟩)

def auctionDeleteAfterTic (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterGuy id evm)
    (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)
    (clearUint48Offset20Word
      (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
        (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)))

def auctionDeletePostState (id : UInt256) (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (auctionDeleteAfterTic id evm)
    (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id)
    (clearUint48Offset26Word
      (Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
        (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id)))

def auctionRuntimeDeleteAccountMap (owner : AccountAddress) (id : UInt256)
    (σ : AccountMap) : AccountMap :=
  sstoreAccountMap owner
    (sstoreAccountMap owner
      (sstoreAccountMap owner σ (auctionBidSlot id) ⟨0⟩)
      (auctionLotSlot id) ⟨0⟩)
    (auctionPackedSlot id) ⟨0⟩

theorem deleteStorage_auction_bid (evm : EVM.State) (locals : Store) (id : UInt256)
    (hget : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbase : locals.get? "bids" = none) :
    deleteStorage? config { contract := contract, locals := locals } evm
      (bidRef (.var "id")) = .ok (auctionDeletePostState id evm) := by
  rw [deleteStorage?]
  rw [resolveStorageRef_auction_bid evm locals id hget hbase]
  simp only [EvalResult.bind, bind]
  rw [Solm.clearStorage?.eq_def]
  simp only [BidStructTy]
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint256_zero (slot := auctionBidSlot id) (hloc := auctionBidLayout evm id)]
  change clearFields? config (auctionDeleteAfterBid id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("lot", uint256St), ("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint256_zero (slot := auctionLotSlot id)
    (hloc := auctionLotLayout (auctionDeleteAfterBid id evm) id)]
  change clearFields? config (auctionDeleteAfterLot id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("guy", addrSt), ("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_addr_zero (slot := auctionPackedSlot id)
    (hloc := auctionGuyLayout (auctionDeleteAfterLot id evm) id)]
  change clearFields? config (auctionDeleteAfterGuy id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("tic", uint48St), ("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint48_offset20_zero (slot := auctionPackedSlot id)
    (hloc := auctionTicLayout (auctionDeleteAfterGuy id evm) id)]
  change clearFields? config (auctionDeleteAfterTic id evm)
      { base := "bids", steps := [.mindex (auctionIdKey id)] }
      [("end", uint48St)] =
    .ok (auctionDeletePostState id evm)
  rw [Solm.clearFields?.eq_def]
  simp only [List.cons_append, List.nil_append]
  rw [clearStorage_uint48_offset26_zero (slot := auctionPackedSlot id)
    (hloc := auctionEndLayout (auctionDeleteAfterTic id evm) id)]
  simp only
  rw [Solm.clearFields?.eq_def]
  simp [auctionDeletePostState]

theorem auctionDeletePackedFinalWord_zero (id : UInt256) (evm : EVM.State) :
    clearUint48Offset26Word
        (Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
          (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id)) =
      ⟨0⟩ := by
  by_cases hacc0 : evm.accountMap.find? evm.executionEnv.codeOwner = none
  · have hbid : auctionDeleteAfterBid id evm = evm := by
      exact storageStore_absent evm evm.executionEnv.codeOwner hacc0 (auctionBidSlot id) ⟨0⟩
    have hlot : auctionDeleteAfterLot id evm = evm := by
      simp [auctionDeleteAfterLot, hbid,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0 (auctionLotSlot id) ⟨0⟩]
    have hguy : auctionDeleteAfterGuy id evm = evm := by
      simp [auctionDeleteAfterGuy, hlot,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0
          (auctionPackedSlot id)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot id)) ⟨0⟩)]
    have htic : auctionDeleteAfterTic id evm = evm := by
      simp [auctionDeleteAfterTic, hguy,
        storageStore_absent evm evm.executionEnv.codeOwner hacc0
          (auctionPackedSlot id)
          (clearUint48Offset20Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot id)))]
    have hload :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot id) = ⟨0⟩ := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hacc0, Option.option]
    rw [htic, hload]
    exact clearUint48Offset26Word_zero
  · obtain ⟨_, hacc0some⟩ := Option.ne_none_iff_exists'.mp hacc0
    have haccLotExists :
        ∃ acc, (auctionDeleteAfterLot id evm).accountMap.find?
          (auctionDeleteAfterLot id evm).executionEnv.codeOwner = some acc := by
      simp [auctionDeleteAfterLot, auctionDeleteAfterBid, Solm.EVM.storageStore,
        State.lookupAccount, hacc0some, Option.option, State.setAccount,
        accountMap_find_insert_self]
    obtain ⟨_, haccLot⟩ := haccLotExists
    have hloadGuy :
        Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
            (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
              (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id))
            ⟨0⟩ := by
      rw [show (auctionDeleteAfterGuy id evm).executionEnv =
          (auctionDeleteAfterLot id evm).executionEnv by
        simp [auctionDeleteAfterGuy, storageStore_executionEnv]]
      exact storageLoad_storageStore_same_present (auctionDeleteAfterLot id evm)
        (auctionDeleteAfterLot id evm).executionEnv.codeOwner haccLot
        (auctionPackedSlot id)
        (setAddressOffset0Word
          (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
            (auctionDeleteAfterLot id evm).executionEnv.codeOwner (auctionPackedSlot id)) ⟨0⟩)
    have haccGuyExists :
        ∃ acc, (auctionDeleteAfterGuy id evm).accountMap.find?
          (auctionDeleteAfterGuy id evm).executionEnv.codeOwner = some acc := by
      simp [auctionDeleteAfterGuy, haccLot, Solm.EVM.storageStore, State.lookupAccount,
        Option.option, State.setAccount, accountMap_find_insert_self]
    obtain ⟨_, haccGuy⟩ := haccGuyExists
    have hloadTic :
        Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
            (auctionDeleteAfterTic id evm).executionEnv.codeOwner (auctionPackedSlot id) =
          clearUint48Offset20Word
            (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
              (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)) := by
      rw [show (auctionDeleteAfterTic id evm).executionEnv =
          (auctionDeleteAfterGuy id evm).executionEnv by
        simp [auctionDeleteAfterTic, storageStore_executionEnv]]
      exact storageLoad_storageStore_same_present (auctionDeleteAfterGuy id evm)
        (auctionDeleteAfterGuy id evm).executionEnv.codeOwner haccGuy
        (auctionPackedSlot id)
        (clearUint48Offset20Word
          (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
            (auctionDeleteAfterGuy id evm).executionEnv.codeOwner (auctionPackedSlot id)))
    rw [hloadTic, hloadGuy]
    exact clearUint48Offset26_after_offset20_after_address_zero _

set_option maxHeartbeats 1000000 in
theorem auctionDeletePostState_accountMapEquiv (id : UInt256) (evm : EVM.State)
    (owner : AccountAddress) (howner : evm.executionEnv.codeOwner = owner) :
    accountMapEquiv (auctionRuntimeDeleteAccountMap owner id evm.accountMap)
      (auctionDeletePostState id evm).accountMap := by
  let srcOwner := evm.executionEnv.codeOwner
  let bidSlot := auctionBidSlot id
  let lotSlot := auctionLotSlot id
  let packedSlot := auctionPackedSlot id
  let m2 :=
    sstoreAccountMap srcOwner (sstoreAccountMap srcOwner evm.accountMap bidSlot ⟨0⟩)
      lotSlot ⟨0⟩
  let vGuy :=
    setAddressOffset0Word
      (Solm.EVM.storageLoad (auctionDeleteAfterLot id evm)
        (auctionDeleteAfterLot id evm).executionEnv.codeOwner packedSlot) ⟨0⟩
  let vTic :=
    clearUint48Offset20Word
      (Solm.EVM.storageLoad (auctionDeleteAfterGuy id evm)
        (auctionDeleteAfterGuy id evm).executionEnv.codeOwner packedSlot)
  let vEnd :=
    clearUint48Offset26Word
      (Solm.EVM.storageLoad (auctionDeleteAfterTic id evm)
        (auctionDeleteAfterTic id evm).executionEnv.codeOwner packedSlot)
  have hfinal : vEnd = ⟨0⟩ := by
    simpa [vEnd, packedSlot] using auctionDeletePackedFinalWord_zero id evm
  have h1 :
      accountMapEquiv (sstoreAccountMap srcOwner m2 packedSlot vEnd)
        (sstoreAccountMap srcOwner (sstoreAccountMap srcOwner m2 packedSlot vGuy)
          packedSlot vEnd) :=
    accountMapEquiv_sstoreAccountMap_self_update m2 srcOwner packedSlot vGuy vEnd
  have h2 :
      accountMapEquiv
        (sstoreAccountMap srcOwner (sstoreAccountMap srcOwner m2 packedSlot vGuy)
          packedSlot vEnd)
        (sstoreAccountMap srcOwner
          (sstoreAccountMap srcOwner
            (sstoreAccountMap srcOwner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd) :=
    accountMapEquiv_sstoreAccountMap_self_update
      (sstoreAccountMap srcOwner m2 packedSlot vGuy) srcOwner packedSlot vTic vEnd
  have h := accountMapEquiv.trans h1 h2
  have hleftEq :
      sstoreAccountMap srcOwner m2 packedSlot vEnd =
        sstoreAccountMap srcOwner m2 packedSlot ⟨0⟩ := by
    rw [hfinal]
  have h' :
      accountMapEquiv (sstoreAccountMap srcOwner m2 packedSlot ⟨0⟩)
        (sstoreAccountMap srcOwner
          (sstoreAccountMap srcOwner
            (sstoreAccountMap srcOwner m2 packedSlot vGuy) packedSlot vTic)
          packedSlot vEnd) := by
    simpa [hleftEq] using h
  simpa [auctionRuntimeDeleteAccountMap, auctionDeletePostState, auctionDeleteAfterTic,
    auctionDeleteAfterGuy, auctionDeleteAfterLot, auctionDeleteAfterBid, m2, srcOwner, bidSlot,
    lotSlot, packedSlot, vGuy, vTic, vEnd, howner, storageStore_accountMap,
    storageStore_executionEnv] using h'

theorem twoWordHashMem_size_ge_64 (key slot : UInt256) (mem : ByteArray) :
    64 ≤ (twoWordHashMem key slot mem).size := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  simpa using
    toByteArray_write_size_ge_off_add32 slot (wordAt0Mem key mem) 32 (by
      have hzero : 32 - (wordAt0Mem key mem).size = 0 := by omega
      rw [hzero]
      exact lt_usize 0 (by norm_num))

theorem twoWordHashMem_read0_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) hkeySize (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_read_back (wordAt0Mem key mem) slot 32 hkeySize

theorem twoWordHashMem_read0_64_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [byteArray_readWithPadding_split (twoWordHashMem key slot mem) 0 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using twoWordHashMem_size_ge_64 key slot mem)]
  rw [twoWordHashMem_read0_any, twoWordHashMem_read32_any]

theorem twoWordHashMem_solcMappingSlot_any (baseSlot key : UInt256) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_any]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem flopperSlotWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flopperSlotWord slot σ I = flopperSlotWord slot τ I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩

theorem flopperUint48Offset6Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flopperUint48Offset6Word slot σ I = flopperUint48Offset6Word slot τ I := by
  simp [flopperUint48Offset6Word, flopperSlotWord_accountMapEquiv hAccounts slot]

theorem flopperUint48Offset20Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flopperUint48Offset20Word slot σ I = flopperUint48Offset20Word slot τ I := by
  simp [flopperUint48Offset20Word, flopperSlotWord_accountMapEquiv hAccounts slot]

theorem flopperUint48Offset26Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flopperUint48Offset26Word slot σ I = flopperUint48Offset26Word slot τ I := by
  simp [flopperUint48Offset26Word, flopperSlotWord_accountMapEquiv hAccounts slot]

theorem flopperAddressReturnWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flopperAddressReturnWord slot σ I = flopperAddressReturnWord slot τ I := by
  simp [flopperAddressReturnWord, flopperSlotWord_accountMapEquiv hAccounts slot]

theorem flopperAddressOfSlot_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    AccountAddress.ofNat (flopperAddressReturnWord slot σ I).toNat =
      AccountAddress.ofNat (flopperAddressReturnWord slot τ I).toNat := by
  simp [flopperAddressReturnWord_accountMapEquiv hAccounts slot]

theorem flopperCodeSize_ne_accountMapEquiv {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ) {target : UInt256}
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ target ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts target
  rw [hsame]
  exact hzero

theorem flopperCodeSize_zero_accountMapEquiv {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ) {target : UInt256}
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ target = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts target
  rw [← hsame]
  exact hzero

theorem flopperCodeSize_ne_accountMapEquiv_addressSlot {σ τ : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ) (slot : UInt256)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flopperAddressReturnWord slot σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flopperAddressReturnWord slot τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (flopperAddressReturnWord slot σ I)
  have htarget :
      flopperAddressReturnWord slot σ I = flopperAddressReturnWord slot τ I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts slot
  rw [hsame, htarget]
  exact hzero

theorem flopperCodeSize_zero_accountMapEquiv_addressSlot {σ τ : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ τ) (slot : UInt256)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flopperAddressReturnWord slot σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flopperAddressReturnWord slot τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (flopperAddressReturnWord slot σ I)
  have htarget :
      flopperAddressReturnWord slot σ I = flopperAddressReturnWord slot τ I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts slot
  rw [← htarget, ← hsame]
  exact hzero

theorem decodeCalldata_legacyAddress_uint256_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiAddress, abiUInt256, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiAddress, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake4]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 32) htake36]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 64) htake68]
  change decodeCalldata.insertValues [x, y, z]
      [.address (AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  rw [hword4, hword36, hword68]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyAddress_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiAddress, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiAddress, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 32) htake32]
      have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 64) (by simpa using htake64n)]
      simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 32) (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem decodeCalldata_legacyUint256_uint256_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiUInt256, abiUInt256, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 32) htake36]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 64) htake68]
  change decodeCalldata.insertValues [x, y, z]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  rw [hword4, hword36, hword68]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUint256_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiUInt256, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := cd.toList.drop 4) (start := 0) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 32) htake32]
      have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 64) (by simpa using htake64n)]
      simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 32) (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem flopper_u256_mul_div_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (y * x) y ≠ x := by
  intro hEq
  have hyNatNe : y.toNat ≠ 0 := by
    intro hy0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hy0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_op_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 :=
    Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem RD.flopperCheckedMulReturns
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hret : (D_J flopperBytecode 0).contains ret = true)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (rd4674 : RD flopperBytecode I g s0 ⟨4674⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    ∃ k' C', RD flopperBytecode I g s0 ret (x * y :: R) mem aw rdata acc k' C' := by
  have rd4701prep := evm_run rd4674 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨4701⟩ (by native_decide) (by evm_ov)]
  by_cases hy0 : y = ⟨0⟩
  · have hcond : UInt256.isZero y ≠ ⟨0⟩ := by
      rw [hy0]
      decide
    have rd4701 := rd4701prep.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd4705 := evm_run rd4701 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
    have rd4710 := rd4705.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd4715 := evm_run rd4710 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd4715.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa [hy0] using rdret⟩
  · have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
    have rd4684 := rd4701prep.jumpiNT (by native_decide) hcond (by evm_ov)
    have rd4696 := evm_run rd4684 with [
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw mul (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨4698⟩ (by native_decide) (by evm_ov)]
    have rd4698 := rd4696.jumpiT (by native_decide) hy0 (by jump_dest) (by evm_ov)
    have hyNatNe : y.toNat ≠ 0 := by
      intro hzero
      exact hy0 (uint256_toNat_eq_zero hzero)
    have hdivWord : UInt256.div (x * y) y = x := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (x * y).toNat = x.toNat * y.toNat := by
        rw [umul_toNat x y hfit]
      rw [hprod]
      simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat
        (Nat.pos_of_ne_zero hyNatNe)
    have rd4705 := evm_run rd4698 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
    have heqCond : UInt256.eq (UInt256.div (x * y) y) x ≠ ⟨0⟩ := by
      rw [hdivWord, u256_eq_refl]
      exact one_ne_zero_uint
    have rd4710 := rd4705.jumpiT (by native_decide) heqCond (by jump_dest)
      (by evm_ov)
    have rd4715 := evm_run rd4710 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd4715.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa using rdret⟩

theorem RD.flopperCheckedMulOverflowReverts
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (rd4674 : RD flopperBytecode I g s0 ⟨4674⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev flopperBytecode g s0 := by
  have hyNe : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (x * y) y ≠ x := by
    intro hbad
    have h := flopper_u256_mul_div_overflow_ne x y hover
    exact h (by
      have hcomm : y * x = x * y := by
        simpa using u256_mul_comm y x
      rw [hcomm]
      exact hbad)
  have rd4701prep := evm_run rd4674 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨4701⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyNe
  have rd4684 := rd4701prep.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd4696 := evm_run rd4684 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨4698⟩ (by native_decide) (by evm_ov)]
  have rd4698 := rd4696.jumpiT (by native_decide) hyNe (by jump_dest) (by evm_ov)
  have rd4705 := evm_run rd4698 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rd4706 := rd4705.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd4706
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.flopperAuctionDeleteTail
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {drop0 drop1 drop2 scratch id : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hMstore0Aw : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw)
    (hMstore32Aw : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw)
    (hKeccakAw : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw)
    (hov : R.length + 10 ≤ 1024)
    (h : RD flopperBytecode I g s0 ⟨1180⟩
      (drop0 :: drop1 :: drop2 :: scratch :: id :: ⟨334⟩ :: R)
      mem aw rdata (cA, σ) k C) :
    RDret flopperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (auctionBidSlot id) ⟨0⟩)
          (auctionLotSlot id) ⟨0⟩)
        (auctionPackedSlot id) ⟨0⟩)
      ByteArray.empty := by
  let mem1 := wordAt0Mem id mem
  let mem2 := twoWordHashMem id ⟨1⟩ mem
  let base := solcMappingSlot ⟨1⟩ id
  have rd1184 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1188 := evm_run rd1184 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd1189 := rd1188.mstore 0 mem1 aw
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by
        rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide, hMstore0Aw]
        simp))
    (by simp [mem1, wordAt0Mem])
    hMstore0Aw
    (by evm_ov)
  have rd1196pre := evm_run rd1189 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1197 := rd1196pre.mstore 0 mem2 aw
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hMstore32Aw]
        simp))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [mem1, mem2, twoWordHashMem, wordAt32Mem])
    hMstore32Aw
    (by evm_ov)
  have rd1200pre := evm_run rd1197 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (mem2.readWithPadding 0 64))) = base := by
    simpa [base, mem2] using twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd1201raw := rd1200pre.keccak256 0 base aw
    (by native_decide)
    (by
      intro s haws hstks
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide, hKeccakAw]
      simp)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by
      rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact hKeccakAw)
    (by evm_ov)
  have rd1203pre := evm_run rd1201raw with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1204raw⟩ := rd1203pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1209pre := evm_run rd1204raw with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1210raw⟩ := rd1209pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1213pre := evm_run rd1210raw with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1214raw⟩ := rd1213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd334 := rd1214raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  have hslot2 : (⟨2⟩ : UInt256) + base = base + ⟨2⟩ := u256_add_comm _ _
  have hstop := RD.stop rd335 (by native_decide) (by evm_ov)
  rw [hslot2] at hstop
  simpa only [base, auctionBidSlot, auctionLotSlot_eq, auctionPackedSlot_eq,
    auctionBaseSlot_eq] using hstop

end Benchmarks.Dss.Flopper
