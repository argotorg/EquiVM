import Examples.OpenZeppelinBench.Ownable2Step.Common
import Reasoning.Memory
import Reasoning.Storage
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-!
# Ownable2StepBench storage helpers

The contract has two scalar `address` slots.  The helper below proves the byte-level load/store
round trip for a Solidity `address` stored at offset 0 in a 32-byte EVM storage word.
-/

theorem ownable2StepStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  unfold storageLocLoad addrLoc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 20))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [fromBytes'_take20_wordLE_solcAddrMask]

theorem ownable2StepHigh160Mask_toNat (old : UInt256) :
    (UInt256.land old (UInt256.lnot solcAddrMask)).toNat =
      (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  rw [u256_land_toNat]
  have hlnot : (UInt256.lnot solcAddrMask).toNat = 2 ^ 256 - 2 ^ 160 := by
    native_decide
  rw [hlnot]
  have hwlt : old.toNat < 2 ^ 256 := by
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  rw [natLandClearLow old.toNat 160 (by norm_num) hwlt]
  have hlt : old.toNat / 2 ^ 160 * 2 ^ 160 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
  rw [Nat.mod_eq_of_lt hlt]

theorem ownable2StepSetAddressNat_lt_size (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 < UInt256.size := by
  have hq : old.toNat / 2 ^ 160 < 2 ^ 96 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 160 * 2 ^ 96 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  have hv : addr.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
  have hvle : addr.toNat ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hv
  have hqle : old.toNat / 2 ^ 160 ≤ 2 ^ 96 - 1 := Nat.le_pred_of_lt hq
  have hqterm :
      old.toNat / 2 ^ 160 * 2 ^ 160 ≤ (2 ^ 96 - 1) * 2 ^ 160 :=
    Nat.mul_le_mul_right _ hqle
  have hmax : (2 ^ 160 - 1) + (2 ^ 96 - 1) * 2 ^ 160 < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem ownable2StepSetAddressWord_eq (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    ownable2StepSetAddressWord old addr =
      UInt256.ofNat (addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160) := by
  unfold ownable2StepSetAddressWord
  apply u256_inj
  rw [u256_lor_toNat, ownable2StepHigh160Mask_toNat,
    u256_land_toNat]
  have hcleanNat :
      Nat.land addr.toNat solcAddrMask.toNat % UInt256.size = addr.toNat := by
    simpa [u256_land_toNat] using congrArg UInt256.toNat
      (solcAddrMask_clean hcanon)
  rw [hcleanNat]
  have hv : addr.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
  rw [nat_lor_comm]
  rw [nat_lor_shift_add addr.toNat (old.toNat / 2 ^ 160) 160 hv]
  rw [Nat.mod_eq_of_lt (ownable2StepSetAddressNat_lt_size old addr hcanon)]
  rw [ulit_toNat' _ (ownable2StepSetAddressNat_lt_size old addr hcanon)]

theorem ownable2StepSetAddressWord_toNat (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    (ownable2StepSetAddressWord old addr).toNat =
      addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  rw [ownable2StepSetAddressWord_eq old addr hcanon]
  exact ulit_toNat' _ (ownable2StepSetAddressNat_lt_size old addr hcanon)

theorem ownable2StepStorageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (addrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (ownable2StepSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  have haddrWord : EVM.Word.ofNat (Fin.toNat (AccountAddress.ofNat addr.toNat)) = addr := by
    apply u256_inj
    unfold EVM.Word.ofNat UInt256.ofNat AccountAddress.ofNat UInt256.toNat
    change ((addr.val.val % AccountAddress.size) % UInt256.size) = addr.val.val
    nth_rewrite 2 [Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size, UInt256.toNat] using hcanon)]
    exact Nat.mod_eq_of_lt addr.val.isLt
  unfold storageLocStore storageLocWriteWord addrLoc
  simp only [valueToWord, haddrWord, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof addr).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
        (ownable2StepSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask,
    fromBytes'_drop_wordLE]
  have hclean : (UInt256.land addr solcAddrMask).toNat = addr.toNat := by
    simpa using congrArg UInt256.toNat (solcAddrMask_clean hcanon)
  rw [hclean]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof addr).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [ownable2StepSetAddressWord_toNat _ _ hcanon]
  ring

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem ownable2StepStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  exact storageStore_accountMap evm a slot val

/-- `EVM.storageStore` does not create accounts. -/
theorem ownable2StepStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  exact storageStore_createdAccounts evm a slot val

end OpenZeppelinBench.Ownable2Step
