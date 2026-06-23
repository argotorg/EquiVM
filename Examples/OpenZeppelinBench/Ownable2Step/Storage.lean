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

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
theorem ownable2StepFromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fromBytes', Nat.ofDigits, ih]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem ownable2StepNat_land_mask_eq_mod (n k : Nat) :
    Nat.land n (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& (2 ^ k - 1)).testBit i = (n % 2 ^ k).testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · rw [decide_eq_true hi]
    simp
  · rw [decide_eq_false hi]
    simp

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
theorem ownable2StepFromBytes'_take20_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 20) =
      (UInt256.land w solcAddrMask).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← ownable2StepFromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 20 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [ownable2StepFromBytes'_eq_ofDigits (bs.take 20), List.map_take]
  rw [← htake, hfull]
  show w.toNat % 256 ^ 20 = (Nat.land w.toNat solcAddrMask.toNat) % UInt256.size
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [ownable2StepNat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ 160 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))
      (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

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
  rw [ownable2StepFromBytes'_take20_wordLE]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem ownable2StepU256_lor_toNat (a b : UInt256) :
    (UInt256.lor a b).toNat = Nat.lor a.toNat b.toNat % UInt256.size := rfl

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem ownable2StepU256_land_toNat (a b : UInt256) :
    (UInt256.land a b).toNat = Nat.land a.toNat b.toNat % UInt256.size := rfl

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
theorem ownable2StepFromBytes'_drop_wordLE (w : UInt256) (n : Nat) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.drop n) = w.toNat / 256 ^ n := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← ownable2StepFromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have hdrop := Nat.ofDigits_div_pow_eq_ofDigits_drop (p := 256) n (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [ownable2StepFromBytes'_eq_ofDigits (bs.drop n), List.map_drop]
  rw [← hdrop, hfull]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`, generic `Nat.testBit` form of left shift.
theorem ownable2StepTestBit_shiftLeft (m k i : Nat) :
    (m <<< k).testBit i = if i < k then false else m.testBit (i - k) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [← Nat.shiftLeft'_false (m := m) (n := k + 1)]
      change (Nat.bit false (Nat.shiftLeft' false m k)).testBit i = _
      cases i with
      | zero => simp
      | succ i =>
          rw [Nat.testBit_bit_succ]
          rw [Nat.shiftLeft'_false]
          rw [ih]
          by_cases hi : i < k
          · have his : i.succ < k.succ := Nat.succ_lt_succ hi
            simp [his, hi]
          · have hns : ¬ i.succ < k.succ := by omega
            simp [hns, hi]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem ownable2StepDivPow160_testBit (n i : Nat) (h160 : 160 ≤ i) :
    (n / 2 ^ 160).testBit (i - 160) = n.testBit i := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  change n / (2 ^ 160 * 2 ^ (i - 160)) % 2 = 1 ↔ n / 2 ^ i % 2 = 1
  rw [← Nat.pow_add]
  rw [show 160 + (i - 160) = i by omega]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem ownable2StepNatLandClearLow160 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 160) = (n / 2 ^ 160) * 2 ^ 160 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 160)).testBit i =
    ((n / 2 ^ 160) * 2 ^ 160).testBit i
  rw [Nat.testBit_and]
  rw [show (2 : Nat) ^ 256 - 2 ^ 160 = (2 ^ 96 - 1) <<< 160 by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]]
  rw [show (n / 2 ^ 160) * 2 ^ 160 = (n / 2 ^ 160) <<< 160 by
    rw [Nat.shiftLeft_eq]]
  rw [ownable2StepTestBit_shiftLeft]
  rw [ownable2StepTestBit_shiftLeft]
  by_cases hi160 : i < 160
  · simp [hi160]
  · simp [hi160]
    have h160 : 160 ≤ i := Nat.le_of_not_gt hi160
    by_cases hi256 : i < 256
    · have hlt : i - 160 < 96 := by omega
      change (n.testBit i && (((2 : Nat) ^ 96 - 1).testBit (i - 160))) =
        (n / 2 ^ 160).testBit (i - 160)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hlt]
      exact (ownable2StepDivPow160_testBit n i h160).symm
    · have hnlt : ¬ i - 160 < 96 := by omega
      change (n.testBit i && (((2 : Nat) ^ 96 - 1).testBit (i - 160))) =
        (n / 2 ^ 160).testBit (i - 160)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hnlt]
      change (n / 2 ^ 160).testBit (i - 160) = false
      have hq : n / 2 ^ 160 < 2 ^ 96 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 160 * 2 ^ 96 = (2 : Nat) ^ 256 by
          rw [← Nat.pow_add]]
        exact hn
      have hpow : n / 2 ^ 160 < 2 ^ (i - 160) := by
        exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Nat.testBit_lt_two_pow hpow

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem ownable2StepNatLorHigh160Low (q v : Nat) (hv : v < 2 ^ 160) :
    Nat.lor (q * 2 ^ 160) v = v + q * 2 ^ 160 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((q * 2 ^ 160) ||| v).testBit i = (v + q * 2 ^ 160).testBit i
  rw [Nat.testBit_or, Nat.testBit_mul_two_pow]
  by_cases hi : i < 160
  · have hnot : ¬ 160 ≤ i := by omega
    simp [hnot]
    have hmod : (v + q * 2 ^ 160) % 2 ^ 160 = v := by
      rw [show q * 2 ^ 160 = 2 ^ 160 * q by ring]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
    have hbits := Nat.testBit_mod_two_pow (v + q * 2 ^ 160) 160 i
    rw [hmod] at hbits
    rw [decide_eq_true hi] at hbits
    simpa using hbits
  · have hle : 160 ≤ i := Nat.le_of_not_gt hi
    have hvbit : v.testBit i = false := by
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
        (Nat.pow_le_pow_right (by norm_num) hle))
    simp [hle, hvbit]
    have hdiv : (v + q * 2 ^ 160) / 2 ^ 160 = q := by
      rw [show q * 2 ^ 160 = 2 ^ 160 * q by ring]
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2 ^ 160),
        Nat.div_eq_of_lt hv, Nat.zero_add]
    change q.testBit (i - 160) = (v + q * 2 ^ 160).testBit i
    rw [← ownable2StepDivPow160_testBit (v + q * 2 ^ 160) i hle, hdiv]

theorem ownable2StepHigh160Mask_toNat (old : UInt256) :
    (UInt256.land old (UInt256.lnot solcAddrMask)).toNat =
      (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  rw [ownable2StepU256_land_toNat]
  have hlnot : (UInt256.lnot solcAddrMask).toNat = 2 ^ 256 - 2 ^ 160 := by
    native_decide
  rw [hlnot]
  have hwlt : old.toNat < 2 ^ 256 := by
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  rw [ownable2StepNatLandClearLow160 old.toNat hwlt]
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
  rw [ownable2StepU256_lor_toNat, ownable2StepHigh160Mask_toNat,
    ownable2StepU256_land_toNat]
  have hcleanNat :
      Nat.land addr.toNat solcAddrMask.toNat % UInt256.size = addr.toNat := by
    simpa [ownable2StepU256_land_toNat] using congrArg UInt256.toNat
      (solcAddrMask_clean hcanon)
  rw [hcleanNat]
  have hv : addr.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
  rw [ownable2StepNatLorHigh160Low (old.toNat / 2 ^ 160) addr.toNat hv]
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
  rw [fromBytes'_append, ownable2StepFromBytes'_take20_wordLE,
    ownable2StepFromBytes'_drop_wordLE]
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
  simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

/-- `EVM.storageStore` does not create accounts. -/
theorem ownable2StepStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

end OpenZeppelinBench.Ownable2Step
