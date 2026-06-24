import Examples.SimpleAuction.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace SimpleAuction

/-!
# SimpleAuction storage helpers

Shared storage-map and mapping-slot helpers for the per-function proofs live here.  Phase-1
workers should keep this file read-only; local helpers that need promotion should be tagged in the
owning function file and reconciled after the parallel body pass.
-/

/-- `wordOfInt (Int.ofNat a.toNat) = a` for an EVM word. -/
theorem simpleAuctionWordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

/-- Storing a full-slot SimpleAuction `uint256` writes exactly the EVM word in the same slot. -/
theorem simpleAuctionStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (simpleAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore storageLocWriteWord simpleAuctionUint256Loc
  simp only [valueToWord, simpleAuctionWordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = val.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

def simpleAuctionSetAddressWord (old addr : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask)) (UInt256.land addr solcAddrMask)

theorem simpleAuctionSourceWord_canonical (I : ExecutionEnv) :
    (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt (by decide : AccountAddress.size ≤ UInt256.size))]
  have hsrc : I.source.val < AccountAddress.size := I.source.isLt
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hsrc

theorem simpleAuctionU256_lor_toNat (a b : UInt256) :
    (UInt256.lor a b).toNat = Nat.lor a.toNat b.toNat % UInt256.size :=
  Reasoning.Theory.u256_lor_toNat a b

theorem simpleAuctionU256_land_toNat (a b : UInt256) :
    (UInt256.land a b).toNat = Nat.land a.toNat b.toNat % UInt256.size :=
  Reasoning.Theory.u256_land_toNat a b

theorem simpleAuctionFromBytes'_drop_wordLE (w : UInt256) (n : Nat) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.drop n) = w.toNat / 256 ^ n :=
  Reasoning.Theory.fromBytes'_drop_wordLE w n

theorem simpleAuctionFromBytes'_take1_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 1) =
      (UInt256.land w ⟨255⟩).toNat := by
  simpa using Reasoning.Theory.fromBytes'_take_wordLE_land_mask w 1 (by decide)

theorem simpleAuctionStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (simpleAuctionBoolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  unfold storageLocLoad simpleAuctionBoolLoc
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [simpleAuctionFromBytes'_take1_wordLE]
  rfl

theorem simpleAuctionStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (simpleAuctionBoolLoc slot) = .bool false := by
  rw [simpleAuctionStorageLocLoad_bool_offset0 evm slot]
  simp [wordToElem, hzero]

theorem simpleAuctionStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (simpleAuctionBoolLoc slot) = .bool true := by
  rw [simpleAuctionStorageLocLoad_bool_offset0 evm slot]
  have hbeq :
      ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

theorem simpleAuctionFromBytes'_drop1_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.drop 1) = w.toNat / 256 := by
  simpa using Reasoning.Theory.fromBytes'_drop_wordLE w 1

theorem simpleAuctionTestBit_shiftLeft (m k i : Nat) :
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

theorem simpleAuctionDivPow8_testBit (n i : Nat) (h8 : 8 ≤ i) :
    (n / 2 ^ 8).testBit (i - 8) = n.testBit i := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  change n / (2 ^ 8 * 2 ^ (i - 8)) % 2 = 1 ↔ n / 2 ^ i % 2 = 1
  rw [← Nat.pow_add]
  rw [show 8 + (i - 8) = i by omega]

theorem simpleAuctionDivPow160_testBit (n i : Nat) (h160 : 160 ≤ i) :
    (n / 2 ^ 160).testBit (i - 160) = n.testBit i := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  change n / (2 ^ 160 * 2 ^ (i - 160)) % 2 = 1 ↔ n / 2 ^ i % 2 = 1
  rw [← Nat.pow_add]
  rw [show 160 + (i - 160) = i by omega]

theorem simpleAuctionNatLandClearLow8 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 8) = (n / 2 ^ 8) * 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 8)).testBit i =
    ((n / 2 ^ 8) * 2 ^ 8).testBit i
  rw [Nat.testBit_and]
  rw [show (2 : Nat) ^ 256 - 2 ^ 8 = (2 ^ 248 - 1) <<< 8 by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]]
  rw [simpleAuctionTestBit_shiftLeft]
  rw [show (n / 2 ^ 8) * 2 ^ 8 = (n / 2 ^ 8) <<< 8 by rw [Nat.shiftLeft_eq]]
  rw [simpleAuctionTestBit_shiftLeft]
  by_cases hi8 : i < 8
  · simp [hi8]
  · simp [hi8]
    have h8 : 8 ≤ i := Nat.le_of_not_gt hi8
    by_cases hi256 : i < 256
    · have hlt : i - 8 < 248 := by omega
      change (n.testBit i && (((2 : Nat) ^ 248 - 1).testBit (i - 8))) =
        (n / 2 ^ 8).testBit (i - 8)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hlt]
      exact (simpleAuctionDivPow8_testBit n i h8).symm
    · have hnlt : ¬ i - 8 < 248 := by omega
      change (n.testBit i && (((2 : Nat) ^ 248 - 1).testBit (i - 8))) =
        (n / 2 ^ 8).testBit (i - 8)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hnlt]
      change (n / 2 ^ 8).testBit (i - 8) = false
      have hq : n / 2 ^ 8 < 2 ^ 248 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 8 * 2 ^ 248 = (2 : Nat) ^ 256 by
          rw [← Nat.pow_add]]
        exact hn
      have hpow : n / 2 ^ 8 < 2 ^ (i - 8) := by
        exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Nat.testBit_lt_two_pow hpow

theorem simpleAuctionNatLandClearLow160 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 160) = (n / 2 ^ 160) * 2 ^ 160 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 160)).testBit i =
    ((n / 2 ^ 160) * 2 ^ 160).testBit i
  rw [Nat.testBit_and]
  rw [show (2 : Nat) ^ 256 - 2 ^ 160 = (2 ^ 96 - 1) <<< 160 by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]]
  rw [simpleAuctionTestBit_shiftLeft]
  rw [show (n / 2 ^ 160) * 2 ^ 160 = (n / 2 ^ 160) <<< 160 by rw [Nat.shiftLeft_eq]]
  rw [simpleAuctionTestBit_shiftLeft]
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
      exact (simpleAuctionDivPow160_testBit n i h160).symm
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

theorem simpleAuctionNatLorShift8One (q : Nat) : Nat.lor (q * 2 ^ 8) 1 = 1 + q * 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((q * 2 ^ 8) ||| 1).testBit i = (1 + q * 2 ^ 8).testBit i
  rw [Nat.testBit_or]
  conv_lhs => rw [show q * 2 ^ 8 = q <<< 8 by rw [Nat.shiftLeft_eq]]
  rw [simpleAuctionTestBit_shiftLeft]
  cases i with
  | zero =>
      simp [Nat.testBit]
      rw [Nat.add_mod]
      have hmul : q * 256 % 2 = 0 := by
        rw [show q * 256 = (q * 128) * 2 by ring]
        exact Nat.mul_mod_left (q * 128) 2
      rw [hmul]
  | succ k =>
      have h1bit : (1 : Nat).testBit (k + 1) = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le (by norm_num : 1 < 2)
          (Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 1 ≤ k + 1))
      rw [h1bit, Bool.or_false]
      rw [show 1 + q * 2 ^ 8 = Nat.bit true (q * 2 ^ 7) by
        simp [Nat.bit]
        omega]
      rw [Nat.testBit_bit_succ]
      conv_rhs => rw [show q * 2 ^ 7 = q <<< 7 by rw [Nat.shiftLeft_eq]]
      rw [simpleAuctionTestBit_shiftLeft]
      by_cases hk : k < 7
      · have hk8 : k + 1 < 8 := by omega
        simp [hk, hk8]
      · have hnk8 : ¬ k + 1 < 8 := by omega
        simp [hk, hnk8]

theorem simpleAuctionNatLorHigh160Low (q v : Nat) (hv : v < 2 ^ 160) :
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
    rw [← simpleAuctionDivPow160_testBit (v + q * 2 ^ 160) i hle, hdiv]

theorem simpleAuctionHigh160Mask_toNat (old : UInt256) :
    (UInt256.land old (UInt256.lnot solcAddrMask)).toNat =
      (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  rw [simpleAuctionU256_land_toNat]
  have hlnot : (UInt256.lnot solcAddrMask).toNat = 2 ^ 256 - 2 ^ 160 := by
    native_decide
  rw [hlnot]
  have hwlt : old.toNat < 2 ^ 256 := by
    change old.val.val < 2 ^ 256
    simpa [UInt256.size] using old.val.isLt
  rw [simpleAuctionNatLandClearLow160 old.toNat hwlt]
  have hlt : old.toNat / 2 ^ 160 * 2 ^ 160 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
  rw [Nat.mod_eq_of_lt hlt]

theorem simpleAuctionSetAddressNat_lt_size (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 < UInt256.size := by
  have hq : old.toNat / 2 ^ 160 < 2 ^ 96 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 160 * 2 ^ 96 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simpa [UInt256.size] using old.val.isLt
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

theorem simpleAuctionSetAddressWord_eq (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    simpleAuctionSetAddressWord old addr =
      UInt256.ofNat (addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160) := by
  unfold simpleAuctionSetAddressWord
  apply u256_inj
  rw [simpleAuctionU256_lor_toNat, simpleAuctionHigh160Mask_toNat,
    simpleAuctionU256_land_toNat]
  have hcleanNat :
      Nat.land addr.toNat solcAddrMask.toNat % UInt256.size = addr.toNat := by
    simpa [simpleAuctionU256_land_toNat] using congrArg UInt256.toNat
      (solcAddrMask_clean hcanon)
  rw [hcleanNat]
  have hv : addr.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
  rw [simpleAuctionNatLorHigh160Low (old.toNat / 2 ^ 160) addr.toNat hv]
  rw [Nat.mod_eq_of_lt (simpleAuctionSetAddressNat_lt_size old addr hcanon)]
  rw [ulit_toNat' _ (simpleAuctionSetAddressNat_lt_size old addr hcanon)]

theorem simpleAuctionSetAddressWord_toNat (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    (simpleAuctionSetAddressWord old addr).toNat =
      addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  rw [simpleAuctionSetAddressWord_eq old addr hcanon]
  exact ulit_toNat' _ (simpleAuctionSetAddressNat_lt_size old addr hcanon)

theorem simpleAuctionStorageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (simpleAuctionAddrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (simpleAuctionSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  have haddrWord : EVM.Word.ofNat (Fin.toNat (AccountAddress.ofNat addr.toNat)) = addr := by
    apply u256_inj
    unfold EVM.Word.ofNat UInt256.ofNat AccountAddress.ofNat UInt256.toNat
    change ((addr.val.val % AccountAddress.size) % UInt256.size) = addr.val.val
    nth_rewrite 2 [Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size, UInt256.toNat] using hcanon)]
    exact Nat.mod_eq_of_lt addr.val.isLt
  unfold storageLocStore storageLocWriteWord simpleAuctionAddrLoc
  simp only [valueToWord, haddrWord, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof addr).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
        (simpleAuctionSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, simpleAuctionFromBytes'_take20_wordLE,
    simpleAuctionFromBytes'_drop_wordLE]
  have hclean : (UInt256.land addr solcAddrMask).toNat = addr.toNat := by
    simpa using congrArg UInt256.toNat (solcAddrMask_clean hcanon)
  rw [hclean]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof addr).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [simpleAuctionSetAddressWord_toNat _ _ hcanon]
  ring

theorem simpleAuctionPackedSetTrueNat_lt_size (n : Nat) (hn : n < UInt256.size) :
    1 + 256 * (n / 256) < UInt256.size := by
  have hq : n / 256 < 2 ^ 248 := by
    norm_num [UInt256.size] at hn ⊢
    omega
  have hmul : 256 * (n / 256) ≤ 256 * (2 ^ 248 - 1) :=
    Nat.mul_le_mul_left 256 (Nat.le_pred_of_lt hq)
  norm_num [UInt256.size] at hmul ⊢
  omega

theorem simpleAuctionPackedSetTrueWord_eq (w : UInt256) :
    UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩ =
      UInt256.ofNat (1 + 256 * (w.toNat / 256)) := by
  apply u256_inj
  unfold UInt256.lor UInt256.land UInt256.toNat Fin.lor Fin.land
  change (Nat.lor ((Nat.land w.val.val (UInt256.lnot (⟨255⟩ : UInt256)).toNat) %
      UInt256.size) 1) %
      UInt256.size = (1 + 256 * (w.toNat / 256)) % UInt256.size
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  change (Nat.lor ((Nat.land w.toNat (2 ^ 256 - 2 ^ 8)) % UInt256.size) 1) %
      UInt256.size = (1 + 256 * (w.toNat / 256)) % UInt256.size
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    simpa [UInt256.size] using w.val.isLt
  have hland_lt : Nat.land w.toNat (2 ^ 256 - 2 ^ 8) < UInt256.size := by
    rw [simpleAuctionNatLandClearLow8 w.toNat hwlt]
    exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hland_lt]
  rw [simpleAuctionNatLandClearLow8 w.toNat hwlt]
  rw [show 256 = 2 ^ 8 by norm_num]
  rw [Nat.mul_comm (2 ^ 8) (w.toNat / 2 ^ 8)]
  rw [simpleAuctionNatLorShift8One]

theorem simpleAuctionPackedSetTrueWord_toNat (w : UInt256) :
    (UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩).toNat =
      1 + 256 * (w.toNat / 256) := by
  rw [simpleAuctionPackedSetTrueWord_eq]
  exact ulit_toNat' _ (simpleAuctionPackedSetTrueNat_lt_size w.toNat w.val.isLt)

theorem simpleAuctionStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (simpleAuctionBoolLoc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord simpleAuctionBoolLoc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (⟨1⟩ : UInt256)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1 =
      [1] by
        native_decide]
  rw [fromBytes'_append, simpleAuctionFromBytes'_drop1_wordLE]
  simp [fromBytes']
  rw [simpleAuctionPackedSetTrueWord_toNat]

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem simpleAuctionStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  simp only [Solm.EVM.storageStore, sstoreAccountMap, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

/-- `EVM.storageStore` does not create accounts. -/
theorem simpleAuctionStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

/-! ## Storage-map preservation re-exports -/

theorem simpleAuctionUInt256_compare_eq_val_compare (a b : UInt256) :
    compare a b = compare a.val b.val := uInt256_compare_eq_val_compare a b

theorem simpleAuctionStorage_findD_insert_ne
    (storage : Storage) (readSlot writeSlot val default : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).findD readSlot default = storage.findD readSlot default :=
  storage_findD_insert_ne storage readSlot writeSlot val default hne

theorem simpleAuctionStorage_findD_erase_ne
    (storage : Storage) (readSlot writeSlot default : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).findD readSlot default = storage.findD readSlot default :=
  storage_findD_erase_ne storage readSlot writeSlot default hne

theorem simpleAuctionStorage_findD_update_ne
    (storage : Storage) (readSlot writeSlot val default : UInt256) (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).findD
        readSlot default) = storage.findD readSlot default :=
  storage_findD_update_ne storage readSlot writeSlot val default hne

theorem simpleAuctionStorage_find?_insert_ne
    (storage : Storage) (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).find? readSlot = storage.find? readSlot :=
  storage_find?_insert_ne storage readSlot writeSlot val hne

theorem simpleAuctionStorage_find?_erase_ne
    (storage : Storage) (readSlot writeSlot : UInt256) (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).find? readSlot = storage.find? readSlot :=
  storage_find?_erase_ne storage readSlot writeSlot hne

theorem simpleAuctionStorage_find?_update_ne
    (storage : Storage) (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    ((if val == (default : UInt256) then storage.erase writeSlot
      else storage.insert writeSlot val).find? readSlot) = storage.find? readSlot :=
  storage_find?_update_ne storage readSlot writeSlot val hne

theorem simpleAuctionAccountMap_find_insert_self
    (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.insert a acc).find? a = some acc :=
  accountMap_find_insert_self σ a acc

theorem simpleAuctionStorage_findD_insert_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 default : UInt256) :
    ((storage.insert writeSlot val1).insert writeSlot val2).findD readSlot default =
      (storage.insert writeSlot val2).findD readSlot default :=
  storage_findD_insert_insert_self storage writeSlot readSlot val1 val2 default

theorem simpleAuctionStorage_findD_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).findD readSlot
        (default : UInt256)) =
      (storage.insert writeSlot val2).findD readSlot (default : UInt256) :=
  storage_findD_update_insert_self storage writeSlot readSlot val1 val2

end SimpleAuction
