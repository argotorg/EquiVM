import Examples.Ballot.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Storage
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Ballot

/-! ## Ballot-wide storage and ABI helpers -/

/-- `ByteArray` `==` reflects equality. -/
theorem ballotByteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
-- `fromBytes'` is `Nat.ofDigits 256` over little-endian byte values.
theorem fromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fromBytes', Nat.ofDigits, ih]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
-- `Nat.land` is commutative (via test bits).
theorem nat_land_comm (a b : ℕ) : Nat.land a b = Nat.land b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a &&& b).testBit i = (b &&& a).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem u256_land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show (Nat.land a.toNat b.toNat) % UInt256.size =
    (Nat.land b.toNat a.toNat) % UInt256.size
  rw [nat_land_comm]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem u256_add_comm (a b : UInt256) : a + b = b + a := by
  apply u256_inj
  rw [uadd_toNat, uadd_toNat, Nat.add_comm]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem u256_add_assoc (a b c : UInt256) : (a + b) + c = a + (b + c) := by
  apply u256_inj
  simp [uadd_toNat, Nat.add_assoc]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem u256_mul_two_ofNat (a : UInt256) :
    UInt256.mul a ⟨2⟩ = UInt256.ofNat (a.toNat * 2) := by
  apply u256_inj
  show (a.val * (⟨2⟩ : UInt256).val).val = (Fin.ofNat UInt256.size (a.toNat * 2)).val
  rw [Fin.val_mul]
  rfl

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`, generic `Nat.testBit` form of left shift.
theorem ballotTestBit_shiftLeft (m k i : Nat) :
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

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`, bit access after dropping low bits.
theorem ballotDivPow_testBit (n k i : Nat) (hk : k ≤ i) :
    (n / 2 ^ k).testBit (i - k) = n.testBit i := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  rw [show 2 ^ k * 2 ^ (i - k) = 2 ^ i by
    rw [← Nat.pow_add]
    congr
    omega]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
-- Appending high bits above a low field is the same as addition when the low field fits.
theorem ballotNat_lor_shift_add (a b k : Nat) (ha : a < 2 ^ k) :
    Nat.lor a (b * 2 ^ k) = a + b * 2 ^ k := by
  induction k generalizing a b with
  | zero =>
      have ha0 : a = 0 := by omega
      subst a
      norm_num
      change (0 ||| b) = b
      simp
  | succ k ih =>
      have hdiv : Nat.div2 a < 2 ^ k := by
        rw [Nat.div2_val]
        apply Nat.div_lt_of_lt_mul
        rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring_nf]
        exact ha
      nth_rewrite 1 [← Nat.bit_bodd_div2 a]
      rw [show b * 2 ^ (k + 1) = Nat.bit false (b * 2 ^ k) by
        rw [Nat.bit_val, Bool.toNat_false, Nat.pow_succ]
        ring]
      change (Nat.bit (Nat.bodd a) (Nat.div2 a) ||| Nat.bit false (b * 2 ^ k)) =
        a + Nat.bit false (b * 2 ^ k)
      rw [Nat.lor_bit]
      rw [Bool.or_false]
      change Nat.bit (Nat.bodd a) (Nat.lor (Nat.div2 a) (b * 2 ^ k)) =
        a + Nat.bit false (b * 2 ^ k)
      rw [ih (Nat.div2 a) b hdiv]
      rw [Nat.bit_val, Nat.bit_val, Bool.toNat_false]
      have hdecomp : (Nat.bodd a).toNat + Nat.div2 a * 2 = a := by
        simpa [Nat.mul_comm] using Nat.bodd_add_div2 a
      omega

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
-- Byte ranges `[0]`, `[1, 21)`, and `[21, 32)` do not overlap.
theorem ballotNat_lor_packed_address (a q : Nat) (ha : a < 2 ^ 160) :
    Nat.lor 1 (Nat.lor (a * 2 ^ 8) (q * 2 ^ 168)) =
      1 + a * 2 ^ 8 + q * 2 ^ 168 := by
  rw [ballotNat_lor_shift_add (a * 2 ^ 8) q 168]
  · rw [show a * 2 ^ 8 + q * 2 ^ 168 = (a + q * 2 ^ 160) * 2 ^ 8 by ring]
    rw [ballotNat_lor_shift_add 1 (a + q * 2 ^ 160) 8 (by norm_num)]
    ring
  · calc
      a * 2 ^ 8 < 2 ^ 160 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right ha (by norm_num)
      _ = 2 ^ 168 := by norm_num [Nat.pow_add]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
-- Clearing the low 168 bits keeps the bytes above an address-at-offset-1 field.
theorem ballotNatLandClearLow168 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 168) = (n / 2 ^ 168) * 2 ^ 168 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 168)).testBit i =
    ((n / 2 ^ 168) * 2 ^ 168).testBit i
  rw [Nat.testBit_and]
  rw [show (2 : Nat) ^ 256 - 2 ^ 168 = (2 ^ 88 - 1) <<< 168 by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]]
  rw [ballotTestBit_shiftLeft]
  rw [show (n / 2 ^ 168) * 2 ^ 168 = (n / 2 ^ 168) <<< 168 by
    rw [Nat.shiftLeft_eq]]
  rw [ballotTestBit_shiftLeft]
  by_cases hi168 : i < 168
  · simp [hi168]
  · simp [hi168]
    have h168 : 168 ≤ i := Nat.le_of_not_gt hi168
    by_cases hi256 : i < 256
    · have hlt : i - 168 < 88 := by omega
      change (n.testBit i && (((2 : Nat) ^ 88 - 1).testBit (i - 168))) =
        (n / 2 ^ 168).testBit (i - 168)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hlt]
      exact (ballotDivPow_testBit n 168 i h168).symm
    · have hnlt : ¬ i - 168 < 88 := by omega
      change (n.testBit i && (((2 : Nat) ^ 88 - 1).testBit (i - 168))) =
        (n / 2 ^ 168).testBit (i - 168)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hnlt]
      change (n / 2 ^ 168).testBit (i - 168) = false
      have hq : n / 2 ^ 168 < 2 ^ 88 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 168 * 2 ^ 88 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
        exact hn
      have hpow : n / 2 ^ 168 < 2 ^ (i - 168) := by
        exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Nat.testBit_lt_two_pow hpow

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem u256_lor_toNat (a b : UInt256) :
    (UInt256.lor a b).toNat = Nat.lor a.toNat b.toNat % UInt256.size := rfl

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem u256_land_toNat (a b : UInt256) :
    (UInt256.land a b).toNat = Nat.land a.toNat b.toNat % UInt256.size := rfl

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem u256_mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = a.toNat * b.toNat % UInt256.size := rfl

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem ballotHigh168Mask_toNat (old : UInt256) :
    (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 168)) old).toNat =
      (old.toNat / 2 ^ 168) * 2 ^ 168 := by
  rw [u256_land_toNat]
  rw [ulit_toNat' _ (by norm_num [UInt256.size])]
  rw [nat_land_comm]
  rw [ballotNatLandClearLow168 old.toNat (by
    change old.val.val < 2 ^ 256
    simpa [UInt256.size] using old.val.isLt)]
  have hlt : old.toNat / 2 ^ 168 * 2 ^ 168 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
  rw [Nat.mod_eq_of_lt hlt]

-- LIBRARY CANDIDATE: `Reasoning.Solm` / packed storage writes.
theorem ballotPackedAddressAfterBoolTrueWord_eq (old val : UInt256)
    (hcanon : val.toNat < EVM.addressModulus) :
    UInt256.lor ⟨1⟩
      (UInt256.lor
        (UInt256.mul (UInt256.land val solcAddrMask) ⟨256⟩)
        (UInt256.land
          (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
          old)) =
      UInt256.ofNat (1 + val.toNat * 2 ^ 8 + (old.toNat / 2 ^ 168) * 2 ^ 168) := by
  have hmask :
      UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩) =
        UInt256.ofNat (2 ^ 256 - 2 ^ 168) := by native_decide
  apply u256_inj
  rw [u256_lor_toNat, u256_lor_toNat, hmask, u256_mul_toNat, u256_land_toNat,
    ballotHigh168Mask_toNat]
  have hcleanNat :
      Nat.land val.toNat solcAddrMask.toNat % UInt256.size = val.toNat := by
    simpa [u256_land_toNat] using congrArg UInt256.toNat (solcAddrMask_clean hcanon)
  rw [hcleanNat]
  rw [show (⟨256⟩ : UInt256).toNat = 2 ^ 8 by decide]
  rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
  change Nat.lor 1
      (Nat.lor (val.toNat * 2 ^ 8 % UInt256.size)
        (old.toNat / 2 ^ 168 * 2 ^ 168) % UInt256.size) % UInt256.size =
    (UInt256.ofNat (1 + val.toNat * 2 ^ 8 + old.toNat / 2 ^ 168 * 2 ^ 168)).toNat
  have hshiftlt : val.toNat * 2 ^ 8 < UInt256.size := by
    calc
      val.toNat * 2 ^ 8 < 2 ^ 160 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right
        (by simpa [EVM.addressModulus, EVM.twoPow] using hcanon) (by norm_num)
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  rw [Nat.mod_eq_of_lt hshiftlt]
  have hq : old.toNat / 2 ^ 168 < 2 ^ 88 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 168 * 2 ^ 88 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simpa [UInt256.size] using old.val.isLt
  have hv : val.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
  have hinnerlt :
      Nat.lor (val.toNat * 2 ^ 8) (old.toNat / 2 ^ 168 * 2 ^ 168) <
        UInt256.size := by
    rw [ballotNat_lor_shift_add (val.toNat * 2 ^ 8) (old.toNat / 2 ^ 168) 168]
    · have hvle : val.toNat ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hv
      have hqle : old.toNat / 2 ^ 168 ≤ 2 ^ 88 - 1 := Nat.le_pred_of_lt hq
      have hvterm : val.toNat * 2 ^ 8 ≤ (2 ^ 160 - 1) * 2 ^ 8 :=
        Nat.mul_le_mul_right _ hvle
      have hqterm :
          old.toNat / 2 ^ 168 * 2 ^ 168 ≤ (2 ^ 88 - 1) * 2 ^ 168 :=
        Nat.mul_le_mul_right _ hqle
      have hmax :
          (2 ^ 160 - 1) * 2 ^ 8 + (2 ^ 88 - 1) * 2 ^ 168 < UInt256.size := by
        norm_num [UInt256.size, Nat.pow_add]
      omega
    · calc
        val.toNat * 2 ^ 8 < 2 ^ 160 * 2 ^ 8 :=
          Nat.mul_lt_mul_of_pos_right hv (by norm_num)
        _ = 2 ^ 168 := by norm_num [Nat.pow_add]
  rw [Nat.mod_eq_of_lt hinnerlt]
  rw [ballotNat_lor_packed_address val.toNat (old.toNat / 2 ^ 168)
    hv]
  have hlt : 1 + val.toNat * 2 ^ 8 + old.toNat / 2 ^ 168 * 2 ^ 168 < UInt256.size := by
    have hvle : val.toNat ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hv
    have hqle : old.toNat / 2 ^ 168 ≤ 2 ^ 88 - 1 := Nat.le_pred_of_lt hq
    have hvterm : val.toNat * 2 ^ 8 ≤ (2 ^ 160 - 1) * 2 ^ 8 :=
      Nat.mul_le_mul_right _ hvle
    have hqterm :
        old.toNat / 2 ^ 168 * 2 ^ 168 ≤ (2 ^ 88 - 1) * 2 ^ 168 :=
      Nat.mul_le_mul_right _ hqle
    have hmax :
        1 + (2 ^ 160 - 1) * 2 ^ 8 + (2 ^ 88 - 1) * 2 ^ 168 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [ulit_toNat' _ hlt, Nat.mod_eq_of_lt hlt]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
-- `n &&& (2^k - 1)` keeps exactly the low `k` bits.
theorem nat_land_mask_eq_mod (n k : Nat) : Nat.land n (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& (2 ^ k - 1)).testBit i = (n % 2 ^ k).testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · rw [decide_eq_true hi]
    simp
  · rw [decide_eq_false hi]
    simp

-- LIBRARY CANDIDATE: `Reasoning.Memory` / `Reasoning.Solc`.
-- The low 20 little-endian bytes of an EVM word are the solc address-mask result.
theorem fromBytes'_take20_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 20) =
      (UInt256.land w solcAddrMask).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 20 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [fromBytes'_eq_ofDigits (bs.take 20), List.map_take]
  rw [← htake, hfull]
  show w.toNat % 256 ^ 20 = (Nat.land w.toNat solcAddrMask.toNat) % UInt256.size
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ 160 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160)) (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

/-- Loading a Solidity `address` stored at byte offset 0 returns the low-160-bit address word. -/
theorem ballotStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }
      = .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat) := by
  unfold storageLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 20))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [fromBytes'_take20_wordLE]

/-- Loading a full-slot Solidity `uint256` returns the source-level integer for that word. -/
theorem ballotStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad wordLoc wordToElem
  simp only [uint256Int, Fin.val_zero, Nat.zero_add]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

/-- Loading a full-slot Solidity `bytes32` returns the big-endian fixed-bytes value. -/
theorem ballotStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 32, hbound := by decide,
          type := .bytes ⟨31, by decide⟩ }
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  simp only [show 32 - (31 + 1) = 0 by norm_num, List.drop_zero]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

/-- The result of applying solc's address mask is always canonical. -/
theorem solcAddrMask_result_canonical (w : UInt256) :
    (UInt256.land w solcAddrMask).toNat < EVM.addressModulus := by
  have hlandle : ∀ a b : ℕ, Nat.land a b ≤ b := by
    intro a b
    refine Nat.le_of_testBit fun i hi => ?_
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  show (Nat.land w.toNat solcAddrMask.toNat) % UInt256.size < EVM.addressModulus
  have hle : Nat.land w.toNat solcAddrMask.toNat ≤ solcAddrMask.toNat := hlandle _ _
  have hltSize : Nat.land w.toNat solcAddrMask.toNat < UInt256.size :=
    lt_of_le_of_lt hle (by decide)
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by decide)

/-- ABI-encoding an address return is exactly the 32-byte masked address word. -/
theorem ballotAddressReturnEncoding (w : UInt256) :
    encodeReturnValue? addr (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask)) := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask :=
    u256_ofNat_toNat _
  refine scalarReturnEncoding (t := .address) (w := UInt256.land w solcAddrMask) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

/-- ABI-encoding a `Proposal` getter tuple is exactly `name || voteCount`. -/
theorem ballotProposalReturnEncoding (name count : UInt256) :
    encodeReturnValue? (.tuple [bytes32, uint256])
      (.tuple [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE name),
        .int (Int.ofNat count.toNat)]) =
      some (UInt256.toByteArray name ++ UInt256.toByteArray count) := by
  have hnameLen : (EVM.Word.toBytesBE name).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size name
  have hword : EVM.word count.toNat = count := u256_ofNat_toNat count
  have hlt : count.toNat < EVM.twoPow 256 := by
    change count.val.val < EVM.twoPow 256
    exact count.val.isLt
  have hencName :
      encodeABIValue? bytes32 (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE name)) =
        some (EVM.Word.toBytesBE name) := by
    simp only [bytes32, encodeABIValue?, hnameLen, zeroBytes]
    simp
  have hencCount :
      encodeABIValue? uint256 (.int (Int.ofNat count.toNat)) =
        some (EVM.Word.toBytesBE count) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hheadInner : abiTupleHeadSize? [bytes32, uint256] = some 64 := by native_decide
  have hheadOuter : abiTupleHeadSize? [(.tuple [bytes32, uint256])] = some 64 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  have hdynTuple : isDynamicABIType (.tuple [bytes32, uint256]) = false := by native_decide
  have hinner :
      encodeABIValue? (.tuple [bytes32, uint256])
        (.tuple [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE name),
          .int (Int.ofNat count.toNat)]) =
        some (EVM.Word.toBytesBE name ++ EVM.Word.toBytesBE count) := by
    simp only [encodeABIValue?, encodeABIValues?, encodeABIValuesFrom?,
      hheadInner, hencName, hencCount, hdynBytes, hdynUint, bind, Option.bind,
      Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  rw [toByteArray_eq_toBytesBE name, toByteArray_eq_toBytesBE count]
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hheadOuter, hinner, hdynTuple, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

/-- `wordOfInt (Int.ofNat a.toNat) = a` for an EVM word. -/
theorem ballotWordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
-- A nonzero storage write to an existing account is read back from the same slot.
theorem ballotStorageLoad_storageStore_self_nonzero (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) {acc : Account} (hacc : evm.lookupAccount a = some acc)
    (hval : (val == default) = false) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm a slot val) a slot = val := by
  unfold Solm.EVM.storageLoad Solm.EVM.storageStore State.lookupAccount Account.lookupStorage at *
  simp only [hacc, Option.option, State.setAccount, Account.updateStorage, hval]
  simp only [Bool.false_eq_true, if_false]
  rw [accountMap_find_insert_self]
  simp only [Option.option]
  unfold Batteries.RBMap.findD
  rw [Batteries.RBMap.find?_insert_of_eq (t := acc.storage) (k := slot) (v := val)
    (k' := slot) (h := (Std.ReflCmp.compare_self (cmp := compare) : compare slot slot = .eq))]
  rfl

/-- A decoded `uint256` used as a storage key is the original EVM word. -/
theorem ballotKeyValueToWord_int_ofNat_toNat (a : UInt256) :
    keyValueToWord (.int (Int.ofNat a.toNat)) = a := by
  unfold keyValueToWord
  exact ballotWordOfInt_ofNat_toNat a

/-- The shared solc return wrapper computes the fixed one-word return length. -/
abbrev ballotRetEnd : UInt256 := (⟨32⟩ : UInt256) + ⟨128⟩

theorem ballotSubRet32_toNat :
    (UInt256.sub ballotRetEnd ⟨128⟩).toNat = 32 := by
  decide

/-- The standard Solidity panic selector word. -/
def ballotPanicSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩

noncomputable def ballotPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ballotPanicSelector).write 0 mem 0 32

noncomputable def ballotPanicMem (panicCode : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray panicCode).write 0 (ballotPanicMem0 mem) 4 32

end Ballot

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Ballot-local return routines -/

/-- Ballot's Solidity `Panic(0x32)` array-bounds block at pc 1815. -/
theorem RD.ballotPanic32Revert1815 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1815⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev ballotBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = Ballot.ballotPanicSelector := by
    rfl
  have rd1824₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0 ]
  have rd1824 := rd1824₀
  rw [hsel] at rd1824
  have rd1828 := evm_run rd1824 with [
    raw mstore 0 (Ballot.ballotPanicMem0 mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩ ]
  have rd1834 := evm_run rd1828 with [
    raw mstore 0 (Ballot.ballotPanicMem ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x24⟩, push0 ]
  exact rd1834.rev 0 (by decide) mem_cost (by evm_ov)

/-- Ballot's Solidity `Panic(0x11)` checked-arithmetic block at pc 1847. -/
theorem RD.ballotPanic11Revert1847 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1847⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev ballotBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = Ballot.ballotPanicSelector := by
    rfl
  have rd1855₀ := evm_run h with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0 ]
  have rd1855 := rd1855₀
  rw [hsel] at rd1855
  have rd1859 := evm_run rd1855 with [
    raw mstore 0 (Ballot.ballotPanicMem0 mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x11⟩, push1 ⟨4⟩ ]
  have rd1865 := evm_run rd1859 with [
    raw mstore 0 (Ballot.ballotPanicMem ⟨0x11⟩ mem) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0x24⟩, push0 ]
  exact rd1865.rev 0 (by decide) mem_cost (by evm_ov)

/-- Ballot's shared solc ABI encoder for one `address` word at pc 221. -/
theorem RD.ballotRoutineEncodeAddress {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨221⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD ballotBytecode ee g s0 ⟨194⟩ (Ballot.ballotRetEnd :: ret :: R)
      (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd⟩

/-- Ballot's shared one-word return tail at pc 194. -/
theorem RD.ballotReturnOneWord194 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨194⟩ (Ballot.ballotRetEnd :: R)
        (solcReturnMem val) (UInt256.ofNat 5) rdata acc k C) (hov : R.length + 5 ≤ 1024) :
    RDret ballotBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 val)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          Ballot.ballotSubRet32_toNat]
        simpa using solcReturnMem_read128 val)
      (by evm_ov) ]

/-- Ballot's shared one-word return tail at pc 194, generalized to any memory whose free pointer
    word is `0x80` and whose return word lives at `0x80`. -/
theorem RD.ballotReturnOneWord194OfMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨194⟩ (Ballot.ballotRetEnd :: R)
        mem (UInt256.ofNat 5) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hread128 : mem.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret ballotBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      hmload64
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          Ballot.ballotSubRet32_toNat]
        exact hread128)
      (by evm_ov) ]

end Reasoning.Reach
