import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Stepping
import Solm.SolidityLayout
import Ethereum.Theory.StorageExtensionality

/-!
# Storage — ordered-map (`Batteries.RBMap`) facts for EVM storage maps

Generic lookup/update facts for the red-black-tree maps that back EVM storage (`Storage`) and the
account map (`AccountMap`), independent of any contract or keccak layout: a write at one slot
preserves lookup at a different slot.  The `RBNode`/`RBMap` `find?_erase_ne` machinery fills the gap
left by `Batteries` (which ships `find?_insert_of_ne` but no erase analogue).  The `UInt256`
`compare` instances these rely on live in `Reasoning.EVMWord`.
-/

open Ethereum Ethereum.EVM Solm

namespace Reasoning.Theory

theorem storage_findD_insert_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).findD readSlot default =
      storage.findD readSlot default := by
  unfold Batteries.RBMap.findD
  rw [Batteries.RBMap.find?_insert_of_ne]
  intro hcmp
  exact hne (Std.LawfulEqCmp.eq_of_compare hcmp)

theorem keyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w := by
  apply u256_inj
  unfold keyValueToWord AccountAddress.ofNat
  exact Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)

theorem keyValueToWord_address (a : AccountAddress) :
    keyValueToWord (.address a) = UInt256.ofNat a.val := by
  apply u256_inj
  simp [keyValueToWord, UInt256.ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))).symm

theorem keyValueToWord_uint256 (w : UInt256) :
    keyValueToWord (.int (Int.ofNat w.toNat)) = w := by
  unfold keyValueToWord EVM.wordOfInt
  simp only [Int.ofNat_eq_natCast]
  apply u256_inj
  show w.toNat % EVM.twoPow 256 = w.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le w.val.isLt (by decide))

theorem wordOfInt_ofNat_eq (n : Nat) :
    EVM.wordOfInt (Int.ofNat n) = UInt256.ofNat n := by
  apply u256_inj
  show (Int.ofNat n).toNat % EVM.twoPow 256 = (UInt256.ofNat n).toNat
  rw [show (Int.ofNat n).toNat = n from rfl,
    show (UInt256.ofNat n).toNat = n % UInt256.size from rfl,
    show EVM.twoPow 256 = UInt256.size from by decide]

theorem keyValueToWord_fixedBytes32 (w : UInt256) :
    keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE w)) = w := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [keyValueToWord, hlen]
  apply u256_inj
  have hfrom : fromBytesBigEndian (EVM.Word.toBytesBE w) = w.toNat := by
    have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray w)
    simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
      h.trans (fromByteArrayBigEndian_toByteArray w)
  rw [EVM.Word.ofNat, hfrom]
  exact Nat.mod_eq_of_lt w.val.isLt

/-! ## Full-slot uint256 storage -/

def uint256Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide,
    type := .int (.uint ⟨256, by decide⟩) }

theorem storageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint256Loc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
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
  unfold storageLocLoad uint256Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  rw [htake, fromBytes'_toBytesLEWithSizeProof]
  rfl

theorem storageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
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

theorem storageLocStore_uint256_nat (evm : EVM.State) (slot : UInt256) (n : Nat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat n)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat n)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_ofNat_eq, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat n)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
      (UInt256.ofNat n).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem storageLocStore_oneByte
    (evm : EVM.State) (slot valueWord target : UInt256)
    (off : Fin 32) (typ : ABI.ElemType)
    (hbound : off.val + (1 : Fin 33).val - 1 < 32) (v : Value)
    (hval : valueToWord v = some valueWord)
    (htarget : target.toNat =
      fromBytes'
        ((EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take off.val ++
         (EVM.Word.toBytesLEWithSizeProof
              (storageLocWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
                off.val none valueWord)).1.take 1 ++
         (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
            (off.val + 1))) :
    storageLocStore evm
      { slot := slot, offset := off, size := 1, hbound := hbound, type := typ } v =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot target) := by
  unfold storageLocStore
  simp only [hval, bind, Option.bind]
  congr 2
  apply u256_inj
  exact htarget.symm

theorem storageLocStore_oneByte_int_ofNat_update
    (evm : EVM.State) (slot old target : UInt256)
    (off : Fin 32) (typ : ABI.ElemType)
    (hbound : off.val + (1 : Fin 33).val - 1 < 32)
    (byte : Nat)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot = old)
    (hbyte : byte < 256)
    (htarget : target.toNat =
      old.toNat % 2 ^ (8 * off.val) +
        2 ^ (8 * off.val) * byte +
        2 ^ (8 * off.val + 8) * (old.toNat / 2 ^ (8 * off.val + 8))) :
    storageLocStore evm
      { slot := slot, offset := off, size := 1, hbound := hbound, type := typ }
      (.int (Int.ofNat byte)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot target) := by
  have hval : valueToWord (.int (Int.ofNat byte)) = some (UInt256.ofNat byte) := by
    simp [valueToWord]
    exact wordOfInt_ofNat_eq byte
  have hoffLe : off.val ≤ 32 := Nat.le_of_lt off.isLt
  have htargetBytes :
      target.toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take off.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
                  off.val none (UInt256.ofNat byte))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
              (off.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof old).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat byte)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (off.val + 1) = 8 * off.val + 8 by ring]
    rw [show 256 ^ off.val = 2 ^ (8 * off.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ (off.val + 1) = 2 ^ (8 * off.val + 8) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat byte).toNat % 256 = byte by
      rw [ulit_toNat' _ (lt_of_lt_of_le hbyte (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hbyte]
    exact htarget
  exact storageLocStore_oneByte evm slot (UInt256.ofNat byte) target off typ hbound
    (.int (Int.ofNat byte)) hval htargetBytes

private theorem fromBytes'_take_one_eq_mod (bs : List UInt8) :
    fromBytes' (bs.take 1) = fromBytes' bs % 256 := by
  cases bs with
  | nil => simp [fromBytes']
  | cons b bs =>
      simp [fromBytes', Nat.add_mul_mod_self_left]

theorem u256_byteAt_toNat_of_le31 {i w : UInt256} (hi : i.toNat ≤ 31) :
    (UInt256.byteAt i w).toNat =
      (w.toNat / 2 ^ ((31 - i.toNat) * 8)) % 256 := by
  unfold UInt256.byteAt
  rw [if_neg]
  · change (UInt256.land (UInt256.shiftRight w
        (UInt256.ofNat ((31 - i.toNat) * 8))) ⟨255⟩).toNat = _
    rw [u256_land_toNat]
    unfold UInt256.shiftRight
    rw [if_neg]
    · change Nat.land
          (((w.val >>> (UInt256.ofNat ((31 - i.toNat) * 8)).val) :
              Fin UInt256.size).val)
          (⟨255⟩ : UInt256).toNat % UInt256.size = _
      rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
      rw [show (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 by decide]
      rw [nat_land_mask_eq_mod]
      change w.toNat / 2 ^ (UInt256.ofNat ((31 - i.toNat) * 8)).toNat %
          2 ^ 8 % UInt256.size = _
      rw [show (UInt256.ofNat ((31 - i.toNat) * 8)).toNat =
          (31 - i.toNat) * 8 by
        apply ulit_toNat'
        have hle : (31 - i.toNat) * 8 ≤ 31 * 8 :=
          Nat.mul_le_mul_right _ (Nat.sub_le 31 i.toNat)
        norm_num [UInt256.size]
        omega]
      have hlt : (w.toNat / 2 ^ ((31 - i.toNat) * 8) % 2 ^ 8) <
          UInt256.size := by
        exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 8)) (by
          norm_num [UInt256.size])
      rw [Nat.mod_eq_of_lt hlt]
      rw [show 2 ^ 8 = 256 by norm_num]
    · change ¬ (UInt256.ofNat ((31 - i.toNat) * 8)).toNat ≥ 256
      rw [show (UInt256.ofNat ((31 - i.toNat) * 8)).toNat =
          (31 - i.toNat) * 8 by
        apply ulit_toNat'
        have hle : (31 - i.toNat) * 8 ≤ 31 * 8 :=
          Nat.mul_le_mul_right _ (Nat.sub_le 31 i.toNat)
        norm_num [UInt256.size]
        omega]
      omega
  · change ¬ (⟨31⟩ : UInt256).toNat < i.toNat
    rw [show (⟨31⟩ : UInt256).toNat = 31 by decide]
    omega

theorem storageLocLoad_oneByte_byteAt
    {evm : EVM.State} {slot idx : UInt256} {off : Fin 32}
    {hbound : off.val + (1 : Fin 33).val - 1 < 32}
    (hoff : off.val = 31 - idx.toNat)
    (hidx : idx.toNat ≤ 31) :
    storageLocLoad evm
      { slot := slot, offset := off, size := 1, hbound := hbound,
        type := .int (.uint ⟨8, by decide⟩) } =
      .int (UInt256.byteAt idx
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat := by
  unfold storageLocLoad wordToElem
  simp
  change fromBytes' (List.take 1 (List.drop off.val
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)) =
    (UInt256.byteAt idx
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat
  rw [fromBytes'_take_one_eq_mod]
  rw [fromBytes'_drop_wordLE]
  rw [u256_byteAt_toNat_of_le31 hidx]
  rw [hoff]
  rw [show 256 ^ (31 - idx.toNat) = 2 ^ ((31 - idx.toNat) * 8) by
    rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
    ring]

/-! ## Full-slot bytes32 storage -/

def bytes32Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide,
    type := .bytes ⟨31, by decide⟩ }

theorem storageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot) =
      .fixedBytes ⟨31, by decide⟩
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
  unfold storageLocLoad bytes32Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  simp only [show 32 - (31 + 1) = 0 by norm_num, List.drop_zero]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

theorem storageLocStore_bytes32 (evm : EVM.State) (slot word : UInt256) (v : Value)
    (hval : valueToWord v = some word) :
    storageLocStore evm (bytes32Loc slot) v =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word) := by
  unfold storageLocStore storageLocWriteWord bytes32Loc
  simp only [hval, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof word).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = word.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

/-! ## Solidity bytes/string storage layout -/

theorem uInt256_shiftRight_zero_left (s : UInt256) :
    UInt256.shiftRight (⟨0⟩ : UInt256) s = ⟨0⟩ := by
  cases s with
  | mk val =>
    unfold UInt256.shiftRight
    simp
    intro _
    apply Fin.ext
    rw [Fin.shiftRight_val]
    simp [Nat.zero_shiftRight]

theorem fromBytes'_zero_take1_wordLE :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 1) = 0 := by
  native_decide

theorem storageLocLoad_bytesLikeLengthLoc_zero {evm : EVM.State} {base : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base = ⟨0⟩) :
    storageLocLoad evm (bytesLikeLengthLoc base evm) = .int 0 := by
  unfold bytesLikeLengthLoc checkBytesPacked storageLocLoad wordToElem
  simp [hload, fromBytes'_zero_take1_wordLE, uInt256_shiftRight_zero_left]

theorem solidityDecodeBytesLengthHeader_zero :
    solidityDecodeBytesLengthHeader ⟨0⟩ = .ok 0 := by
  have hflag : UInt256.land (⟨0⟩ : UInt256) ⟨1⟩ = ⟨0⟩ := by native_decide
  have hraw : UInt256.div (⟨0⟩ : UInt256) ⟨2⟩ = ⟨0⟩ := by native_decide
  have hmask : UInt256.land (⟨0⟩ : UInt256) ⟨127⟩ = ⟨0⟩ := by native_decide
  have hvalidFinal : UInt256.sub (⟨0⟩ : UInt256)
      (UInt256.lt (⟨0⟩ : UInt256) ⟨32⟩) ≠ ⟨0⟩ := by
    native_decide
  simp [solidityDecodeBytesLengthHeader, hflag, hraw, hmask, hvalidFinal]

theorem solidityDecodeBytesLengthHeader_short_valid {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    solidityDecodeBytesLengthHeader header = .ok len.toNat := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  simp [solidityDecodeBytesLengthHeader, hflag, ← hlen, hvalid0]

theorem solidityDecodeBytesLengthHeader_long_valid {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    solidityDecodeBytesLengthHeader header = .ok len.toNat := by
  simp [solidityDecodeBytesLengthHeader, hflag, ← hlen, hvalid]

theorem ult_ne_zero_toNat_lt {a b : UInt256} (h : UInt256.lt a b ≠ ⟨0⟩) :
    a.toNat < b.toNat := by
  by_contra hlt
  have hz : UInt256.lt a b = ⟨0⟩ := ult_zero (by omega)
  exact h hz

theorem solidityShortBytesValid_lt32 {len : UInt256}
    (hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    len.toNat < 32 := by
  have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
    intro hltZero
    exact hvalid0 (by simp [hltZero, UInt256.sub])
  have hlt := ult_ne_zero_toNat_lt hltNe
  simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hlt

theorem checkBytesPacked_of_storageLoad_land_one_zero {evm : EVM.State}
    {base header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩) :
    checkBytesPacked base evm = true := by
  unfold checkBytesPacked
  rw [hload]
  have hmod : header.toNat % 2 = 0 := by
    have h := congrArg UInt256.toNat hflag
    simpa [uInt256_land_one_toNat] using h
  cases header with
  | mk val =>
      cases val with
      | mk n hn =>
          have hnmod : n % 2 = 0 := by
            simpa [UInt256.toNat] using hmod
          have hfin :
              (⟨n, hn⟩ : Fin UInt256.size) % (2 : Fin UInt256.size) = 0 := by
            apply Fin.ext
            change n % (2 % UInt256.size) = 0
            rw [show 2 % UInt256.size = 2 from by norm_num [UInt256.size], hnmod]
          simp [hfin]

theorem checkBytesPacked_of_storageLoad_land_one_ne_zero {evm : EVM.State}
    {base header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩) :
    checkBytesPacked base evm = false := by
  have hlandOne : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
    have hbit := uInt256_land_one_toNat header
    have hbitLt : (UInt256.land header ⟨1⟩).toNat < 2 := by
      rw [hbit]
      exact Nat.mod_lt _ (by decide)
    have hbitNeZero : (UInt256.land header ⟨1⟩).toNat ≠ 0 := by
      intro hzero
      apply hflag
      rw [← u256_ofNat_toNat (UInt256.land header ⟨1⟩), hzero]
      rfl
    have hto : (UInt256.land header ⟨1⟩).toNat = 1 := by
      omega
    rw [← u256_ofNat_toNat (UInt256.land header ⟨1⟩), hto]
    rfl
  have hmod : header.toNat % 2 = 1 := by
    have h := congrArg UInt256.toNat hlandOne
    simpa [uInt256_land_one_toNat] using h
  unfold checkBytesPacked
  rw [hload]
  cases header with
  | mk val =>
      cases val with
      | mk n hn =>
          have hnmod : n % 2 = 1 := by
            simpa [UInt256.toNat] using hmod
          have hfinNe :
              ¬ ((⟨n, hn⟩ : Fin UInt256.size) % (2 : Fin UInt256.size) = 0) := by
            intro hfin
            have hval := congrArg Fin.val hfin
            change n % (2 % UInt256.size) = 0 at hval
            rw [show 2 % UInt256.size = 2 from by norm_num [UInt256.size]] at hval
            omega
          exact decide_eq_false hfinNe

@[simp] theorem bytesLikeLengthLoc_slot (baseSlot : UInt256) (evm : EVM.State) :
    (bytesLikeLengthLoc baseSlot evm).slot = baseSlot := by
  unfold bytesLikeLengthLoc
  split <;> rfl

/-! ## Solidity address storage at byte offset 0 -/

def addressOffset0Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

theorem storageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addressOffset0Loc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  unfold storageLocLoad addressOffset0Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 20))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [fromBytes'_take20_wordLE_solcAddrMask]

def setAddressOffset0Word (old addr : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask)) (UInt256.land addr solcAddrMask)

theorem addressOffset0High160Mask_toNat (old : UInt256) :
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

theorem setAddressOffset0Nat_lt_size (old addr : UInt256)
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

theorem setAddressOffset0Word_eq (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    setAddressOffset0Word old addr =
      UInt256.ofNat (addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160) := by
  unfold setAddressOffset0Word
  apply u256_inj
  rw [u256_lor_toNat, addressOffset0High160Mask_toNat, u256_land_toNat]
  have hcleanNat :
      Nat.land addr.toNat solcAddrMask.toNat % UInt256.size = addr.toNat := by
    simpa [u256_land_toNat] using congrArg UInt256.toNat
      (solcAddrMask_clean hcanon)
  rw [hcleanNat]
  have hv : addr.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
  rw [nat_lor_comm]
  rw [nat_lor_shift_add addr.toNat (old.toNat / 2 ^ 160) 160 hv]
  rw [Nat.mod_eq_of_lt (setAddressOffset0Nat_lt_size old addr hcanon)]
  rw [ulit_toNat' _ (setAddressOffset0Nat_lt_size old addr hcanon)]

theorem setAddressOffset0Word_toNat (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    (setAddressOffset0Word old addr).toNat =
      addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  rw [setAddressOffset0Word_eq old addr hcanon]
  exact ulit_toNat' _ (setAddressOffset0Nat_lt_size old addr hcanon)

theorem valueToWord_address_ofNat_canonical (addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    valueToWord (.address (AccountAddress.ofNat addr.toNat)) = some addr := by
  have haddrWord : EVM.Word.ofNat (↑(AccountAddress.ofNat addr.toNat) : Nat) = addr := by
    apply u256_inj
    unfold EVM.Word.ofNat UInt256.ofNat AccountAddress.ofNat UInt256.toNat
    change ((addr.val.val % AccountAddress.size) % UInt256.size) = addr.val.val
    nth_rewrite 2 [Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size, UInt256.toNat] using hcanon)]
    exact Nat.mod_eq_of_lt addr.val.isLt
  simp [valueToWord, haddrWord]

theorem storageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (addressOffset0Loc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  unfold storageLocStore storageLocWriteWord addressOffset0Loc
  simp only [valueToWord_address_ofNat_canonical addr hcanon, bind, Option.bind]
  have hvlen := (EVM.Word.toBytesLEWithSizeProof addr).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask, fromBytes'_drop_wordLE]
  have hclean : (UInt256.land addr solcAddrMask).toNat = addr.toNat := by
    simpa using congrArg UInt256.toNat (solcAddrMask_clean hcanon)
  rw [hclean]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof addr).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [setAddressOffset0Word_toNat _ _ hcanon]
  ring

/-! ## Solidity address storage at byte offset 1 -/

def addressOffset1Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 1, size := 20, hbound := by decide, type := .address }

theorem storageLocLoad_address_offset1 (evm : EVM.State) (slot : UInt256)
    {hbound : (1 : Fin 32).val + (20 : Fin 33).val - 1 < 32} :
    storageLocLoad evm
        { slot := slot, offset := 1, size := 20, hbound := hbound, type := .address } =
      .address (AccountAddress.ofNat
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨256⟩)
          solcAddrMask).toNat) := by
  unfold storageLocLoad wordToElem
  simp only [Fin.val_one]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 1 21))) = _
  rw [List.extract_eq_take_drop, fromBytes'_drop1_take20_wordLE_solcAddrMask]

/-! ## Packed bool storage at byte offset 0 -/

def boolOffset0Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def setBoolOffset0Word (old word : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩))
    (UInt256.isZero (UInt256.isZero word))

theorem storageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolOffset0Loc slot) =
      wordToElem .bool
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  unfold storageLocLoad boolOffset0Loc
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [fromBytes'_take_wordLE_land_mask (n := 1) _ (by decide)]
  rfl

theorem storageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolOffset0Loc slot) = .bool false := by
  rw [storageLocLoad_bool_offset0 evm slot]
  simp [wordToElem, hzero]

theorem storageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolOffset0Loc slot) = .bool true := by
  rw [storageLocLoad_bool_offset0 evm slot]
  have hbeq :
      ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

theorem natLandClearLow8 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 8) = (n / 2 ^ 8) * 2 ^ 8 := by
  simpa using natLandClearLow n 8 (by norm_num) hn

theorem natLorShift8One (q : Nat) : Nat.lor (q * 2 ^ 8) 1 = 1 + q * 2 ^ 8 := by
  rw [nat_lor_comm, nat_lor_shift_add 1 q 8 (by norm_num)]

theorem packedSetTrueNat_lt_size (n : Nat) (hn : n < UInt256.size) :
    1 + 256 * (n / 256) < UInt256.size := by
  have hq : n / 256 < 2 ^ 248 := by
    norm_num [UInt256.size] at hn ⊢
    omega
  have hmul : 256 * (n / 256) ≤ 256 * (2 ^ 248 - 1) :=
    Nat.mul_le_mul_left 256 (Nat.le_pred_of_lt hq)
  norm_num [UInt256.size] at hmul ⊢
  omega

theorem packedSetTrueWord_eq (w : UInt256) :
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
    simp [UInt256.size]
  have hland_lt : Nat.land w.toNat (2 ^ 256 - 2 ^ 8) < UInt256.size := by
    rw [natLandClearLow8 w.toNat hwlt]
    exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hland_lt]
  rw [natLandClearLow8 w.toNat hwlt]
  rw [show 256 = 2 ^ 8 by norm_num]
  rw [Nat.mul_comm (2 ^ 8) (w.toNat / 2 ^ 8)]
  rw [natLorShift8One]

theorem packedSetTrueWord_toNat (w : UInt256) :
    (UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩).toNat =
      1 + 256 * (w.toNat / 256) := by
  rw [packedSetTrueWord_eq]
  exact ulit_toNat' _ (packedSetTrueNat_lt_size w.toNat w.val.isLt)

theorem packedSetFalseWord_eq (w : UInt256) :
    UInt256.land w (UInt256.lnot ⟨255⟩) =
      UInt256.ofNat (256 * (w.toNat / 256)) := by
  apply u256_inj
  rw [u256_land_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    simp [UInt256.size]
  rw [natLandClearLow8 w.toNat hwlt]
  have hlt : w.toNat / 2 ^ 8 * 2 ^ 8 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hlt]
  have hlt' : 256 * (w.toNat / 256) < UInt256.size := by
    simpa [Nat.mul_comm] using hlt
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm (w.toNat / 256) 256]
  rw [ulit_toNat' _ hlt']

theorem packedSetFalseWord_toNat (w : UInt256) :
    (UInt256.land w (UInt256.lnot ⟨255⟩)).toNat = 256 * (w.toNat / 256) := by
  rw [packedSetFalseWord_eq]
  have hlt : 256 * (w.toNat / 256) < UInt256.size := by
    have hle : 256 * (w.toNat / 256) ≤ w.toNat :=
      Nat.mul_div_le w.toNat 256
    exact lt_of_le_of_lt hle w.val.isLt
  exact ulit_toNat' _ hlt

theorem storageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord boolOffset0Loc
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
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp [fromBytes']
  rw [packedSetTrueWord_toNat]

theorem storageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩))) := by
  unfold storageLocStore storageLocWriteWord boolOffset0Loc
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1 =
      [0] by
        native_decide]
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp [fromBytes']
  rw [packedSetFalseWord_toNat]

theorem storageLocStore_bool_word_offset0 (evm : EVM.State) (slot word : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (wordToElem .bool word) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) word)) := by
  by_cases hzero : word = ⟨0⟩
  · subst hzero
    have hbool : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by
      native_decide
    simp only [wordToElem, beq_self_eq_true, ↓reduceIte]
    simpa [setBoolOffset0Word, hbool, u256_lor_zero] using
      storageLocStore_bool_false_offset0 evm slot
  · have hbeq : (word.val == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hval
      apply hzero
      apply u256_inj
      simpa [UInt256.toNat] using hval
    have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    simp only [wordToElem, hbeq, Bool.false_eq_true, ↓reduceIte]
    simpa [setBoolOffset0Word, hiszero] using storageLocStore_bool_true_offset0 evm slot

private theorem rbnode_append_toList {α : Type u} (l r : Batteries.RBNode α) :
    (l.append r).toList = l.toList ++ r.toList := by
  fun_induction Batteries.RBNode.append l r <;> simp [List.append_assoc]
  case case3 a1 x1 b1 c y d a x b h ih1 =>
    have hnode : a.toList ++ x :: b.toList = b1.toList ++ c.toList := by
      simpa [h] using ih1
    simpa [List.append_assoc] using congrArg (fun xs => xs ++ (y :: d.toList)) hnode
  case case4 ih1 =>
    rw [ih1, List.append_assoc]
  case case5 a1 x1 b1 c y d a x b h ih1 =>
    have hnode : a.toList ++ x :: b.toList = b1.toList ++ c.toList := by
      simpa [h] using ih1
    simpa [List.append_assoc] using congrArg (fun xs => xs ++ (y :: d.toList)) hnode
  case case6 ih1 =>
    rw [ih1, List.append_assoc]
  case case7 ih1 =>
    rw [ih1]
    simp [List.append_assoc]
  case case8 ih1 =>
    simpa using ih1

private theorem rbnode_mem_of_mem_append {α : Type u} {x : α} {l r : Batteries.RBNode α}
    (h : x ∈ l.append r) : x ∈ l ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [rbnode_append_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_append_of_mem {α : Type u} {x : α} {l r : Batteries.RBNode α}
    (h : x ∈ l ∨ x ∈ r) : x ∈ l.append r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [rbnode_append_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_of_mem_balLeft {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balLeft v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balLeft_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_balLeft_of_mem {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l ∨ x = v ∨ x ∈ r) : x ∈ l.balLeft v r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [Batteries.RBNode.balLeft_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_of_mem_balRight {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l.balRight v r) :
    x ∈ l ∨ x = v ∨ x ∈ r := by
  rw [← Batteries.RBNode.mem_toList] at h
  rw [Batteries.RBNode.balRight_toList] at h
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_balRight_of_mem {α : Type u} {x v : α}
    {l r : Batteries.RBNode α} (h : x ∈ l ∨ x = v ∨ x ∈ r) : x ∈ l.balRight v r := by
  rw [← Batteries.RBNode.mem_toList]
  rw [Batteries.RBNode.balRight_toList]
  simpa [Batteries.RBNode.mem_toList] using h

private theorem rbnode_mem_node_of_left {α : Type u} {x y : α} {c : Batteries.RBColor}
    {a b : Batteries.RBNode α} (h : x ∈ a) : x ∈ Batteries.RBNode.node c a y b := by
  exact Or.inr (Or.inl h)

private theorem rbnode_mem_node_of_right {α : Type u} {x y : α} {c : Batteries.RBColor}
    {a b : Batteries.RBNode α} (h : x ∈ b) : x ∈ Batteries.RBNode.node c a y b := by
  exact Or.inr (Or.inr h)

private theorem rbnode_mem_of_mem_del {α : Type u} {x : α} (cut : α → Ordering) :
    ∀ {t : Batteries.RBNode α}, x ∈ Batteries.RBNode.del cut t → x ∈ t
  | .nil, h => by cases h
  | .node c a y b, h => by
      unfold Batteries.RBNode.del at h
      cases hcut : cut y <;> simp [hcut] at h
      · cases hblack : Batteries.RBNode.isBlack a <;> simp [hblack] at h
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with hdel | hb
            · exact rbnode_mem_node_of_left (rbnode_mem_of_mem_del cut hdel)
            · exact rbnode_mem_node_of_right hb
        · rcases rbnode_mem_of_mem_balLeft h with hdel | hrest
          · exact rbnode_mem_node_of_left (rbnode_mem_of_mem_del cut hdel)
          · rcases hrest with hy | hb
            · exact Or.inl hy
            · exact rbnode_mem_node_of_right hb
      · rcases rbnode_mem_of_mem_append h with ha | hb
        · exact rbnode_mem_node_of_left ha
        · exact rbnode_mem_node_of_right hb
      · cases hblack : Batteries.RBNode.isBlack b <;> simp [hblack] at h
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hdel
            · exact rbnode_mem_node_of_left ha
            · exact rbnode_mem_node_of_right (rbnode_mem_of_mem_del cut hdel)
        · rcases rbnode_mem_of_mem_balRight h with ha | hrest
          · exact rbnode_mem_node_of_left ha
          · rcases hrest with hy | hdel
            · exact Or.inl hy
            · exact rbnode_mem_node_of_right (rbnode_mem_of_mem_del cut hdel)

private theorem rbnode_mem_del_of_mem_ne {α : Type u} {x : α} (cut : α → Ordering) :
    ∀ {t : Batteries.RBNode α}, x ∈ t → cut x ≠ .eq → x ∈ Batteries.RBNode.del cut t
  | .nil, h, _ => by cases h
  | .node c a y b, h, hne => by
      unfold Batteries.RBNode.del
      cases hcut : cut y <;> simp
      · cases hblack : Batteries.RBNode.isBlack a <;> simp
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hb
            · exact Or.inr (Or.inl (rbnode_mem_del_of_mem_ne cut ha hne))
            · exact Or.inr (Or.inr hb)
        · rcases h with hy | hrest
          · exact rbnode_mem_balLeft_of_mem (Or.inr (Or.inl hy))
          · rcases hrest with ha | hb
            · exact rbnode_mem_balLeft_of_mem
                (Or.inl (rbnode_mem_del_of_mem_ne cut ha hne))
            · exact rbnode_mem_balLeft_of_mem (Or.inr (Or.inr hb))
      · rcases h with hy | hrest
        · exact False.elim (hne (by simpa [hy] using hcut))
        · rcases hrest with ha | hb
          · exact rbnode_mem_append_of_mem (Or.inl ha)
          · exact rbnode_mem_append_of_mem (Or.inr hb)
      · cases hblack : Batteries.RBNode.isBlack b <;> simp
        · rcases h with hy | hrest
          · exact Or.inl hy
          · rcases hrest with ha | hb
            · exact Or.inr (Or.inl ha)
            · exact Or.inr (Or.inr (rbnode_mem_del_of_mem_ne cut hb hne))
        · rcases h with hy | hrest
          · exact rbnode_mem_balRight_of_mem (Or.inr (Or.inl hy))
          · rcases hrest with ha | hb
            · exact rbnode_mem_balRight_of_mem (Or.inl ha)
            · exact rbnode_mem_balRight_of_mem
                (Or.inr (Or.inr (rbnode_mem_del_of_mem_ne cut hb hne)))

private theorem rbnode_mem_of_mem_erase {α : Type u} {x : α}
    (cut : α → Ordering) {t : Batteries.RBNode α} :
    x ∈ Batteries.RBNode.erase cut t → x ∈ t := by
  intro h
  rw [← Batteries.RBNode.mem_toList] at h
  unfold Batteries.RBNode.erase at h
  rw [Batteries.RBNode.setBlack_toList] at h
  exact rbnode_mem_of_mem_del cut (Batteries.RBNode.mem_toList.1 h)

private theorem rbnode_mem_erase_of_mem_ne {α : Type u} {x : α}
    (cut : α → Ordering) {t : Batteries.RBNode α}
    (h : x ∈ t) (hne : cut x ≠ .eq) : x ∈ Batteries.RBNode.erase cut t := by
  rw [← Batteries.RBNode.mem_toList]
  unfold Batteries.RBNode.erase
  rw [Batteries.RBNode.setBlack_toList]
  exact Batteries.RBNode.mem_toList.2 (rbnode_mem_del_of_mem_ne cut h hne)

private theorem rbmap_mem_toList_of_mem_toList_erase {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {m : Batteries.RBMap α β cmp} {write : α} {pair : α × β}
    (h : pair ∈ (m.erase write).toList) : pair ∈ m.toList := by
  have hnode : pair ∈ (m.erase write).1 := Batteries.RBMap.mem_toList.1 h
  have hmnode : pair ∈ m.1 := by
    unfold Batteries.RBMap.erase Batteries.RBSet.erase at hnode
    exact rbnode_mem_of_mem_erase (fun pair : α × β => cmp write pair.1) hnode
  exact Batteries.RBMap.mem_toList.2 hmnode

private theorem rbmap_mem_toList_erase_of_mem_toList_ne {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {m : Batteries.RBMap α β cmp} {write : α} {pair : α × β}
    (h : pair ∈ m.toList) (hne : cmp write pair.1 ≠ .eq) : pair ∈ (m.erase write).toList := by
  have hnode : pair ∈ m.1 := Batteries.RBMap.mem_toList.1 h
  have heraseNode : pair ∈ (m.erase write).1 := by
    unfold Batteries.RBMap.erase Batteries.RBSet.erase
    exact rbnode_mem_erase_of_mem_ne (fun pair : α × β => cmp write pair.1) hnode hne
  exact Batteries.RBMap.mem_toList.2 heraseNode

/-- The generic RBMap lemma missing from `Batteries`: erasing one key preserves lookup at a
    different key. -/
theorem rbmap_find?_erase_ne {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : Batteries.RBMap α β cmp) (read write : α) (hne : read ≠ write) :
    (m.erase write).find? read = m.find? read := by
  cases hold : m.find? read with
  | none =>
      cases hnew : (m.erase write).find? read with
      | none => rfl
      | some v =>
          have holdSome : m.find? read = some v := by
            obtain ⟨y, hyErase, hcmp⟩ := (Batteries.RBMap.find?_some).1 hnew
            exact (Batteries.RBMap.find?_some).2
              ⟨y, rbmap_mem_toList_of_mem_toList_erase hyErase, hcmp⟩
          rw [hold] at holdSome
          cases holdSome
  | some v =>
      have hnewSome : (m.erase write).find? read = some v := by
        obtain ⟨y, hy, hcmp⟩ := (Batteries.RBMap.find?_some).1 hold
        have hcut : cmp write y ≠ .eq := by
          intro hwrite
          have hyEq : read = y := Std.LawfulEqCmp.eq_of_compare hcmp
          have hwEq : write = y := Std.LawfulEqCmp.eq_of_compare hwrite
          exact hne (hyEq.trans hwEq.symm)
        exact (Batteries.RBMap.find?_some).2
          ⟨y, rbmap_mem_toList_erase_of_mem_toList_ne hy hcut, hcmp⟩
      cases hnew : (m.erase write).find? read with
      | none =>
          rw [hnew] at hnewSome
          cases hnewSome
      | some v' =>
          have holdFromNew : m.find? read = some v' := by
            obtain ⟨y, hyErase, hcmp⟩ := (Batteries.RBMap.find?_some).1 hnew
            exact (Batteries.RBMap.find?_some).2
              ⟨y, rbmap_mem_toList_of_mem_toList_erase hyErase, hcmp⟩
          rw [hold] at holdFromNew
          cases holdFromNew
          rfl

/-- Erasing a storage word preserves lookup at a different storage slot. -/
theorem storage_findD_erase_ne (storage : Storage) (readSlot writeSlot default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).findD readSlot default =
      storage.findD readSlot default := by
  unfold Batteries.RBMap.findD
  rw [rbmap_find?_erase_ne]
  exact hne

theorem storage_findD_insert_self (storage : Storage) (slot val default : UInt256) :
    (storage.insert slot val).findD slot default = val := by
  unfold Batteries.RBMap.findD
  rw [Batteries.RBMap.find?_insert_of_eq (t := storage) (k := slot) (v := val)
    (k' := slot) Std.ReflCmp.compare_self]
  rfl

/-- Updating a storage slot with EVM/Solidity semantics preserves lookup at a different slot.
    Nonzero writes insert; zero writes erase. -/
theorem storage_findD_update_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).findD
        readSlot default) =
      storage.findD readSlot default := by
  by_cases hzero : (val == default) = true
  · simpa [hzero] using storage_findD_erase_ne storage readSlot writeSlot default hne
  · simpa [hzero] using storage_findD_insert_ne storage readSlot writeSlot val default hne

theorem storage_find?_insert_ne (storage : Storage) (readSlot writeSlot val : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).find? readSlot = storage.find? readSlot := by
  rw [Batteries.RBMap.find?_insert_of_ne]
  intro hcmp
  exact hne (Std.LawfulEqCmp.eq_of_compare hcmp)

theorem storage_find?_erase_ne (storage : Storage) (readSlot writeSlot : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).find? readSlot = storage.find? readSlot :=
  rbmap_find?_erase_ne storage readSlot writeSlot hne

private theorem rbnode_not_memP_del {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut] :
    ∀ {t : Batteries.RBNode α}, Batteries.RBNode.Ordered cmp t →
      ¬ Batteries.RBNode.MemP cut (Batteries.RBNode.del cut t)
  | .nil, _, h => by cases h
  | .node _ a y b, ht, h => by
      unfold Batteries.RBNode.del at h
      rcases ht with ⟨ay, yb, ha, hb⟩
      cases hcut : cut y with
      | lt =>
          cases hblack : Batteries.RBNode.isBlack a <;> simp [hcut, hblack] at h
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases hx with rfl | hdel | hbmem
            · exact nomatch heq.symm.trans hcut
            · exact rbnode_not_memP_del ha (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.lt_trans
                  (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases rbnode_mem_of_mem_balLeft hx with hdel | hrest
            · exact rbnode_not_memP_del ha (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
            · rcases hrest with rfl | hbmem
              · exact nomatch heq.symm.trans hcut
              · exact nomatch heq.symm.trans
                  (Batteries.RBNode.IsCut.lt_trans
                    (Batteries.RBNode.All_def.1 yb _ hbmem).1 hcut)
      | eq =>
          simp [hcut] at h
          rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
          rcases rbnode_mem_of_mem_append hx with hamem | hbmem
          · have hcmp : cmp y x = .gt :=
              Std.OrientedCmp.gt_iff_lt.2 (Batteries.RBNode.All_def.1 ay _ hamem).1
            have hcutx : cut x = .gt := by
              rw [← Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut)
                (x := y) (y := x) hcut]
              exact hcmp
            exact nomatch heq.symm.trans hcutx
          · have hcmp : cmp y x = .lt := (Batteries.RBNode.All_def.1 yb _ hbmem).1
            have hcutx : cut x = .lt := by
              rw [← Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut)
                (x := y) (y := x) hcut]
              exact hcmp
            exact nomatch heq.symm.trans hcutx
      | gt =>
          cases hblack : Batteries.RBNode.isBlack b <;> simp [hcut, hblack] at h
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases hx with rfl | hamem | hdel
            · exact nomatch heq.symm.trans hcut
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.gt_trans
                  (Batteries.RBNode.All_def.1 ay _ hamem).1 hcut)
            · exact rbnode_not_memP_del hb (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)
          · rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
            rcases rbnode_mem_of_mem_balRight hx with hamem | hrest
            · exact nomatch heq.symm.trans
                (Batteries.RBNode.IsCut.gt_trans
                  (Batteries.RBNode.All_def.1 ay _ hamem).1 hcut)
            · rcases hrest with rfl | hdel
              · exact nomatch heq.symm.trans hcut
              · exact rbnode_not_memP_del hb
                  (Batteries.RBNode.memP_def.2 ⟨x, hdel, heq⟩)

private theorem rbnode_not_memP_erase {α : Type u} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    {t : Batteries.RBNode α} (ht : Batteries.RBNode.Ordered cmp t) :
    ¬ Batteries.RBNode.MemP cut (Batteries.RBNode.erase cut t) := by
  intro h
  rcases Batteries.RBNode.memP_def.1 h with ⟨x, hx, heq⟩
  have hxdel : x ∈ Batteries.RBNode.del cut t := by
    rw [← Batteries.RBNode.mem_toList] at hx ⊢
    unfold Batteries.RBNode.erase at hx
    simpa using hx
  exact rbnode_not_memP_del ht (Batteries.RBNode.memP_def.2 ⟨x, hxdel, heq⟩)

private theorem rbmap_find?_erase_self {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Batteries.RBMap α β cmp) (write : α) :
    (m.erase write).find? write = none := by
  cases hfind : (m.erase write).find? write with
  | none => rfl
  | some v =>
      have hsome : ∃ y, (y, v) ∈ (m.erase write).toList ∧ cmp write y = .eq :=
        (Batteries.RBMap.find?_some).1 hfind
      rcases hsome with ⟨y, hymem, hcmp⟩
      have hmemNode : (y, v) ∈ (m.erase write).1 := Batteries.RBMap.mem_toList.1 hymem
      have hno := rbnode_not_memP_erase
        (cmp := Ordering.byKey Prod.fst cmp)
        (cut := Ordering.byKey Prod.fst cmp (write, v))
        (t := m.1) m.2.out.1
      cases hno (Batteries.RBNode.memP_def.2 ⟨(y, v), hmemNode, hcmp⟩)

/-- Erasing a storage slot removes lookup at that same slot. -/
theorem storage_find?_erase_self (storage : Storage) (slot : UInt256) :
    (storage.erase slot).find? slot = none :=
  rbmap_find?_erase_self storage slot

theorem storage_findD_erase_self (storage : Storage) (slot default : UInt256) :
    (storage.erase slot).findD slot default = default := by
  unfold Batteries.RBMap.findD
  rw [storage_find?_erase_self]
  rfl

/-- Updating a storage slot with EVM/Solidity semantics preserves `find?` at a different slot.
    Nonzero writes insert; zero writes erase. -/
theorem storage_find?_update_ne (storage : Storage) (readSlot writeSlot val : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == (default : UInt256) then storage.erase writeSlot
      else storage.insert writeSlot val).find? readSlot) =
      storage.find? readSlot := by
  by_cases hzero : (val == (default : UInt256)) = true
  · simpa [hzero] using storage_find?_erase_ne storage readSlot writeSlot hne
  · simpa [hzero] using storage_find?_insert_ne storage readSlot writeSlot val hne

/-- Lookup-level same-key overwrite for `RBMap.insert`.

The structurally stronger equality of `RBMap`s is false in general, because inserting a missing key
and then overwriting it can recolor the root differently from a single insert.  Lookup equivalence
is the reusable form for simplifying reads after double writes. -/
theorem rbmap_find?_insert_insert_self {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Batteries.RBMap α β cmp) (write read : α) (v1 v2 : β) :
    ((m.insert write v1).insert write v2).find? read =
      (m.insert write v2).find? read := by
  by_cases h : cmp read write = .eq
  · rw [Batteries.RBMap.find?_insert_of_eq (t := m.insert write v1) (k := write)
      (v := v2) (k' := read) h,
      Batteries.RBMap.find?_insert_of_eq (t := m) (k := write) (v := v2) (k' := read) h]
  · rw [Batteries.RBMap.find?_insert_of_ne (t := m.insert write v1) (k := write)
      (v := v2) (k' := read) h,
      Batteries.RBMap.find?_insert_of_ne (t := m) (k := write) (v := v1)
        (k' := read) h,
      Batteries.RBMap.find?_insert_of_ne (t := m) (k := write) (v := v2)
        (k' := read) h]

/-- `findD` version of same-key overwrite for `RBMap.insert`. -/
theorem rbmap_findD_insert_insert_self {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Batteries.RBMap α β cmp) (write read : α) (v1 v2 default : β) :
    ((m.insert write v1).insert write v2).findD read default =
      (m.insert write v2).findD read default := by
  unfold Batteries.RBMap.findD
  rw [rbmap_find?_insert_insert_self]

/-- Storage-slot lookup after two same-slot writes is the same as after the final write. -/
theorem storage_findD_insert_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 default : UInt256) :
    ((storage.insert writeSlot val1).insert writeSlot val2).findD readSlot default =
      (storage.insert writeSlot val2).findD readSlot default :=
  rbmap_findD_insert_insert_self storage writeSlot readSlot val1 val2 default

theorem storage_find?_insert_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    ((storage.insert writeSlot val1).insert writeSlot val2).find? readSlot =
      (storage.insert writeSlot val2).find? readSlot :=
  rbmap_find?_insert_insert_self storage writeSlot readSlot val1 val2

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- Reading after an arbitrary zero-aware storage update followed by a same-slot nonzero insert is
    the same as reading after just the final insert. -/
theorem storage_findD_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).findD readSlot
        (default : UInt256)) =
      (storage.insert writeSlot val2).findD readSlot (default : UInt256) := by
  by_cases hread : readSlot = writeSlot
  · subst readSlot
    unfold Batteries.RBMap.findD
    rw [Batteries.RBMap.find?_insert_of_eq
      (t := if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1)
      (k := writeSlot) (v := val2) (k' := writeSlot) Std.ReflCmp.compare_self]
    rw [Batteries.RBMap.find?_insert_of_eq (t := storage) (k := writeSlot) (v := val2)
      (k' := writeSlot) Std.ReflCmp.compare_self]
  · by_cases hzero : val1 = (default : UInt256)
    · simp only [hzero, if_true]
      rw [storage_findD_insert_ne (storage.erase writeSlot) readSlot writeSlot val2 default hread]
      rw [storage_findD_insert_ne storage readSlot writeSlot val2 default hread]
      rw [storage_findD_erase_ne storage readSlot writeSlot default hread]
    · simp only [hzero, if_false]
      rw [storage_findD_insert_insert_self]

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- `find?` after an arbitrary zero-aware storage update followed by a same-slot nonzero insert is
    the same as `find?` after just the final insert. -/
theorem storage_find?_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).find? readSlot) =
      (storage.insert writeSlot val2).find? readSlot := by
  by_cases hread : readSlot = writeSlot
  · subst readSlot
    rw [Batteries.RBMap.find?_insert_of_eq
      (t := if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1)
      (k := writeSlot) (v := val2) (k' := writeSlot) Std.ReflCmp.compare_self]
    rw [Batteries.RBMap.find?_insert_of_eq (t := storage) (k := writeSlot) (v := val2)
      (k' := writeSlot) Std.ReflCmp.compare_self]
  · by_cases hzero : val1 = (default : UInt256)
    · simp only [hzero, if_true]
      rw [storage_find?_insert_ne (storage.erase writeSlot) readSlot writeSlot val2 hread]
      rw [storage_find?_insert_ne storage readSlot writeSlot val2 hread]
      rw [storage_find?_erase_ne storage readSlot writeSlot hread]
    · simp only [hzero, if_false]
      rw [storage_find?_insert_insert_self]

/-- Account lookup after two same-address writes is the same as after the final write. -/
theorem accountMap_find?_insert_insert_self (σ : AccountMap)
    (write read : AccountAddress) (acc1 acc2 : Account) :
    ((σ.insert write acc1).insert write acc2).find? read =
      (σ.insert write acc2).find? read :=
  rbmap_find?_insert_insert_self σ write read acc1 acc2

/-- Inserting one account preserves lookup at a different address. -/
theorem accountMap_find?_insert_ne (σ : AccountMap) (read write : AccountAddress)
    (acc : Account) (hne : read ≠ write) :
    (σ.insert write acc).find? read = σ.find? read := by
  rw [Batteries.RBMap.find?_insert_of_ne]
  intro hcmp
  exact hne (Std.LawfulEqCmp.eq_of_compare hcmp)

/-- Looking up the account just inserted at its own address returns that account. -/
theorem accountMap_find_insert_self (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.insert a acc).find? a = some acc := by
  rw [Batteries.RBMap.find?_insert_of_eq]
  exact Std.ReflCmp.compare_self

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- A zero-aware `SSTORE` to one storage slot preserves an observable read from a different slot
    of the same account. -/
theorem sstoreAccountMap_storage_findD_ne (σ : AccountMap) (a : AccountAddress)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    (((sstoreAccountMap a σ writeSlot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      ((σ.find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) := by
  unfold sstoreAccountMap
  cases hσ : σ.find? a with
  | none =>
      simp [hσ, Option.option]
  | some acc =>
      simp [Option.option, accountMap_find_insert_self]
      by_cases hzero : val = (default : UInt256)
      · simpa [hzero] using storage_findD_update_ne acc.storage readSlot writeSlot val default hne
      · simpa [hzero] using storage_findD_update_ne acc.storage readSlot writeSlot val default hne

/-- Zero-aware `SSTORE` readback for the writing account, with the slot collision case exposed in
the result instead of assumed away.  If the account is absent, `sstoreAccountMap` is a no-op, so the
colliding read still returns the default word. -/
theorem sstoreAccountMap_storage_findD_eq_if (σ : AccountMap) (a : AccountAddress)
    (readSlot writeSlot val : UInt256) :
    (((sstoreAccountMap a σ writeSlot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      if readSlot = writeSlot then
        ((σ.find? a).option (default : UInt256) (fun _ => val))
      else
        ((σ.find? a).option (default : UInt256)
          (fun acc => acc.storage.findD readSlot (default : UInt256))) := by
  by_cases hslot : readSlot = writeSlot
  · subst readSlot
    unfold sstoreAccountMap
    cases hσ : σ.find? a with
    | none =>
        simp [hσ, Option.option]
    | some acc =>
        simp [Option.option, accountMap_find_insert_self]
        by_cases hzero : val = (default : UInt256)
        · subst val
          simpa using storage_findD_erase_self acc.storage writeSlot (default : UInt256)
        · simpa [hzero] using
            storage_findD_insert_self acc.storage writeSlot val (default : UInt256)
  · simp [hslot, sstoreAccountMap_storage_findD_ne σ a readSlot writeSlot val hslot]

theorem sstoreAccountMap_storage_findD_eq_if_of_before
    {σ : AccountMap} {a : AccountAddress} {readSlot writeSlot val word : UInt256}
    (hword :
      ((σ.find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) = word) :
    (((sstoreAccountMap a σ writeSlot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      if readSlot = writeSlot then
        ((σ.find? a).option (default : UInt256) (fun _ => val))
      else
        word := by
  rw [sstoreAccountMap_storage_findD_eq_if, hword]

theorem sstoreAccountMap_storage_findD_eq_of_before_of_ne
    {σ : AccountMap} {a : AccountAddress} {readSlot writeSlot val word : UInt256}
    (hne : readSlot ≠ writeSlot)
    (hword :
      ((σ.find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) = word) :
    (((sstoreAccountMap a σ writeSlot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) = word := by
  rw [sstoreAccountMap_storage_findD_eq_if_of_before hword]
  exact if_neg hne

theorem sstoreAccountMap_storage_findD_self_of_find_some
    (σ : AccountMap) (a : AccountAddress) (acc : Account) (slot val : UInt256)
    (hacc : σ.find? a = some acc) (hval : (val == (default : UInt256)) = false) :
    (((sstoreAccountMap a σ slot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256))) = val := by
  unfold sstoreAccountMap
  simp [hacc, Option.option, hval, accountMap_find_insert_self]
  exact storage_findD_insert_self acc.storage slot val (default : UInt256)

theorem sstoreAccountMap_storage_findD_self_of_find_some_any
    (σ : AccountMap) (a : AccountAddress) (acc : Account) (slot val : UInt256)
    (hacc : σ.find? a = some acc) :
    (((sstoreAccountMap a σ slot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256))) = val := by
  unfold sstoreAccountMap
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    simp [hacc, Option.option, accountMap_find_insert_self, hval,
      storage_findD_erase_self]
  · simp [hacc, Option.option, hzero, accountMap_find_insert_self]
    exact storage_findD_insert_self acc.storage slot val (default : UInt256)

theorem accountEquiv_refl (acc : Account) : accountEquiv acc acc := by
  exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem accountMapEquiv_refl (σ : AccountMap) : accountMapEquiv σ σ := by
  intro addr
  cases σ.find? addr <;> simp [accountEquiv_refl]

theorem accountMapEquiv_find?_some_exists {σ τ : AccountMap} {addr : AccountAddress}
    (hστ : accountMapEquiv σ τ) {acc : Account}
    (hfind : σ.find? addr = some acc) :
    ∃ acc', τ.find? addr = some acc' := by
  specialize hστ addr
  rw [hfind] at hστ
  cases hτ : τ.find? addr with
  | none => simp [hτ] at hστ
  | some acc' => exact ⟨acc', rfl⟩

theorem accountMapEquiv_find?_none {σ τ : AccountMap} {addr : AccountAddress}
    (hστ : accountMapEquiv σ τ)
    (hfind : σ.find? addr = none) :
    τ.find? addr = none := by
  specialize hστ addr
  rw [hfind] at hστ
  cases hτ : τ.find? addr with
  | none => rfl
  | some acc => simp [hτ] at hστ

theorem accountEquiv_storage_findD {acc₁ acc₂ : Account} (slot default : UInt256)
    (hacc : accountEquiv acc₁ acc₂) :
    acc₁.storage.findD slot default = acc₂.storage.findD slot default := by
  unfold Batteries.RBMap.findD
  rw [hacc.2.2.2.1 slot]

theorem accountMapEquiv_storage_findD {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) (slot default : UInt256) :
    ((σ.find? addr).option default (fun acc => acc.storage.findD slot default)) =
      ((τ.find? addr).option default (fun acc => acc.storage.findD slot default)) := by
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;> simp [hσ, hτ, Option.option] at hστ ⊢
  exact accountEquiv_storage_findD slot default hστ

/-- Erasing the same persistent storage slot from equivalent accounts preserves equivalence. -/
theorem accountEquiv_erase_storage_of_equiv {acc₁ acc₂ : Account}
    (slot : UInt256) (hacc : accountEquiv acc₁ acc₂) :
    accountEquiv {acc₁ with storage := acc₁.storage.erase slot}
      {acc₂ with storage := acc₂.storage.erase slot} := by
  rcases hacc with ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩
  refine ⟨hnonce, hbalance, hcode, ?_, htstorage⟩
  intro readSlot
  by_cases hread : readSlot = slot
  · subst readSlot
    rw [storage_find?_erase_self, storage_find?_erase_self]
  · rw [storage_find?_erase_ne acc₁.storage readSlot slot hread,
      storage_find?_erase_ne acc₂.storage readSlot slot hread, hstorage readSlot]

theorem storageLoad_accountMapEquiv {evm1 evm2 : EVM.State}
    (hAccounts : accountMapEquiv evm1.accountMap evm2.accountMap)
    (addr : AccountAddress) (slot : UInt256) :
    Solm.EVM.storageLoad evm1 addr slot = Solm.EVM.storageLoad evm2 addr slot := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  exact accountMapEquiv_storage_findD hAccounts addr slot (default : UInt256)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- Inserting the same nonzero storage word into equivalent accounts preserves account
    equivalence. -/
theorem accountEquiv_insert_storage_of_equiv {acc₁ acc₂ : Account} (slot val : UInt256)
    (hacc : accountEquiv acc₁ acc₂) :
    accountEquiv {acc₁ with storage := acc₁.storage.insert slot val}
      {acc₂ with storage := acc₂.storage.insert slot val} := by
  rcases hacc with ⟨hn, hb, hc, hs, ht⟩
  refine ⟨hn, hb, hc, ?_, ht⟩
  intro readSlot
  by_cases hread : readSlot = slot
  · subst readSlot
    rw [Batteries.RBMap.find?_insert_of_eq (t := acc₁.storage) (k := slot) (v := val)
      (k' := slot) Std.ReflCmp.compare_self]
    rw [Batteries.RBMap.find?_insert_of_eq (t := acc₂.storage) (k := slot) (v := val)
      (k' := slot) Std.ReflCmp.compare_self]
  · rw [storage_find?_insert_ne acc₁.storage readSlot slot val hread]
    rw [storage_find?_insert_ne acc₂.storage readSlot slot val hread]
    exact hs readSlot

theorem accountEquiv_update_insert_self (acc : Account) (slot val1 val2 : UInt256) :
    accountEquiv {acc with storage := acc.storage.insert slot val2}
      {acc with storage :=
        (if val1 = (default : UInt256) then acc.storage.erase slot
         else acc.storage.insert slot val1).insert slot val2} := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro readSlot
    exact (storage_find?_update_insert_self acc.storage slot readSlot val1 val2).symm
  · simp

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- `accountMapEquiv` is preserved by the same nonzero `SSTORE` on both maps. -/
theorem accountMapEquiv_sstoreAccountMap_insert {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) (hval : (val == (default : UInt256)) = false) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) := by
  intro addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    specialize hστ a
    cases hσ : σ.find? a with
    | none =>
        cases hτ : τ.find? a with
        | none =>
            simp [hσ, hτ, Option.option]
        | some accτ =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
    | some accσ =>
        cases hτ : τ.find? a with
        | none =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
        | some accτ =>
            have hacc : accountEquiv accσ accτ := by simpa [hσ, hτ] using hστ
            simpa [hσ, hτ, Option.option, hval, accountMap_find_insert_self] using
              accountEquiv_insert_storage_of_equiv slot val hacc
  · unfold sstoreAccountMap
    specialize hστ addr
    cases hσa : σ.find? a <;> cases hτa : τ.find? a <;>
      simp only [Option.option]
    · exact hστ
    · rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- `accountMapEquiv` is preserved by the same zero `SSTORE` on both maps. -/
theorem accountMapEquiv_sstoreAccountMap_erase {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) (hval : (val == (default : UInt256)) = true) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) := by
  intro addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    specialize hστ a
    cases hσ : σ.find? a with
    | none =>
        cases hτ : τ.find? a with
        | none =>
            simp [hσ, hτ, Option.option]
        | some accτ =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
    | some accσ =>
        cases hτ : τ.find? a with
        | none =>
            have hbad : False := by
              simp [hσ, hτ] at hστ
            exact False.elim hbad
        | some accτ =>
            have hacc : accountEquiv accσ accτ := by simpa [hσ, hτ] using hστ
            simpa [hσ, hτ, Option.option, hval, accountMap_find_insert_self] using
              accountEquiv_erase_storage_of_equiv (acc₁ := accσ) (acc₂ := accτ) slot hacc
  · unfold sstoreAccountMap
    specialize hστ addr
    cases hσa : σ.find? a <;> cases hτa : τ.find? a <;>
      simp only [Option.option]
    · exact hστ
    · rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      exact hστ
    · rw [accountMap_find?_insert_ne σ addr a _ haddr]
      rw [accountMap_find?_insert_ne τ addr a _ haddr]
      exact hστ

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- `accountMapEquiv` is preserved by the same zero-aware `SSTORE` on both maps. -/
theorem accountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) := by
  by_cases hval : (val == (default : UInt256)) = true
  · exact accountMapEquiv_sstoreAccountMap_erase a slot val hστ hval
  · have hfalse : (val == (default : UInt256)) = false := by
      cases h : (val == (default : UInt256)) <;> simp [h] at hval ⊢
    exact accountMapEquiv_sstoreAccountMap_insert a slot val hστ hfalse

theorem accountMapEquiv_sstoreAccountMap_storage_findD {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (a : AccountAddress)
    (readSlot writeSlot val default : UInt256) :
    (((sstoreAccountMap a σ writeSlot val).find? a).option default
        (fun acc => acc.storage.findD readSlot default)) =
      (((sstoreAccountMap a τ writeSlot val).find? a).option default
        (fun acc => acc.storage.findD readSlot default)) := by
  exact accountMapEquiv_storage_findD
    (accountMapEquiv_sstoreAccountMap a writeSlot val hστ) a readSlot default

theorem sstoreAccountMap_absent_same {owner : AccountAddress} {τ : AccountMap}
    {slot val : UInt256} (hmissing : τ.find? owner = none) :
    sstoreAccountMap owner τ slot val = τ := by
  unfold sstoreAccountMap
  rw [hmissing]
  rfl

theorem storageStore_accountMapEquiv {evm1 evm2 : EVM.State}
    (hAccounts : accountMapEquiv evm1.accountMap evm2.accountMap)
    (addr : AccountAddress) (slot val : UInt256) :
    accountMapEquiv (Solm.EVM.storageStore evm1 addr slot val).accountMap
      (Solm.EVM.storageStore evm2 addr slot val).accountMap := by
  simp [storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap addr slot val hAccounts

theorem accountMapEquiv_storageStore_of_accountMapEquiv {evm : EVM.State}
    {σ : AccountMap} (hAccounts : accountMapEquiv σ evm.accountMap)
    (addr : AccountAddress) (slot val : UInt256) :
    accountMapEquiv (sstoreAccountMap addr σ slot val)
      (Solm.EVM.storageStore evm addr slot val).accountMap := by
  simp [storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap addr slot val hAccounts

theorem accountMapEquiv_storageStore_two_of_accountMapEquiv {evm : EVM.State}
    {σ : AccountMap} (hAccounts : accountMapEquiv σ evm.accountMap)
    (addr₁ addr₂ : AccountAddress) (slot₁ val₁ slot₂ val₂ : UInt256) :
    accountMapEquiv
      (sstoreAccountMap addr₂ (sstoreAccountMap addr₁ σ slot₁ val₁) slot₂ val₂)
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm addr₁ slot₁ val₁)
        addr₂ slot₂ val₂).accountMap := by
  simp [storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap addr₂ slot₂ val₂
    (accountMapEquiv_sstoreAccountMap addr₁ slot₁ val₁ hAccounts)

theorem storageStore_executionEnv (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_absent (evm : EVM.State) (addr : AccountAddress)
    (hmissing : evm.accountMap.find? addr = none) (slot val : UInt256) :
    Solm.EVM.storageStore evm addr slot val = evm := by
  simp [Solm.EVM.storageStore, State.lookupAccount, hmissing, Option.option]

theorem storageLoad_initState_codeOwner_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (slot : UInt256) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD slot ⟨0⟩)) := by
  have hword :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot (⟨0⟩ : UInt256)
  simpa [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage] using
    hword.symm

theorem accountMapEquiv_storageStore_initState_codeOwner
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (slot val : UInt256) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm slot val)
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot val).accountMap := by
  simp [initState, storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner slot val hAccounts

theorem accountMapEquiv_storageStore_initState_codeOwner_two
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (slot1 val1 slot2 val2 : UInt256) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm slot1 val1) slot2 val2)
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          I.codeOwner slot1 val1)
        I.codeOwner slot2 val2).accountMap := by
  simp [initState, storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner slot2 val2
    (accountMapEquiv_sstoreAccountMap I.codeOwner slot1 val1 hAccounts)

theorem storageLocStore_oneByte_absent_same
    {evm : EVM.State} {slot : UInt256} {off : Fin 32} {byte : UInt8}
    {typ : ABI.ElemType} {hbound : off.val + (1 : Fin 33).val - 1 < 32}
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    storageLocStore evm
      { slot := slot, offset := off, size := 1, hbound := hbound, type := typ }
      (.int byte.toNat) = some evm := by
  unfold storageLocStore
  simp [storageLocWriteWord, valueToWord,
    storageStore_absent evm evm.executionEnv.codeOwner hmissing]

theorem writeSolidityBytesDataWordsFrom_absent_same :
    ∀ {evm : EVM.State} {baseSlot : UInt256} {value : ByteArray} {idx fuel : Nat},
      evm.accountMap.find? evm.executionEnv.codeOwner = none →
      writeSolidityBytesDataWordsFrom evm baseSlot value idx fuel = evm
  | evm, baseSlot, value, idx, 0, _hmissing => rfl
  | evm, baseSlot, value, idx, fuel + 1, hmissing => by
      simp [writeSolidityBytesDataWordsFrom,
        storageStore_absent evm evm.executionEnv.codeOwner hmissing]
      exact writeSolidityBytesDataWordsFrom_absent_same
        (evm := evm) (baseSlot := baseSlot) (value := value) (idx := idx + 1)
        (fuel := fuel) hmissing

def solidityDataWordsForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (baseSlot : UInt256) (bytes : ByteArray) (idx : Nat) : Nat → AccountMap
  | 0 => τ
  | n + 1 =>
      solidityDataWordsForwardFrom owner
        (sstoreAccountMap owner τ (solidityBytesDataSlot baseSlot idx)
          (uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)))
        baseSlot bytes (idx + 1) n

def accountStorageWord (σ : AccountMap) (owner : AccountAddress) (slot : UInt256) : UInt256 :=
  (σ.find? owner).option (default : UInt256)
    (fun acc => acc.storage.findD slot (default : UInt256))

theorem accountStorageWord_eq_storageLoad_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {owner : AccountAddress} {slot : UInt256}
    (howner : evm.executionEnv.codeOwner = owner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountStorageWord σ owner slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  have hword :
      accountStorageWord σ owner slot = accountStorageWord evm.accountMap owner slot :=
    accountMapEquiv_storage_findD hAccounts owner slot (default : UInt256)
  have hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
        accountStorageWord evm.accountMap owner slot := by
    rw [howner]
    rfl
  exact hword.trans hload.symm

theorem storageLoad_eq_accountStorageWord_of_accountMapEquiv_of_word_eq
    {evm : EVM.State} {σ τ : AccountMap} {owner : AccountAddress} {slot : UInt256}
    (howner : evm.executionEnv.codeOwner = owner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hword : accountStorageWord σ owner slot = accountStorageWord τ owner slot) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      accountStorageWord τ owner slot := by
  exact (accountStorageWord_eq_storageLoad_of_accountMapEquiv howner hAccounts).symm.trans hword

def solidityDataWordAt (bytes : ByteArray) (idx : Nat) : UInt256 :=
  uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)

def solidityDataWordsForwardFromReadback
    (ownerPresent : Bool) (current : UInt256) (readSlot baseSlot : UInt256)
    (bytes : ByteArray) (idx : Nat) : Nat → UInt256
  | 0 => current
  | fuel + 1 =>
      let current' :=
        if readSlot = solidityBytesDataSlot baseSlot idx then
          if ownerPresent then solidityDataWordAt bytes idx else (default : UInt256)
        else
          current
      solidityDataWordsForwardFromReadback ownerPresent current' readSlot baseSlot bytes
        (idx + 1) fuel

theorem option_const_eq_if_isSome {α β : Type} [Inhabited β] (opt : Option α) (val : β) :
    opt.option (default : β) (fun _ => val) = if opt.isSome then val else default := by
  cases opt <;> rfl

theorem sstoreAccountMap_find?_owner_isSome
    (σ : AccountMap) (owner : AccountAddress) (slot val : UInt256) :
    ((sstoreAccountMap owner σ slot val).find? owner).isSome =
      (σ.find? owner).isSome := by
  unfold sstoreAccountMap
  cases hσ : σ.find? owner with
  | none =>
      simp [hσ, Option.option]
  | some acc =>
      simp [Option.option, accountMap_find_insert_self]

theorem sstoreAccountMap_find?_some_exists_of_find_some
    {σ : AccountMap} {a : AccountAddress} {acc : Account} {slot val : UInt256}
    (hacc : σ.find? a = some acc) :
    ∃ acc', (sstoreAccountMap a σ slot val).find? a = some acc' := by
  unfold sstoreAccountMap
  simp [hacc, Option.option, accountMap_find_insert_self]

theorem accountStorageWord_after_sstore_eq_if
    (σ : AccountMap) (owner : AccountAddress) (readSlot writeSlot val : UInt256) :
    accountStorageWord (sstoreAccountMap owner σ writeSlot val) owner readSlot =
      if readSlot = writeSlot then
        if (σ.find? owner).isSome then val else (default : UInt256)
      else
        accountStorageWord σ owner readSlot := by
  rw [accountStorageWord, sstoreAccountMap_storage_findD_eq_if]
  simp [accountStorageWord, option_const_eq_if_isSome]

theorem accountStorageWord_solidityDataWordsForwardFrom_eq_readback
    (σ : AccountMap) (owner : AccountAddress) (readSlot baseSlot : UInt256)
    (bytes : ByteArray) :
    ∀ (idx fuel : Nat),
      accountStorageWord
          (solidityDataWordsForwardFrom owner σ baseSlot bytes idx fuel) owner readSlot =
        solidityDataWordsForwardFromReadback (σ.find? owner).isSome
          (accountStorageWord σ owner readSlot) readSlot baseSlot bytes idx fuel
  | idx, 0 => rfl
  | idx, fuel + 1 => by
      simp [solidityDataWordsForwardFrom]
      rw [accountStorageWord_solidityDataWordsForwardFrom_eq_readback
        (sstoreAccountMap owner σ (solidityBytesDataSlot baseSlot idx)
          (uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)))
        owner readSlot baseSlot bytes (idx + 1) fuel]
      rw [sstoreAccountMap_find?_owner_isSome]
      rw [accountStorageWord_after_sstore_eq_if]
      simp [solidityDataWordAt, solidityDataWordsForwardFromReadback]

theorem solidityDataWordsForwardFromReadback_eq_current_of_ne
    (ownerPresent : Bool) (current readSlot baseSlot : UInt256) (bytes : ByteArray) :
    ∀ (idx fuel : Nat),
      (∀ i, i < fuel → readSlot ≠ solidityBytesDataSlot baseSlot (idx + i)) →
      solidityDataWordsForwardFromReadback ownerPresent current readSlot baseSlot bytes idx fuel =
        current
  | idx, 0, _ => rfl
  | idx, fuel + 1, hne => by
      have hhead : readSlot ≠ solidityBytesDataSlot baseSlot idx := by
        simpa using hne 0 (Nat.zero_lt_succ fuel)
      have htail :
          ∀ i, i < fuel → readSlot ≠ solidityBytesDataSlot baseSlot (idx + 1 + i) := by
        intro i hi
        have h := hne (i + 1) (Nat.succ_lt_succ hi)
        have hidx : idx + (i + 1) = idx + 1 + i := by omega
        simpa [hidx] using h
      simp [solidityDataWordsForwardFromReadback, hhead]
      exact solidityDataWordsForwardFromReadback_eq_current_of_ne ownerPresent current readSlot
        baseSlot bytes (idx + 1) fuel htail

theorem accountStorageWord_solidityDataWordsForwardFrom_eq_of_ne
    (σ : AccountMap) (owner : AccountAddress) (readSlot baseSlot : UInt256)
    (bytes : ByteArray) (idx fuel : Nat)
    (hne : ∀ i, i < fuel → readSlot ≠ solidityBytesDataSlot baseSlot (idx + i)) :
    accountStorageWord
        (solidityDataWordsForwardFrom owner σ baseSlot bytes idx fuel) owner readSlot =
      accountStorageWord σ owner readSlot := by
  rw [accountStorageWord_solidityDataWordsForwardFrom_eq_readback]
  exact solidityDataWordsForwardFromReadback_eq_current_of_ne
    (σ.find? owner).isSome (accountStorageWord σ owner readSlot) readSlot baseSlot bytes
    idx fuel hne

def accountStorageWordsForwardFrom (owner : AccountAddress) (σ : AccountMap)
    (slotAt wordAt : Nat → UInt256) (idx : Nat) : Nat → AccountMap
  | 0 => σ
  | fuel + 1 =>
      accountStorageWordsForwardFrom owner
        (sstoreAccountMap owner σ (slotAt idx) (wordAt idx)) slotAt wordAt (idx + 1) fuel

def accountStorageWriteLoopReadback
    (ownerPresent : Bool) (current readSlot : UInt256)
    (slotAt wordAt : Nat → UInt256) (idx : Nat) : Nat → UInt256
  | 0 => current
  | fuel + 1 =>
      let current' :=
        if readSlot = slotAt idx then
          if ownerPresent then wordAt idx else (default : UInt256)
        else
          current
      accountStorageWriteLoopReadback ownerPresent current' readSlot slotAt wordAt
        (idx + 1) fuel

theorem accountStorageWord_accountStorageWordsForwardFrom_eq_readback
    (σ : AccountMap) (owner : AccountAddress) (readSlot : UInt256)
    (slotAt wordAt : Nat → UInt256) :
    ∀ (idx fuel : Nat),
      accountStorageWord
          (accountStorageWordsForwardFrom owner σ slotAt wordAt idx fuel) owner readSlot =
        accountStorageWriteLoopReadback (σ.find? owner).isSome
          (accountStorageWord σ owner readSlot) readSlot slotAt wordAt idx fuel
  | idx, 0 => rfl
  | idx, fuel + 1 => by
      simp [accountStorageWordsForwardFrom]
      rw [accountStorageWord_accountStorageWordsForwardFrom_eq_readback
        (sstoreAccountMap owner σ (slotAt idx) (wordAt idx)) owner readSlot slotAt wordAt
        (idx + 1) fuel]
      rw [sstoreAccountMap_find?_owner_isSome]
      rw [accountStorageWord_after_sstore_eq_if]
      simp [accountStorageWriteLoopReadback]

theorem accountStorageWriteLoopReadback_eq_current_of_ne
    (ownerPresent : Bool) (current readSlot : UInt256) (slotAt wordAt : Nat → UInt256) :
    ∀ (idx fuel : Nat),
      (∀ i, i < fuel → readSlot ≠ slotAt (idx + i)) →
      accountStorageWriteLoopReadback ownerPresent current readSlot slotAt wordAt idx fuel =
        current
  | idx, 0, _ => rfl
  | idx, fuel + 1, hne => by
      have hhead : readSlot ≠ slotAt idx := by
        simpa using hne 0 (Nat.zero_lt_succ fuel)
      have htail : ∀ i, i < fuel → readSlot ≠ slotAt (idx + 1 + i) := by
        intro i hi
        have h := hne (i + 1) (Nat.succ_lt_succ hi)
        have hidx : idx + (i + 1) = idx + 1 + i := by omega
        simpa [hidx] using h
      simp [accountStorageWriteLoopReadback, hhead]
      exact accountStorageWriteLoopReadback_eq_current_of_ne ownerPresent current readSlot
        slotAt wordAt (idx + 1) fuel htail

theorem accountStorageWord_accountStorageWordsForwardFrom_eq_of_ne
    (σ : AccountMap) (owner : AccountAddress) (readSlot : UInt256)
    (slotAt wordAt : Nat → UInt256) (idx fuel : Nat)
    (hne : ∀ i, i < fuel → readSlot ≠ slotAt (idx + i)) :
    accountStorageWord
        (accountStorageWordsForwardFrom owner σ slotAt wordAt idx fuel) owner readSlot =
      accountStorageWord σ owner readSlot := by
  rw [accountStorageWord_accountStorageWordsForwardFrom_eq_readback]
  exact accountStorageWriteLoopReadback_eq_current_of_ne
    (σ.find? owner).isSome (accountStorageWord σ owner readSlot) readSlot slotAt wordAt
    idx fuel hne

theorem accountStorageWordsForwardFrom_find?_some_exists_of_find_some
    {σ : AccountMap} {owner : AccountAddress} {acc : Account}
    {slotAt wordAt : Nat → UInt256} {idx : Nat}
    (hacc : σ.find? owner = some acc) :
    ∀ fuel, ∃ acc',
      (accountStorageWordsForwardFrom owner σ slotAt wordAt idx fuel).find? owner = some acc'
  | 0 => ⟨acc, by simpa [accountStorageWordsForwardFrom] using hacc⟩
  | fuel + 1 => by
      obtain ⟨acc', hacc'⟩ :=
        sstoreAccountMap_find?_some_exists_of_find_some
          (σ := σ) (a := owner) (acc := acc) (slot := slotAt idx) (val := wordAt idx) hacc
      exact accountStorageWordsForwardFrom_find?_some_exists_of_find_some
        (σ := sstoreAccountMap owner σ (slotAt idx) (wordAt idx)) (owner := owner)
        (acc := acc') (slotAt := slotAt) (wordAt := wordAt) (idx := idx + 1) hacc' fuel

theorem accountStorageWordsForwardFrom_absent_same
    {owner : AccountAddress} {σ : AccountMap} {slotAt wordAt : Nat → UInt256} {idx : Nat}
    (hmissing : σ.find? owner = none) :
    ∀ fuel, accountStorageWordsForwardFrom owner σ slotAt wordAt idx fuel = σ
  | 0 => rfl
  | fuel + 1 => by
      simp [accountStorageWordsForwardFrom]
      rw [sstoreAccountMap_absent_same (owner := owner) (τ := σ)
        (slot := slotAt idx) (val := wordAt idx) hmissing]
      exact accountStorageWordsForwardFrom_absent_same
        (owner := owner) (σ := σ) (slotAt := slotAt) (wordAt := wordAt)
        (idx := idx + 1) hmissing fuel

def accountStorageStatefulWordsForwardFrom (α : Type) (owner : AccountAddress)
    (σ : AccountMap) (slotAt wordAt : α → UInt256) (next : α → α) (state : α) :
    Nat → AccountMap
  | 0 => σ
  | fuel + 1 =>
      accountStorageStatefulWordsForwardFrom α owner
        (sstoreAccountMap owner σ (slotAt state) (wordAt state)) slotAt wordAt next
        (next state) fuel

def accountStorageStatefulLoopState {α : Type} (next : α → α) : α → Nat → α
  | state, 0 => state
  | state, fuel + 1 => accountStorageStatefulLoopState next (next state) fuel

theorem accountStorageStatefulWordsForwardFrom_absent_same
    {α : Type} {owner : AccountAddress} {σ : AccountMap}
    {slotAt wordAt : α → UInt256} {next : α → α} {state : α}
    (hmissing : σ.find? owner = none) :
    ∀ fuel,
      accountStorageStatefulWordsForwardFrom α owner σ slotAt wordAt next state fuel = σ
  | 0 => rfl
  | fuel + 1 => by
      simp [accountStorageStatefulWordsForwardFrom]
      rw [sstoreAccountMap_absent_same (owner := owner) (τ := σ)
        (slot := slotAt state) (val := wordAt state) hmissing]
      exact accountStorageStatefulWordsForwardFrom_absent_same
        (owner := owner) (σ := σ) (slotAt := slotAt) (wordAt := wordAt)
        (next := next) (state := next state) hmissing fuel

theorem accountMapEquiv_accountStorageStatefulWordsForwardFrom
    {α : Type} {owner : AccountAddress} {σ τ : AccountMap}
    {slotAt wordAt : α → UInt256} {next : α → α} {state : α} :
    ∀ fuel, accountMapEquiv σ τ →
      accountMapEquiv
        (accountStorageStatefulWordsForwardFrom α owner σ slotAt wordAt next state fuel)
        (accountStorageStatefulWordsForwardFrom α owner τ slotAt wordAt next state fuel)
  | 0, hAccounts => hAccounts
  | fuel + 1, hAccounts => by
      simp [accountStorageStatefulWordsForwardFrom]
      exact accountMapEquiv_accountStorageStatefulWordsForwardFrom fuel
        (accountMapEquiv_sstoreAccountMap owner (slotAt state) (wordAt state) hAccounts)

theorem accountMapEquiv_sstore_accountStorageStatefulWordsForwardFrom
    {α : Type} {owner : AccountAddress} {σ τ : AccountMap}
    {slotAt wordAt : α → UInt256} {next : α → α} {state : α}
    {slot val : UInt256} {fuel : Nat}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner
        (accountStorageStatefulWordsForwardFrom α owner σ slotAt wordAt next state fuel)
        slot val)
      (sstoreAccountMap owner
        (accountStorageStatefulWordsForwardFrom α owner τ slotAt wordAt next state fuel)
        slot val) := by
  exact accountMapEquiv_sstoreAccountMap owner slot val
    (accountMapEquiv_accountStorageStatefulWordsForwardFrom fuel hAccounts)

theorem accountMapEquiv_sstore_two_accountStorageStatefulWordsForwardFrom
    {α : Type} {owner : AccountAddress} {σ τ : AccountMap}
    {slotAt wordAt : α → UInt256} {next : α → α} {state : α}
    {slot₁ val₁ slot₂ val₂ : UInt256} {fuel : Nat}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner
        (sstoreAccountMap owner
          (accountStorageStatefulWordsForwardFrom α owner σ slotAt wordAt next state fuel)
          slot₁ val₁)
        slot₂ val₂)
      (sstoreAccountMap owner
        (sstoreAccountMap owner
          (accountStorageStatefulWordsForwardFrom α owner τ slotAt wordAt next state fuel)
          slot₁ val₁)
        slot₂ val₂) := by
  exact accountMapEquiv_sstoreAccountMap owner slot₂ val₂
    (accountMapEquiv_sstore_accountStorageStatefulWordsForwardFrom
      (owner := owner) (slot := slot₁) (val := val₁) hAccounts)

theorem accountMapEquiv_accountStorageWordsForwardFrom_stateful
    {α : Type} (owner : AccountAddress) (σ : AccountMap)
    (slotAt₁ wordAt₁ : Nat → UInt256) (slotAt₂ wordAt₂ : α → UInt256)
    (next : α → α) :
    ∀ (idx : Nat) (state : α) (fuel : Nat),
      (∀ i, i < fuel →
        slotAt₁ (idx + i) = slotAt₂ (accountStorageStatefulLoopState next state i)) →
      (∀ i, i < fuel →
        wordAt₁ (idx + i) = wordAt₂ (accountStorageStatefulLoopState next state i)) →
      accountMapEquiv
        (accountStorageWordsForwardFrom owner σ slotAt₁ wordAt₁ idx fuel)
        (accountStorageStatefulWordsForwardFrom α owner σ slotAt₂ wordAt₂ next state fuel)
  | idx, state, 0, _hslot, _hword => accountMapEquiv_refl σ
  | idx, state, fuel + 1, hslot, hword => by
      simp [accountStorageWordsForwardFrom, accountStorageStatefulWordsForwardFrom]
      have hslot0 : slotAt₁ idx = slotAt₂ state := by
        simpa [accountStorageStatefulLoopState] using hslot 0 (Nat.zero_lt_succ fuel)
      have hword0 : wordAt₁ idx = wordAt₂ state := by
        simpa [accountStorageStatefulLoopState] using hword 0 (Nat.zero_lt_succ fuel)
      rw [hslot0, hword0]
      apply accountMapEquiv_accountStorageWordsForwardFrom_stateful
      · intro i hi
        have h := hslot (i + 1) (Nat.succ_lt_succ hi)
        have hidx : idx + (i + 1) = idx + 1 + i := by omega
        simpa [hidx, accountStorageStatefulLoopState] using h
      · intro i hi
        have h := hword (i + 1) (Nat.succ_lt_succ hi)
        have hidx : idx + (i + 1) = idx + 1 + i := by omega
        simpa [hidx, accountStorageStatefulLoopState] using h

theorem writeSolidityBytesDataWordsFrom_executionEnv
    (evm : EVM.State) (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat) :
    (writeSolidityBytesDataWordsFrom evm baseSlot bytes idx fuel).executionEnv =
      evm.executionEnv := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [writeSolidityBytesDataWordsFrom, ih, storageStore_executionEnv]

theorem writeSolidityBytesDataWordsFrom_createdAccounts
    (evm : EVM.State) (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat) :
    (writeSolidityBytesDataWordsFrom evm baseSlot bytes idx fuel).createdAccounts =
      evm.createdAccounts := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [writeSolidityBytesDataWordsFrom, ih, storageStore_createdAccounts]

theorem writeSolidityBytesDataWordsFrom_accountMap
    (evm : EVM.State) (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat) :
    (writeSolidityBytesDataWordsFrom evm baseSlot bytes idx fuel).accountMap =
      solidityDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
        baseSlot bytes idx fuel := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [writeSolidityBytesDataWordsFrom, solidityDataWordsForwardFrom,
        storageStore_accountMap, storageStore_executionEnv, ih]

theorem storageStore_writeSolidityBytesDataWordsFrom_accountMap
    (evm : EVM.State) (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom evm baseSlot bytes idx fuel)
        (writeSolidityBytesDataWordsFrom evm baseSlot bytes idx fuel).executionEnv.codeOwner
        headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (solidityDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
          baseSlot bytes idx fuel)
        headerSlot header := by
  simp [writeSolidityBytesDataWordsFrom_accountMap,
    writeSolidityBytesDataWordsFrom_executionEnv, storageStore_accountMap]

theorem storageStore_writeSolidityBytesDataWordsFrom_after_storageStore_accountMap
    (evm : EVM.State) (lenSlot lenVal : UInt256)
    (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
          baseSlot bytes idx fuel)
        evm.executionEnv.codeOwner headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (solidityDataWordsForwardFrom evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap lenSlot lenVal)
          baseSlot bytes idx fuel)
        headerSlot header := by
  simp [writeSolidityBytesDataWordsFrom_accountMap,
    storageStore_accountMap, storageStore_executionEnv]

theorem accountMap_after_lengthStore_writeDataWords_storeHeader
    (evm : EVM.State) (lenSlot lenVal : UInt256)
    (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
          baseSlot bytes idx fuel)
        evm.executionEnv.codeOwner headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (solidityDataWordsForwardFrom evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap lenSlot lenVal)
          baseSlot bytes idx fuel)
        headerSlot header := by
  exact storageStore_writeSolidityBytesDataWordsFrom_after_storageStore_accountMap
    evm lenSlot lenVal baseSlot bytes idx fuel headerSlot header

theorem solidityBytesHeaderWordAfterDataSstore_eq_if
    (σ : AccountMap) (owner : AccountAddress) (baseSlot : UInt256)
    (wordIndex : Nat) (val : UInt256) :
    (((sstoreAccountMap owner σ (solidityBytesDataSlot baseSlot wordIndex) val).find? owner).option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      if baseSlot = solidityBytesDataSlot baseSlot wordIndex then
        ((σ.find? owner).option (default : UInt256) (fun _ => val))
      else
        ((σ.find? owner).option (default : UInt256)
          (fun acc => acc.storage.findD baseSlot (default : UInt256))) := by
  exact sstoreAccountMap_storage_findD_eq_if σ owner baseSlot
    (solidityBytesDataSlot baseSlot wordIndex) val

theorem solidityBytesHeaderWordAfterDataSstore_eq_if_of_before
    {σ : AccountMap} {owner : AccountAddress} {baseSlot val word : UInt256}
    {wordIndex : Nat}
    (hword :
      ((σ.find? owner).option (default : UInt256)
        (fun acc => acc.storage.findD baseSlot (default : UInt256))) = word) :
    (((sstoreAccountMap owner σ (solidityBytesDataSlot baseSlot wordIndex) val).find? owner).option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      if baseSlot = solidityBytesDataSlot baseSlot wordIndex then
        ((σ.find? owner).option (default : UInt256) (fun _ => val))
      else
        word := by
  exact sstoreAccountMap_storage_findD_eq_if_of_before hword

theorem solidityBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
    {σ : AccountMap} {owner : AccountAddress} {baseSlot val word : UInt256}
    {wordIndex : Nat}
    (hne : baseSlot ≠ solidityBytesDataSlot baseSlot wordIndex)
    (hword :
      ((σ.find? owner).option (default : UInt256)
        (fun acc => acc.storage.findD baseSlot (default : UInt256))) = word) :
    (((sstoreAccountMap owner σ (solidityBytesDataSlot baseSlot wordIndex) val).find? owner).option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      word := by
  exact sstoreAccountMap_storage_findD_eq_of_before_of_ne hne hword

theorem solidityDataWordsForwardFrom_append
    (owner : AccountAddress) (τ : AccountMap) (baseSlot : UInt256)
    (bytes : ByteArray) :
    ∀ (idx fuel tail : Nat),
      solidityDataWordsForwardFrom owner τ baseSlot bytes idx (fuel + tail) =
        solidityDataWordsForwardFrom owner
          (solidityDataWordsForwardFrom owner τ baseSlot bytes idx fuel)
          baseSlot bytes (idx + fuel) tail
  | idx, 0, tail => by simp [solidityDataWordsForwardFrom]
  | idx, fuel + 1, tail => by
      simp [solidityDataWordsForwardFrom]
      have ih := solidityDataWordsForwardFrom_append owner
        (sstoreAccountMap owner τ (solidityBytesDataSlot baseSlot idx)
          (uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)))
        baseSlot bytes (idx + 1) fuel tail
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem solidityDataWordsForwardFrom_succ_last
    (owner : AccountAddress) (τ : AccountMap) (baseSlot : UInt256)
    (bytes : ByteArray) (idx fuel : Nat) :
    solidityDataWordsForwardFrom owner τ baseSlot bytes idx (fuel + 1) =
      sstoreAccountMap owner
        (solidityDataWordsForwardFrom owner τ baseSlot bytes idx fuel)
        (solidityBytesDataSlot baseSlot (idx + fuel))
        (uInt256OfByteArray (bytes.readWithPadding ((idx + fuel) * 32) 32)) := by
  have happ := solidityDataWordsForwardFrom_append owner τ baseSlot bytes idx fuel 1
  rw [happ]
  simp [solidityDataWordsForwardFrom]

theorem accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last
    {owner : AccountAddress} {σ τ : AccountMap} {baseSlot slot word : UInt256}
    {bytes : ByteArray} {idx fuel : Nat}
    (hAccounts :
      accountMapEquiv σ (solidityDataWordsForwardFrom owner τ baseSlot bytes idx fuel))
    (hslot : slot = solidityBytesDataSlot baseSlot (idx + fuel))
    (hword : word = uInt256OfByteArray (bytes.readWithPadding ((idx + fuel) * 32) 32)) :
    accountMapEquiv
      (sstoreAccountMap owner σ slot word)
      (solidityDataWordsForwardFrom owner τ baseSlot bytes idx (fuel + 1)) := by
  rw [solidityDataWordsForwardFrom_succ_last]
  simpa [hslot, hword] using accountMapEquiv_sstoreAccountMap owner slot word hAccounts

theorem accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
    {owner : AccountAddress} {σ τ : AccountMap}
    {baseSlot headerSlot header : UInt256} {bytes : ByteArray} {idx fuel : Nat}
    (hAccounts :
      accountMapEquiv σ (solidityDataWordsForwardFrom owner τ baseSlot bytes idx fuel)) :
    accountMapEquiv
      (sstoreAccountMap owner σ headerSlot header)
      (sstoreAccountMap owner
        (solidityDataWordsForwardFrom owner τ baseSlot bytes idx fuel)
        headerSlot header) := by
  exact accountMapEquiv_sstoreAccountMap owner headerSlot header hAccounts

theorem accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom_succ_last
    {owner : AccountAddress} {σ τ : AccountMap}
    {baseSlot slot word headerSlot header : UInt256} {bytes : ByteArray} {idx fuel : Nat}
    (hAccounts :
      accountMapEquiv σ (solidityDataWordsForwardFrom owner τ baseSlot bytes idx fuel))
    (hslot : slot = solidityBytesDataSlot baseSlot (idx + fuel))
    (hword : word = uInt256OfByteArray (bytes.readWithPadding ((idx + fuel) * 32) 32)) :
    accountMapEquiv
      (sstoreAccountMap owner (sstoreAccountMap owner σ slot word) headerSlot header)
      (sstoreAccountMap owner
        (solidityDataWordsForwardFrom owner τ baseSlot bytes idx (fuel + 1))
        headerSlot header) := by
  exact accountMapEquiv_sstoreAccountMap owner headerSlot header
    (accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last hAccounts hslot hword)

theorem solidityBytesDataWordCount_mono {a b : Nat} (h : a ≤ b) :
    solidityBytesDataWordCount a ≤ solidityBytesDataWordCount b := by
  unfold solidityBytesDataWordCount
  exact Nat.div_le_div_right (Nat.add_le_add_right h 31)

theorem solidityBytesDataWordCount_sub_eq_zero_of_le {a b : Nat} (h : a ≤ b) :
    solidityBytesDataWordCount a - solidityBytesDataWordCount b = 0 := by
  exact Nat.sub_eq_zero_of_le (solidityBytesDataWordCount_mono h)

theorem solidityBytesDataWordCount_eq_div_of_mod_zero {n : Nat} (hmod : n % 32 = 0) :
    solidityBytesDataWordCount n = n / 32 := by
  unfold solidityBytesDataWordCount
  have hdiv := Nat.div_add_mod n 32
  omega

theorem solidityBytesDataWordCount_eq_div_succ_of_mod_ne {n : Nat} (hmod : n % 32 ≠ 0) :
    solidityBytesDataWordCount n = n / 32 + 1 := by
  unfold solidityBytesDataWordCount
  have hdiv := Nat.div_add_mod n 32
  have hremLt := Nat.mod_lt n (by decide : 0 < 32)
  have hremPos : 0 < n % 32 := Nat.pos_of_ne_zero hmod
  omega

theorem accountMapEquiv_solidityDataWordsForwardFrom
    {owner : AccountAddress} {τ σ : AccountMap} {baseSlot : UInt256}
    {bytes : ByteArray} {idx : Nat} :
    ∀ fuel,
      accountMapEquiv τ σ →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ baseSlot bytes idx fuel)
        (solidityDataWordsForwardFrom owner σ baseSlot bytes idx fuel)
  | 0, h => by
      simpa [solidityDataWordsForwardFrom] using h
  | fuel + 1, h => by
      have hstore := accountMapEquiv_sstoreAccountMap owner
        (solidityBytesDataSlot baseSlot idx)
        (uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)) h
      simpa [solidityDataWordsForwardFrom] using
        accountMapEquiv_solidityDataWordsForwardFrom (owner := owner)
          (baseSlot := baseSlot) (bytes := bytes) (idx := idx + 1) fuel hstore

theorem solidityDataWordsForwardFrom_find?_some_exists_of_find_some
    {σ : AccountMap} {owner : AccountAddress} {acc : Account}
    {baseSlot : UInt256} {bytes : ByteArray} {idx : Nat}
    (hacc : σ.find? owner = some acc) :
    ∀ fuel, ∃ acc',
      (solidityDataWordsForwardFrom owner σ baseSlot bytes idx fuel).find? owner = some acc'
  | 0 => ⟨acc, by simpa [solidityDataWordsForwardFrom] using hacc⟩
  | fuel + 1 => by
      obtain ⟨acc', hacc'⟩ :=
        sstoreAccountMap_find?_some_exists_of_find_some
          (σ := σ) (a := owner) (acc := acc) (slot := solidityBytesDataSlot baseSlot idx)
          (val := uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)) hacc
      exact solidityDataWordsForwardFrom_find?_some_exists_of_find_some
        (σ := sstoreAccountMap owner σ (solidityBytesDataSlot baseSlot idx)
          (uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)))
        (owner := owner) (acc := acc') (baseSlot := baseSlot) (bytes := bytes)
        (idx := idx + 1) hacc' fuel

def clearDataWordsForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (base idx : UInt256) : Nat → AccountMap
  | 0 => τ
  | n + 1 =>
      clearDataWordsForwardFrom owner
        (sstoreAccountMap owner τ (base + idx) ⟨0⟩) base ((⟨1⟩ : UInt256) + idx) n

def uint256SuccFrom (idx : UInt256) : Nat → UInt256
  | 0 => idx
  | n + 1 => (⟨1⟩ : UInt256) + uint256SuccFrom idx n

theorem uint256SuccFrom_one_add (idx : UInt256) :
    ∀ i, uint256SuccFrom ((⟨1⟩ : UInt256) + idx) i = uint256SuccFrom idx (i + 1)
  | 0 => rfl
  | i + 1 => by
      simp [uint256SuccFrom, uint256SuccFrom_one_add idx i]

theorem uint256SuccFrom_add_ofNat (base : UInt256) :
    ∀ i j, uint256SuccFrom (base + UInt256.ofNat i) j = base + UInt256.ofNat (i + j)
  | i, 0 => by simp [uint256SuccFrom]
  | i, j + 1 => by
      rw [uint256SuccFrom, uint256SuccFrom_add_ofNat base i j]
      rw [u256_add_comm (⟨1⟩ : UInt256) (base + UInt256.ofNat (i + j))]
      rw [u256_add_assoc base (UInt256.ofNat (i + j)) (⟨1⟩ : UInt256)]
      rw [u256_add_comm (UInt256.ofNat (i + j)) (⟨1⟩ : UInt256)]
      rw [u256_one_add_ofNat]
      congr 1

def accountStorageSuccessiveWordsForwardFrom
    (α : Type) (owner : AccountAddress) (σ : AccountMap)
    (slot : UInt256) (state : α) (wordAt : α → Nat → UInt256)
    (next : α → α) : Nat → AccountMap
  | 0 => σ
  | fuel + 1 =>
      accountStorageSuccessiveWordsForwardFrom α owner
        (sstoreAccountMap owner σ slot (wordAt state 0))
        ((⟨1⟩ : UInt256) + slot) (next state) wordAt next fuel

theorem accountStorageWordsForwardFrom_ext
    (owner : AccountAddress) (σ : AccountMap)
    (slotAt₁ wordAt₁ slotAt₂ wordAt₂ : Nat → UInt256) :
    ∀ (idx₁ idx₂ fuel : Nat),
      (∀ i, i < fuel → slotAt₁ (idx₁ + i) = slotAt₂ (idx₂ + i)) →
      (∀ i, i < fuel → wordAt₁ (idx₁ + i) = wordAt₂ (idx₂ + i)) →
      accountStorageWordsForwardFrom owner σ slotAt₁ wordAt₁ idx₁ fuel =
        accountStorageWordsForwardFrom owner σ slotAt₂ wordAt₂ idx₂ fuel
  | idx₁, idx₂, 0, _, _ => rfl
  | idx₁, idx₂, fuel + 1, hslot, hword => by
      simp [accountStorageWordsForwardFrom]
      have hslot0 : slotAt₁ idx₁ = slotAt₂ idx₂ := by
        simpa using hslot 0 (Nat.zero_lt_succ fuel)
      have hword0 : wordAt₁ idx₁ = wordAt₂ idx₂ := by
        simpa using hword 0 (Nat.zero_lt_succ fuel)
      rw [hslot0, hword0]
      apply accountStorageWordsForwardFrom_ext
      · intro i hi
        have h := hslot (i + 1) (Nat.succ_lt_succ hi)
        have hidx₁ : idx₁ + (i + 1) = idx₁ + 1 + i := by omega
        have hidx₂ : idx₂ + (i + 1) = idx₂ + 1 + i := by omega
        simpa [hidx₁, hidx₂] using h
      · intro i hi
        have h := hword (i + 1) (Nat.succ_lt_succ hi)
        have hidx₁ : idx₁ + (i + 1) = idx₁ + 1 + i := by omega
        have hidx₂ : idx₂ + (i + 1) = idx₂ + 1 + i := by omega
        simpa [hidx₁, hidx₂] using h

theorem accountStorageSuccessiveWordsForwardFrom_eq_accountStorageWordsForwardFrom
    {α : Type} (owner : AccountAddress) (σ : AccountMap)
    (slot : UInt256) (state : α) (wordAt : α → Nat → UInt256) (next : α → α)
    (hwordSucc : ∀ state i, wordAt (next state) i = wordAt state (i + 1)) :
    ∀ fuel,
      accountStorageSuccessiveWordsForwardFrom α owner σ slot state wordAt next fuel =
        accountStorageWordsForwardFrom owner σ
          (fun i => uint256SuccFrom slot i) (fun i => wordAt state i) 0 fuel
  | 0 => rfl
  | fuel + 1 => by
      simp [accountStorageSuccessiveWordsForwardFrom, accountStorageWordsForwardFrom,
        uint256SuccFrom]
      rw [accountStorageSuccessiveWordsForwardFrom_eq_accountStorageWordsForwardFrom
        owner
        (sstoreAccountMap owner σ slot (wordAt state 0))
        ((⟨1⟩ : UInt256) + slot) (next state) wordAt next hwordSucc fuel]
      apply accountStorageWordsForwardFrom_ext
      · intro i hi
        have hnat : i + 1 = 1 + i := by omega
        simp [uint256SuccFrom_one_add, hnat]
      · intro i hi
        simpa [Nat.add_comm] using hwordSucc state i

theorem solidityDataWordsForwardFrom_eq_accountStorageWordsForwardFrom
    (owner : AccountAddress) (σ : AccountMap) (baseSlot : UInt256) (bytes : ByteArray) :
    ∀ idx fuel,
      solidityDataWordsForwardFrom owner σ baseSlot bytes idx fuel =
        accountStorageWordsForwardFrom owner σ
          (fun i => solidityBytesDataSlot baseSlot i) (fun i => solidityDataWordAt bytes i)
          idx fuel
  | idx, 0 => rfl
  | idx, fuel + 1 => by
      simp [solidityDataWordsForwardFrom, accountStorageWordsForwardFrom, solidityDataWordAt]
      exact solidityDataWordsForwardFrom_eq_accountStorageWordsForwardFrom owner
        (sstoreAccountMap owner σ (solidityBytesDataSlot baseSlot idx)
          (uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)))
        baseSlot bytes (idx + 1) fuel

theorem accountMapEquiv_solidityDataWordsForwardFrom_accountStorageWordsForwardFrom
    (owner : AccountAddress) (σ : AccountMap) (baseSlot : UInt256) (bytes : ByteArray)
    (slotAt wordAt : Nat → UInt256) :
    ∀ (idx₁ idx₂ fuel : Nat),
      (∀ i, i < fuel → solidityBytesDataSlot baseSlot (idx₁ + i) = slotAt (idx₂ + i)) →
      (∀ i, i < fuel → solidityDataWordAt bytes (idx₁ + i) = wordAt (idx₂ + i)) →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner σ baseSlot bytes idx₁ fuel)
        (accountStorageWordsForwardFrom owner σ slotAt wordAt idx₂ fuel)
  | idx₁, idx₂, fuel, hslot, hword => by
      rw [solidityDataWordsForwardFrom_eq_accountStorageWordsForwardFrom]
      have hEq := accountStorageWordsForwardFrom_ext owner σ
        (fun i => solidityBytesDataSlot baseSlot i) (fun i => solidityDataWordAt bytes i)
        slotAt wordAt idx₁ idx₂ fuel hslot hword
      rw [hEq]
      exact accountMapEquiv_refl _

theorem clearDataWordsForwardFrom_eq_accountStorageWordsForwardFrom
    (owner : AccountAddress) (σ : AccountMap) (base idx : UInt256) :
    ∀ fuel,
      clearDataWordsForwardFrom owner σ base idx fuel =
        accountStorageWordsForwardFrom owner σ
          (fun i => base + uint256SuccFrom idx i) (fun _ => (⟨0⟩ : UInt256)) 0 fuel
  | 0 => rfl
  | fuel + 1 => by
      simp [clearDataWordsForwardFrom, accountStorageWordsForwardFrom, uint256SuccFrom]
      rw [clearDataWordsForwardFrom_eq_accountStorageWordsForwardFrom owner
        (sstoreAccountMap owner σ (base + idx) ⟨0⟩) base ((⟨1⟩ : UInt256) + idx) fuel]
      apply accountStorageWordsForwardFrom_ext
      · intro i hi
        have hnat : i + 1 = 1 + i := by omega
        simp [uint256SuccFrom_one_add, hnat]
      · intro i hi
        rfl

theorem accountStorageWord_clearDataWordsForwardFrom_eq_readback
    (σ : AccountMap) (owner : AccountAddress) (readSlot base idx : UInt256) (fuel : Nat) :
    accountStorageWord (clearDataWordsForwardFrom owner σ base idx fuel) owner readSlot =
      accountStorageWriteLoopReadback (σ.find? owner).isSome
        (accountStorageWord σ owner readSlot) readSlot
        (fun i => base + uint256SuccFrom idx i) (fun _ => (⟨0⟩ : UInt256)) 0 fuel := by
  rw [clearDataWordsForwardFrom_eq_accountStorageWordsForwardFrom]
  exact accountStorageWord_accountStorageWordsForwardFrom_eq_readback σ owner readSlot
    (fun i => base + uint256SuccFrom idx i) (fun _ => (⟨0⟩ : UInt256)) 0 fuel

theorem accountStorageWord_clearDataWordsForwardFrom_eq_of_ne
    (σ : AccountMap) (owner : AccountAddress) (readSlot base idx : UInt256) (fuel : Nat)
    (hne : ∀ i, i < fuel → readSlot ≠ base + uint256SuccFrom idx i) :
    accountStorageWord (clearDataWordsForwardFrom owner σ base idx fuel) owner readSlot =
      accountStorageWord σ owner readSlot := by
  rw [accountStorageWord_clearDataWordsForwardFrom_eq_readback]
  exact accountStorageWriteLoopReadback_eq_current_of_ne
    (σ.find? owner).isSome (accountStorageWord σ owner readSlot) readSlot
    (fun i => base + uint256SuccFrom idx i) (fun _ => (⟨0⟩ : UInt256)) 0 fuel
    (by simpa using hne)

theorem clearDataWordsForwardFrom_find?_some_exists_of_find_some
    {σ : AccountMap} {owner : AccountAddress} {acc : Account}
    {base idx : UInt256}
    (hacc : σ.find? owner = some acc) :
    ∀ fuel, ∃ acc',
      (clearDataWordsForwardFrom owner σ base idx fuel).find? owner = some acc'
  | 0 => ⟨acc, by simpa [clearDataWordsForwardFrom] using hacc⟩
  | fuel + 1 => by
      obtain ⟨acc', hacc'⟩ :=
        sstoreAccountMap_find?_some_exists_of_find_some
          (σ := σ) (a := owner) (acc := acc) (slot := base + idx) (val := ⟨0⟩) hacc
      exact clearDataWordsForwardFrom_find?_some_exists_of_find_some
        (σ := sstoreAccountMap owner σ (base + idx) ⟨0⟩) (owner := owner)
        (acc := acc') (base := base) (idx := (⟨1⟩ : UInt256) + idx) hacc' fuel

theorem clearSolidityBytesDataWordsFrom_executionEnv
    (evm : EVM.State) (baseSlot : UInt256) (idx fuel : Nat) :
    (clearSolidityBytesDataWordsFrom evm baseSlot idx fuel).executionEnv =
      evm.executionEnv := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [clearSolidityBytesDataWordsFrom, ih, storageStore_executionEnv]

theorem clearSolidityBytesDataWordsFrom_createdAccounts
    (evm : EVM.State) (baseSlot : UInt256) (idx fuel : Nat) :
    (clearSolidityBytesDataWordsFrom evm baseSlot idx fuel).createdAccounts =
      evm.createdAccounts := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [clearSolidityBytesDataWordsFrom, ih, storageStore_createdAccounts]

theorem clearSolidityBytesDataWordsFrom_accountMap
    (evm : EVM.State) (baseSlot : UInt256) (idx fuel : Nat) :
    (clearSolidityBytesDataWordsFrom evm baseSlot idx fuel).accountMap =
      clearDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
        (solidityBytesDataBaseSlot baseSlot) (UInt256.ofNat idx) fuel := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [clearSolidityBytesDataWordsFrom, clearDataWordsForwardFrom, solidityBytesDataSlot,
        storageStore_accountMap, storageStore_executionEnv, ih, u256_one_add_ofNat]

theorem storageStore_clear_writeSolidityBytesDataWordsFrom_accountMap
    (evm : EVM.State) (clearBaseSlot : UInt256) (clearIdx clearFuel : Nat)
    (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm clearBaseSlot clearIdx clearFuel)
          baseSlot bytes idx fuel)
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm clearBaseSlot clearIdx clearFuel)
          baseSlot bytes idx fuel).executionEnv.codeOwner
        headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (solidityDataWordsForwardFrom evm.executionEnv.codeOwner
          (clearDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
            (solidityBytesDataBaseSlot clearBaseSlot) (UInt256.ofNat clearIdx) clearFuel)
          baseSlot bytes idx fuel)
        headerSlot header := by
  simp [writeSolidityBytesDataWordsFrom_accountMap,
    writeSolidityBytesDataWordsFrom_executionEnv,
    clearSolidityBytesDataWordsFrom_accountMap,
    clearSolidityBytesDataWordsFrom_executionEnv, storageStore_accountMap]

theorem storageStore_clear_writeSolidityBytesDataWordsFrom_after_storageStore_accountMap
    (evm : EVM.State) (lenSlot lenVal : UInt256)
    (clearBaseSlot : UInt256) (clearIdx clearFuel : Nat)
    (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
            clearBaseSlot clearIdx clearFuel)
          baseSlot bytes idx fuel)
        evm.executionEnv.codeOwner headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (solidityDataWordsForwardFrom evm.executionEnv.codeOwner
          (clearDataWordsForwardFrom evm.executionEnv.codeOwner
            (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap lenSlot lenVal)
            (solidityBytesDataBaseSlot clearBaseSlot) (UInt256.ofNat clearIdx) clearFuel)
          baseSlot bytes idx fuel)
        headerSlot header := by
  simp [writeSolidityBytesDataWordsFrom_accountMap,
    clearSolidityBytesDataWordsFrom_accountMap,
    clearSolidityBytesDataWordsFrom_executionEnv,
    storageStore_accountMap, storageStore_executionEnv]

theorem storageStore_clear_writeSolidityBytesDataWordsFrom_after_storageStore_executionEnv_accountMap
    (evm : EVM.State) (lenSlot lenVal : UInt256)
    (clearBaseSlot : UInt256) (clearIdx clearFuel : Nat)
    (baseSlot : UInt256) (bytes : ByteArray) (idx fuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
            clearBaseSlot clearIdx clearFuel)
          baseSlot bytes idx fuel)
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
            clearBaseSlot clearIdx clearFuel)
          baseSlot bytes idx fuel).executionEnv.codeOwner
        headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (solidityDataWordsForwardFrom evm.executionEnv.codeOwner
          (clearDataWordsForwardFrom evm.executionEnv.codeOwner
            (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap lenSlot lenVal)
            (solidityBytesDataBaseSlot clearBaseSlot) (UInt256.ofNat clearIdx) clearFuel)
          baseSlot bytes idx fuel)
        headerSlot header := by
  simp [writeSolidityBytesDataWordsFrom_accountMap,
    writeSolidityBytesDataWordsFrom_executionEnv,
    clearSolidityBytesDataWordsFrom_accountMap,
    clearSolidityBytesDataWordsFrom_executionEnv,
    storageStore_accountMap, storageStore_executionEnv]

theorem storageStore_clearSolidityBytesDataWordsFrom_after_storageStore_accountMap
    (evm : EVM.State) (lenSlot lenVal : UInt256)
    (clearBaseSlot : UInt256) (clearIdx clearFuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
          clearBaseSlot clearIdx clearFuel)
        evm.executionEnv.codeOwner headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (clearDataWordsForwardFrom evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap lenSlot lenVal)
          (solidityBytesDataBaseSlot clearBaseSlot) (UInt256.ofNat clearIdx) clearFuel)
        headerSlot header := by
  simp [clearSolidityBytesDataWordsFrom_accountMap,
    storageStore_accountMap, storageStore_executionEnv]

theorem storageStore_clearSolidityBytesDataWordsFrom_after_storageStore_executionEnv_accountMap
    (evm : EVM.State) (lenSlot lenVal : UInt256)
    (clearBaseSlot : UInt256) (clearIdx clearFuel : Nat)
    (headerSlot header : UInt256) :
    (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
          clearBaseSlot clearIdx clearFuel)
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner lenSlot lenVal)
          clearBaseSlot clearIdx clearFuel).executionEnv.codeOwner
        headerSlot header).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (clearDataWordsForwardFrom evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap lenSlot lenVal)
          (solidityBytesDataBaseSlot clearBaseSlot) (UInt256.ofNat clearIdx) clearFuel)
        headerSlot header := by
  simp [clearSolidityBytesDataWordsFrom_accountMap,
    clearSolidityBytesDataWordsFrom_executionEnv,
    storageStore_accountMap, storageStore_executionEnv]

theorem accountMapEquiv_clearDataWordsForwardFrom {σ τ : AccountMap}
    (owner : AccountAddress) (base idx : UInt256) :
    ∀ fuel, accountMapEquiv σ τ →
      accountMapEquiv
        (clearDataWordsForwardFrom owner σ base idx fuel)
        (clearDataWordsForwardFrom owner τ base idx fuel)
  | 0, hAccounts => hAccounts
  | n + 1, hAccounts => by
      simp [clearDataWordsForwardFrom]
      exact accountMapEquiv_clearDataWordsForwardFrom owner base ((⟨1⟩ : UInt256) + idx) n
        (accountMapEquiv_sstoreAccountMap owner (base + idx) ⟨0⟩ hAccounts)

theorem accountMapEquiv_storageStore_clearSolidityBytesDataWordsFrom
    {evm : EVM.State} {σ : AccountMap}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (clearBaseSlot : UInt256) (clearIdx clearFuel : Nat)
    (headerSlot header : UInt256) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner
        (clearDataWordsForwardFrom evm.executionEnv.codeOwner σ
          (solidityBytesDataBaseSlot clearBaseSlot) (UInt256.ofNat clearIdx) clearFuel)
        headerSlot header)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm clearBaseSlot clearIdx clearFuel)
        evm.executionEnv.codeOwner headerSlot header).accountMap := by
  simp [clearSolidityBytesDataWordsFrom_accountMap, storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner headerSlot header
    (accountMapEquiv_clearDataWordsForwardFrom evm.executionEnv.codeOwner
      (solidityBytesDataBaseSlot clearBaseSlot) (UInt256.ofNat clearIdx) clearFuel hAccounts)

theorem accountMapEquiv_clearDataWordsForwardFrom_shift_base_offset
    {owner : AccountAddress} {σ τ : AccountMap} (base offset idx : UInt256) :
    ∀ fuel, accountMapEquiv σ τ →
      accountMapEquiv
        (clearDataWordsForwardFrom owner σ (base + offset) idx fuel)
        (clearDataWordsForwardFrom owner τ base (offset + idx) fuel)
  | 0, hAccounts => by
      simpa [clearDataWordsForwardFrom] using hAccounts
  | fuel + 1, hAccounts => by
      simp [clearDataWordsForwardFrom]
      have hslot : (base + offset) + idx = base + (offset + idx) := by
        exact u256_add_assoc base offset idx
      have hstep := accountMapEquiv_sstoreAccountMap owner
        (base + (offset + idx)) (⟨0⟩ : UInt256) hAccounts
      have htail := accountMapEquiv_clearDataWordsForwardFrom_shift_base_offset
        (owner := owner)
        (σ := sstoreAccountMap owner σ ((base + offset) + idx) ⟨0⟩)
        (τ := sstoreAccountMap owner τ (base + (offset + idx)) ⟨0⟩)
        base offset ((⟨1⟩ : UInt256) + idx) fuel
        (by simpa [hslot] using hstep)
      have hidx :
          offset + ((⟨1⟩ : UInt256) + idx) =
            (⟨1⟩ : UInt256) + (offset + idx) := by
        rw [u256_add_comm offset ((⟨1⟩ : UInt256) + idx)]
        rw [u256_add_assoc]
        rw [u256_add_comm idx offset]
      simpa [hidx] using htail

theorem solidityBytesBaseSlotAndLength?_ok_of_layout
    {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256} {len : Nat}
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .ok len) :
    solidityBytesBaseSlotAndLength? layout er evm = .ok (baseSlot, len) := by
  obtain ⟨loc, hloc, hslot⟩ := hbase
  unfold solidityBytesBaseSlotAndLength?
  rw [hloc]
  simp [hslot, hload, hdecode]

theorem solidityBytesBaseSlotAndLength?_revert_of_layout
    {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256}
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .revert) :
    solidityBytesBaseSlotAndLength? layout er evm = .revert := by
  obtain ⟨loc, hloc, hslot⟩ := hbase
  unfold solidityBytesBaseSlotAndLength?
  rw [hloc]
  simp [hslot, hload, hdecode]

theorem readStorageBytesLength?_ok_of_layout
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256} {len : Nat}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .ok len) :
    readStorageBytesLength? cfg evm er = .ok len := by
  obtain ⟨loc, hloc, hslot⟩ := hbase
  simp [readStorageBytesLength?, hcfg, solidityStorageLayout, solidityReadBytesLength?,
    storageNatResultToEval, hloc, hslot, hload, hdecode]

theorem readStorageBytesLength?_revert_of_layout
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .revert) :
    readStorageBytesLength? cfg evm er = .revert := by
  obtain ⟨loc, hloc, hslot⟩ := hbase
  simp [readStorageBytesLength?, hcfg, solidityStorageLayout, solidityReadBytesLength?,
    storageNatResultToEval, hloc, hslot, hload, hdecode]

theorem readStorageBytesLength?_ok_of_header_load
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256} {len : Nat}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .ok len) :
    readStorageBytesLength? cfg evm er = .ok len := by
  exact readStorageBytesLength?_ok_of_layout hcfg hbase hload hdecode

theorem readStorageBytesLength?_revert_of_header_load
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .revert) :
    readStorageBytesLength? cfg evm er = .revert := by
  exact readStorageBytesLength?_revert_of_layout hcfg hbase hload hdecode

theorem solidityDecodeBytesLengthHeader_revert_of_readStorageBytesLength_revert
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hlen : readStorageBytesLength? cfg evm er = .revert) :
    solidityDecodeBytesLengthHeader header = .revert := by
  obtain ⟨loc, hloc, hslot⟩ := hbase
  simp [readStorageBytesLength?, hcfg, solidityStorageLayout, solidityReadBytesLength?,
    storageNatResultToEval, hloc, hslot, hload] at hlen
  cases hdecode : solidityDecodeBytesLengthHeader header <;> simp [hdecode] at hlen
  rfl

theorem assignStorageRef_storage_bytes_ok_of_write
    {cfg : Config} {solm : Frame} {evm evm' : EVM.State}
    {ref : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {value : ByteArray}
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, ty))
    (hwrite : writeStorage? cfg evm er ty (.bytes value) = .ok evm') :
    assignStorageRef? cfg solm evm .storage ref (.bytes value) = .ok (solm, evm') := by
  simp [assignStorageRef?, hresolve, hwrite, EvalResult.bind, bind, pure]

theorem assignStorageRef_storage_bytes_revert_of_write
    {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ref : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {value : ByteArray}
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, ty))
    (hwrite : writeStorage? cfg evm er ty (.bytes value) = .revert) :
    assignStorageRef? cfg solm evm .storage ref (.bytes value) = .revert := by
  simp [assignStorageRef?, hresolve, hwrite, EvalResult.bind, bind, pure]

theorem assignStorageRef_storage_scalar_ok_of_resolve_match_store
    {cfg : Config} {solm : Frame} {evm evm' : EVM.State}
    {ref : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {value : Value}
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, ty))
    (hstore :
      (match cfg.storage.layout er evm with
      | some loc => storageLocStore evm loc value
      | none => none) = some evm')
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True) :
    assignStorageRef? cfg solm evm .storage ref value = .ok (solm, evm') := by
  rw [assignStorageRef?]
  rw [hresolve]
  cases hloc : cfg.storage.layout er evm with
  | none =>
      simp [hloc] at hstore
  | some loc =>
      have hstoreLoc : storageLocStore evm loc value = some evm' := by
        simpa [hloc] using hstore
      cases value <;> simp at hscalar ⊢
      all_goals simp [hloc, hstoreLoc, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem assignStorageRef_storage_revert_of_resolve
    {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ref : StorageRef} {value : Value}
    (hresolve : resolveStorageRef? cfg solm evm ref = .revert) :
    assignStorageRef? cfg solm evm .storage ref value = .revert := by
  rw [assignStorageRef?]
  rw [hresolve]
  cases value <;> rfl

theorem evalExpr_storage_scalar_of_resolve_layout
    {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ref : StorageRef} {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .elem t))
    (hloc : cfg.storage.layout er evm = some loc) :
    evalExpr? cfg solm evm (.storage ref) = .ok (storageLocLoad evm loc) := by
  rw [evalExpr?]
  rw [hresolve]
  simp [readStorage?, hloc, EvalResult.bind, bind]

theorem clearSolidityStringShortZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    clearStorage? cfg evm er .string =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, checkBytesPacked, hload,
    solidityBytesHeaderWord, storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearSolidityStringShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage? cfg evm er .string =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, hpacked, solidityBytesHeaderWord,
    storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearSolidityStringLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage? cfg evm er .string =
      .ok (clearSolidityBytesDataWordsFrom
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
        baseSlot 0 ((len.toNat + 31) / 32)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, hpacked, solidityBytesHeaderWord,
    storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem deleteSolidityStringShortZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hclear := clearSolidityStringShortZero
    (cfg := cfg) (layout := layout) (evm := evm) (er := er) (baseSlot := baseSlot)
    hcfg hbase hload
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem deleteSolidityStringShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hclear := clearSolidityStringShortPacked
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hpacked hflag hlen hvalid
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem deleteSolidityStringLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (clearSolidityBytesDataWordsFrom
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
        baseSlot 0 ((len.toNat + 31) / 32)) := by
  have hclear := clearSolidityStringLongPrepared
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem writeSolidityStringShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot
        (solidityShortBytesWord value)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize]

theorem writeSolidityStringShortFromLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm baseSlot 0
          ((len.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom evm baseSlot 0
          ((len.toNat + 31) / 32)).executionEnv.codeOwner
        baseSlot (solidityShortBytesWord value)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityStringLongPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityStringLongPackedAbsent
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? cfg evm er .string (.bytes value) = .ok evm := by
  have hwrite := writeSolidityStringLongPacked
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len) (value := value)
    hcfg hbase hvalueSize hload hpacked hflag hlen hvalid
  have hdata :
      writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size) = evm :=
    writeSolidityBytesDataWordsFrom_absent_same
      (evm := evm) (baseSlot := baseSlot) (value := value) (idx := 0)
      (fuel := solidityBytesDataWordCount value.size) hmissing
  have hstore :
      Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evm baseSlot value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evm baseSlot value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          baseSlot (solidityBytesHeaderWord value.size) = evm := by
    rw [hdata]
    exact storageStore_absent evm evm.executionEnv.codeOwner hmissing baseSlot
      (solidityBytesHeaderWord value.size)
  simpa [hstore] using hwrite

theorem writeSolidityStringLongFromLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityStringMalformedLong
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    simp [solidityDecodeBytesLengthHeader, hflag, hbad]
  have hslot :=
    solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot]

theorem writeSolidityStringMalformedShort
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    have hbad0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
      simpa [hflag] using hbad
    simp [solidityDecodeBytesLengthHeader, hflag, hbad0]
  have hslot :=
    solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot]

theorem writeSolidityStringEmptyFromZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes ByteArray.empty) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, solidityShortBytesWord,
    hslot, checkBytesPacked, hload]
  rw [empty_readWithPadding_word_zero]
  rfl

theorem assignSolidityStringEmptyFromZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    assignStorageRef? cfg solm evm .storage ref (.bytes ByteArray.empty) =
      .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hwrite := writeSolidityStringEmptyFromZero
    (cfg := cfg) (layout := layout) (evm := evm) (er := er) (baseSlot := baseSlot)
    hcfg hbase hload
  simp [assignStorageRef?, hresolve, hwrite, EvalResult.bind, bind, pure]

theorem readSolidityStringShortPackedExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, readStorage? cfg evm er .string = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := solidityShortBytesValid_lt32 hvalid0
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  let copy : ByteArray := header.toByteArray.extract 0 len.toNat
  have hcopySize : copy.size = len.toNat := by
    have hle32 : len.toNat ≤ 32 := by omega
    simp [copy, ByteArray.size_extract, hle32]
  refine ⟨copy, ?_, hcopySize⟩
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot, hload, hlt32, copy]

theorem readSolidityStringLongExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, readStorage? cfg evm er .string = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  let copy : ByteArray :=
    if len.toNat < 32 then
      header.toByteArray.extract 0 len.toNat
    else
      (readSolidityBytesDataWordsFrom evm baseSlot 0
        (solidityBytesDataWordCount len.toNat)).extract 0 len.toNat
  have hcopySize : copy.size = len.toNat := by
    by_cases hlt : len.toNat < 32
    · have hle32 : len.toNat ≤ 32 := by omega
      simp [copy, hlt, ByteArray.size_extract, hle32]
    · have hcover : len.toNat ≤ 32 * solidityBytesDataWordCount len.toNat := by
        unfold solidityBytesDataWordCount
        omega
      simp [copy, hlt, ByteArray.size_extract, hcover]
  refine ⟨copy, ?_, hcopySize⟩
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot, hload, copy]
  by_cases hlt : len.toNat < 32 <;> simp [hlt]

theorem evalSolidityStringShortPackedExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, evalExpr? cfg solm evm (.storage ref) = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  obtain ⟨copy, hread, hcopy⟩ := readSolidityStringShortPackedExists
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  refine ⟨copy, ?_, hcopy⟩
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]

theorem evalSolidityStringLongExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, evalExpr? cfg solm evm (.storage ref) = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  obtain ⟨copy, hread, hcopy⟩ := readSolidityStringLongExists
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  refine ⟨copy, ?_, hcopy⟩
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]

theorem clearSolidityBytesShortZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    clearStorage? cfg evm er .bytes =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, checkBytesPacked, hload,
    solidityBytesHeaderWord, storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearSolidityBytesShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage? cfg evm er .bytes =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, hpacked, solidityBytesHeaderWord,
    storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearSolidityBytesLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage? cfg evm er .bytes =
      .ok (clearSolidityBytesDataWordsFrom
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
        baseSlot 0 ((len.toNat + 31) / 32)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, hpacked, solidityBytesHeaderWord,
    storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem deleteSolidityBytesShortZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hclear := clearSolidityBytesShortZero
    (cfg := cfg) (layout := layout) (evm := evm) (er := er) (baseSlot := baseSlot)
    hcfg hbase hload
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem deleteSolidityBytesShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hclear := clearSolidityBytesShortPacked
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hpacked hflag hlen hvalid
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem deleteSolidityBytesLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (clearSolidityBytesDataWordsFrom
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
        baseSlot 0 ((len.toNat + 31) / 32)) := by
  have hclear := clearSolidityBytesLongPrepared
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem writeSolidityBytesShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot
        (solidityShortBytesWord value)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize]

theorem writeSolidityBytesShortFromLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm baseSlot 0
          ((len.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom evm baseSlot 0
          ((len.toNat + 31) / 32)).executionEnv.codeOwner
        baseSlot (solidityShortBytesWord value)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityBytesLongPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityBytesLongPackedAbsent
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? cfg evm er .bytes (.bytes value) = .ok evm := by
  have hwrite := writeSolidityBytesLongPacked
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len) (value := value)
    hcfg hbase hvalueSize hload hpacked hflag hlen hvalid
  have hdata :
      writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size) = evm :=
    writeSolidityBytesDataWordsFrom_absent_same
      (evm := evm) (baseSlot := baseSlot) (value := value) (idx := 0)
      (fuel := solidityBytesDataWordCount value.size) hmissing
  have hstore :
      Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evm baseSlot value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evm baseSlot value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          baseSlot (solidityBytesHeaderWord value.size) = evm := by
    rw [hdata]
    exact storageStore_absent evm evm.executionEnv.codeOwner hmissing baseSlot
      (solidityBytesHeaderWord value.size)
  simpa [hstore] using hwrite

theorem writeSolidityBytesLongFromLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .bytes (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityBytesMalformedLong
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? cfg evm er .bytes (.bytes value) = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    simp [solidityDecodeBytesLengthHeader, hflag, hbad]
  have hslot :=
    solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot]

theorem writeSolidityBytesMalformedShort
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? cfg evm er .bytes (.bytes value) = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    have hbad0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
      simpa [hflag] using hbad
    simp [solidityDecodeBytesLengthHeader, hflag, hbad0]
  have hslot :=
    solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot]

theorem writeSolidityBytesEmptyFromZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    writeStorage? cfg evm er .bytes (.bytes ByteArray.empty) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, solidityShortBytesWord,
    hslot, checkBytesPacked, hload]
  rw [empty_readWithPadding_word_zero]
  rfl

theorem assignSolidityBytesEmptyFromZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    assignStorageRef? cfg solm evm .storage ref (.bytes ByteArray.empty) =
      .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hwrite := writeSolidityBytesEmptyFromZero
    (cfg := cfg) (layout := layout) (evm := evm) (er := er) (baseSlot := baseSlot)
    hcfg hbase hload
  simp [assignStorageRef?, hresolve, hwrite, EvalResult.bind, bind, pure]

theorem readSolidityBytesShortPackedExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, readStorage? cfg evm er .bytes = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := solidityShortBytesValid_lt32 hvalid0
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  let copy : ByteArray := header.toByteArray.extract 0 len.toNat
  have hcopySize : copy.size = len.toNat := by
    have hle32 : len.toNat ≤ 32 := by omega
    simp [copy, ByteArray.size_extract, hle32]
  refine ⟨copy, ?_, hcopySize⟩
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot, hload, hlt32, copy]

theorem readSolidityBytesLongExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, readStorage? cfg evm er .bytes = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  let copy : ByteArray :=
    if len.toNat < 32 then
      header.toByteArray.extract 0 len.toNat
    else
      (readSolidityBytesDataWordsFrom evm baseSlot 0
        (solidityBytesDataWordCount len.toNat)).extract 0 len.toNat
  have hcopySize : copy.size = len.toNat := by
    by_cases hlt : len.toNat < 32
    · have hle32 : len.toNat ≤ 32 := by omega
      simp [copy, hlt, ByteArray.size_extract, hle32]
    · have hcover : len.toNat ≤ 32 * solidityBytesDataWordCount len.toNat := by
        unfold solidityBytesDataWordCount
        omega
      simp [copy, hlt, ByteArray.size_extract, hcover]
  refine ⟨copy, ?_, hcopySize⟩
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot, hload, copy]
  by_cases hlt : len.toNat < 32 <;> simp [hlt]

theorem evalSolidityBytesShortPackedExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, evalExpr? cfg solm evm (.storage ref) = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  obtain ⟨copy, hread, hcopy⟩ := readSolidityBytesShortPackedExists
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  refine ⟨copy, ?_, hcopy⟩
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]

theorem evalSolidityBytesLongExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, evalExpr? cfg solm evm (.storage ref) = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  obtain ⟨copy, hread, hcopy⟩ := readSolidityBytesLongExists
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  refine ⟨copy, ?_, hcopy⟩
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]

theorem readSolidityBytesRevertOfDecodeRevert
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .revert) :
    readStorage? cfg evm er .bytes = .revert := by
  have hslot :=
    solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot]

theorem evalSolidityBytesRevertOfDecodeRevert
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .revert) :
    evalExpr? cfg solm evm (.storage ref) = .revert := by
  have hread := readSolidityBytesRevertOfDecodeRevert
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header)
    hcfg hbase hload hdecode
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]

theorem readSolidityBytesEmptyOfZeroHeader
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    readStorage? cfg evm er .bytes = .ok (.bytes ByteArray.empty) := by
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload
      solidityDecodeBytesLengthHeader_zero
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot, hload]

theorem evalSolidityBytesEmptyOfZeroHeader
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .bytes))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    evalExpr? cfg solm evm (.storage ref) = .ok (.bytes ByteArray.empty) := by
  have hread := readSolidityBytesEmptyOfZeroHeader
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) hcfg hbase hload
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]


theorem storageLoad_storageStore_same_present (evm : EVM.State) (addr : AccountAddress)
    {acc : Account} (hacc : evm.accountMap.find? addr = some acc) (slot val : UInt256) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr slot val) addr slot = val := by
  unfold Solm.EVM.storageLoad Solm.EVM.storageStore State.lookupAccount
  rw [hacc]
  simp only [Option.option]
  unfold State.setAccount
  rw [accountMap_find_insert_self]
  unfold Account.updateStorage Account.lookupStorage
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    subst val
    simp
    exact storage_findD_erase_self acc.storage slot ⟨0⟩
  · simp [hzero]
    exact storage_findD_insert_self acc.storage slot val ⟨0⟩

theorem storageLoad_storageStore_same_zero (evm : EVM.State) (addr : AccountAddress)
    (slot : UInt256) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr slot ⟨0⟩) addr slot =
      (⟨0⟩ : UInt256) := by
  unfold Solm.EVM.storageLoad Solm.EVM.storageStore State.lookupAccount
  cases hacc : evm.accountMap.find? addr with
  | none =>
      simp [hacc, Option.option]
  | some acc =>
      simp only [Option.option]
      unfold State.setAccount
      rw [accountMap_find_insert_self]
      unfold Account.updateStorage Account.lookupStorage
      simp
      exact storage_findD_erase_self acc.storage slot ⟨0⟩

theorem storageLoad_storageStore_codeOwner_same_present
    (evm : EVM.State) {acc : Account}
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (slot val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val).executionEnv.codeOwner
        slot = val := by
  simpa [storageStore_executionEnv] using
    storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc slot val

theorem readStorageBytesLength?_ok_of_layout_after_storageStore_present
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256} {len : Nat}
    {acc : Account}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] }
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot header) =
        some loc ∧ loc.slot = baseSlot)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hdecode : solidityDecodeBytesLengthHeader header = .ok len) :
    readStorageBytesLength? cfg
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot header) er =
      .ok len := by
  exact readStorageBytesLength?_ok_of_layout
    (cfg := cfg) (layout := layout) (er := er)
    (evm := Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot header)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase
    (by
      simpa [storageStore_executionEnv] using
        storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
          baseSlot header)
    hdecode

theorem readStorageBytesLength?_ok_of_layout_after_storageStore_zero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] }
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) =
        some loc ∧ loc.slot = baseSlot) :
    readStorageBytesLength? cfg
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) er =
      .ok 0 := by
  exact readStorageBytesLength?_ok_of_layout
    (cfg := cfg) (layout := layout) (er := er)
    (evm := Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
    (baseSlot := baseSlot) (header := (⟨0⟩ : UInt256)) (len := 0)
    hcfg hbase
    (by
      simpa [storageStore_executionEnv] using
        storageLoad_storageStore_same_zero evm evm.executionEnv.codeOwner baseSlot)
    solidityDecodeBytesLengthHeader_zero

theorem storageLoad_storageStore_ne (evm : EVM.State) (addr : AccountAddress)
    {readSlot writeSlot val : UInt256} (hne : readSlot ≠ writeSlot) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr writeSlot val) addr readSlot =
      Solm.EVM.storageLoad evm addr readSlot := by
  simp only [Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount]
  cases hacc : evm.accountMap.find? addr with
  | none =>
      simp [hacc, Option.option]
  | some acc =>
      simp only [Option.option]
      unfold State.setAccount
      rw [accountMap_find_insert_self]
      unfold Account.updateStorage Account.lookupStorage
      by_cases hzero : (val == (default : UInt256)) = true
      · have hval : val = (default : UInt256) := eq_of_beq hzero
        subst val
        simp [storage_findD_erase_ne acc.storage readSlot writeSlot ⟨0⟩ hne]
      · simp [hzero, storage_findD_insert_ne acc.storage readSlot writeSlot val ⟨0⟩ hne]

/-- `storageLoad` after `storageStore`, with the slot collision case exposed in the result.  If the
account is absent, `storageStore` is a no-op, so a colliding read returns zero rather than `val`. -/
theorem storageLoad_storageStore_eq_if (evm : EVM.State) (addr : AccountAddress)
    (readSlot writeSlot val : UInt256) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr writeSlot val) addr readSlot =
      if readSlot = writeSlot then
        (evm.accountMap.find? addr).option (default : UInt256) (fun _ => val)
      else
        Solm.EVM.storageLoad evm addr readSlot := by
  simp only [Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount]
  by_cases hslot : readSlot = writeSlot
  · subst readSlot
    cases hacc : evm.accountMap.find? addr with
    | none =>
        simp [hacc, Option.option]
        rfl
    | some acc =>
        simp only [Option.option]
        unfold State.setAccount
        rw [accountMap_find_insert_self]
        unfold Account.updateStorage Account.lookupStorage
        by_cases hzero : (val == (default : UInt256)) = true
        · have hval : val = (default : UInt256) := eq_of_beq hzero
          subst val
          simpa using storage_findD_erase_self acc.storage writeSlot (default : UInt256)
        · simp [hzero, storage_findD_insert_self]
  · simp [hslot]
    exact storageLoad_storageStore_ne evm addr hslot

theorem storageLoad_storageStore_eq_if_of_before
    {evm : EVM.State} {addr : AccountAddress} {readSlot writeSlot val word : UInt256}
    (hload : Solm.EVM.storageLoad evm addr readSlot = word) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr writeSlot val) addr readSlot =
      if readSlot = writeSlot then
        (evm.accountMap.find? addr).option (default : UInt256) (fun _ => val)
      else
        word := by
  rw [storageLoad_storageStore_eq_if, hload]

theorem storageLoad_storageStore_eq_of_before_of_ne
    {evm : EVM.State} {addr : AccountAddress} {readSlot writeSlot val word : UInt256}
    (hne : readSlot ≠ writeSlot)
    (hload : Solm.EVM.storageLoad evm addr readSlot = word) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr writeSlot val) addr readSlot =
      word := by
  rw [storageLoad_storageStore_eq_if_of_before hload]
  exact if_neg hne

theorem storageLoad_storageStore_ne_after_storageStore_same_present
    (evm : EVM.State) (addr : AccountAddress) {acc : Account}
    (hacc : evm.accountMap.find? addr = some acc)
    {readSlot writeSlot header tag : UInt256} (hne : readSlot ≠ writeSlot) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm addr readSlot header) addr writeSlot tag)
        addr readSlot = header := by
  exact storageLoad_storageStore_eq_of_before_of_ne
    (evm := Solm.EVM.storageStore evm addr readSlot header) (addr := addr)
    (readSlot := readSlot) (writeSlot := writeSlot) (val := tag) hne
    (storageLoad_storageStore_same_present evm addr hacc readSlot header)

theorem storageLoad_storageStore_ne_after_storageStore_same_zero
    (evm : EVM.State) (addr : AccountAddress)
    {readSlot writeSlot tag : UInt256} (hne : readSlot ≠ writeSlot) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm addr readSlot ⟨0⟩) addr writeSlot tag)
        addr readSlot = (⟨0⟩ : UInt256) := by
  exact storageLoad_storageStore_eq_of_before_of_ne
    (evm := Solm.EVM.storageStore evm addr readSlot ⟨0⟩) (addr := addr)
    (readSlot := readSlot) (writeSlot := writeSlot) (val := tag) hne
    (storageLoad_storageStore_same_zero evm addr readSlot)

theorem readStorageBytesLength?_ok_of_layout_after_storageStore_ne_present
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {owner : AccountAddress}
    {baseSlot header tagSlot tag : UInt256} {len : Nat} {acc : Account}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (howner : evm.executionEnv.codeOwner = owner)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] }
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm owner baseSlot header) owner tagSlot tag) =
        some loc ∧ loc.slot = baseSlot)
    (hacc : evm.accountMap.find? owner = some acc)
    (hne : baseSlot ≠ tagSlot)
    (hdecode : solidityDecodeBytesLengthHeader header = .ok len) :
    readStorageBytesLength? cfg
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm owner baseSlot header) owner tagSlot tag) er =
      .ok len := by
  subst owner
  exact readStorageBytesLength?_ok_of_layout
    (cfg := cfg) (layout := layout) (er := er)
    (evm := Solm.EVM.storageStore
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot header)
      evm.executionEnv.codeOwner tagSlot tag)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase
    (by
      simpa [storageStore_executionEnv] using
        storageLoad_storageStore_ne_after_storageStore_same_present
          evm evm.executionEnv.codeOwner hacc (readSlot := baseSlot)
          (writeSlot := tagSlot) (header := header) (tag := tag) hne)
    hdecode

theorem readStorageBytesLength?_ok_of_layout_after_storageStore_ne_zero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {er : EvaledStorageRef} {evm : EVM.State} {owner : AccountAddress}
    {baseSlot tagSlot tag : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (howner : evm.executionEnv.codeOwner = owner)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] }
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm owner baseSlot ⟨0⟩) owner tagSlot tag) =
        some loc ∧ loc.slot = baseSlot)
    (hne : baseSlot ≠ tagSlot) :
    readStorageBytesLength? cfg
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm owner baseSlot ⟨0⟩) owner tagSlot tag) er =
      .ok 0 := by
  subst owner
  exact readStorageBytesLength?_ok_of_layout
    (cfg := cfg) (layout := layout) (er := er)
    (evm := Solm.EVM.storageStore
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
      evm.executionEnv.codeOwner tagSlot tag)
    (baseSlot := baseSlot) (header := (⟨0⟩ : UInt256)) (len := 0)
    hcfg hbase
    (by
      simpa [storageStore_executionEnv] using
        storageLoad_storageStore_ne_after_storageStore_same_zero
          evm evm.executionEnv.codeOwner (readSlot := baseSlot)
          (writeSlot := tagSlot) (tag := tag) hne)
    solidityDecodeBytesLengthHeader_zero

theorem storageLoad_storageStore_codeOwner_eq_if (evm : EVM.State)
    (readSlot writeSlot val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner writeSlot val)
        evm.executionEnv.codeOwner readSlot =
      if readSlot = writeSlot then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner readSlot := by
  exact storageLoad_storageStore_eq_if evm evm.executionEnv.codeOwner readSlot writeSlot val

theorem storageLoad_storageStore_codeOwner_eq_if_of_before
    {evm : EVM.State} {readSlot writeSlot val word : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner readSlot = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner writeSlot val)
        evm.executionEnv.codeOwner readSlot =
      if readSlot = writeSlot then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        word := by
  exact storageLoad_storageStore_eq_if_of_before hload

theorem storageLoad_storageStore_codeOwner_eq_of_before_of_ne
    {evm : EVM.State} {readSlot writeSlot val word : UInt256}
    (hne : readSlot ≠ writeSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner readSlot = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner writeSlot val)
        evm.executionEnv.codeOwner readSlot =
      word := by
  exact storageLoad_storageStore_eq_of_before_of_ne hne hload

theorem storageLoadSolidityBytesHeaderAfterDataStore_codeOwner_eq_if
    (evm : EVM.State) (baseSlot : UInt256) (wordIndex : Nat) (val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (solidityBytesDataSlot baseSlot wordIndex) val)
        evm.executionEnv.codeOwner baseSlot =
      if baseSlot = solidityBytesDataSlot baseSlot wordIndex then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot := by
  exact storageLoad_storageStore_codeOwner_eq_if evm baseSlot
    (solidityBytesDataSlot baseSlot wordIndex) val

theorem storageLoadSolidityBytesHeaderAfterDataStore_codeOwner_eq_if_of_before
    {evm : EVM.State} {baseSlot val word : UInt256} {wordIndex : Nat}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (solidityBytesDataSlot baseSlot wordIndex) val)
        evm.executionEnv.codeOwner baseSlot =
      if baseSlot = solidityBytesDataSlot baseSlot wordIndex then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        word := by
  exact storageLoad_storageStore_codeOwner_eq_if_of_before hload

theorem storageLoadSolidityBytesHeaderAfterDataStore_codeOwner_eq_of_before_of_ne
    {evm : EVM.State} {baseSlot val word : UInt256} {wordIndex : Nat}
    (hne : baseSlot ≠ solidityBytesDataSlot baseSlot wordIndex)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (solidityBytesDataSlot baseSlot wordIndex) val)
        evm.executionEnv.codeOwner baseSlot =
      word := by
  exact storageLoad_storageStore_codeOwner_eq_of_before_of_ne hne hload

structure EVMStateEquiv (evm₁ evm₂ : EVM.State) : Prop where
  executionEnv : evm₁.executionEnv = evm₂.executionEnv
  createdAccounts : evm₁.createdAccounts = evm₂.createdAccounts
  accountMap : accountMapEquiv evm₁.accountMap evm₂.accountMap

namespace EVMStateEquiv

theorem initState {cA gh bl σ₁ σ₀₁ σ₂ σ₀₂ A I g}
    (hAccounts : accountMapEquiv σ₁ σ₂) :
    EVMStateEquiv (initState cA gh bl σ₁ σ₀₁ g A I)
      (initState cA gh bl σ₂ σ₀₂ g A I) :=
  ⟨rfl, rfl, by simpa [initState] using hAccounts⟩

theorem storageLoad {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256) :
    Solm.EVM.storageLoad evm₁ addr₁ slot = Solm.EVM.storageLoad evm₂ addr₂ slot := by
  subst addr₂
  exact storageLoad_accountMapEquiv h.accountMap addr₁ slot

theorem storageLoad_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner slot := by
  rw [h.executionEnv]
  exact storageLoad_accountMapEquiv h.accountMap evm₂.executionEnv.codeOwner slot

theorem storageStore {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256)
    {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv (Solm.EVM.storageStore evm₁ addr₁ slot val₁)
      (Solm.EVM.storageStore evm₂ addr₂ slot val₂) := by
  subst addr₂
  subst val₂
  refine ⟨?_, ?_, ?_⟩
  · rw [storageStore_executionEnv, storageStore_executionEnv]
    exact h.executionEnv
  · rw [storageStore_createdAccounts, storageStore_createdAccounts]
    exact h.createdAccounts
  · exact storageStore_accountMapEquiv h.accountMap addr₁ slot val₁

theorem storageStore_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) :=
  h.storageStore (congrArg ExecutionEnv.codeOwner h.executionEnv) slot hval

end EVMStateEquiv

theorem storageLoad_storageStore_accountMapEquiv {evm1 evm2 : EVM.State}
    (hAccounts : accountMapEquiv evm1.accountMap evm2.accountMap)
    (addr : AccountAddress) (writeSlot val1 val2 readSlot : UInt256)
    (hval : val1 = val2) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm1 addr writeSlot val1) addr readSlot =
      Solm.EVM.storageLoad (Solm.EVM.storageStore evm2 addr writeSlot val2) addr readSlot := by
  subst val2
  exact storageLoad_accountMapEquiv
    (storageStore_accountMapEquiv hAccounts addr writeSlot val1) addr readSlot

theorem accountMapEquiv_sstoreAccountMap_two {σ τ : AccountMap}
    (a1 a2 : AccountAddress) (slot1 val1 slot2 val2 : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap a2 (sstoreAccountMap a1 σ slot1 val1) slot2 val2)
      (sstoreAccountMap a2 (sstoreAccountMap a1 τ slot1 val1) slot2 val2) := by
  exact accountMapEquiv_sstoreAccountMap a2 slot2 val2
    (accountMapEquiv_sstoreAccountMap a1 slot1 val1 hστ)

theorem accountMapEquiv_sstoreAccountMap_sameOwner {σ τ : AccountMap}
    (owner : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner σ slot val)
      (sstoreAccountMap owner τ slot val) := by
  exact accountMapEquiv_sstoreAccountMap owner slot val hστ

theorem accountMapEquiv_sstoreAccountMap_sameOwner_two {σ τ : AccountMap}
    (owner : AccountAddress) (slot1 val1 slot2 val2 : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner (sstoreAccountMap owner σ slot1 val1) slot2 val2)
      (sstoreAccountMap owner (sstoreAccountMap owner τ slot1 val1) slot2 val2) := by
  exact accountMapEquiv_sstoreAccountMap_two owner owner slot1 val1 slot2 val2 hστ

theorem accountMapEquiv_sstoreAccountMap_three {σ τ : AccountMap}
    (a1 a2 a3 : AccountAddress) (slot1 val1 slot2 val2 slot3 val3 : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap a3
        (sstoreAccountMap a2 (sstoreAccountMap a1 σ slot1 val1) slot2 val2) slot3 val3)
      (sstoreAccountMap a3
        (sstoreAccountMap a2 (sstoreAccountMap a1 τ slot1 val1) slot2 val2) slot3 val3) := by
  exact accountMapEquiv_sstoreAccountMap a3 slot3 val3
    (accountMapEquiv_sstoreAccountMap_two a1 a2 slot1 val1 slot2 val2 hστ)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- A single nonzero `SSTORE` is account-map equivalent to a zero-aware write followed by the same
    final same-slot nonzero `SSTORE`. -/
theorem accountMapEquiv_sstoreAccountMap_self_update_insert
    (σ : AccountMap) (a : AccountAddress) (slot val1 val2 : UInt256)
    (hfinal : (val2 == (default : UInt256)) = false) :
    accountMapEquiv (sstoreAccountMap a σ slot val2)
      (sstoreAccountMap a (sstoreAccountMap a σ slot val1) slot val2) := by
  intro addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    cases hσ : σ.find? a with
    | none =>
        simp [hσ, Option.option]
    | some acc =>
        simp [hfinal, accountMap_find_insert_self, Option.option]
        by_cases hzero : val1 = (default : UInt256)
        · simpa [hzero] using accountEquiv_update_insert_self acc slot val1 val2
        · simpa [hzero] using accountEquiv_update_insert_self acc slot val1 val2
  · unfold sstoreAccountMap
    cases hσ : σ.find? a
    · simp only [hσ, Option.option]
      cases σ.find? addr <;> simp [accountEquiv_refl]
    · simp only [Option.option, hfinal, Bool.false_eq_true, if_false]
      rw [accountMap_find_insert_self]
      rw [accountMap_find?_insert_ne σ addr a _ haddr]
      rw [accountMap_find?_insert_ne (σ.insert a _) addr a _ haddr]
      rw [accountMap_find?_insert_ne σ addr a _ haddr]
      cases σ.find? addr <;> simp [accountEquiv_refl]

theorem accountEquiv_update_erase_self (acc : Account) (slot val1 : UInt256) :
    accountEquiv {acc with storage := acc.storage.erase slot}
      {acc with storage :=
        (if val1 = (default : UInt256) then acc.storage.erase slot
         else acc.storage.insert slot val1).erase slot} := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro readSlot
    by_cases hread : readSlot = slot
    · subst readSlot
      rw [storage_find?_erase_self, storage_find?_erase_self]
    · by_cases hzero : val1 = (default : UInt256)
      · rw [if_pos hzero]
        rw [storage_find?_erase_ne acc.storage readSlot slot hread]
        rw [storage_find?_erase_ne (acc.storage.erase slot) readSlot slot hread]
        rw [storage_find?_erase_ne acc.storage readSlot slot hread]
      · rw [if_neg hzero]
        rw [storage_find?_erase_ne acc.storage readSlot slot hread]
        rw [storage_find?_erase_ne (acc.storage.insert slot val1) readSlot slot hread]
        rw [storage_find?_insert_ne acc.storage readSlot slot val1 hread]
  · simp

theorem accountMapEquiv_sstoreAccountMap_self_update
    (σ : AccountMap) (a : AccountAddress) (slot val1 val2 : UInt256) :
    accountMapEquiv (sstoreAccountMap a σ slot val2)
      (sstoreAccountMap a (sstoreAccountMap a σ slot val1) slot val2) := by
  by_cases hfinal : (val2 == (default : UInt256)) = false
  · exact accountMapEquiv_sstoreAccountMap_self_update_insert σ a slot val1 val2 hfinal
  · have hfinalTrue : (val2 == (default : UInt256)) = true := by
      cases h : (val2 == (default : UInt256)) <;> simp [h] at hfinal ⊢
    have hval2 : val2 = (default : UInt256) := eq_of_beq hfinalTrue
    subst val2
    intro addr
    by_cases haddr : addr = a
    · subst addr
      unfold sstoreAccountMap
      cases hσ : σ.find? a with
      | none =>
          simp [hσ, Option.option]
      | some acc =>
          simp [Option.option, accountMap_find_insert_self]
          by_cases hzero1 : val1 = (default : UInt256)
          · simpa [hzero1] using accountEquiv_update_erase_self acc slot val1
          · simpa [hzero1] using accountEquiv_update_erase_self acc slot val1
    · unfold sstoreAccountMap
      cases hσ : σ.find? a
      · simp only [hσ, Option.option]
        cases σ.find? addr <;> simp [accountEquiv_refl]
      · simp only [Option.option, hfinalTrue]
        rw [accountMap_find_insert_self]
        rw [accountMap_find?_insert_ne σ addr a _ haddr]
        rw [accountMap_find?_insert_ne (σ.insert a _) addr a _ haddr]
        rw [accountMap_find?_insert_ne σ addr a _ haddr]
        cases σ.find? addr <;> simp [accountEquiv_refl]

theorem accountMapEquiv_sstoreAccountMap_comm
    (σ : AccountMap) (a : AccountAddress) (slot1 val1 slot2 val2 : UInt256)
    (hne : slot1 ≠ slot2) :
    accountMapEquiv
      (sstoreAccountMap a (sstoreAccountMap a σ slot1 val1) slot2 val2)
      (sstoreAccountMap a (sstoreAccountMap a σ slot2 val2) slot1 val1) := by
  intro addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    cases hσ : σ.find? a with
    | none =>
        simp [hσ, Option.option]
    | some acc =>
        by_cases hzero1 : val1 = (default : UInt256) <;>
          by_cases hzero2 : val2 = (default : UInt256)
        all_goals
          simp [Option.option, accountMap_find_insert_self, hzero1, hzero2]
          refine ⟨rfl, rfl, rfl, ?_, by simp⟩
          intro readSlot
          by_cases hread1 : readSlot = slot1
          · subst readSlot
            simp [hne, storage_find?_erase_ne,
              storage_find?_insert_ne, storage_find?_erase_self,
              Batteries.RBMap.find?_insert_of_eq, Std.ReflCmp.compare_self]
          · by_cases hread2 : readSlot = slot2
            · subst readSlot
              simp [Ne.symm hne, storage_find?_erase_ne,
                storage_find?_insert_ne, storage_find?_erase_self,
                Batteries.RBMap.find?_insert_of_eq, Std.ReflCmp.compare_self]
            · simp [hread1, hread2, storage_find?_erase_ne,
                storage_find?_insert_ne]
  · unfold sstoreAccountMap
    cases hσ : σ.find? a <;>
      simp [hσ, Option.option, accountMap_find_insert_self,
        accountMap_find?_insert_ne, haddr]
    · cases σ.find? addr <;> simp [accountEquiv_refl]
    · cases σ.find? addr <;> simp [accountEquiv_refl]

theorem accountMapEquiv_sstoreAccountMap_zero_comm
    (σ : AccountMap) (a : AccountAddress) (slot1 slot2 : UInt256) :
    accountMapEquiv
      (sstoreAccountMap a (sstoreAccountMap a σ slot2 ⟨0⟩) slot1 ⟨0⟩)
      (sstoreAccountMap a (sstoreAccountMap a σ slot1 ⟨0⟩) slot2 ⟨0⟩) := by
  by_cases hne : slot1 ≠ slot2
  · exact accountMapEquiv.symm
      (accountMapEquiv_sstoreAccountMap_comm σ a slot1 ⟨0⟩ slot2 ⟨0⟩ hne)
  · have heq : slot1 = slot2 := by exact Classical.not_not.mp hne
    subst slot2
    exact accountMapEquiv_refl _

theorem accountMapEquiv_sstoreAccountMap_erase_comm
    (σ : AccountMap) (a : AccountAddress) (slot val eraseSlot : UInt256)
    (hne : slot ≠ eraseSlot) :
    accountMapEquiv
      (sstoreAccountMap a (sstoreAccountMap a σ eraseSlot ⟨0⟩) slot val)
      (sstoreAccountMap a (sstoreAccountMap a σ slot val) eraseSlot ⟨0⟩) :=
  accountMapEquiv.symm
    (accountMapEquiv_sstoreAccountMap_comm σ a slot val eraseSlot ⟨0⟩ hne)

theorem accountMapEquiv_sstore_accountStorageStatefulWordsForwardFrom_comm_ne
    {α : Type} {owner : AccountAddress} {σ τ : AccountMap}
    (slot val : UInt256) (slotAt wordAt : α → UInt256) (next : α → α) :
    ∀ (state : α) (fuel : Nat),
      (∀ i, i < fuel → slot ≠ slotAt (accountStorageStatefulLoopState next state i)) →
      accountMapEquiv σ τ →
      accountMapEquiv
        (accountStorageStatefulWordsForwardFrom α owner
          (sstoreAccountMap owner σ slot val) slotAt wordAt next state fuel)
        (sstoreAccountMap owner
          (accountStorageStatefulWordsForwardFrom α owner τ slotAt wordAt next state fuel)
          slot val)
  | state, 0, _hdisjoint, hAccounts => accountMapEquiv_sstoreAccountMap owner slot val hAccounts
  | state, fuel + 1, hdisjoint, hAccounts => by
      simp [accountStorageStatefulWordsForwardFrom]
      have hhead : slot ≠ slotAt state := by
        simpa [accountStorageStatefulLoopState] using hdisjoint 0 (Nat.zero_lt_succ fuel)
      have htail :
          ∀ i, i < fuel →
            slot ≠ slotAt (accountStorageStatefulLoopState next (next state) i) := by
        intro i hi
        simpa [accountStorageStatefulLoopState] using hdisjoint (i + 1) (Nat.succ_lt_succ hi)
      have hstep := accountMapEquiv_sstoreAccountMap owner (slotAt state) (wordAt state) hAccounts
      have hcomm₀ :
          accountMapEquiv
            (sstoreAccountMap owner
              (sstoreAccountMap owner σ slot val) (slotAt state) (wordAt state))
            (sstoreAccountMap owner
              (sstoreAccountMap owner τ (slotAt state) (wordAt state)) slot val) := by
        have hcommLeft :=
          accountMapEquiv_sstoreAccountMap_comm σ owner slot val (slotAt state) (wordAt state)
            hhead
        have hcong := accountMapEquiv_sstoreAccountMap owner slot val hstep
        exact accountMapEquiv.trans hcommLeft hcong
      have hcong :=
        accountMapEquiv_accountStorageStatefulWordsForwardFrom
          (owner := owner)
          (slotAt := slotAt) (wordAt := wordAt) (next := next) (state := next state)
          fuel hcomm₀
      have htailComm :=
        accountMapEquiv_sstore_accountStorageStatefulWordsForwardFrom_comm_ne
          (owner := owner)
          (σ := sstoreAccountMap owner τ (slotAt state) (wordAt state))
          (τ := sstoreAccountMap owner τ (slotAt state) (wordAt state))
          slot val slotAt wordAt next (next state) fuel htail (accountMapEquiv_refl _)
      exact accountMapEquiv.trans hcong htailComm

theorem accountMapEquiv_sstore_clearDataWordsForwardFrom {σ τ : AccountMap}
    (owner : AccountAddress) (base idx slot val : UInt256) (fuel : Nat)
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner
        (clearDataWordsForwardFrom owner σ base idx fuel) slot val)
      (sstoreAccountMap owner
        (clearDataWordsForwardFrom owner τ base idx fuel) slot val) := by
  exact accountMapEquiv_sstoreAccountMap owner slot val
    (accountMapEquiv_clearDataWordsForwardFrom owner base idx fuel hAccounts)

theorem accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm {σ τ : AccountMap}
    (owner : AccountAddress) (base idx slot : UInt256) :
    ∀ fuel, accountMapEquiv σ τ →
      accountMapEquiv
        (sstoreAccountMap owner
          (clearDataWordsForwardFrom owner σ base idx fuel) slot ⟨0⟩)
        (clearDataWordsForwardFrom owner
          (sstoreAccountMap owner τ slot ⟨0⟩) base idx fuel)
  | 0, hAccounts => accountMapEquiv_sstoreAccountMap owner slot ⟨0⟩ hAccounts
  | n + 1, hAccounts => by
      simp [clearDataWordsForwardFrom]
      have hdata := accountMapEquiv_sstoreAccountMap owner (base + idx) ⟨0⟩ hAccounts
      have ih := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
        owner base ((⟨1⟩ : UInt256) + idx) slot n hdata
      have hcomm₀ :=
        accountMapEquiv_sstoreAccountMap_zero_comm τ owner slot (base + idx)
      have hcomm := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) n hcomm₀
      exact accountMapEquiv.trans ih hcomm

theorem accountMapEquiv_sstore_clearDataWordsForwardFrom_comm_ne {σ τ : AccountMap}
    (owner : AccountAddress) (base idx slot val : UInt256) :
    ∀ fuel,
      (∀ i, i < fuel → slot ≠ base + uint256SuccFrom idx i) →
      accountMapEquiv σ τ →
      accountMapEquiv
        (sstoreAccountMap owner
          (clearDataWordsForwardFrom owner σ base idx fuel) slot val)
        (clearDataWordsForwardFrom owner
          (sstoreAccountMap owner τ slot val) base idx fuel)
  | 0, _hdisjoint, hAccounts => accountMapEquiv_sstoreAccountMap owner slot val hAccounts
  | n + 1, hdisjoint, hAccounts => by
      simp [clearDataWordsForwardFrom]
      have hdata := accountMapEquiv_sstoreAccountMap owner (base + idx) ⟨0⟩ hAccounts
      have htail :
          ∀ i, i < n →
            slot ≠ base + uint256SuccFrom ((⟨1⟩ : UInt256) + idx) i := by
        intro i hi
        have hne := hdisjoint (i + 1) (Nat.succ_lt_succ hi)
        simpa [uint256SuccFrom_one_add] using hne
      have ih := accountMapEquiv_sstore_clearDataWordsForwardFrom_comm_ne
        owner base ((⟨1⟩ : UInt256) + idx) slot val n htail hdata
      have hcomm₀ :=
        accountMapEquiv_sstoreAccountMap_erase_comm τ owner slot val (base + idx)
          (hdisjoint 0 (Nat.zero_lt_succ n))
      have hcomm := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) n hcomm₀
      exact accountMapEquiv.trans ih hcomm

theorem accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_absorb_first
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} (fuel : Nat) :
    accountMapEquiv
      (sstoreAccountMap owner
        (clearDataWordsForwardFrom owner τ base idx (fuel + 1)) (base + idx) ⟨0⟩)
      (clearDataWordsForwardFrom owner τ base idx (fuel + 1)) := by
  simp [clearDataWordsForwardFrom]
  have hcomm := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
    owner base ((⟨1⟩ : UInt256) + idx) (base + idx) fuel
    (accountMapEquiv_refl (sstoreAccountMap owner τ (base + idx) ⟨0⟩))
  have hself := accountMapEquiv_sstoreAccountMap_self_update
    τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
  have htailSelf := accountMapEquiv_clearDataWordsForwardFrom owner base
    ((⟨1⟩ : UInt256) + idx) fuel hself
  exact accountMapEquiv.trans hcomm (accountMapEquiv.symm htailSelf)

theorem accountMapEquiv_clearDataWordsForwardFrom_succ_last
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ fuel,
      accountMapEquiv
        (clearDataWordsForwardFrom owner τ base idx (fuel + 1))
        (sstoreAccountMap owner
          (clearDataWordsForwardFrom owner τ base idx fuel)
          (base + uint256SuccFrom idx fuel) ⟨0⟩)
  | 0 => by
      simp [clearDataWordsForwardFrom, uint256SuccFrom, accountMapEquiv_refl]
  | fuel + 1 => by
      have ih := accountMapEquiv_clearDataWordsForwardFrom_succ_last
        (owner := owner)
        (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx)) fuel
      simpa [clearDataWordsForwardFrom, uint256SuccFrom_one_add, u256_add_assoc] using ih

theorem accountMapEquiv_clearDataWordsForwardFrom_double_prefix
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ oldFuel newFuel : Nat, oldFuel ≤ newFuel →
      accountMapEquiv
        (clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base idx oldFuel) base idx newFuel)
        (clearDataWordsForwardFrom owner τ base idx newFuel)
  | 0, newFuel, _hle => by
      simp [clearDataWordsForwardFrom, accountMapEquiv_refl]
  | oldFuel + 1, 0, hle => by
      omega
  | oldFuel + 1, newFuel + 1, hle => by
      simp [clearDataWordsForwardFrom]
      have hcomm := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
        owner base ((⟨1⟩ : UInt256) + idx) (base + idx) oldFuel
        (accountMapEquiv_refl (sstoreAccountMap owner τ (base + idx) ⟨0⟩))
      have hself := accountMapEquiv_sstoreAccountMap_self_update
        τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
      have htailSelf := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) oldFuel hself
      have hbase := accountMapEquiv.trans hcomm (accountMapEquiv.symm htailSelf)
      have hcong := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) newFuel hbase
      have htail := accountMapEquiv_clearDataWordsForwardFrom_double_prefix
        (owner := owner) (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx))
        oldFuel newFuel (by omega)
      exact accountMapEquiv.trans hcong htail

theorem accountMapEquiv_clearDataWordsForwardFrom_split
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ (pref tail : Nat),
      accountMapEquiv
        (clearDataWordsForwardFrom owner τ base idx (pref + tail))
        (clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base (uint256SuccFrom idx pref) tail)
          base idx pref)
  | 0, tail => by
      simp [clearDataWordsForwardFrom, uint256SuccFrom, accountMapEquiv_refl]
  | pref + 1, tail => by
      have hfuel : pref + 1 + tail = pref + tail + 1 := by omega
      rw [hfuel]
      simp [clearDataWordsForwardFrom]
      have ih := accountMapEquiv_clearDataWordsForwardFrom_split
        (owner := owner) (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx)) pref tail
      have hcomm := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
        owner base (uint256SuccFrom ((⟨1⟩ : UInt256) + idx) pref)
        (base + idx) tail (accountMapEquiv_refl τ)
      have htail := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) pref (accountMapEquiv.symm hcomm)
      exact accountMapEquiv.trans ih (by
        simpa [uint256SuccFrom_one_add] using htail)

-- LIBRARY CANDIDATE: `Reasoning.Storage`.
/-- Same-account/same-slot overwrite at the lookup level for `sstoreAccountMap` when the final write
    is nonzero.  This is the EVM/Solidity storage-update analogue of
    `storage_findD_update_insert_self`. -/
theorem sstoreAccountMap_self_storage_findD_update_insert_self
    (σ : AccountMap) (a : AccountAddress) (writeSlot readSlot val1 val2 : UInt256)
    (hfinal : (val2 == (default : UInt256)) = false) :
    (((sstoreAccountMap a (sstoreAccountMap a σ writeSlot val1) writeSlot val2).find? a).option
        (default : UInt256) (fun acc => acc.storage.findD readSlot default)) =
      (((sstoreAccountMap a σ writeSlot val2).find? a).option
        (default : UInt256) (fun acc => acc.storage.findD readSlot default)) := by
  cases hacc : σ.find? a with
  | none =>
      have hfirst : sstoreAccountMap a σ writeSlot val1 = σ := by
        simp only [sstoreAccountMap, hacc, Option.option]
      have hsecond : sstoreAccountMap a σ writeSlot val2 = σ := by
        simp only [sstoreAccountMap, hacc, Option.option]
      rw [hfirst, hsecond]
  | some acc =>
      let acc1 : Account :=
        if val1 == (default : UInt256) then {acc with storage := acc.storage.erase writeSlot}
        else {acc with storage := acc.storage.insert writeSlot val1}
      let acc2 : Account := {acc with storage := acc.storage.insert writeSlot val2}
      have hfirst : sstoreAccountMap a σ writeSlot val1 = σ.insert a acc1 := by
        simp only [sstoreAccountMap, hacc, Option.option, acc1]
      have hsecond :
          sstoreAccountMap a (sstoreAccountMap a σ writeSlot val1) writeSlot val2 =
            (σ.insert a acc1).insert a
              {acc1 with storage := acc1.storage.insert writeSlot val2} := by
        rw [hfirst]
        simp only [sstoreAccountMap, accountMap_find_insert_self, Option.option, hfinal,
          Bool.false_eq_true, if_false]
      have hright : sstoreAccountMap a σ writeSlot val2 = σ.insert a acc2 := by
        simp only [sstoreAccountMap, hacc, hfinal, Option.option, Bool.false_eq_true, if_false,
          acc2]
      rw [hsecond, hright]
      rw [accountMap_find_insert_self, accountMap_find_insert_self]
      change (acc1.storage.insert writeSlot val2).findD readSlot default =
        (acc.storage.insert writeSlot val2).findD readSlot default
      by_cases hzero : val1 = (default : UInt256)
      · simpa [acc1, hzero] using
          storage_findD_update_insert_self acc.storage writeSlot readSlot val1 val2
      · simpa [acc1, hzero] using
          storage_findD_update_insert_self acc.storage writeSlot readSlot val1 val2

end Reasoning.Theory
