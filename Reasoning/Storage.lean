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

theorem sstoreAccountMap_storage_findD_self_of_find_some
    (σ : AccountMap) (a : AccountAddress) (acc : Account) (slot val : UInt256)
    (hacc : σ.find? a = some acc) (hval : (val == (default : UInt256)) = false) :
    (((sstoreAccountMap a σ slot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256))) = val := by
  unfold sstoreAccountMap
  simp [hacc, Option.option, hval, accountMap_find_insert_self]
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

theorem storageStore_executionEnv (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_absent (evm : EVM.State) (addr : AccountAddress)
    (hmissing : evm.accountMap.find? addr = none) (slot val : UInt256) :
    Solm.EVM.storageStore evm addr slot val = evm := by
  simp [Solm.EVM.storageStore, State.lookupAccount, hmissing, Option.option]

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

def clearDataWordsForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (base idx : UInt256) : Nat → AccountMap
  | 0 => τ
  | n + 1 =>
      clearDataWordsForwardFrom owner
        (sstoreAccountMap owner τ (base + idx) ⟨0⟩) base ((⟨1⟩ : UInt256) + idx) n

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
