import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Stepping
import Solm.SolidityLayout
import Ethereum.Theory.StaticStorage

/-!
# Storage — EVM storage maps, Solidity storage layout, and account-map equality

Contract-agnostic layers, bottom up:

- **Ordered-map (`Std.ExtTreeMap`) facts** for EVM storage (`Storage`) and account maps
  (`AccountMap`): a write at one slot preserves lookup at a
  different slot.  The standard `ExtTreeMap` insert and erase lookup lemmas provide these facts.
- **`StorageLoc` load/store facts** for the Solidity value encodings: full-slot uint256/bytes32,
  packed unsigned integers, addresses at byte offsets 0/1, packed bools.
- **The Solidity bytes/string storage layout**: writing, reading, deleting, and clearing the
  length slot and the keccak-addressed data words.
- **`EVMStateEquiv`**: equality of execution environments and extensional account maps, with
  preservation lemmas for storage reads and writes used by the refinement proofs.

The `UInt256` `compare` instances these rely on live in `Reasoning.EVMWord`.
-/

open Ethereum Ethereum.EVM Solm

namespace Reasoning.Theory

abbrev codeOwnerStorageWord (ee : ExecutionEnv) (σ : AccountMap) (slot : UInt256) : UInt256 :=
  σ.get? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD slot ⟨0⟩)

theorem codeOwnerStorageWord_initState {σ σ₀ A I} {g : Sat256}
    (slot : UInt256) :
    Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner slot =
      codeOwnerStorageWord I σ slot := by
  simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
    codeOwnerStorageWord]

-- EVM storage uses `getD`; this packages the key inequality as the comparison needed by Std.
theorem storage_getD_insert_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).getD readSlot default =
      storage.getD readSlot default := by
  have hcmp : compare writeSlot readSlot ≠ .eq := by
    intro hcmp
    exact hne (Std.LawfulEqCmp.eq_of_compare hcmp).symm
  rw [Std.ExtTreeMap.getD_insert, if_neg hcmp]

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

theorem keyValueToWord_address_ofNat_mask (w : UInt256) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) =
      UInt256.land solcAddrMask w := by
  rw [keyValueToWord_address]
  apply u256_inj
  rw [uland_toNat]
  unfold AccountAddress.ofNat UInt256.ofNat UInt256.toNat
  change (w.val.val % AccountAddress.size) % UInt256.size =
    Nat.land solcAddrMask.toNat w.val.val
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))
    (by norm_num [UInt256.size]))

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
  have htakeNat :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 32 =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    apply List.take_of_length_le
    rw [(EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
  have htakeFin :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0
            (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    exact htakeNat
  unfold storageLocLoad uint256Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  rw [normalizeInt_uint_eq_self]
  · congr
    rw [htakeFin, fromBytes'_toBytesLEWithSizeProof]
    rfl
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 32) <
        EVM.twoPow 256
    rw [htakeNat]
    have hle := EVM.fromBytes'_le (bs := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)
    rw [(EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2] at hle
    exact hle

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

/-! ## Packed unsigned integer storage -/

theorem storageLocLoad_uint_offset0 (evm : EVM.State) (slot : UInt256)
    (size : Fin 33) (width : ABI.BitWidth)
    {hbound : (0 : Fin 32).val + size.val - 1 < 32}
    (hwidth : width.val = 8 * size.val) (hbits : 8 * size.val ≤ 256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := size, hbound := hbound,
          type := .int (.uint width) } =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (2 ^ (8 * size.val) - 1))).toNat) := by
  unfold storageLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  rw [normalizeInt_uint_eq_self]
  · change Value.int (Int.ofNat (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 size.val))) = _
    rw [List.extract_eq_take_drop, List.drop_zero]
    simpa [Nat.sub_zero] using
      fromBytes'_take_wordLE_land_mask
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) size.val hbits
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    change fromBytes' (((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 size.val) <
        EVM.twoPow width.val
    rw [List.extract_eq_take_drop, List.drop_zero, hwidth]
    have hle := EVM.fromBytes'_le (bs := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take size.val)
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
      Nat.min_eq_left (by omega)] at hle
    exact hle

theorem storageLocLoad_uint_offset (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (width : ABI.BitWidth)
    {hbound : offset.val + size.val - 1 < 32}
    (hwidth : width.val = 8 * size.val)
    (hoff : 8 * offset.val < 256) (hsize : 8 * size.val ≤ 256) :
    storageLocLoad evm
        { slot := slot, offset := offset, size := size, hbound := hbound,
          type := .int (.uint width) } =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ offset.val)))
          (UInt256.ofNat (256 ^ size.val - 1))).toNat) := by
  unfold storageLocLoad wordToElem
  change Value.int (normalizeInt (.uint width) (Int.ofNat (fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract
        offset.val (offset.val + size.val))))) = _
  rw [normalizeInt_uint_eq_self]
  · rw [List.extract_eq_take_drop]
    simpa [Nat.add_sub_cancel_left] using
      fromBytes'_drop_take_wordLE_land_div_mask
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val size.val hoff hsize
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    change fromBytes' (((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract
        offset.val (offset.val + size.val)) < EVM.twoPow width.val
    rw [List.extract_eq_take_drop, Nat.add_sub_cancel_left, hwidth]
    have hle := EVM.fromBytes'_le (bs := ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop offset.val).take
        size.val)
    rw [List.length_take, List.length_drop, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
      Nat.min_eq_left (by omega)] at hle
    exact hle

theorem storageLocStore_int_some (evm : EVM.State) (loc : StorageLoc) (n : Int) :
    ∃ evm', storageLocStore evm loc (.int n) = some evm' := by
  unfold storageLocStore
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

/-! ## Solidity bytes/string storage layout -/

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
    change w.val.val < UInt256.size
    exact w.val.isLt
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

set_option maxRecDepth 2000000 in
theorem packedAddressAfterBoolTrueNat_lt_size (old val : UInt256)
    (hcanon : val.toNat < EVM.addressModulus) :
    1 + val.toNat * 2 ^ 8 + old.toNat / 2 ^ 168 * 2 ^ 168 < UInt256.size := by
  have hq : old.toNat / 2 ^ 168 < 2 ^ 88 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 168 * 2 ^ 88 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simp [UInt256.size]
  have hv : val.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
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

set_option maxRecDepth 2000000 in
theorem packedAddressAfterBoolTrueWord_eq (old val : UInt256)
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
    u256_land_high_mask_toNat old 168 (by norm_num)]
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
    simp [UInt256.size]
  have hv : val.toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using hcanon
  have hinnerlt :
      Nat.lor (val.toNat * 2 ^ 8) (old.toNat / 2 ^ 168 * 2 ^ 168) <
        UInt256.size := by
    rw [nat_lor_shift_add (val.toNat * 2 ^ 8) (old.toNat / 2 ^ 168) 168]
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
  rw [nat_lor_packed_bool_address_high val.toNat (old.toNat / 2 ^ 168) hv]
  have hlt := packedAddressAfterBoolTrueNat_lt_size old val hcanon
  rw [ulit_toNat' _ hlt, Nat.mod_eq_of_lt hlt]

theorem packedAddressAfterBoolTrueBytes_toNat (old val : UInt256)
    (hcanon : val.toNat < EVM.addressModulus) :
    let w1 := UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩
    fromBytes'
        ((EVM.Word.toBytesLEWithSizeProof w1).1.take 1 ++
          (EVM.Word.toBytesLEWithSizeProof val).1.take 20 ++
          (EVM.Word.toBytesLEWithSizeProof w1).1.drop 21) =
      1 + val.toNat * 2 ^ 8 + (old.toNat / 2 ^ 168) * 2 ^ 168 := by
  intro w1
  have hw1nat : w1.toNat = 1 + 256 * (old.toNat / 256) := by
    simpa [w1] using packedSetTrueWord_toNat old
  have hlow : fromBytes' ((EVM.Word.toBytesLEWithSizeProof w1).1.take 1) = 1 := by
    rw [fromBytes'_take_wordLE_land_mask _ 1 (by decide)]
    rw [u256_land_toNat]
    rw [hw1nat]
    change Nat.land (1 + 256 * (old.toNat / 256)) (2 ^ 8 - 1) % UInt256.size = 1
    rw [nat_land_mask_eq_mod]
    norm_num
    rw [Nat.mod_eq_of_lt (by norm_num [UInt256.size])]
  have hval : fromBytes' ((EVM.Word.toBytesLEWithSizeProof val).1.take 20) = val.toNat := by
    rw [fromBytes'_take20_wordLE_solcAddrMask]
    simpa [u256_land_toNat] using congrArg UInt256.toNat (solcAddrMask_clean hcanon)
  have hhigh : fromBytes' ((EVM.Word.toBytesLEWithSizeProof w1).1.drop 21) =
      old.toNat / 2 ^ 168 := by
    rw [fromBytes'_drop_wordLE]
    rw [hw1nat]
    rw [show 256 ^ 21 = 2 ^ 168 by norm_num [Nat.pow_succ, Nat.pow_add]]
    rw [show 2 ^ 168 = 256 * 2 ^ 160 by norm_num [Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul]
    rw [← Nat.div_div_eq_div_mul]
    rw [show (1 + 256 * (old.toNat / 256)) / 256 = old.toNat / 256 by
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256)]
      simp]
  rw [fromBytes'_append, fromBytes'_append, hlow, hval, hhigh]
  have hlen1 : ((EVM.Word.toBytesLEWithSizeProof w1).1.take 1).length = 1 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w1).2]
    norm_num
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof val).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
    norm_num
  rw [hlen1, List.length_append, hlen1, hlen20]
  norm_num [Nat.pow_add]
  ring

theorem packedSetFalseWord_eq (w : UInt256) :
    UInt256.land w (UInt256.lnot ⟨255⟩) =
      UInt256.ofNat (256 * (w.toNat / 256)) := by
  apply u256_inj
  rw [u256_land_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < UInt256.size
    exact w.val.isLt
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

/-- Erasing a storage word preserves lookup at a different storage slot. -/
theorem storage_getD_erase_ne (storage : Storage) (readSlot writeSlot default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).getD readSlot default =
      storage.getD readSlot default := by
  have hcmp : compare writeSlot readSlot ≠ .eq := by
    intro hcmp
    exact hne (Std.LawfulEqCmp.eq_of_compare hcmp).symm
  rw [Std.ExtTreeMap.getD_erase, if_neg hcmp]

/-- Updating a storage slot with EVM/Solidity semantics preserves lookup at a different slot.
    Nonzero writes insert; zero writes erase. -/
theorem storage_getD_update_ne (storage : Storage) (readSlot writeSlot val default : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == default then storage.erase writeSlot else storage.insert writeSlot val).getD
        readSlot default) =
      storage.getD readSlot default := by
  by_cases hzero : (val == default) = true
  · simpa [hzero] using storage_getD_erase_ne storage readSlot writeSlot default hne
  · simpa [hzero] using storage_getD_insert_ne storage readSlot writeSlot val default hne

theorem storage_get?_insert_ne (storage : Storage) (readSlot writeSlot val : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.insert writeSlot val).get? readSlot = storage.get? readSlot := by
  change (storage.insert writeSlot val)[readSlot]? = storage[readSlot]?
  rw [Std.ExtTreeMap.getElem?_insert]
  have hcmp : compare writeSlot readSlot ≠ .eq := by
    intro h
    exact hne (Std.LawfulEqCmp.eq_of_compare h).symm
  rw [if_neg hcmp]

theorem storage_get?_erase_ne (storage : Storage) (readSlot writeSlot : UInt256)
    (hne : readSlot ≠ writeSlot) :
    (storage.erase writeSlot).get? readSlot = storage.get? readSlot := by
  change (storage.erase writeSlot)[readSlot]? = storage[readSlot]?
  rw [Std.ExtTreeMap.getElem?_erase]
  have hcmp : compare writeSlot readSlot ≠ .eq := by
    intro h
    exact hne (Std.LawfulEqCmp.eq_of_compare h).symm
  rw [if_neg hcmp]

/-- Updating a storage slot with EVM/Solidity semantics preserves `get?` at a different slot.
    Nonzero writes insert; zero writes erase. -/
theorem storage_get?_update_ne (storage : Storage) (readSlot writeSlot val : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((if val == (default : UInt256) then storage.erase writeSlot
      else storage.insert writeSlot val).get? readSlot) =
      storage.get? readSlot := by
  by_cases hzero : (val == (default : UInt256)) = true
  · simpa [hzero] using storage_get?_erase_ne storage readSlot writeSlot hne
  · simpa [hzero] using storage_get?_insert_ne storage readSlot writeSlot val hne

/-- Lookup-level same-key overwrite for `ExtTreeMap.insert`. -/
theorem extTreeMap_get?_insert_insert_self {α β : Type}
    {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : Std.ExtTreeMap α β cmp) (write read : α) (v1 v2 : β) :
    ((m.insert write v1).insert write v2).get? read =
      (m.insert write v2).get? read := by
  change ((m.insert write v1).insert write v2)[read]? = (m.insert write v2)[read]?
  by_cases heq : write = read
  · subst read
    simp
  · have hcmp : cmp write read ≠ .eq := by
      intro h
      exact heq (Std.LawfulEqCmp.eq_of_compare h)
    simp [Std.ExtTreeMap.getElem?_insert, hcmp]

theorem extTreeMap_insert_insert_self {α β : Type} {cmp : α → α → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (m : Std.ExtTreeMap α β cmp) (key : α) (v1 v2 : β) :
    (m.insert key v1).insert key v2 = m.insert key v2 := by
  apply Std.ExtTreeMap.ext_getElem?
  intro read
  exact extTreeMap_get?_insert_insert_self m key read v1 v2

/-- Reading after an arbitrary zero-aware storage update followed by a same-slot nonzero insert is
    the same as reading after just the final insert. -/
theorem storage_getD_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).getD readSlot
        (default : UInt256)) =
      (storage.insert writeSlot val2).getD readSlot (default : UInt256) := by
  by_cases hread : readSlot = writeSlot
  · subst readSlot
    simp
  · by_cases hzero : val1 = (default : UInt256)
    · simp only [hzero, if_true]
      rw [storage_getD_insert_ne (storage.erase writeSlot) readSlot writeSlot val2 default hread]
      rw [storage_getD_insert_ne storage readSlot writeSlot val2 default hread]
      rw [storage_getD_erase_ne storage readSlot writeSlot default hread]
    · simp only [hzero, if_false]
      rw [extTreeMap_insert_insert_self]

/-- `get?` after an arbitrary zero-aware storage update followed by a same-slot nonzero insert is
    the same as `get?` after just the final insert. -/
theorem storage_get?_update_insert_self (storage : Storage)
    (writeSlot readSlot val1 val2 : UInt256) :
    (((if val1 = (default : UInt256) then storage.erase writeSlot
        else storage.insert writeSlot val1).insert writeSlot val2).get? readSlot) =
      (storage.insert writeSlot val2).get? readSlot := by
  by_cases hread : readSlot = writeSlot
  · subst readSlot
    simp
  · by_cases hzero : val1 = (default : UInt256)
    · simp only [hzero, if_true]
      rw [storage_get?_insert_ne (storage.erase writeSlot) readSlot writeSlot val2 hread]
      rw [storage_get?_insert_ne storage readSlot writeSlot val2 hread]
      rw [storage_get?_erase_ne storage readSlot writeSlot hread]
    · simp only [hzero, if_false]
      exact extTreeMap_get?_insert_insert_self storage writeSlot readSlot val1 val2

/-- Inserting one account preserves lookup at a different address. -/
theorem accountMap_get?_insert_ne (σ : AccountMap) (read write : AccountAddress)
    (acc : Account) (hne : read ≠ write) :
    (σ.insert write acc).get? read = σ.get? read := by
  change (σ.insert write acc)[read]? = σ[read]?
  rw [Std.ExtTreeMap.getElem?_insert]
  have hcmp : compare write read ≠ .eq := by
    intro hcmp
    exact hne (Std.LawfulEqCmp.eq_of_compare hcmp).symm
  rw [if_neg hcmp]

/-- A zero-aware `SSTORE` to one storage slot preserves an observable read from a different slot
    of the same account. -/
theorem sstoreAccountMap_storage_getD_ne (σ : AccountMap) (a : AccountAddress)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    (((sstoreAccountMap a σ writeSlot val).get? a).option (default : UInt256)
        (fun acc => acc.storage.getD readSlot (default : UInt256))) =
      ((σ.get? a).option (default : UInt256)
        (fun acc => acc.storage.getD readSlot (default : UInt256))) := by
  unfold sstoreAccountMap
  cases hσ : σ.get? a with
  | none =>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, hσ, Option.option]
  | some acc =>
      simp [Option.option]
      by_cases hzero : val = (default : UInt256)
      · simpa [hzero] using storage_getD_update_ne acc.storage readSlot writeSlot val default hne
      · simpa [hzero] using storage_getD_update_ne acc.storage readSlot writeSlot val default hne

theorem accountStorageStateEq_storage_getD {σ τ : AccountMap}
    (hστ : accountStorageStateEq σ τ) (addr : AccountAddress) (slot defaultValue : UInt256) :
    ((σ.get? addr).option defaultValue (fun acc => acc.storage.getD slot defaultValue)) =
      ((τ.get? addr).option defaultValue (fun acc => acc.storage.getD slot defaultValue)) := by
  specialize hστ addr
  cases hσ : σ.get? addr <;> cases hτ : τ.get? addr <;>
    simp [Std.ExtTreeMap.getD_eq_getD_getElem?,
      ← Std.ExtTreeMap.get?_eq_getElem?, hσ, hτ, Option.option] at hστ ⊢
  all_goals
    have hstorage := congrArg (fun storage => storage.getD slot defaultValue) hστ.1
    simpa [Std.ExtTreeMap.getD_eq_getD_getElem?] using hstorage

/-- A final insert overwrites any earlier zero-aware write to the same slot. -/
theorem storage_update_insert_self (storage : Storage) (slot val1 val2 : UInt256) :
    (if val1 = (default : UInt256) then storage.erase slot
      else storage.insert slot val1).insert slot val2 =
      storage.insert slot val2 := by
  apply Std.ExtTreeMap.ext_getElem?
  intro readSlot
  change
    (((if val1 = (default : UInt256) then storage.erase slot
      else storage.insert slot val1).insert slot val2).get? readSlot) =
      (storage.insert slot val2).get? readSlot
  exact storage_get?_update_insert_self storage slot readSlot val1 val2

theorem sstoreAccountMap_absent_same {owner : AccountAddress} {τ : AccountMap}
    {slot val : UInt256} (hmissing : τ.get? owner = none) :
    sstoreAccountMap owner τ slot val = τ := by
  unfold sstoreAccountMap
  rw [hmissing]
  rfl

theorem storageStore_executionEnv (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_eq_accountMap_update (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    {evm with accountMap := (Solm.EVM.storageStore evm addr slot val).accountMap} =
      Solm.EVM.storageStore evm addr slot val := by
  unfold Solm.EVM.storageStore
  cases evm.lookupAccount addr <;> simp [Option.option, State.setAccount]

theorem stateAccountMapUpdate_trans {a b c : EVM.State}
    (hab : {a with accountMap := b.accountMap} = b)
    (hbc : {b with accountMap := c.accountMap} = c) :
    {a with accountMap := c.accountMap} = c := by
  calc
    {a with accountMap := c.accountMap} =
        {{a with accountMap := b.accountMap} with accountMap := c.accountMap} := rfl
    _ = {b with accountMap := c.accountMap} := by rw [hab]
    _ = c := hbc

theorem storageStore_absent (evm : EVM.State) (addr : AccountAddress)
    (hmissing : evm.accountMap.get? addr = none) (slot val : UInt256) :
    Solm.EVM.storageStore evm addr slot val = evm := by
  simp [Solm.EVM.storageStore, State.lookupAccount,
    -Std.ExtTreeMap.get?_eq_getElem?, hmissing, Option.option]

theorem writeSolidityBytesDataWordsFrom_absent_same :
    ∀ {evm : EVM.State} {baseSlot : UInt256} {value : ByteArray} {idx fuel : Nat},
      evm.accountMap.get? evm.executionEnv.codeOwner = none →
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
    (writeSolidityBytesDataWordsFrom evm baseSlot bytes idx fuel).substate.createdAccounts =
      evm.substate.createdAccounts := by
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
    (clearSolidityBytesDataWordsFrom evm baseSlot idx fuel).substate.createdAccounts =
      evm.substate.createdAccounts := by
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
    (hmissing : evm.accountMap.get? evm.executionEnv.codeOwner = none) :
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

theorem storageLoad_storageStore_same_present (evm : EVM.State) (addr : AccountAddress)
    {acc : Account} (hacc : evm.accountMap.get? addr = some acc) (slot val : UInt256) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr slot val) addr slot = val := by
  unfold Solm.EVM.storageLoad Solm.EVM.storageStore State.lookupAccount
  rw [hacc]
  simp only [Option.option]
  unfold State.setAccount
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]
  unfold Account.updateStorage Account.lookupStorage
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    subst val
    simp
    rfl
  · simp [hzero]

theorem storageLocStore_address_offset1_after_bool_true (evm : EVM.State)
    (slot val : UInt256) {acc : Account} (hacc : evm.lookupAccount evm.executionEnv.codeOwner =
      some acc) (hcanon : val.toNat < EVM.addressModulus)
    {hbound : (1 : Fin 32).val + (20 : Fin 33).val - 1 < 32} :
    storageLocStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (UInt256.lor
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
              (UInt256.lnot ⟨255⟩)) ⟨1⟩))
        { slot := slot, offset := 1, size := 20, hbound := hbound, type := .address }
        (.address (AccountAddress.ofNat val.toNat)) =
      some (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (UInt256.lor
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
              (UInt256.lnot ⟨255⟩)) ⟨1⟩))
        evm.executionEnv.codeOwner slot
        (UInt256.lor ⟨1⟩
          (UInt256.lor
            (UInt256.mul (UInt256.land val solcAddrMask) ⟨256⟩)
            (UInt256.land
              (UInt256.lnot
                (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))))) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord_address_ofNat_canonical val hcanon, bind, Option.bind]
  rw [storageStore_executionEnv]
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let boolWord := UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩
  have hload :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot boolWord)
          evm.executionEnv.codeOwner slot = boolWord := by
    exact storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner
      (by simpa [State.lookupAccount] using hacc) slot boolWord
  rw [hload]
  apply congrArg some
  apply congrArg
    (fun w => Solm.EVM.storageStore
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot boolWord)
      evm.executionEnv.codeOwner slot w)
  apply u256_inj
  rw [packedAddressAfterBoolTrueWord_eq old val hcanon]
  change fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof boolWord).1.take 1 ++
        (EVM.Word.toBytesLEWithSizeProof val).1.take 20 ++
        (EVM.Word.toBytesLEWithSizeProof boolWord).1.drop 21) =
    (UInt256.ofNat (1 + val.toNat * 2 ^ 8 + old.toNat / 2 ^ 168 * 2 ^ 168)).toNat
  rw [packedAddressAfterBoolTrueBytes_toNat old val hcanon]
  have hlt := packedAddressAfterBoolTrueNat_lt_size old val hcanon
  rw [ulit_toNat' _ hlt]

theorem storageLoad_storageStore_ne (evm : EVM.State) (addr : AccountAddress)
    {readSlot writeSlot val : UInt256} (hne : readSlot ≠ writeSlot) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr writeSlot val) addr readSlot =
      Solm.EVM.storageLoad evm addr readSlot := by
  simp only [Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount]
  cases hacc : evm.accountMap.get? addr with
  | none =>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option]
  | some acc =>
      simp only [Option.option]
      unfold State.setAccount
      simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]
      unfold Account.updateStorage Account.lookupStorage
      by_cases hzero : (val == (default : UInt256)) = true
      · have hval : val = (default : UInt256) := eq_of_beq hzero
        subst val
        simp [storage_getD_erase_ne acc.storage readSlot writeSlot ⟨0⟩ hne]
      · simp [hzero, storage_getD_insert_ne acc.storage readSlot writeSlot val ⟨0⟩ hne]

structure EVMStateEquiv (evm₁ evm₂ : EVM.State) : Prop where
  executionEnv : evm₁.executionEnv = evm₂.executionEnv
  accountMap : evm₁.accountMap = evm₂.accountMap

namespace EVMStateEquiv

theorem initState {σ₁ σ₀₁ σ₂ σ₀₂ A I g}
    (hAccounts : σ₁ = σ₂) :
    EVMStateEquiv (initState σ₁ σ₀₁ g A I)
      (initState σ₂ σ₀₂ g A I) :=
  ⟨rfl, by simpa [initState] using hAccounts⟩

theorem storageLoad {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256) :
    Solm.EVM.storageLoad evm₁ addr₁ slot = Solm.EVM.storageLoad evm₂ addr₂ slot := by
  subst addr₂
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, h.accountMap]

theorem storageLoad_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner slot := by
  rw [h.executionEnv]
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, h.accountMap]

theorem storageStore {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256)
    {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv (Solm.EVM.storageStore evm₁ addr₁ slot val₁)
      (Solm.EVM.storageStore evm₂ addr₂ slot val₂) := by
  subst addr₂
  subst val₂
  refine ⟨?_, ?_⟩
  · rw [storageStore_executionEnv, storageStore_executionEnv]
    exact h.executionEnv
  · simpa [storageStore_accountMap] using
      congrArg (fun accounts => sstoreAccountMap addr₁ accounts slot val₁) h.accountMap

theorem storageStore_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner slot val₂) :=
  h.storageStore (congrArg ExecutionEnv.codeOwner h.executionEnv) slot hval

end EVMStateEquiv

private theorem u256_val_ne_of_ne {x y : UInt256} (h : x ≠ y) : x.val ≠ y.val := by
  intro hv
  apply h
  cases x with
  | mk xv =>
    cases y with
    | mk yv =>
      cases hv
      rfl

theorem storage_update_erase_self (storage : Storage) (slot val : UInt256) :
    (if val = (default : UInt256) then storage.erase slot
      else storage.insert slot val).erase slot = storage.erase slot := by
  apply Std.ExtTreeMap.ext_getElem?
  intro read
  change
    (((if val = (default : UInt256) then storage.erase slot
      else storage.insert slot val).erase slot).get? read) =
      (storage.erase slot).get? read
  by_cases hread : read = slot
  · subst read
    simp [Std.ExtTreeMap.get?_eq_getElem?]
  · by_cases hzero : val = (default : UInt256)
    · simp only [hzero, if_true]
      rw [storage_get?_erase_ne (storage.erase slot) read slot hread,
        storage_get?_erase_ne storage read slot hread]
    · simp only [hzero, if_false]
      rw [storage_get?_erase_ne (storage.insert slot val) read slot hread,
        storage_get?_insert_ne storage read slot val hread,
        storage_get?_erase_ne storage read slot hread]

/-- The final write determines the account map at a slot, including zero-as-erase writes. -/
theorem sstoreAccountMap_self_update
    (σ : AccountMap) (a : AccountAddress) (slot val1 val2 : UInt256) :
    sstoreAccountMap a σ slot val2 =
      sstoreAccountMap a (sstoreAccountMap a σ slot val1) slot val2 := by
  unfold sstoreAccountMap
  cases hσ : σ.get? a with
  | none =>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, hσ, Option.option]
  | some acc =>
      simp only [Option.option]
      by_cases hzero1 : val1 = (default : UInt256) <;>
        by_cases hzero2 : val2 = (default : UInt256)
      all_goals
        simp [hzero1, hzero2]
        rw [extTreeMap_insert_insert_self]
        congr 1
        first
        | simpa [hzero1] using (storage_update_erase_self acc.storage slot val1).symm
        | simpa [hzero1] using (storage_update_insert_self acc.storage slot val1 val2).symm

/-- Writes to distinct slots of one account commute as extensional map equalities. -/
theorem sstoreAccountMap_comm
    (σ : AccountMap) (a : AccountAddress) (slot1 val1 slot2 val2 : UInt256)
    (hne : slot1 ≠ slot2) :
    sstoreAccountMap a (sstoreAccountMap a σ slot1 val1) slot2 val2 =
      sstoreAccountMap a (sstoreAccountMap a σ slot2 val2) slot1 val1 := by
  apply Std.ExtTreeMap.ext_getElem?
  intro addr
  change
    (sstoreAccountMap a (sstoreAccountMap a σ slot1 val1) slot2 val2).get? addr =
      (sstoreAccountMap a (sstoreAccountMap a σ slot2 val2) slot1 val1).get? addr
  by_cases haddr : addr = a
  · subst addr
    unfold sstoreAccountMap
    cases hσ : σ.get? a with
    | none =>
        simp [-Std.ExtTreeMap.get?_eq_getElem?, hσ, Option.option]
    | some acc =>
        by_cases hzero1 : val1 = (default : UInt256) <;>
          by_cases hzero2 : val2 = (default : UInt256)
        all_goals
          simp [Option.option, hzero1, hzero2]
          apply Std.ExtTreeMap.ext_getElem?
          intro readSlot
          change _ = _
          have hval12 := u256_val_ne_of_ne hne
          have hval21 := u256_val_ne_of_ne (Ne.symm hne)
          by_cases hread1 : readSlot = slot1
          · subst readSlot
            simp [Std.ExtTreeMap.getElem_insert, hval21]
          · by_cases hread2 : readSlot = slot2
            · subst readSlot
              simp [Std.ExtTreeMap.getElem_insert, hval12]
            ·
              have hval1 := u256_val_ne_of_ne (Ne.symm hread1)
              have hval2 := u256_val_ne_of_ne (Ne.symm hread2)
              simp [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert,
                hval1, hval2]
  · have hother (τ : AccountMap) (slot val : UInt256) :
        (sstoreAccountMap a τ slot val).get? addr = τ.get? addr := by
      unfold sstoreAccountMap
      cases hτ : τ.get? a with
      | none => simp [Option.option]
      | some acc =>
          simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?]
          simpa only [Std.ExtTreeMap.get?_eq_getElem?] using
            accountMap_get?_insert_ne τ addr a _ haddr
    simp only [hother]

theorem valueToWord_bytes32_word (word : UInt256) :
    valueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE word)) = some word := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size word
  simpa [valueToWord, keyValueToWord, hlen] using
    congrArg some (keyValueToWord_fixedBytes32 word)

theorem storageWordWrite_accounts {σ : AccountMap} {evm : EVM.State}
    (h : σ = evm.accountMap) (slot : UInt256) (f : UInt256 → UInt256) :
    (sstoreAccountMap evm.executionEnv.codeOwner σ slot
        (f (Reasoning.Reach.solcSlotWord σ evm.executionEnv slot))) =
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))).accountMap := by
  rw [storageStore_accountMap, h]
  rfl

/-- General uint256 scalar store: truncates the stored `Int` to a word via `wordOfInt`.
    LIBRARY CANDIDATE: `Reasoning.Storage` (generalizes `storageLocStore_uint256`). -/
theorem storageLocStore_uint256_int (evm : EVM.State) (slot : UInt256) (n : Int) :
    storageLocStore evm (uint256Loc slot) (.int n) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt n)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (EVM.wordOfInt n).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem storageStore_σ₀ (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_substate (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

theorem sstoreAccountMap_storage_getD_self_present
    (σ : AccountMap) (a : AccountAddress) {acc : Account}
    (hacc : σ.get? a = some acc) (slot val : UInt256) :
    (((sstoreAccountMap a σ slot val).get? a).option (default : UInt256)
        (fun acc => acc.storage.getD slot (default : UInt256))) = val := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option]
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    subst val
    simp
  · simp [hzero]

theorem storageLocStore_uint8 (evm : EVM.State) (slot value : UInt256)
    (hc : value.toNat < 256) :
    storageLocStore evm
      { slot := slot, offset := 0, size := 1, hbound := by decide,
        type := .int (.uint ⟨8, by decide⟩) }
      (.int (Int.ofNat value.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) value)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof value).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 1) = _
  rw [fromBytes'_append, fromBytes'_take_wordLE_land_mask value 1 (by decide),
    fromBytes'_drop_wordLE]
  rw [u256_lor_toNat, packedSetFalseWord_toNat]
  rw [nat_lor_comm]
  rw [show 256 = 2 ^ 8 by decide, Nat.mul_comm (2 ^ 8)]
  rw [nat_lor_shift_add value.toNat _ 8 hc]
  have hbound := (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
  rw [Nat.mod_eq_of_lt (show value.toNat +
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 8 * 2 ^ 8 <
        UInt256.size from by
      change _ < 2 ^ 256
      change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256
        at hbound
      omega)]
  simp only [List.length_take, (EVM.Word.toBytesLEWithSizeProof value).2]
  change (UInt256.land value ⟨255⟩).toNat +
    256 * ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 256) = _
  rw [lowByteClean hc]
  omega

theorem canonicalAddress_eq_zero_iff (value : UInt256)
    (hc : value.toNat < EVM.addressModulus) :
    AccountAddress.ofNat value.toNat = AccountAddress.ofNat 0 ↔ value = ⟨0⟩ := by
  constructor
  · intro h
    have hv := congrArg (fun a => valueToWord (.address a)) h
    dsimp only at hv
    rw [valueToWord_address_ofNat_canonical value hc] at hv
    exact Option.some.inj hv
  · intro h
    rw [h]
    rfl

theorem sourceAddress_eq_iff (I : ExecutionEnv) (w : UInt256)
    (hc : w.toNat < EVM.addressModulus) :
    I.source = AccountAddress.ofNat w.toNat ↔ solcSourceWord I = w := by
  constructor
  · intro h
    have hw := congrArg (fun a => valueToWord (.address a)) h
    dsimp only at hw
    rw [valueToWord_address_ofNat_canonical w hc] at hw
    exact Option.some.inj hw
  · intro h
    rw [← h, solcSource_ofNat]

theorem wordToElemBool (word : UInt256) :
    wordToElem .bool word = .bool (!decide (word = ⟨0⟩)) := by
  by_cases hw : word = ⟨0⟩
  · subst word; rfl
  · have hv : (word.val == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      apply hw
      exact u256_inj (congrArg Fin.val he)
    simp [wordToElem, hw, hv]

end Reasoning.Theory

/-! ## State projections and storage round trips -/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

theorem storageStore_executionEnv' (evm : EVM.State)
    (addr : AccountAddress) (slot value : UInt256) :
    (Solm.EVM.storageStore evm addr slot value).executionEnv = evm.executionEnv := by
  unfold Solm.EVM.storageStore
  cases State.lookupAccount evm addr <;> rfl

theorem slotWord_eq_of_accounts_eq
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256)
    (henv : evm.executionEnv = I)
    (hAccounts : σ = evm.accountMap) :
  solcSlotWord σ I slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord, henv, hAccounts]

theorem storageStore_present (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : evm.accountMap.get? addr = some acc) :
    ∃ acc', (Solm.EVM.storageStore evm addr slot val).accountMap.get? addr = some acc' := by
  unfold Solm.EVM.storageStore State.lookupAccount
  rw [hacc]
  simp [Option.option, State.setAccount, Std.ExtTreeMap.getElem?_insert_self]

theorem keyValueToWord_int_ofNat_of_lt {n : Nat} (hn : n < UInt256.size) :
    keyValueToWord (.int (Int.ofNat n)) = UInt256.ofNat n := by
  have hto : (UInt256.ofNat n).toNat = n := ulit_toNat' n hn
  simpa [hto] using keyValueToWord_uint256 (UInt256.ofNat n)

theorem storageLocStore_uint256_pred (evm : EVM.State) (slot len : UInt256)
    (hpos : 0 < len.toNat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat len.toNat - 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (len.toNat - 1))) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_natCast_pred_of_pos len hpos, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat (len.toNat - 1))).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
        (UInt256.ofNat (len.toNat - 1)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem storageLocStore_uint256_succ (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat val.toNat + 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (val + ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_natCast_succ, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (val + ⟨1⟩)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (val + ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem storageLocStore_uint256_ofNat (evm : EVM.State) (slot : UInt256) (n : Nat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat n)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (EVM.word (Int.ofNat n).toNat)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  rw [wordOfInt_nonneg]
  · have hslen := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.word (Int.ofNat n).toNat)).2
    congr 2
    apply u256_inj
    show fromBytes'
        (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
          ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
        (EVM.word (Int.ofNat n).toNat).toNat
    rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
      List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
      List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]
  · simp

theorem storageStore_σ0 (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.get? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_substate' (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).substate = evm.substate := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.get? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem sstoreAccountMap_get?_owner_some_of_some
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.get? a = some acc) :
    ∃ acc', (sstoreAccountMap a σ slot val).get? a = some acc' := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self]
  exact ⟨if val == (default : UInt256) then { acc with storage := acc.storage.erase slot }
    else { acc with storage := acc.storage.insert slot val }, rfl⟩

theorem sstoreAccountMap_storage_getD_self_zero_present
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.get? a = some acc) :
    (((sstoreAccountMap a σ slot val).get? a).option (⟨0⟩ : UInt256)
        (fun acc => acc.storage.getD slot ⟨0⟩)) = val := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (⟨0⟩ : UInt256) := by
      simpa using eq_of_beq hzero
    subst val
    simp [hzero]
  · have hfalse : (val == (default : UInt256)) = false := by
      cases h : (val == (default : UInt256)) <;> simp [h] at hzero ⊢
    simp [hfalse]

theorem keyValueToWord_uint256_natCast (w : UInt256) :
    keyValueToWord (.int ((w.toNat : Nat) : Int)) = w := by
  simpa using keyValueToWord_uint256 w

theorem evmState_ext {s t : EVM.State}
    (hAccountMap : s.accountMap = t.accountMap)
    (hSigma0 : s.σ₀ = t.σ₀)
    (hGas : s.totalGasUsedInBlock = t.totalGasUsedInBlock)
    (hReceipts : s.transactionReceipts = t.transactionReceipts)
    (hSubstate : s.substate = t.substate)
    (hEnv : s.executionEnv = t.executionEnv)
    (hMachine : s.machineState = t.machineState) : s = t := by
  cases s
  cases t
  simp_all

theorem storageStore_totalGasUsedInBlock
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).totalGasUsedInBlock =
      evm.totalGasUsedInBlock := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_transactionReceipts
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).transactionReceipts = evm.transactionReceipts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_machineState
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).machineState = evm.machineState := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

/-- Bridge the Solm `storageLoad` at `I.codeOwner` to the EVM-side `solcSlotWord`. -/
theorem storageLoad_eq_solcSlotWord (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256) :
    Solm.EVM.storageLoad evm I.codeOwner slot = solcSlotWord evm.accountMap I slot := by
  simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Ethereum.Account.lookupStorage]

theorem solcSlotWordAt_sstore_ne (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    solcSlotWordAt readSlot (sstoreAccountMap I.codeOwner σ writeSlot val) I =
      solcSlotWordAt readSlot σ I := by
  exact sstoreAccountMap_storage_getD_ne σ I.codeOwner readSlot writeSlot val hne

theorem solcSlotWord_sstore_ne' (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    solcSlotWord (sstoreAccountMap I.codeOwner σ writeSlot val) I readSlot =
      solcSlotWord σ I readSlot := by
  simpa [solcSlotWordAt] using solcSlotWordAt_sstore_ne σ I readSlot writeSlot val hne

/-- `storageLoad` at `evm`'s own code owner reads `solcSlotWord` over `evm.accountMap`. -/
theorem storageLoad_eq_solcSlotWord_of_codeOwner_eq (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      solcSlotWord evm.accountMap I slot := by
  rw [hco]
  simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Ethereum.Account.lookupStorage]

/-- `storageStore` leaves `executionEnv` untouched. -/
theorem storageStore_executionEnv_eq (evm : EVM.State) (a : AccountAddress) (s v : UInt256) :
    (Solm.EVM.storageStore evm a s v).executionEnv = evm.executionEnv := by
  exact Reasoning.Theory.storageStore_executionEnv evm a s v

theorem storageLoad_storageStore_self_nonzero (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) {acc : Account} (hacc : evm.lookupAccount a = some acc)
    (_hval : (val == default) = false) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm a slot val) a slot = val :=
  storageLoad_storageStore_same_present evm a (by simpa [State.lookupAccount] using hacc) slot val

theorem storageLocLoad_bool_offset0' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32} :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool }
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem storageLocLoad_bool_offset0_false' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool false := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_false evm slot hzero

theorem storageLocLoad_bool_offset0_true' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool true := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_true evm slot hnz

theorem storageLocStore_bool_true_offset0' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32} :
    storageLocStore evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool }
        (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  simpa [boolOffset0Loc] using storageLocStore_bool_true_offset0 evm slot

@[simp] theorem storageStore_executionEnv'' (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).executionEnv = evm.executionEnv := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.get? a <;> rfl

theorem accountMap_balance_eq_of_eq {σ τ : AccountMap}
    (hστ : σ = τ) (addr : AccountAddress) :
    (σ.get? addr |>.elim ⟨0⟩ (·.balance)) =
      (τ.get? addr |>.elim ⟨0⟩ (·.balance)) := by
  rw [hστ]

theorem storageLocStore_word_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint256Loc slot) (.int n) = some evm' := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

/-- `solcSlotWordAt` transports across `EVMStateEquiv` (same codeOwner storage view). -/
theorem solcSlotWordAt_eq_of_equiv {a b : EVM.State} (h : EVMStateEquiv a b) (s : UInt256) :
    solcSlotWordAt s a.accountMap a.executionEnv = solcSlotWordAt s b.accountMap b.executionEnv :=
      by
  rw [h.executionEnv, h.accountMap]

/-- On `evm0`, a code-owner storage read at `slot` is the layout word `solcSlotWordAt slot σ I`. -/
theorem storageLoad_initState_ofUInt256_solcSlotWordAt {σ σ₀ A I} {g : UInt256} (slot : UInt256) :
    Solm.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner slot =
      solcSlotWordAt slot σ I := by
  have hco : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
      I.codeOwner := rfl
  rw [hco, codeOwnerStorageWord_initState]
  rfl

theorem storageLoad_after_initState_store
    {σ σ₀ A I} {g : Sat256} (writeSlot readSlot val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner writeSlot val)
        I.codeOwner readSlot =
      solcSlotWordAt readSlot (sstoreAccountMap I.codeOwner σ writeSlot val) I := by
  simp [Solm.EVM.storageLoad, solcSlotWordAt, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount,
    Account.lookupStorage]

theorem storageLoad_after_initState_store₂
    {σ σ₀ A I} {g : Sat256}
    (slot₁ slot₂ readSlot val₁ val₂ : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState σ σ₀ g A I)
            I.codeOwner slot₁ val₁)
          I.codeOwner slot₂ val₂)
        I.codeOwner readSlot =
      solcSlotWordAt readSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ slot₁ val₁) slot₂ val₂) I := by
  simp [Solm.EVM.storageLoad, solcSlotWordAt, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount, Account.lookupStorage]

theorem storageLoad_after_initState_store₃
    {σ σ₀ A I} {g : Sat256}
    (slot₁ slot₂ slot₃ readSlot val₁ val₂ val₃ : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore (initState σ σ₀ g A I)
              I.codeOwner slot₁ val₁)
            I.codeOwner slot₂ val₂)
          I.codeOwner slot₃ val₃)
        I.codeOwner readSlot =
      solcSlotWordAt readSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ slot₁ val₁) slot₂ val₂)
          slot₃ val₃) I := by
  simp [Solm.EVM.storageLoad, solcSlotWordAt, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount, Account.lookupStorage]

theorem storageLoad_codeOwner_eq_solcSlotWordAt (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      solcSlotWordAt slot evm.accountMap I := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWordAt,
    solcSlotWord, howner]

/-- The storage word at an arbitrary slot, as read from `initState σ`. -/
theorem storageLoad_initState_solcSlotWord {σ σ₀ A I} {g : Sat256} (slot : UInt256) :
    EVM.storageLoad (initState σ σ₀ g A I)
        (initState σ σ₀ g A I).executionEnv.codeOwner slot =
      solcSlotWord σ I slot := by
  simp [EVM.storageLoad, State.lookupAccount, initState, solcSlotWord, solcSlotWord,
    Account.lookupStorage]

end Reasoning.Theory
