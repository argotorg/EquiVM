import ABI.Decode
import Reasoning.Memory

/-!
# ABI — calldata decode and return-value encode facts

Small, reusable facts for evaluating the Solm ABI decoder on common static calldata shapes.
These lemmas keep examples from unfolding the recursive ABI decoder with large `simp` calls.
-/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM

/-- The ABI type `uint256`, named here so contracts do not need to import another example's spec. -/
abbrev abiUInt256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))

/-- The EVM/Solm word decoded from calldata at byte offset `off`. -/
abbrev calldataWord (cd : ByteArray) (off : Nat) : UInt256 :=
  uInt256OfByteArray (cd.readBytes off 32)

/-! ## Generic scalar-word calldata decoding -/

/--
ABI types whose top-level calldata representation is a single scalar word and whose decoder path
runs through `decodeABIWord?`.

This intentionally excludes fixed bytes/function for now: they are also one word on the wire, but
their decoder validates padding bytes rather than only the decoded word. Arrays, tuples, strings,
and dynamic bytes are a later structural tier.
-/
def isABIScalarWordType : ABIType → Bool
  | .elem (.bytes _) => false
  | .elem .function => false
  | .elem _ => true
  | _ => false

/-- Decode one scalar ABI word at byte offset `start`. -/
def decodeScalarWord? (ty : ABIType) (bytes : List UInt8) (start : Nat) :
    Option (Solm.Value × Nat) := do
  let word <- readWord? bytes start
  let value <- decodeABIWord? ty word
  some (value, start + 32)

/-- Decode a flat list of scalar ABI words, advancing by 32 bytes per type. -/
def decodeScalarWords? : List ABIType → List UInt8 → Nat → Option (List Solm.Value)
  | [], _, _ => some []
  | ty :: tys, bytes, cursor => do
      let (value, _) <- decodeScalarWord? ty bytes cursor
      let values <- decodeScalarWords? tys bytes (cursor + 32)
      some (value :: values)

theorem isABIScalarWordType_dynamic {ty : ABIType} (h : isABIScalarWordType ty = true) :
    isDynamicABIType ty = false := by
  cases ty <;> simp [isABIScalarWordType, isDynamicABIType] at h ⊢

theorem isABIScalarWordTypes_any_dynamic {types : List ABIType}
    (h : types.all isABIScalarWordType = true) :
    types.any isDynamicABIType = false := by
  induction types with
  | nil => rfl
  | cons ty tys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      rcases h with ⟨hty, htys⟩
      simp [List.any_cons, isABIScalarWordType_dynamic hty, ih htys]

theorem isABIScalarWordTypes_total_guard {types : List ABIType}
    (h : types.all isABIScalarWordType = true) :
    solcTotalSizeDynamicGuard types = false := by
  cases types with
  | nil => rfl
  | cons ty tys =>
      cases tys with
      | nil =>
          cases ty <;> simp [solcTotalSizeDynamicGuard, isABIScalarWordType] at h ⊢
      | cons ty' tys' =>
          simp [solcTotalSizeDynamicGuard]

theorem isABIScalarWordType_size {ty : ABIType} (h : isABIScalarWordType ty = true) :
    staticABIEncodedSize? ty = some 32 := by
  cases ty <;> simp [isABIScalarWordType, staticABIEncodedSize?] at h ⊢

theorem decodeABIValue_scalarWord_eq {ty : ABIType} {bytes : List UInt8} {start : Nat}
    (h : isABIScalarWordType ty = true) :
    decodeABIValue? ty bytes start = decodeScalarWord? ty bytes start := by
  cases ty with
  | elem e =>
      cases e <;> simp [isABIScalarWordType, decodeABIValue?, decodeScalarWord?] at h ⊢
  | array ty n => simp [isABIScalarWordType] at h
  | bytes => simp [isABIScalarWordType] at h
  | string => simp [isABIScalarWordType] at h
  | dynamicArray ty => simp [isABIScalarWordType] at h
  | tuple tys => simp [isABIScalarWordType] at h

theorem abiTupleHeadSize_scalarWords_eq {types : List ABIType}
    (hscalar : types.all isABIScalarWordType = true) :
    abiTupleHeadSize? types = some (32 * types.length) := by
  induction types with
  | nil => simp [abiTupleHeadSize?]
  | cons ty tys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hscalar
      rcases hscalar with ⟨hty, htys⟩
      have hdyn := isABIScalarWordType_dynamic hty
      have hsize := isABIScalarWordType_size hty
      rw [abiTupleHeadSize?]
      rw [ih htys]
      rw [hdyn]
      simp only [Bool.false_eq_true, if_false]
      rw [hsize]
      simp [List.length_cons, Nat.mul_add, Nat.add_comm]

theorem decodeABIValues_scalarWords_eq {types : List ABIType} {bytes : List UInt8}
    {cursor total : Nat}
    (hscalar : types.all isABIScalarWordType = true)
    (hend : cursor + 32 * types.length = total) :
    decodeABIValues? types bytes 0 cursor total total =
      match decodeScalarWords? types bytes cursor with
      | some values => some (values, total)
      | none => none := by
  induction types generalizing cursor with
  | nil =>
      simp [decodeABIValues?, decodeScalarWords?] at hend ⊢
  | cons ty tys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hscalar
      rcases hscalar with ⟨hty, htys⟩
      have hdyn := isABIScalarWordType_dynamic hty
      have hsize := isABIScalarWordType_size hty
      rw [decodeABIValues?]
      rw [hdyn]
      simp only [Bool.false_eq_true, if_false]
      rw [hsize]
      rw [decodeABIValue_scalarWord_eq (bytes := bytes) (start := 0 + cursor) hty]
      simp only [Nat.zero_add, decodeScalarWords?, decodeScalarWord?]
      cases readWord? bytes cursor with
      | none => simp
      | some word =>
        simp
        cases decodeABIWord? ty word with
        | none => simp
        | some value =>
          simp
          have hle : cursor + 32 ≤ total := by
            rw [← hend]
            simp [List.length_cons]
          rw [max_eq_left hle]
          have hend' : cursor + 32 + 32 * tys.length = total := by
            simpa [List.length_cons, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using hend
          rw [ih htys hend']
          cases decodeScalarWords? tys bytes (cursor + 32) <;> simp

/--
Evaluate `decodeCalldata` for any flat list of scalar-word ABI types.

The theorem leaves per-word validity to `decodeScalarWords?`: e.g. `address` may fail if the word
is non-canonical, `bool` may fail if it is not `0`/`1`, and short calldata fails when a word cannot
be read.
-/
theorem decodeCalldata_scalarWords_eq {names : List Solm.Ident} {types : List ABIType}
    {cd : ByteArray} (hscalar : types.all isABIScalarWordType = true) :
    decodeCalldata names types cd =
      if cd.toList.length < 4 then
        none
      else if types.isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length then
        none
      else
        match decodeScalarWords? types (cd.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues names values ∅
        | none => none := by
  unfold decodeCalldata
  by_cases hlt : cd.toList.length < 4
  · conv_lhs => rw [if_pos hlt]
    conv_rhs => rw [if_pos hlt]
  · conv_lhs => rw [if_neg hlt]
    conv_rhs => rw [if_neg hlt]
    cases types with
    | nil =>
        simp [decodeCalldata.decodeArgs, decodeScalarWords?]
        cases names <;> rfl
    | cons ty tys =>
        by_cases hbig : (ty :: tys).isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length
        · conv_lhs => rw [if_pos hbig]
          conv_rhs => rw [if_pos hbig]
        · conv_lhs => rw [if_neg hbig]
          conv_rhs => rw [if_neg hbig]
          have hnotDynamicHuge :
              ¬ (solcTotalSizeDynamicGuard (ty :: tys) = true ∧
                2 ^ 255 ≤ cd.toList.length) := by
            intro h
            have hany := isABIScalarWordTypes_total_guard hscalar
            rw [hany] at h
            cases h.1
          conv_lhs => rw [if_neg hnotDynamicHuge]
          have hhead := abiTupleHeadSize_scalarWords_eq hscalar
          simp only [decodeCalldata.decodeArgs]
          rw [hhead]
          simp only [bind, Option.bind]
          have hvals := decodeABIValues_scalarWords_eq (types := ty :: tys)
            (bytes := cd.toList.drop 4) (cursor := 0) (total := 32 * (ty :: tys).length)
            hscalar (by simp)
          rw [hvals]
          cases decodeScalarWords? (ty :: tys) (cd.toList.drop 4) 0 with
          | none => rfl
          | some values =>
              simp only
              cases decodeCalldata.insertValues names values ∅ <;> rfl

/-! ## Common scalar calldata convenience lemmas -/

theorem decodeABIValue_address_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hcanon : (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.addressModulus) :
    decodeABIValue? (.elem .address) bytes start
      = some (.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  simp only
  rw [if_pos (show (↑(ABI.bytesToWord (List.take 32 (List.drop start bytes))).val : ℕ)
    < EVM.addressModulus from hcanon)]
  rfl

theorem decodeABIValue_address_none_noncanon {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.addressModulus) :
    decodeABIValue? (.elem .address) bytes start = none := by
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  simp only
  rw [if_neg (show ¬ (↑(ABI.bytesToWord (List.take 32 (List.drop start bytes))).val : ℕ)
    < EVM.addressModulus from hnc)]

theorem decodeABIValue_address_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? (.elem .address) bytes start = none := by
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_neg hshort]

theorem decodeABIValue_uint256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? abiUInt256 bytes start
      = some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
          start + 32) := by
  simp only [abiUInt256, decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp only
  rw [if_neg (show ¬ ((256 : ℕ) = 0) from by decide)]
  rw [if_pos (show (↑(ABI.bytesToWord (List.take 32 (List.drop start bytes))).val : ℕ)
    < EVM.twoPow 256 from (ABI.bytesToWord ((bytes.drop start).take 32)).val.isLt)]
  rfl

theorem decodeABIValue_uint256_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? abiUInt256 bytes start = none := by
  simp only [abiUInt256, decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_neg hshort]

theorem decodeScalarWord_address_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hcanon : (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWord? (.elem .address) bytes start
      = some (.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .address) (bytes := bytes)
    (start := start) (by decide)]
  exact decodeABIValue_address_ok hlen hcanon

theorem decodeScalarWord_address_none_noncanon {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWord? (.elem .address) bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .address) (bytes := bytes)
    (start := start) (by decide)]
  exact decodeABIValue_address_none_noncanon hlen hnc

theorem decodeScalarWord_address_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? (.elem .address) bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .address) (bytes := bytes)
    (start := start) (by decide)]
  exact decodeABIValue_address_none_short hshort

theorem decodeScalarWord_uint256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? abiUInt256 bytes start
      = some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
          start + 32) := by
  rw [← decodeABIValue_scalarWord_eq (ty := abiUInt256) (bytes := bytes)
    (start := start) (by decide)]
  exact decodeABIValue_uint256_ok hlen

theorem decodeScalarWord_uint256_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? abiUInt256 bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := abiUInt256) (bytes := bytes)
    (start := start) (by decide)]
  exact decodeABIValue_uint256_none_short hshort

theorem decodeCalldata_empty_ok {cd : ByteArray} (hsz4 : 4 ≤ cd.size) :
    decodeCalldata [] [] cd = some (∅ : Solm.Store) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := []) (types := []) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp [decodeScalarWords?, decodeCalldata.insertValues]

theorem decodeScalarWords_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeScalarWords? [abiUInt256] bytes 0 =
      some [.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)] := by
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_uint256_ok (start := 0) (by simpa using hlen0)]
  rfl

theorem decodeScalarWords_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWords? [abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]; omega
  rw [decodeScalarWord_uint256_none_short (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem decodeCalldata_uint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_uint256_ok (bytes := cd.toList.drop 4) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]

theorem decodeCalldata_uint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hshort : cd.size < 36) :
    decodeCalldata [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  by_cases hsz4 : cd.size < 4
  · rw [if_pos (by rw [htlen]; omega : cd.toList.length < 4)]
  · rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
    rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
    rw [decodeScalarWords_uint256_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_uint256_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

private theorem readNat?_calldata_head4 {cd : ByteArray}
    (hsz36 : 36 ≤ cd.size) :
    ABI.readNat? (cd.toList.drop 4) 0 = some (calldataWord cd 4).toNat := by
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  simp [ABI.readNat?, ABI.readWord?, ABI.readBytes?, htake4, hword4, UInt256.toNat]

theorem decodeCalldata_string_none_offset_huge {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hoff : ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    decodeCalldata [x] [.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hread := readNat?_calldata_head4 (cd := cd) hsz36
  rw [if_neg hlen4]
  by_cases hhuge : [ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length
  · rw [if_pos hhuge]
  · rw [if_neg hhuge]
    by_cases htotalHuge :
        solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
    · rw [if_pos htotalHuge]
    · rw [if_neg htotalHuge]
      change (match decodeCalldata.decodeArgs [x] [.string] (cd.toList.drop 4) ∅ with
        | some (store, _) => some store
        | none => none) = none
      simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
        ABI.isDynamicABIType, hread, bind, Option.bind_some, if_true]
      rw [if_pos hoff]

theorem decodeCalldata_bytes_none_offset_huge {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hoff : ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    decodeCalldata [x] [.bytes] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hread := readNat?_calldata_head4 (cd := cd) hsz36
  rw [if_neg hlen4]
  by_cases hhuge : [ABIType.bytes].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length
  · rw [if_pos hhuge]
  · rw [if_neg hhuge]
    by_cases htotalHuge :
        solcTotalSizeDynamicGuard [ABIType.bytes] = true ∧ 2 ^ 255 ≤ cd.toList.length
    · rw [if_pos htotalHuge]
    · rw [if_neg htotalHuge]
      change (match decodeCalldata.decodeArgs [x] [.bytes] (cd.toList.drop 4) ∅ with
        | some (store, _) => some store
        | none => none) = none
      simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
        ABI.isDynamicABIType, hread, bind, Option.bind_some, if_true]
      rw [if_pos hoff]

theorem decodeCalldata_string_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem decodeCalldata_string_none_total_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 ≤ cd.size) :
    decodeCalldata [x] [.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hargs : [ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length
  · rw [if_pos hargs]
  · rw [if_neg hargs]
    rw [if_pos]
    exact ⟨by decide, by rw [htlen]; exact hbig⟩

theorem decodeCalldata_bytes_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [.bytes] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

private theorem readNat?_calldata_dynamic_length_none {cd : ByteArray}
    {off : Nat} (hshort : cd.size < 4 + off + 32) :
    ABI.readNat? (cd.toList.drop 4) off = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnotRead : ¬ 32 ≤ (cd.toList.drop 4).length - off := by
    rw [List.length_drop, htlen]
    omega
  have hnotRead' : ¬ 32 ≤ cd.toList.length - (4 + off) := by
    omega
  unfold ABI.readNat? ABI.readWord? ABI.readBytes?
  simp [List.drop_drop, hnotRead']

theorem decode_word_at_eq_any (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size) :
    ABI.bytesToWord ((cd.toList.drop off).take 32) =
      uInt256OfByteArray (cd.readBytes off 32) := by
  by_cases hoff : off < 2 ^ 64
  · exact decode_word_at_eq cd off hsz hoff
  · rw [uInt256OfByteArray_eq]
    unfold ABI.bytesToWord fromByteArrayBigEndian
    congr 2
    rw [byteArray_toList_eq (cd.readBytes off 32)]
    unfold ByteArray.readBytes
    rw [if_neg]
    · simp only [ByteArray.toList_data_append, byteArray_zeroes_toList]
      have hreadSize : (ByteArray.mk (((cd.toList.drop off).take 32).toArray)).size = 32 := by
        show (((cd.toList.drop off).take 32).toArray).size = 32
        have hlen : ((cd.toList.drop off).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          rw [byteArray_toList_eq, Array.length_toList]
          have hds : cd.data.size = cd.size := rfl
          rw [hds]
          omega
        simp [hlen]
      rw [hreadSize]
      simp [byteArray_toList_eq]
    · simp
      exact Nat.le_of_not_gt hoff

private theorem readNat?_calldata_dynamic_length {cd : ByteArray}
    {off : Nat} (hlen : 4 + off + 32 ≤ cd.size) :
    ABI.readNat? (cd.toList.drop 4) off = some (calldataWord cd (4 + off)).toNat := by
  have htake : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.drop_drop, List.length_take, List.length_drop, htlen]
    omega
  have hword :
      ABI.bytesToWord (((cd.toList.drop 4).drop off).take 32) = calldataWord cd (4 + off) := by
    rw [List.drop_drop]
    exact decode_word_at_eq_any cd (4 + off) (by omega)
  unfold ABI.readNat? ABI.readWord? ABI.readBytes?
  rw [if_pos htake]
  have hword' :
      ABI.bytesToWord ((cd.toList.drop (4 + off)).take 32) = calldataWord cd (4 + off) := by
    simpa [List.drop_drop] using hword
  simpa [hword', UInt256.toNat]

private theorem readBytes?_calldata_dynamic_payload {cd : ByteArray}
    {off len : Nat}
    (hpayload : (((cd.toList.drop 4).drop (off + 32)).take len).length = len) :
    ABI.readBytes? (cd.toList.drop 4) (off + 32) len =
      some (((cd.toList.drop 4).drop (off + 32)).take len) := by
  unfold ABI.readBytes?
  rw [if_pos hpayload]

private theorem readBytes?_calldata_dynamic_payload_none {cd : ByteArray}
    {off len : Nat}
    (hpayload : (((cd.toList.drop 4).drop (off + 32)).take len).length ≠ len) :
    ABI.readBytes? (cd.toList.drop 4) (off + 32) len = none := by
  unfold ABI.readBytes?
  rw [if_neg hpayload]

theorem decodeCalldata_string_some {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hsizeSign : cd.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    decodeCalldata [x] [.string] cd =
      some ((∅ : Solm.Store).insert x
        (.bytes (ByteArray.mk
          ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
            (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray)))) := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hreadHead := readNat?_calldata_head4 (cd := cd) hsz36
  have hnotHuge :
      ¬ ([ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  have hnotTotalHuge :
      ¬ (solcTotalSizeDynamicGuard [ABIType.string] = true ∧
        2 ^ 255 ≤ cd.toList.length) := by
    intro h
    rw [htlen] at h
    omega
  have hreadLen :
      ABI.readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat =
        some (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat :=
    readNat?_calldata_dynamic_length hlenWord
  have hreadPayload :
      ABI.readBytes? (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32)
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat =
        some (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :=
    readBytes?_calldata_dynamic_payload hpayload
  rw [if_neg hlen4, if_neg hnotHuge, if_neg hnotTotalHuge]
  change (match decodeCalldata.decodeArgs [x] [.string] (cd.toList.drop 4) ∅ with
    | some (store, _) => some store
    | none => none) =
      some ((∅ : Solm.Store).insert x
        (.bytes (ByteArray.mk
          ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
            (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray))))
  simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
    ABI.isDynamicABIType, hreadHead, bind, Option.bind_some, if_true]
  rw [if_neg hoffMax]
  simp only [ABI.decodeABIValue?, Nat.zero_add, bind, Option.bind]
  rw [hreadLen]
  simp [hlenMax, hreadPayload, decodeCalldata.insertValues]

theorem decodeCalldata_bytes_some {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hsizeSign : cd.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    decodeCalldata [x] [.bytes] cd =
      some ((∅ : Solm.Store).insert x
        (.bytes (ByteArray.mk
          ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
            (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray)))) := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hreadHead := readNat?_calldata_head4 (cd := cd) hsz36
  have hnotHuge :
      ¬ ([ABIType.bytes].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  have hnotTotalHuge :
      ¬ (solcTotalSizeDynamicGuard [ABIType.bytes] = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    intro h
    rw [htlen] at h
    omega
  have hreadLen :
      ABI.readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat =
        some (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat :=
    readNat?_calldata_dynamic_length hlenWord
  have hreadPayload :
      ABI.readBytes? (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32)
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat =
        some (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :=
    readBytes?_calldata_dynamic_payload hpayload
  rw [if_neg hlen4, if_neg hnotHuge, if_neg hnotTotalHuge]
  change (match decodeCalldata.decodeArgs [x] [.bytes] (cd.toList.drop 4) ∅ with
    | some (store, _) => some store
    | none => none) =
      some ((∅ : Solm.Store).insert x
        (.bytes (ByteArray.mk
          ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
            (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray))))
  simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
    ABI.isDynamicABIType, hreadHead, bind, Option.bind_some, if_true]
  rw [if_neg hoffMax]
  simp only [ABI.decodeABIValue?, Nat.zero_add, bind, Option.bind]
  rw [hreadLen]
  simp [hlenMax, hreadPayload, decodeCalldata.insertValues]

theorem decodeCalldata_string_none_payload_short {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    decodeCalldata [x] [.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hreadHead := readNat?_calldata_head4 (cd := cd) hsz36
  have hnotHuge :
      ¬ ([ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  have hreadLen :
      ABI.readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat =
        some (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat :=
    readNat?_calldata_dynamic_length hlenWord
  have hreadPayload :
      ABI.readBytes? (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32)
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat = none :=
    readBytes?_calldata_dynamic_payload_none hpayload
  rw [if_neg hlen4, if_neg hnotHuge]
  by_cases htotalHuge :
      solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos htotalHuge]
  · rw [if_neg htotalHuge]
    change (match decodeCalldata.decodeArgs [x] [.string] (cd.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = none
    simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
      ABI.isDynamicABIType, hreadHead, bind, Option.bind_some, if_true]
    rw [if_neg hoffMax]
    simp only [ABI.decodeABIValue?, Nat.zero_add, bind, Option.bind]
    rw [hreadLen]
    simp [hlenMax, hreadPayload]

theorem decodeCalldata_string_none_length_huge {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    decodeCalldata [x] [.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hreadHead := readNat?_calldata_head4 (cd := cd) hsz36
  have hnotHuge :
      ¬ ([ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  have hreadLen :
      ABI.readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat =
        some (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat :=
    readNat?_calldata_dynamic_length hlenWord
  rw [if_neg hlen4, if_neg hnotHuge]
  by_cases htotalHuge :
      solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos htotalHuge]
  · rw [if_neg htotalHuge]
    change (match decodeCalldata.decodeArgs [x] [.string] (cd.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = none
    simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
      ABI.isDynamicABIType, hreadHead, bind, Option.bind_some, if_true]
    rw [if_neg hoffMax]
    simp only [ABI.decodeABIValue?, Nat.zero_add, bind, Option.bind]
    rw [hreadLen]
    simp [hlenHuge]

theorem decodeCalldata_bytes_none_payload_short {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    decodeCalldata [x] [.bytes] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hreadHead := readNat?_calldata_head4 (cd := cd) hsz36
  have hnotHuge :
      ¬ ([ABIType.bytes].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  have hreadLen :
      ABI.readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat =
        some (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat :=
    readNat?_calldata_dynamic_length hlenWord
  have hreadPayload :
      ABI.readBytes? (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32)
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat = none :=
    readBytes?_calldata_dynamic_payload_none hpayload
  rw [if_neg hlen4, if_neg hnotHuge]
  by_cases htotalHuge :
      solcTotalSizeDynamicGuard [ABIType.bytes] = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos htotalHuge]
  · rw [if_neg htotalHuge]
    change (match decodeCalldata.decodeArgs [x] [.bytes] (cd.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = none
    simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
      ABI.isDynamicABIType, hreadHead, bind, Option.bind_some, if_true]
    rw [if_neg hoffMax]
    simp only [ABI.decodeABIValue?, Nat.zero_add, bind, Option.bind]
    rw [hreadLen]
    simp [hlenMax, hreadPayload]

theorem decodeCalldata_string_none_length_short {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hshort : cd.size < 4 + (calldataWord cd 4).toNat + 32) :
    decodeCalldata [x] [.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hreadHead := readNat?_calldata_head4 (cd := cd) hsz36
  have hnotHuge :
      ¬ ([ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  have hreadLen :
      ABI.readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat = none :=
    readNat?_calldata_dynamic_length_none hshort
  rw [if_neg hlen4, if_neg hnotHuge]
  by_cases htotalHuge :
      solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos htotalHuge]
  · rw [if_neg htotalHuge]
    change (match decodeCalldata.decodeArgs [x] [.string] (cd.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = none
    simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
      ABI.isDynamicABIType, hreadHead, bind, Option.bind_some, if_true]
    by_cases hoff : ABI.solcMaxU64 < (calldataWord cd 4).toNat
    · rw [if_pos hoff]
    · rw [if_neg hoff]
      simp [ABI.decodeABIValue?, hreadLen]

theorem decodeCalldata_bytes_none_length_short {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hshort : cd.size < 4 + (calldataWord cd 4).toNat + 32) :
    decodeCalldata [x] [.bytes] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen4 : ¬ cd.toList.length < 4 := by
    omega
  have hreadHead := readNat?_calldata_head4 (cd := cd) hsz36
  have hnotHuge :
      ¬ ([ABIType.bytes].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  have hreadLen :
      ABI.readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat = none :=
    readNat?_calldata_dynamic_length_none hshort
  rw [if_neg hlen4, if_neg hnotHuge]
  by_cases htotalHuge :
      solcTotalSizeDynamicGuard [ABIType.bytes] = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos htotalHuge]
  · rw [if_neg htotalHuge]
    change (match decodeCalldata.decodeArgs [x] [.bytes] (cd.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = none
    simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
      ABI.isDynamicABIType, hreadHead, bind, Option.bind_some, if_true]
    by_cases hoff : ABI.solcMaxU64 < (calldataWord cd 4).toNat
    · rw [if_pos hoff]
    · rw [if_neg hoff]
      simp [ABI.decodeABIValue?, hreadLen]

theorem decodeScalarWords_addr_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 32) hlen32]
  rfl

theorem decodeScalarWords_addr_uint256_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_addr_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [.elem .address, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]; omega
    by_cases hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]
      rw [decodeScalarWord_uint256_none_short (start := 32) htake32n]
    · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]

theorem decodeABIValues_addr_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [.elem .address, abiUInt256] bytes 0 0 64 64 =
      some ([.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  rw [decodeABIValues_scalarWords_eq (types := [.elem .address, abiUInt256])
    (bytes := bytes) (cursor := 0) (total := 64) (by decide) (by norm_num)]
  rw [decodeScalarWords_addr_uint256_ok hlen0 hlen32 hcanon]

theorem decodeABIValues_addr_uint256_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [.elem .address, abiUInt256] bytes 0 0 64 64 = none := by
  rw [decodeABIValues_scalarWords_eq (types := [.elem .address, abiUInt256])
    (bytes := bytes) (cursor := 0) (total := 64) (by decide) (by norm_num)]
  rw [decodeScalarWords_addr_uint256_none_noncanon hlen0 hnc]

theorem decodeABIValues_addr_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [.elem .address, abiUInt256] bytes 0 0 64 64 = none := by
  rw [decodeABIValues_scalarWords_eq (types := [.elem .address, abiUInt256])
    (bytes := bytes) (cursor := 0) (total := 64) (by decide) (by norm_num)]
  rw [decodeScalarWords_addr_uint256_none_short hshort]

theorem decodeCalldata_addr_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_uint256_ok (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon)]
  change decodeCalldata.insertValues [x, y]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]

theorem decodeCalldata_addr_uint256_none_noncanon {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_uint256_none_noncanon (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc)]

theorem decodeCalldata_addr_uint256_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_uint256_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_addr_uint256_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩


/-! ## Address-argument calldata decoding (single + two address) -/

/-! ## Single-address calldata decoding -/

theorem decodeScalarWords_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [(.elem .address)] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address] bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  rfl

theorem decodeScalarWords_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [(.elem .address)] bytes 0 = none := by
  change decodeScalarWords? [.elem .address] bytes 0 = none
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWords? [(.elem .address)] bytes 0 = none := by
  change decodeScalarWords? [.elem .address] bytes 0 = none
  simp only [decodeScalarWords?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem decodeCalldata_address_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [(.elem .address)] cd =
      some ((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [(.elem .address)]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_ok (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hcanon)]
  change decodeCalldata.insertValues [x]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]

theorem decodeCalldata_address_none_noncanon {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [(.elem .address)] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [(.elem .address)]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_none_noncanon (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc)]

theorem decodeCalldata_address_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [(.elem .address)] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [(.elem .address)]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

theorem decodeCalldata_address_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [(.elem .address)] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [(.elem .address)]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

/-! ## Two-address calldata decoding -/

theorem decodeScalarWords_address_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [(.elem .address), (.elem .address)] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
      .address (Ethereum.AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)]
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rfl

theorem decodeScalarWords_address_address_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [(.elem .address), (.elem .address)] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_address_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [(.elem .address), (.elem .address)] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

theorem decodeScalarWords_address_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [(.elem .address), (.elem .address)] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]; omega
    by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
        (by simpa using hcanon0)]
      simp only [Option.bind, bind]
      rw [decodeScalarWord_address_none_short (start := 32) htake32n]
    · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
        (by simpa using hcanon0)]
      simp only [Option.bind, bind]

theorem decodeCalldata_address_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [(.elem .address), (.elem .address)]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_ok (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hcanon1)]
  change decodeCalldata.insertValues [x, y]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]
  rw [hword36]

theorem decodeCalldata_address_address_none_noncanon0 {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [(.elem .address), (.elem .address)]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_none_noncanon0 (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc0)]

theorem decodeCalldata_address_address_none_noncanon1 {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [(.elem .address), (.elem .address)]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_none_noncanon1 (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hnc1)]

theorem decodeCalldata_address_address_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [(.elem .address), (.elem .address)]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_address_address_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [(.elem .address), (.elem .address)]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩


/-! ## Return-value (`RETURN`) ABI encoding -/

/-- **Scalar RETURN-encoding core.**  Given a scalar value `v` whose ABI encoding is the 32
    big-endian bytes of the word `w` (`hval`), a single-value `RETURN` encodes to exactly `w`'s
    32-byte word.  This is the shared tail of every scalar return-encoding proof; each scalar type
    (`bool`, `uint256`, `address`, …) supplies only its per-type word fact `hval` (plus the trivial
    `hdyn`/`hhead`). -/
theorem scalarReturnEncoding {t : ABI.ElemType} {v : Solm.Value} {w : EVM.Word}
    (hdyn : isDynamicABIType (.elem t) = false)
    (hhead : abiTupleHeadSize? [(.elem t)] = some 32)
    (hval : encodeABIValue? (.elem t) v = some (EVM.Word.toBytesBE w)) :
    encodeReturnValue? (.elem t) v = some (UInt256.toByteArray w) := by
  rw [toByteArray_eq_toBytesBE,
    show encodeReturnValue? (.elem t) v = encodeReturnValues? [(.elem t)] [v] from rfl]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, encodeABIValuesFrom?, hval, hdyn,
    bind, Option.bind, if_false, Bool.false_eq_true, List.nil_append, List.append_nil]

/-- ABI-encoding `true` is the one-word value `1` (for `bool`-returning functions). -/
theorem boolTrueReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some (UInt256.toByteArray ⟨1⟩) :=
  scalarReturnEncoding (t := .bool) (w := ⟨1⟩) rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
        decide)
    (by simp [encodeABIValue?, encodeABIWord?, Bool.toUInt256_true]; rfl)

/-- ABI-encoding a `uint256` return value is exactly the EVM's returned word bytes. -/
theorem uint256ReturnEncoding (v : UInt256) :
    encodeReturnValue? (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  have hltNat : v.toNat < EVM.twoPow 256 := by
    change v.val.val < EVM.twoPow 256
    exact v.val.isLt
  refine scalarReturnEncoding (t := (.int (.uint ⟨256, by decide⟩))) (w := v) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, hword, hltNat]

end Reasoning.Theory
