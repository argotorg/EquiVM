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

/-- The four-byte fixed ABI width, named here so contracts do not share example-local specs. -/
def abiBytes4Width : Fin 32 := ⟨3, by decide⟩

/-- The ABI type `bytes4`, named here so contracts do not share example-local specs. -/
abbrev abiBytes4 : ABIType := .elem (.bytes abiBytes4Width)

/-- The thirty-two-byte fixed ABI width, named here so contracts do not share specs. -/
def abiBytes32Width : Fin 32 := ⟨31, by decide⟩

/-- The ABI type `bytes32`, named here so contracts do not share example-local specs. -/
abbrev abiBytes32 : ABIType := .elem (.bytes abiBytes32Width)

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

theorem readWord?_some_length {bytes : List UInt8} {offset : Nat} {word : EVM.Word}
    (h : readWord? bytes offset = some word) : offset + 32 ≤ bytes.length := by
  unfold readWord? at h
  cases hread : readBytes? bytes offset 32 with
  | none => simp [hread] at h
  | some slice =>
      unfold readBytes? at hread
      by_cases hlen : ((bytes.drop offset).take 32).length = 32
      · have hmin : min 32 (bytes.length - offset) = 32 := by
          simpa [List.length_take, List.length_drop] using hlen
        have hle : 32 ≤ bytes.length - offset := by
          by_cases hle : 32 ≤ bytes.length - offset
          · exact hle
          · have hlt : bytes.length - offset < 32 := Nat.lt_of_not_ge hle
            have hmin' : min 32 (bytes.length - offset) = bytes.length - offset :=
              Nat.min_eq_right (Nat.le_of_lt hlt)
            rw [hmin'] at hmin
            omega
        omega
      · change
          (if ((bytes.drop offset).take 32).length = 32 then
            some ((bytes.drop offset).take 32)
          else none) = some slice at hread
        simp at hread
        omega

theorem decodeScalarWord?_some_length {ty : ABIType} {bytes : List UInt8} {cursor : Nat}
    {value : Solm.Value × Nat}
    (h : decodeScalarWord? ty bytes cursor = some value) : cursor + 32 ≤ bytes.length := by
  unfold decodeScalarWord? at h
  cases hread : readWord? bytes cursor with
  | none => simp [hread] at h
  | some word => exact readWord?_some_length hread

theorem decodeScalarWords?_some_length {types : List ABIType} {bytes : List UInt8}
    {cursor : Nat} {values : List Solm.Value}
    (hcursor : cursor ≤ bytes.length)
    (h : decodeScalarWords? types bytes cursor = some values) :
    cursor + 32 * types.length ≤ bytes.length := by
  induction types generalizing cursor values with
  | nil =>
      simp [decodeScalarWords?] at h
      simpa using hcursor
  | cons ty tys ih =>
      unfold decodeScalarWords? at h
      cases hword : decodeScalarWord? ty bytes cursor with
      | none => simp [hword] at h
      | some value =>
          cases hrest : decodeScalarWords? tys bytes (cursor + 32) with
          | none => simp [hword, hrest] at h
          | some restValues =>
              have hhead := decodeScalarWord?_some_length hword
              have htail := ih hhead hrest
              simp [hword, hrest] at h
              simpa [List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using htail

theorem isABIScalarWordType_dynamic {ty : ABIType} (h : isABIScalarWordType ty = true) :
    isDynamicABIType ty = false := by
  cases ty <;> simp [isABIScalarWordType, isDynamicABIType] at h ⊢

theorem isABIScalarWordTypes_any_dynamic_false {types : List ABIType}
    (h : types.all isABIScalarWordType = true) :
    types.any isDynamicABIType = false := by
  induction types with
  | nil => rfl
  | cons ty tys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      rcases h with ⟨hty, htys⟩
      simp [isABIScalarWordType_dynamic hty, ih htys]

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
      else if types.isEmpty = false ∧ usesLegacyAddressTypes types = false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length then
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
    have hdynFalse : types.any isDynamicABIType = false :=
      isABIScalarWordTypes_any_dynamic_false hscalar
    conv_lhs => rw [if_neg (by simp [hdynFalse])]
    cases types with
    | nil =>
        simp [decodeCalldata.decodeArgs, decodeScalarWords?]
        cases names <;> rfl
    | cons ty tys =>
        by_cases hbig : (ty :: tys).isEmpty = false ∧
            usesLegacyAddressTypes (ty :: tys) = false ∧
            2 ^ 255 ≤ (cd.toList.drop 4).length
        · conv_lhs => rw [if_pos hbig]
          conv_rhs => rw [if_pos hbig]
        · conv_lhs => rw [if_neg hbig]
          conv_rhs => rw [if_neg hbig]
          have htotalFalse : solcTotalSizeDynamicGuard (ty :: tys) = false :=
            isABIScalarWordTypes_total_guard hscalar
          conv_lhs => rw [if_neg (by simp [htotalFalse])]
          have hhead := abiTupleHeadSize_scalarWords_eq hscalar
          simp only [decodeCalldata.decodeArgs]
          rw [hhead]
          simp only [bind, Option.bind]
          have hvals := decodeABIValues_scalarWords_eq (types := ty :: tys)
            (bytes := cd.toList.drop 4) (cursor := 0) (total := 32 * (ty :: tys).length)
            hscalar (by simp)
          rw [hvals]
          cases hscal : decodeScalarWords? (ty :: tys) (cd.toList.drop 4) 0 with
          | none =>
              by_cases hshort : (cd.toList.drop 4).length < 32 * (ty :: tys).length
              · rw [if_pos hshort]
              · rw [if_neg hshort]
          | some values =>
              have hnotShort : ¬(cd.toList.drop 4).length < 32 * (ty :: tys).length := by
                have hlen := decodeScalarWords?_some_length (Nat.zero_le _) hscal
                omega
              rw [if_neg hnotShort]
              simp only
              cases decodeCalldata.insertValues names values ∅ <;> rfl

theorem decodeReturnValues_scalarWords_eq {types : List ABIType} {returndata : ByteArray}
    (hscalar : types.all isABIScalarWordType = true) :
    ABI.decodeReturnValues? types returndata =
      if types.isEmpty = false ∧ 2 ^ 255 ≤ returndata.toList.length then
        none
      else
        match decodeScalarWords? types returndata.toList 0 with
        | some values => some values
        | none => none := by
  unfold ABI.decodeReturnValues?
  by_cases hbig : types.isEmpty = false ∧ 2 ^ 255 ≤ returndata.toList.length
  · conv_lhs => rw [if_pos hbig]
    conv_rhs => rw [if_pos hbig]
  · conv_lhs => rw [if_neg hbig]
    conv_rhs => rw [if_neg hbig]
    cases types with
    | nil =>
        simp [ABI.abiTupleHeadSize?, decodeScalarWords?, ABI.decodeABIValues?]
    | cons ty tys =>
        have hhead := abiTupleHeadSize_scalarWords_eq hscalar
        rw [hhead]
        simp only [bind, Option.bind]
        have hvals := decodeABIValues_scalarWords_eq (types := ty :: tys)
          (bytes := returndata.toList) (cursor := 0) (total := 32 * (ty :: tys).length)
          hscalar (by simp)
        rw [hvals]
        cases decodeScalarWords? (ty :: tys) returndata.toList 0 <;> rfl

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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
    rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩

/-! ## Dynamic string calldata convenience lemmas -/

theorem readNat_drop4_zero_eq_calldataWord {cd : ByteArray}
    (hsz36 : 36 ≤ cd.size) :
    readNat? (cd.toList.drop 4) 0 = some (calldataWord cd 4).toNat := by
  unfold readNat? readWord?
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  rw [hread]
  have hword : bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  simp only [Option.bind, bind, hword]
  rfl

theorem readNat_drop4_dynamic_eq_calldataWord {cd : ByteArray}
    (_hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size) :
    readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat =
      some (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat := by
  unfold readNat? readWord?
  have hread : readBytes? (cd.toList.drop 4) (calldataWord cd 4).toNat 32 =
      some (((cd.toList.drop 4).drop (calldataWord cd 4).toNat).take 32) := by
    unfold readBytes?
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    have hlen :
        (((cd.toList.drop 4).drop (calldataWord cd 4).toNat).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_pos hlen]
  rw [hread]
  have hword :
      bytesToWord (((cd.toList.drop 4).drop (calldataWord cd 4).toNat).take 32) =
        calldataWord cd (4 + (calldataWord cd 4).toNat) := by
    have h := decode_word_at_eq_any cd (4 + (calldataWord cd 4).toNat) hlenWord
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simp only [Option.bind, bind, hword]
  rfl

theorem readBytes_drop4_string_payload {cd : ByteArray}
    (hpayload :
      (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    readBytes? (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32)
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat =
      some (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) := by
  unfold readBytes?
  rw [if_pos hpayload]

theorem decodeCalldata_string_none_total_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 ≤ cd.size) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  unfold decodeCalldata
  by_cases hlt4 : cd.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    have hdyn : [ABIType.string].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length := by
      exact ⟨by simp [isDynamicABIType], by rw [htlen]; exact hbig⟩
    rw [if_pos hdyn]

theorem decodeCalldata_string_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [ABIType.string] cd = none :=
  decodeCalldata_string_none_total_huge (x := x) (by omega)

theorem decodeCalldata_string_none_offset_huge {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size)
    (hoff : solcMaxU64 < (calldataWord cd 4).toNat) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn : [ABIType.string].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.string].isEmpty = false ∧ usesLegacyAddressTypes [ABIType.string] = false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      by_cases htotal : solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
      · rw [if_pos htotal]
      · rw [if_neg htotal]
        have hread := readNat_drop4_zero_eq_calldataWord (cd := cd) hsz36
        simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
          abiTupleHeadSize?, hread, hoff]

theorem decodeCalldata_string_none_length_short {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hshort : cd.size < 4 + (calldataWord cd 4).toNat + 32) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn : [ABIType.string].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.string].isEmpty = false ∧ usesLegacyAddressTypes [ABIType.string] = false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      by_cases htotal : solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
      · rw [if_pos htotal]
      · rw [if_neg htotal]
        by_cases hoff : solcMaxU64 < (calldataWord cd 4).toNat
        · have hread := readNat_drop4_zero_eq_calldataWord (cd := cd) hsz36
          simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
            abiTupleHeadSize?, hread, hoff]
        · have hreadOff := readNat_drop4_zero_eq_calldataWord (cd := cd) hsz36
          have hreadLen :
              readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat = none := by
            unfold readNat? readWord? readBytes?
            have hlen :
                ¬ (((cd.toList.drop 4).drop (calldataWord cd 4).toNat).take 32).length = 32 := by
              rw [List.length_take, List.length_drop, List.length_drop, htlen]
              omega
            rw [if_neg hlen]
            rfl
          simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
            abiTupleHeadSize?, hreadOff, hoff, hreadLen]

theorem decodeCalldata_string_none_length_huge {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenHuge : solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn : [ABIType.string].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.string].isEmpty = false ∧ usesLegacyAddressTypes [ABIType.string] = false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      by_cases htotal : solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
      · rw [if_pos htotal]
      · rw [if_neg htotal]
        have hreadOff := readNat_drop4_zero_eq_calldataWord (cd := cd) hsz36
        have hreadLen := readNat_drop4_dynamic_eq_calldataWord (cd := cd) hoffMax hlenWord
        simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
          abiTupleHeadSize?, hreadOff, hoffMax, hreadLen, hlenHuge]

theorem decodeCalldata_string_none_payload_short {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn : [ABIType.string].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.string].isEmpty = false ∧ usesLegacyAddressTypes [ABIType.string] = false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      by_cases htotal : solcTotalSizeDynamicGuard [ABIType.string] = true ∧ 2 ^ 255 ≤ cd.toList.length
      · rw [if_pos htotal]
      · rw [if_neg htotal]
        have hreadOff := readNat_drop4_zero_eq_calldataWord (cd := cd) hsz36
        have hreadLen := readNat_drop4_dynamic_eq_calldataWord (cd := cd) hoffMax hlenWord
        have hpayloadRead :
            readBytes? (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32)
              (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat = none := by
          unfold readBytes?
          rw [if_neg hpayload]
        simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
          abiTupleHeadSize?, hreadOff, hoffMax, hreadLen, hlenMax, hpayloadRead]

axiom decodeCalldata_string_some {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hsizeSign : cd.size < 2 ^ 255)
    (hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    decodeCalldata [x] [ABIType.string] cd =
      some ((∅ : Solm.Store).insert x (.bytes (ByteArray.mk
        (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray)))

/-! ## Fixed-bytes calldata convenience lemmas -/

abbrev calldataBytes4Arg (cd : ByteArray) : List UInt8 :=
  ((cd.toList.drop 4).take 32).take 4

theorem decodeCalldata_bytes4_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((cd.toList.drop 4).take 32) 4 28 = some ()) :
    decodeCalldata [x] [abiBytes4] cd =
      some ((∅ : Solm.Store).insert x (.fixedBytes abiBytes4Width (calldataBytes4Arg cd))) := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes4].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([abiBytes4].isEmpty = false ∧ usesLegacyAddressTypes [abiBytes4] = false ∧
      2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rintro ⟨_, _, hlen⟩
    rw [List.length_drop, htlen] at hlen
    omega
  rw [if_neg hnotHuge]
  have hnotTotal : ¬ (solcTotalSizeDynamicGuard [abiBytes4] = true ∧
      2 ^ 255 ≤ cd.toList.length) := by
    simp [solcTotalSizeDynamicGuard]
  rw [if_neg hnotTotal]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, abiBytes4, ABI.decodeABIValues?,
    ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread, hpad,
    calldataBytes4Arg, abiBytes4Width, hnotArgShort]

theorem decodeCalldata_bytes4_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [abiBytes4] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes4].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([abiBytes4].isEmpty = false ∧ usesLegacyAddressTypes [abiBytes4] = false ∧
      2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rintro ⟨_, _, hlen⟩
    rw [List.length_drop, htlen] at hlen
    omega
  rw [if_neg hnotHuge]
  have hnotTotal : ¬ (solcTotalSizeDynamicGuard [abiBytes4] = true ∧
      2 ^ 255 ≤ cd.toList.length) := by
    simp [solcTotalSizeDynamicGuard]
  rw [if_neg hnotTotal]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, abiBytes4, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem decodeCalldata_bytes4_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [abiBytes4] cd = none := by
  unfold decodeCalldata
  by_cases hlt4 : cd.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have hnotDyn : ¬ ([abiBytes4].any isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length) := by
      simp [abiBytes4, isDynamicABIType]
    rw [if_neg hnotDyn]
    have hHuge : [abiBytes4].isEmpty = false ∧ usesLegacyAddressTypes [abiBytes4] = false ∧
        2 ^ 255 ≤ (cd.toList.drop 4).length := by
      refine ⟨by simp, by native_decide, ?_⟩
      have htlen : cd.toList.length = cd.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_drop, htlen]
      omega
    rw [if_pos hHuge]

theorem decodeCalldata_bytes4_none_pad {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((cd.toList.drop 4).take 32) 4 28 = none) :
    decodeCalldata [x] [abiBytes4] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes4].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([abiBytes4].isEmpty = false ∧ usesLegacyAddressTypes [abiBytes4] = false ∧
      2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rintro ⟨_, _, hlen⟩
    rw [List.length_drop, htlen] at hlen
    omega
  rw [if_neg hnotHuge]
  have hnotTotal : ¬ (solcTotalSizeDynamicGuard [abiBytes4] = true ∧
      2 ^ 255 ≤ cd.toList.length) := by
    simp [solcTotalSizeDynamicGuard]
  rw [if_neg hnotTotal]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  simp [decodeCalldata.decodeArgs, abiBytes4, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread, hpad, abiBytes4Width]

theorem decodeCalldata_bytes32_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x] [abiBytes32] cd =
      some ((∅ : Solm.Store).insert x (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([abiBytes32].isEmpty = false ∧ usesLegacyAddressTypes [abiBytes32] = false ∧
      2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rintro ⟨_, _, hlen⟩
    rw [List.length_drop, htlen] at hlen
    omega
  rw [if_neg hnotHuge]
  have hnotTotal : ¬ (solcTotalSizeDynamicGuard [abiBytes32] = true ∧
      2 ^ 255 ≤ cd.toList.length) := by
    simp [solcTotalSizeDynamicGuard]
  rw [if_neg hnotTotal]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hpad : zeroPadding? ((cd.toList.drop 4).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?
    simp
  have htake : List.take 32 ((cd.toList.drop 4).take 32) = (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, abiBytes32, ABI.decodeABIValues?,
    ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread, hpad,
    abiBytes32Width, htake, hnotArgShort]

theorem decodeCalldata_bytes32_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [abiBytes32] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([abiBytes32].isEmpty = false ∧ usesLegacyAddressTypes [abiBytes32] = false ∧
      2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rintro ⟨_, _, hlen⟩
    rw [List.length_drop, htlen] at hlen
    omega
  rw [if_neg hnotHuge]
  have hnotTotal : ¬ (solcTotalSizeDynamicGuard [abiBytes32] = true ∧
      2 ^ 255 ≤ cd.toList.length) := by
    simp [solcTotalSizeDynamicGuard]
  rw [if_neg hnotTotal]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, abiBytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem decodeCalldata_bytes32_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [abiBytes32] cd = none := by
  unfold decodeCalldata
  by_cases hlt4 : cd.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length) := by
      simp [abiBytes32, isDynamicABIType]
    rw [if_neg hnotDyn]
    have hHuge : [abiBytes32].isEmpty = false ∧ usesLegacyAddressTypes [abiBytes32] = false ∧
        2 ^ 255 ≤ (cd.toList.drop 4).length := by
      refine ⟨by simp, by native_decide, ?_⟩
      have htlen : cd.toList.length = cd.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_drop, htlen]
      omega
    rw [if_pos hHuge]

/-! ## Fixed bytes32 plus address calldata decoding -/

theorem decodeABIValue_bytes32_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? abiBytes32 bytes start =
      some (.fixedBytes abiBytes32Width ((bytes.drop start).take 32), start + 32) := by
  simp only [abiBytes32, abiBytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
  rw [if_pos hlen]
  simp [zeroPadding?, readBytes?]

theorem decodeABIValue_bytes32_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? abiBytes32 bytes start = none := by
  simp only [abiBytes32, abiBytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
  rw [if_neg hshort]

theorem decodeABIValues_bytes32_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [abiBytes32, .elem .address] bytes 0 0 64 64 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  have hcanonVal :
      ↑(ABI.bytesToWord (List.take 32 (List.drop 32 bytes))).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hcanon
  rw [if_pos hcanonVal]
  simp [UInt256.toNat]

theorem decodeABIValues_bytes32_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, .elem .address] bytes 0 0 64 64 = none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem decodeABIValues_bytes32_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [abiBytes32, .elem .address] bytes 0 0 64 64 = none := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  have hncVal :
      ¬ ↑(ABI.bytesToWord (List.take 32 (List.drop 32 bytes))).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hnc
  rw [if_neg hncVal]
  simp

theorem decodeCalldata_bytes32_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, .elem .address] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanon)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decodeCalldata_bytes32_address_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, .elem .address] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]
  rw [if_pos (by rw [List.length_drop, htlen]; omega : (cd.toList.drop 4).length < 64)]

theorem decodeCalldata_bytes32_address_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_pos]
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩

theorem decodeCalldata_bytes32_address_none_noncanon {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, .elem .address] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_none_noncanon (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hnc)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]

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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩


/-! ## Address-and-bool calldata decoding -/

theorem decodeScalarWord_bool_ok_zero {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hzero : ABI.bytesToWord ((bytes.drop start).take 32) = ⟨0⟩) :
    decodeScalarWord? (.elem .bool) bytes start = some (.bool false, start + 32) := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  simp [hzero]

theorem decodeScalarWord_bool_ok_one {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hone : ABI.bytesToWord ((bytes.drop start).take 32) = ⟨1⟩) :
    decodeScalarWord? (.elem .bool) bytes start = some (.bool true, start + 32) := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  simp [hone, UInt256.size]

theorem decodeScalarWord_bool_none_noncanon {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hnz : ABI.bytesToWord ((bytes.drop start).take 32) ≠ ⟨0⟩)
    (hno : ABI.bytesToWord ((bytes.drop start).take 32) ≠ ⟨1⟩) :
    decodeScalarWord? (.elem .bool) bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  have hnzNat : ¬ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat = 0 := by
    intro h
    exact hnz (uint256_toNat_eq_zero h)
  have hnoNat : ¬ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat = 1 := by
    intro h
    apply hno
    apply u256_inj
    simpa [UInt256.toNat] using h
  dsimp only [Option.bind]
  rw [if_neg (by simpa [UInt256.toNat] using hnzNat),
    if_neg (by simpa [UInt256.toNat] using hnoNat)]

theorem decodeScalarWord_bool_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? (.elem .bool) bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_neg hshort]

theorem decodeScalarWords_addr_bool_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hbool :
      ABI.bytesToWord ((bytes.drop 32).take 32) = ⟨0⟩ ∨
      ABI.bytesToWord ((bytes.drop 32).take 32) = ⟨1⟩) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        wordToElem .bool (ABI.bytesToWord ((bytes.drop 32).take 32))] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  simp only [Option.bind, bind]
  rcases hbool with hzero | hone
  · rw [decodeScalarWord_bool_ok_zero (start := 32) hlen32 hzero]
    simp [wordToElem, hzero]
  · rw [decodeScalarWord_bool_ok_one (start := 32) hlen32 hone]
    simp [wordToElem, hone]

theorem decodeScalarWords_addr_bool_none_noncanon_addr {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_addr_bool_none_noncanon_bool {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnz : ABI.bytesToWord ((bytes.drop 32).take 32) ≠ ⟨0⟩)
    (hno : ABI.bytesToWord ((bytes.drop 32).take 32) ≠ ⟨1⟩) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_bool_none_noncanon (start := 32) hlen32 hnz hno]

theorem decodeScalarWords_addr_bool_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    by_cases hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]
      rw [decodeScalarWord_bool_none_short (start := 32) htake32n]
    · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]

theorem decodeCalldata_addr_bool_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hbool : calldataWord cd 36 = ⟨0⟩ ∨ calldataWord cd 36 = ⟨1⟩) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (wordToElem .bool (calldataWord cd 36))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_ok (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon) (by
      rcases hbool with hzero | hone
      · left
        rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
            simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
        exact hzero
      · right
        rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
            simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
        exact hone)]
  change decodeCalldata.insertValues [x, y]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        wordToElem .bool (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32))] ∅ =
    some (((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (wordToElem .bool (calldataWord cd 36)))
  simp [decodeCalldata.insertValues]
  rw [hword4]
  rw [hword36]

theorem decodeCalldata_addr_bool_none_noncanon_addr {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_none_noncanon_addr (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc)]

theorem decodeCalldata_addr_bool_none_noncanon_bool {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnz : calldataWord cd 36 ≠ ⟨0⟩) (hno : calldataWord cd 36 ≠ ⟨1⟩) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_none_noncanon_bool (bytes := cd.toList.drop 4)
    htake4 htake36' (by rw [hword4]; exact hcanon)]
  · rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
    exact hnz
  · rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
    exact hno

theorem decodeCalldata_addr_bool_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

theorem decodeCalldata_addr_bool_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩


/-! ## Address-argument calldata decoding (single + two address) -/

/-! ## Single-address calldata decoding -/

theorem decodeScalarWords_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [(.elem .address)] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)] := by
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  rfl

theorem decodeScalarWords_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [(.elem .address)] bytes 0 = none := by
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWords? [(.elem .address)] bytes 0 = none := by
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩

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
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

theorem decodeScalarWords_address_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [(.elem .address), (.elem .address)] bytes 0 = none := by
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩

/-! ## One-address plus two-uint256 calldata decoding -/

theorem decodeScalarWords_address_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  rw [decodeScalarWord_uint256_ok (start := 32) hlen32]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rfl

theorem decodeScalarWords_address_uint256_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_uint256_none_short (start := 32) htake32n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_uint256_ok (start := 32) htake32]
        rw [decodeScalarWord_uint256_none_short (start := 64) htake64n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]

theorem decodeCalldata_address_uint256_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_uint256_uint256_ok (bytes := cd.toList.drop 4) htake4
    htake36' htake68' (by rw [hword4]; exact hcanon0)]
  change decodeCalldata.insertValues [x, y, z]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36, hword68]

theorem decodeCalldata_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_uint256_uint256_none_noncanon0 (bytes := cd.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc0)]

theorem decodeCalldata_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_uint256_uint256_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩

/-! ## Two-address plus uint256 calldata decoding -/

theorem decodeScalarWords_address_address_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rfl

theorem decodeScalarWords_address_address_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_address_uint256_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

theorem decodeScalarWords_address_address_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_address_none_short (start := 32) htake32n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · by_cases hcanon32 :
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus
        · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
          rw [decodeScalarWord_address_ok (start := 32) htake32 hcanon32]
          rw [decodeScalarWord_uint256_none_short (start := 64) htake64n]
        · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
          rw [decodeScalarWord_address_none_noncanon (start := 32) htake32 hcanon32]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]

theorem decodeCalldata_address_address_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_ok (bytes := cd.toList.drop 4) htake4
    htake36' htake68'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hcanon1)]
  change decodeCalldata.insertValues [x, y, z]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]
  rw [hword68]

theorem decodeCalldata_address_address_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_none_noncanon0 (bytes := cd.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc0)]

theorem decodeCalldata_address_address_uint256_none_noncanon1 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
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
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_none_noncanon1 (bytes := cd.toList.drop 4)
    htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hnc1)]

theorem decodeCalldata_address_address_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_address_address_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, .elem .address, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩

/-! ## Two-address plus two-uint256 calldata decoding -/

theorem decodeScalarWords_address_address_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat <
      EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rw [decodeScalarWord_uint256_ok (start := 96) hlen96]
  rfl

theorem decodeScalarWords_address_address_uint256_uint256_none_noncanon0
    {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256] bytes 0 =
      none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_address_uint256_uint256_none_noncanon1
    {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256] bytes 0 =
      none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

theorem decodeScalarWords_address_address_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 128) :
    decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256] bytes 0 =
      none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_address_none_short (start := 32) htake32n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      by_cases h96 : bytes.length < 96
      · have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
        · by_cases hcanon32 :
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_ok (start := 32) htake32 hcanon32]
            rw [decodeScalarWord_uint256_none_short (start := 64) htake64n]
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_none_noncanon (start := 32) htake32 hcanon32]
        · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
      · have htake64 : ((bytes.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have htake96n : ¬ ((bytes.drop 96).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
        · by_cases hcanon32 :
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_ok (start := 32) htake32 hcanon32]
            rw [decodeScalarWord_uint256_ok (start := 64) htake64]
            rw [decodeScalarWord_uint256_none_short (start := 96) htake96n]
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_none_noncanon (start := 32) htake32 hcanon32]
        · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]

theorem decodeCalldata_address_address_uint256_uint256_ok {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w]
        [.elem .address, .elem .address, abiUInt256, abiUInt256] cd =
      some (((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
        (.int (Int.ofNat (calldataWord cd 100).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  have htake100' : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake100
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [.elem .address, .elem .address, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_ok (bytes := cd.toList.drop 4)
    htake4 htake36' htake68' htake100'
    (by rw [hword4]; exact hcanon0)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanon1)]
  change decodeCalldata.insertValues [x, y, z, w]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat)] ∅ =
    some (((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
      (.int (Int.ofNat (calldataWord cd 100).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36, hword68, hword100]

theorem decodeCalldata_address_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [.elem .address, .elem .address, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_none_noncanon0
    (bytes := cd.toList.drop 4) htake4 (by rw [hword4]; exact hnc0)]

theorem decodeCalldata_address_address_uint256_uint256_none_noncanon1 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [.elem .address, .elem .address, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_none_noncanon1
    (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hnc1)]

theorem decodeCalldata_address_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 132) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [.elem .address, .elem .address, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, _, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_none_short
    (bytes := cd.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_address_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z w : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [.elem .address, .elem .address, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by native_decide, by rw [List.length_drop, htlen]; omega⟩

/-! ## Dynamic array calldata decoding -/

/-- A successful dynamic-array ABI decode always produces a Solm array value. -/
theorem decodeABIValue_dynamicArray_is_array {elemTy : ABIType} {bytes : List UInt8}
    {start : Nat} {v : Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray elemTy) bytes start = some (v, endOffset)) :
    ∃ xs, v = .array xs := by
  unfold decodeABIValue? at h
  cases hsize : readNat? bytes start with
  | none => simp [hsize] at h
  | some size =>
      by_cases hmax : solcMaxU64 < size
      · simp [hsize, hmax] at h
      · by_cases hbool : elemTy = .elem .bool
        · subst elemTy
          simp [hsize, hmax] at h
          cases helems : decodeABIRawBoolArrayElems? size bytes (start + 32) with
          | none => simp [helems] at h
          | some p =>
              rcases p with ⟨xs, _⟩
              simp [helems] at h
              exact ⟨xs, h.1.symm⟩
        · by_cases hdyn : isDynamicABIType elemTy
          · simp [hsize, hmax, hdyn] at h
            cases helems : decodeABIArrayDynamicElems? elemTy size bytes (start + 32) with
            | none => simp [helems] at h
            | some p =>
                rcases p with ⟨xs, _⟩
                simp [helems] at h
                exact ⟨xs, h.1.symm⟩
          · simp [hsize, hmax, hdyn] at h
            cases hstatic : staticABIEncodedSize? elemTy with
            | none => simp [hstatic] at h
            | some elemSize =>
                simp [hstatic] at h
                cases helems : decodeABIArrayStaticElems? elemTy size elemSize bytes (start + 32) with
                | none => simp [helems] at h
                | some p =>
                    rcases p with ⟨xs, _⟩
                    simp [helems] at h
                    exact ⟨xs, h.1.symm⟩

theorem readBytes32_some_length {bytes : List UInt8} {off : Nat} {out : List UInt8}
    (h : readBytes? bytes off 32 = some out) : off + 32 ≤ bytes.length := by
  unfold readBytes? at h
  by_cases hle : 32 ≤ bytes.length - off
  · omega
  · simp [hle] at h

theorem readNat?_some_length {bytes : List UInt8} {off n : Nat}
    (h : readNat? bytes off = some n) : off + 32 ≤ bytes.length := by
  unfold readNat? readWord? at h
  cases hbytes : readBytes? bytes off 32 with
  | none => simp [hbytes] at h
  | some _ => exact readBytes32_some_length hbytes

theorem readNat?_exists_of_length {bytes : List UInt8} {off : Nat}
    (h : off + 32 ≤ bytes.length) : ∃ n, readNat? bytes off = some n := by
  unfold readNat? readWord? readBytes?
  have hlen : ((bytes.drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  simp [hlen]

theorem readNat?_some_bytesToWord {bytes : List UInt8} {off n : Nat}
    (h : readNat? bytes off = some n) :
    ABI.bytesToWord ((bytes.drop off).take 32) = UInt256.ofNat n := by
  unfold readNat? readWord? readBytes? at h
  by_cases hle : 32 ≤ bytes.length - off
  · simp [hle] at h
    cases h
    exact (u256_ofNat_toNat _).symm
  · simp [hle] at h

theorem decodeABIValue_uint256_exists {bytes : List UInt8} {start : Nat}
    (h : start + 32 ≤ bytes.length) :
    ∃ v, decodeABIValue? abiUInt256 bytes start = some (v, start + 32) := by
  have hlen : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  exact ⟨.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
    decodeABIValue_uint256_ok hlen⟩

theorem decodeABIValue_bytes32_exists {bytes : List UInt8} {start : Nat}
    (h : start + 32 ≤ bytes.length) :
    ∃ v, decodeABIValue? abiBytes32 bytes start = some (v, start + 32) := by
  have hlen : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  exact ⟨.fixedBytes abiBytes32Width ((bytes.drop start).take 32),
    decodeABIValue_bytes32_ok hlen⟩

theorem decodeABIValue_elem_end_le {elem : ElemType} {bytes : List UInt8}
    {start : Nat} {v : Value} {endOffset : Nat}
    (h : decodeABIValue? (.elem elem) bytes start = some (v, endOffset)) :
    endOffset = start + 32 ∧ start + 32 ≤ bytes.length := by
  cases elem <;> unfold decodeABIValue? at h
  case bool =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem .bool) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case address =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem .address) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case legacyAddress =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        simp [hread, decodeABIWord?] at h
        exact ⟨h.2.symm, readWord?_some_length hread⟩
  case int it =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem (.int it)) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case fixed ft =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word => simp [decodeABIWord?] at h
  case bytes n =>
    cases hread : readBytes? bytes start 32 with
    | none => simp [hread] at h
    | some wordBytes =>
        simp [hread] at h
        cases hzero : zeroPadding? wordBytes (n.val + 1) (31 - n.val) with
        | none => simp [hzero] at h
        | some u =>
            simp [hzero] at h
            exact ⟨h.2.symm, readBytes32_some_length hread⟩
  case function =>
    cases hread : readBytes? bytes start 32 with
    | none => simp [hread] at h
    | some wordBytes =>
        cases hzero : zeroPadding? wordBytes 24 8 with
        | none => simp [hread, hzero] at h
        | some u =>
            simp [hread, hzero] at h
            exact ⟨h.2.symm, readBytes32_some_length hread⟩

theorem decodeABIArrayStaticElems_elem32_facts {elem : ElemType} {n : Nat}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (hstart : start ≤ bytes.length)
    (h : decodeABIArrayStaticElems? (.elem elem) n 32 bytes start = some (values, endOffset)) :
    endOffset = start + 32 * n ∧ endOffset ≤ bytes.length ∧ values.length = n := by
  induction n generalizing start values endOffset with
  | zero =>
      simp [decodeABIArrayStaticElems?] at h
      rcases h with ⟨hvalues, hend⟩
      cases hvalues
      cases hend
      exact ⟨by omega, hstart, rfl⟩
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at h
      cases hval : decodeABIValue? (.elem elem) bytes start with
      | none => simp [hval] at h
      | some p =>
          rcases p with ⟨value, end0⟩
          obtain ⟨hend0, hend0le⟩ := decodeABIValue_elem_end_le hval
          simp [hval] at h
          cases hrest : decodeABIArrayStaticElems? (.elem elem) n 32 bytes end0 with
          | none => simp [hrest] at h
          | some q =>
              rcases q with ⟨valuesRest, restEnd⟩
              simp [hrest] at h
              rcases h with ⟨hend0', htail⟩
              rcases htail with ⟨hvalues, hend⟩
              cases hvalues
              cases hend
              obtain ⟨ihEq, ihLe, ihLen⟩ := ih (by omega) hrest
              exact ⟨by omega, ihLe, by simp [ihLen]⟩

theorem decodeABIArrayStaticElems_uint256_exists_of_length {n : Nat}
    {bytes : List UInt8} {start : Nat} (h : start + 32 * n ≤ bytes.length) :
    ∃ values, decodeABIArrayStaticElems? abiUInt256 n 32 bytes start =
        some (values, start + 32 * n) ∧ values.length = n := by
  induction n generalizing start with
  | zero =>
      refine ⟨[], ?_, rfl⟩
      simp [decodeABIArrayStaticElems?]
  | succ n ih =>
      obtain ⟨v, hv⟩ := decodeABIValue_uint256_exists (bytes := bytes) (start := start) (by omega)
      obtain ⟨values, hvalues, hlen⟩ := ih (start := start + 32) (by omega)
      refine ⟨v :: values, ?_, by simp [hlen]⟩
      rw [decodeABIArrayStaticElems?, hv]
      have hmul : 32 + 32 * n = 32 * (n + 1) := by omega
      simp [hvalues, hmul, Nat.add_assoc]

theorem decodeABIArrayStaticElems_bytes32_exists_of_length {n : Nat}
    {bytes : List UInt8} {start : Nat} (h : start + 32 * n ≤ bytes.length) :
    ∃ values, decodeABIArrayStaticElems? abiBytes32 n 32 bytes start =
        some (values, start + 32 * n) ∧ values.length = n := by
  induction n generalizing start with
  | zero =>
      refine ⟨[], ?_, rfl⟩
      simp [decodeABIArrayStaticElems?]
  | succ n ih =>
      obtain ⟨v, hv⟩ := decodeABIValue_bytes32_exists (bytes := bytes) (start := start) (by omega)
      obtain ⟨values, hvalues, hlen⟩ := ih (start := start + 32) (by omega)
      refine ⟨v :: values, ?_, by simp [hlen]⟩
      rw [decodeABIArrayStaticElems?, hv]
      have hmul : 32 + 32 * n = 32 * (n + 1) := by omega
      simp [hvalues, hmul, Nat.add_assoc]

theorem decodeABIRawBoolArrayElems_facts {n : Nat} {bytes : List UInt8}
    {start : Nat} {values : List Value} {endOffset : Nat}
    (hstart : start ≤ bytes.length)
    (h : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset)) :
    endOffset = start + 32 * n ∧ endOffset ≤ bytes.length ∧ values.length = n := by
  induction n generalizing start values endOffset with
  | zero =>
      simp [decodeABIRawBoolArrayElems?] at h
      rcases h with ⟨hvalues, hend⟩
      cases hvalues
      cases hend
      exact ⟨by omega, hstart, rfl⟩
  | succ n ih =>
      rw [decodeABIRawBoolArrayElems?] at h
      cases hread : readNat? bytes start with
      | none => simp [hread] at h
      | some word =>
          simp [hread] at h
          cases hrest : decodeABIRawBoolArrayElems? n bytes (start + 32) with
          | none => simp [hrest] at h
          | some p =>
              rcases p with ⟨valuesRest, restEnd⟩
              simp [hrest] at h
              rcases h with ⟨hvalues, hend⟩
              cases hvalues
              cases hend
              obtain ⟨ihEq, ihLe, ihLen⟩ :=
                ih (readNat?_some_length hread) hrest
              exact ⟨by omega, ihLe, by simp [ihLen]⟩

theorem decodeABIRawBoolArrayElems_exists_of_length {n : Nat} {bytes : List UInt8}
    {start : Nat} (h : start + 32 * n ≤ bytes.length) :
    ∃ values, decodeABIRawBoolArrayElems? n bytes start =
        some (values, start + 32 * n) ∧ values.length = n := by
  induction n generalizing start with
  | zero =>
      refine ⟨[], ?_, rfl⟩
      simp [decodeABIRawBoolArrayElems?]
  | succ n ih =>
      have hreadLen : start + 32 ≤ bytes.length := by omega
      obtain ⟨word, hread⟩ := readNat?_exists_of_length hreadLen
      have htail : start + 32 + 32 * n ≤ bytes.length := by omega
      obtain ⟨values, hvalues, hlen⟩ := ih htail
      refine ⟨rawBoolWordValue word :: values, ?_, by simp [hlen]⟩
      rw [decodeABIRawBoolArrayElems?, hread, hvalues]
      have hmul : 32 + 32 * n = 32 * (n + 1) := by omega
      simp [hmul, Nat.add_assoc]

theorem decodeABIValue_dynamicArray_uint256_exists {bytes : List UInt8}
    {start len : Nat}
    (hread : readNat? bytes start = some len)
    (hmax : ¬ solcMaxU64 < len)
    (hend : start + 32 + 32 * len ≤ bytes.length) :
    ∃ values, decodeABIValue? (.dynamicArray abiUInt256) bytes start =
        some (.array values, start + 32 + 32 * len) ∧ values.length = len := by
  obtain ⟨values, hvalues, hlen⟩ :=
    decodeABIArrayStaticElems_uint256_exists_of_length (bytes := bytes) (start := start + 32)
      (n := len) (by omega)
  refine ⟨values, ?_, hlen⟩
  unfold decodeABIValue? abiUInt256
  simp [hread, hmax, isDynamicABIType, staticABIEncodedSize?, hvalues, Nat.add_assoc]

theorem decodeABIValue_dynamicArray_bool_exists {bytes : List UInt8}
    {start len : Nat}
    (hread : readNat? bytes start = some len)
    (hmax : ¬ solcMaxU64 < len)
    (hend : start + 32 + 32 * len ≤ bytes.length) :
    ∃ values, decodeABIValue? (.dynamicArray (.elem .bool)) bytes start =
        some (.array values, start + 32 + 32 * len) ∧ values.length = len := by
  obtain ⟨values, hvalues, hlen⟩ :=
    decodeABIRawBoolArrayElems_exists_of_length (bytes := bytes) (start := start + 32)
      (n := len) (by omega)
  refine ⟨values, ?_, hlen⟩
  unfold decodeABIValue?
  simp [hread, hmax, hvalues, Nat.add_assoc]

theorem decodeABIValue_dynamicArray_bytes32_exists {bytes : List UInt8}
    {start len : Nat}
    (hread : readNat? bytes start = some len)
    (hmax : ¬ solcMaxU64 < len)
    (hend : start + 32 + 32 * len ≤ bytes.length) :
    ∃ values, decodeABIValue? (.dynamicArray abiBytes32) bytes start =
        some (.array values, start + 32 + 32 * len) ∧ values.length = len := by
  obtain ⟨values, hvalues, hlen⟩ :=
    decodeABIArrayStaticElems_bytes32_exists_of_length (bytes := bytes) (start := start + 32)
      (n := len) (by omega)
  refine ⟨values, ?_, hlen⟩
  unfold decodeABIValue? abiBytes32
  simp [hread, hmax, isDynamicABIType, staticABIEncodedSize?, hvalues, Nat.add_assoc]

theorem decodeABIValue_dynamicArray_elem32_facts {elem : ElemType}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray (.elem elem)) bytes start =
      some (.array values, endOffset)) :
    ∃ len, readNat? bytes start = some len ∧ ¬ solcMaxU64 < len ∧
      endOffset = start + 32 + 32 * len ∧ endOffset ≤ bytes.length ∧ values.length = len := by
  unfold decodeABIValue? at h
  cases hread : readNat? bytes start with
  | none => simp [hread] at h
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at h
      · by_cases hbool : elem = .bool
        · subst elem
          simp [hread, hmax] at h
          cases hraw : decodeABIRawBoolArrayElems? len bytes (start + 32) with
          | none => simp [hraw] at h
          | some p =>
              rcases p with ⟨values', end'⟩
              simp [hraw] at h
              rcases h with ⟨hvalues, hendOffset⟩
              obtain ⟨hend, hle, hlen⟩ :=
                decodeABIRawBoolArrayElems_facts (readNat?_some_length hread) hraw
              refine ⟨len, rfl, hmax, ?_, ?_, ?_⟩
              · rw [← hendOffset]
                exact hend
              · rwa [hendOffset] at hle
              · rwa [hvalues] at hlen
        · simp [hread, hmax, hbool, staticABIEncodedSize?, isDynamicABIType] at h
          cases hstatic : decodeABIArrayStaticElems? (.elem elem) len 32 bytes (start + 32) with
          | none => simp [hstatic] at h
          | some p =>
              rcases p with ⟨values', end'⟩
              simp [hstatic] at h
              rcases h with ⟨hvalues, hendOffset⟩
              obtain ⟨hend, hle, hlen⟩ :=
                decodeABIArrayStaticElems_elem32_facts (readNat?_some_length hread) hstatic
              refine ⟨len, rfl, hmax, ?_, ?_, ?_⟩
              · rw [← hendOffset]
                exact hend
              · rwa [hendOffset] at hle
              · rwa [hvalues] at hlen

theorem decodeABIValue_uint256_readNat {bytes : List UInt8} {start endOffset : Nat}
    {value : UInt256}
    (h : decodeABIValue? abiUInt256 bytes start =
      some (.int (Int.ofNat value.toNat), endOffset)) :
    readNat? bytes start = some value.toNat ∧ endOffset = start + 32 := by
  obtain ⟨_hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? abiUInt256 bytes start =
        some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
          start + 32) := decodeABIValue_uint256_ok htake
  rw [hok] at h
  injection h with hpair
  injection hpair with hval hend'
  injection hval with hint
  have hword :
      (ABI.bytesToWord ((bytes.drop start).take 32)).toNat = value.toNat :=
    Int.ofNat.inj hint
  constructor
  · unfold readNat? readWord? readBytes?
    simp [htake]
    simpa [UInt256.toNat] using hword
  · exact hend'.symm

theorem decodeABIRawBoolArrayElems_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i word : Nat} {values : List Value}
    (hdec : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset))
    (hlookup : lookupNth? values i = some (rawBoolWordValue word)) :
    readNat? bytes (start + 32 * i) = some word := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIRawBoolArrayElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      cases i <;> simp [lookupNth?] at hlookup
  | succ n ih =>
      rw [decodeABIRawBoolArrayElems?] at hdec
      cases hread : readNat? bytes start with
      | none => simp [hread] at hdec
      | some headWord =>
          simp [hread] at hdec
          cases hrest : decodeABIRawBoolArrayElems? n bytes (start + 32) with
          | none => simp [hrest] at hdec
          | some p =>
              rcases p with ⟨tailValues, restEnd⟩
              simp [hrest] at hdec
              rcases hdec with ⟨hvalues, hend⟩
              cases hvalues
              cases hend
              cases i with
              | zero =>
                  simp [lookupNth?, rawBoolWordValue] at hlookup
                  cases hlookup
                  simpa using hread
              | succ i =>
                  simp [lookupNth?] at hlookup
                  have htail := ih hrest hlookup
                  have hoff : start + 32 * (i + 1) = start + 32 + 32 * i := by omega
                  simpa [hoff, Nat.add_assoc] using htail

theorem decodeABIArrayStaticElems_uint256_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {value : UInt256}
    {values : List Value}
    (hdec : decodeABIArrayStaticElems? abiUInt256 n 32 bytes start = some (values, endOffset))
    (hlookup : lookupNth? values i = some (.int (Int.ofNat value.toNat))) :
    readNat? bytes (start + 32 * i) = some value.toNat := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      cases i <;> simp [lookupNth?] at hlookup
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? abiUInt256 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? abiUInt256 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? abiUInt256 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? abiUInt256 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, hend⟩
                cases hvalues
                cases hend
                cases i with
                | zero =>
                    simp [lookupNth?] at hlookup
                    cases hlookup
                    exact (decodeABIValue_uint256_readNat hval).1
                | succ i =>
                    simp [lookupNth?] at hlookup
                    have htail := ih hrest hlookup
                    have hoff : start + 32 * (i + 1) = headEnd + 32 * i := by omega
                    simpa [hoff] using htail
          · simp [hval, hendHead] at hdec

theorem bytesToWord_toBytesBE (w : UInt256) :
    ABI.bytesToWord (EVM.Word.toBytesBE w) = w := by
  unfold ABI.bytesToWord
  rw [← toByteArray_eq_toBytesBE w, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem decodeABIValue_bytes32_readNat {bytes : List UInt8} {start endOffset : Nat}
    {value : UInt256}
    (h : decodeABIValue? abiBytes32 bytes start =
      some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE value), endOffset)) :
    readNat? bytes start = some value.toNat ∧ endOffset = start + 32 := by
  obtain ⟨_hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? abiBytes32 bytes start =
        some (.fixedBytes abiBytes32Width ((bytes.drop start).take 32), start + 32) :=
    decodeABIValue_bytes32_ok htake
  rw [hok] at h
  injection h with hpair
  injection hpair with hval hend'
  injection hval with _ hbytes
  constructor
  · unfold readNat? readWord? readBytes?
    rw [if_pos htake]
    simp only [bind, Option.bind]
    rw [hbytes]
    simp [bytesToWord_toBytesBE, UInt256.toNat]
  · exact hend'.symm

theorem decodeABIArrayStaticElems_bytes32_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {value : UInt256}
    {values : List Value}
    (hdec : decodeABIArrayStaticElems? abiBytes32 n 32 bytes start = some (values, endOffset))
    (hlookup :
      lookupNth? values i =
        some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE value))) :
    readNat? bytes (start + 32 * i) = some value.toNat := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      cases i <;> simp [lookupNth?] at hlookup
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? abiBytes32 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? abiBytes32 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? abiBytes32 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? abiBytes32 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, hend⟩
                cases hvalues
                cases hend
                cases i with
                | zero =>
                    simp [lookupNth?] at hlookup
                    cases hlookup
                    exact (decodeABIValue_bytes32_readNat hval).1
                | succ i =>
                    simp [lookupNth?] at hlookup
                    have htail := ih hrest hlookup
                    have hoff : start + 32 * (i + 1) = headEnd + 32 * i := by omega
                    simpa [hoff] using htail
          · simp [hval, hendHead] at hdec

theorem decodeABIValue_dynamicArray_uint256_lookup_readNat {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value} {value : UInt256}
    (hdec :
      decodeABIValue? (.dynamicArray abiUInt256) bytes start = some (.array values, endOffset))
    (hlookup : lookupNth? values i = some (.int (Int.ofNat value.toNat))) :
    readNat? bytes (start + 32 + 32 * i) = some value.toNat := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax] at hdec
        cases hstatic : decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_uint256_lookup_readNat hstatic hlookup

theorem decodeABIValue_dynamicArray_bool_lookup_readNat {bytes : List UInt8}
    {start endOffset i word : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray (.elem .bool)) bytes start = some (.array values, endOffset))
    (hlookup : lookupNth? values i = some (rawBoolWordValue word)) :
    readNat? bytes (start + 32 + 32 * i) = some word := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax] at hdec
        cases hraw : decodeABIRawBoolArrayElems? len bytes (start + 32) with
        | none => simp [hraw] at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            simp [hraw] at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIRawBoolArrayElems_lookup_readNat hraw hlookup

theorem decodeABIValue_dynamicArray_bytes32_lookup_readNat {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value} {value : UInt256}
    (hdec :
      decodeABIValue? (.dynamicArray abiBytes32) bytes start = some (.array values, endOffset))
    (hlookup :
      lookupNth? values i =
        some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE value))) :
    readNat? bytes (start + 32 + 32 * i) = some value.toNat := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax] at hdec
        cases hstatic : decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_bytes32_lookup_readNat hstatic hlookup

theorem decodeABIValue_uint256_shape {bytes : List UInt8} {start endOffset : Nat}
    {value : Value}
    (h : decodeABIValue? abiUInt256 bytes start = some (value, endOffset)) :
    ∃ word : UInt256, value = .int (Int.ofNat word.toNat) ∧ endOffset = start + 32 := by
  obtain ⟨_hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? abiUInt256 bytes start =
        some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
          start + 32) := decodeABIValue_uint256_ok htake
  rw [hok] at h
  injection h with hpair
  injection hpair with hvalue hend
  exact ⟨ABI.bytesToWord ((bytes.drop start).take 32), hvalue.symm, hend.symm⟩

theorem decodeABIValue_bytes32_shape {bytes : List UInt8} {start endOffset : Nat}
    {value : Value}
    (h : decodeABIValue? abiBytes32 bytes start = some (value, endOffset)) :
    ∃ word : UInt256,
      value = .fixedBytes abiBytes32Width (EVM.Word.toBytesBE word) ∧
        endOffset = start + 32 := by
  obtain ⟨_hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? abiBytes32 bytes start =
        some (.fixedBytes abiBytes32Width ((bytes.drop start).take 32), start + 32) :=
    decodeABIValue_bytes32_ok htake
  rw [hok] at h
  injection h with hpair
  injection hpair with hvalue hend
  refine ⟨ABI.bytesToWord ((bytes.drop start).take 32), ?_, hend.symm⟩
  rw [← hvalue]
  congr 2
  exact (toBytesBE_bytesToWord_of_length htake).symm

theorem decodeABIArrayStaticElems_uint256_lookup_shape {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {values : List Value}
    (hdec : decodeABIArrayStaticElems? abiUInt256 n 32 bytes start = some (values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256, lookupNth? values i = some (.int (Int.ofNat value.toNat)) := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      simp at hbound
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? abiUInt256 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? abiUInt256 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? abiUInt256 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? abiUInt256 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, _hend⟩
                cases hvalues
                cases i with
                | zero =>
                    obtain ⟨value, hshape, _hend⟩ := decodeABIValue_uint256_shape hval
                    refine ⟨value, ?_⟩
                    simp [lookupNth?, hshape]
                | succ i =>
                    simp at hbound
                    obtain ⟨value, hlookup⟩ := ih hrest hbound
                    refine ⟨value, ?_⟩
                    simpa [lookupNth?] using hlookup
          · simp [hval, hendHead] at hdec

theorem decodeABIRawBoolArrayElems_lookup_shape {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {values : List Value}
    (hdec : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset))
    (hbound : i < values.length) :
    ∃ word : Nat, lookupNth? values i = some (rawBoolWordValue word) := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIRawBoolArrayElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      simp at hbound
  | succ n ih =>
      rw [decodeABIRawBoolArrayElems?] at hdec
      cases hread : readNat? bytes start with
      | none => simp [hread] at hdec
      | some word =>
          simp [hread] at hdec
          cases hrest : decodeABIRawBoolArrayElems? n bytes (start + 32) with
          | none => simp [hrest] at hdec
          | some p =>
              rcases p with ⟨tailValues, restEnd⟩
              simp [hrest] at hdec
              rcases hdec with ⟨hvalues, _hend⟩
              cases hvalues
              cases i with
              | zero =>
                  refine ⟨word, ?_⟩
                  simp [lookupNth?]
              | succ i =>
                  simp at hbound
                  obtain ⟨word', hlookup⟩ := ih hrest hbound
                  refine ⟨word', ?_⟩
                  simpa [lookupNth?] using hlookup

theorem decodeABIArrayStaticElems_bytes32_lookup_shape {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {values : List Value}
    (hdec : decodeABIArrayStaticElems? abiBytes32 n 32 bytes start = some (values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256,
      lookupNth? values i =
        some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE value)) := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      simp at hbound
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? abiBytes32 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? abiBytes32 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? abiBytes32 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? abiBytes32 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, _hend⟩
                cases hvalues
                cases i with
                | zero =>
                    obtain ⟨value, hshape, _hend⟩ := decodeABIValue_bytes32_shape hval
                    refine ⟨value, ?_⟩
                    simp [lookupNth?, hshape]
                | succ i =>
                    simp at hbound
                    obtain ⟨value, hlookup⟩ := ih hrest hbound
                    refine ⟨value, ?_⟩
                    simpa [lookupNth?] using hlookup
          · simp [hval, hendHead] at hdec

theorem decodeABIValue_dynamicArray_uint256_lookup_shape {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray abiUInt256) bytes start = some (.array values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256, lookupNth? values i = some (.int (Int.ofNat value.toNat)) := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax] at hdec
        cases hstatic : decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_uint256_lookup_shape hstatic hbound

theorem decodeABIValue_dynamicArray_bool_lookup_shape {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray (.elem .bool)) bytes start = some (.array values, endOffset))
    (hbound : i < values.length) :
    ∃ word : Nat, lookupNth? values i = some (rawBoolWordValue word) := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax] at hdec
        cases hraw : decodeABIRawBoolArrayElems? len bytes (start + 32) with
        | none => simp [hraw] at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            simp [hraw] at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIRawBoolArrayElems_lookup_shape hraw hbound

theorem decodeABIValue_dynamicArray_bytes32_lookup_shape {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray abiBytes32) bytes start = some (.array values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256,
      lookupNth? values i =
        some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE value)) := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax] at hdec
        cases hstatic : decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_bytes32_lookup_shape hstatic hbound

/-! ## Return decoding -/

theorem bytesToWord_take32_eq_extract0_32 {returndata : ByteArray} :
    ABI.bytesToWord (returndata.toList.take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (returndata.extract 0 32), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  rw [byteArray_toList_eq]
  simp

theorem fromByteArrayBigEndian_extract0_32_lt {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    fromByteArrayBigEndian (returndata.extract 0 32) < UInt256.size := by
  unfold fromByteArrayBigEndian fromBytesBigEndian
  have h := EVM.fromBytes'_le (bs := (returndata.extract 0 32).toList.reverse)
  rw [List.length_reverse] at h
  have hsz : (returndata.extract 0 32).toList.length = 32 := by
    have hszBA : (returndata.extract 0 32).size = 32 := by
      rw [ByteArray.size_extract]
      omega
    rw [byteArray_toList_eq, Array.length_toList]
    exact hszBA
  rw [hsz] at h
  simpa [UInt256.size] using h

theorem decodeReturnValue_uint256_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < (2 : Nat) ^ 255) :
    ABI.decodeReturnValue? abiUInt256 returndata =
      some (.int (Int.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : (returndata.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [abiUInt256]) (returndata := returndata)
    (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [decodeScalarWords_uint256_ok (bytes := returndata.toList) htake0]
  simp [hword, UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem decodeReturnValue_uint256_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValue? abiUInt256 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [abiUInt256]) (returndata := returndata)
    (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [decodeScalarWords_uint256_none_short (bytes := returndata.toList) (by rw [hlen]; omega)]

theorem decodeReturnValue_uint256_none_huge {returndata : ByteArray}
    (hhuge : (2 : Nat) ^ 255 ≤ returndata.size) :
    ABI.decodeReturnValue? abiUInt256 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [abiUInt256]) (returndata := returndata)
    (by decide)]
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhuge⟩)]

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

/-- ABI-encoding `false` is the one-word value `0` (for `bool`-returning functions). -/
theorem boolFalseReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool false) = some (UInt256.toByteArray ⟨0⟩) :=
  scalarReturnEncoding (t := .bool) (w := (⟨0⟩ : UInt256)) rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
        decide)
    (by simp [encodeABIValue?, encodeABIWord?, Bool.toUInt256_false]; rfl)

/-- ABI-encoding a packed-storage bool return agrees with solc's `iszero(iszero(word & 0xff))`. -/
theorem boolWordReturnEncoding (w : UInt256) :
    encodeReturnValue? (.elem .bool) (wordToElem .bool (UInt256.land w ⟨255⟩)) =
      some (UInt256.toByteArray
        (UInt256.isZero (UInt256.isZero (UInt256.land w ⟨255⟩)))) := by
  by_cases hval : (UInt256.land w ⟨255⟩).val = 0
  · have hz : UInt256.land w ⟨255⟩ = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    have hnorm : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by decide
    simpa [wordToElem, hz, hnorm] using boolFalseReturnEncoding
  · have hz : UInt256.land w ⟨255⟩ ≠ ⟨0⟩ := by
      intro hx
      apply hval
      rw [hx]
    have hiz : UInt256.isZero (UInt256.land w ⟨255⟩) = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have hnorm : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by decide
    simpa [wordToElem, hval, hiz, hnorm] using boolTrueReturnEncoding

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

/-- ABI-encoding a `bytes32` return value is exactly the returned word's 32 bytes. -/
theorem bytes32ReturnEncoding (w : UInt256) :
    encodeReturnValue? (.elem (.bytes ⟨31, by decide⟩))
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE w)) =
      some (UInt256.toByteArray w) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  refine scalarReturnEncoding (t := .bytes ⟨31, by decide⟩) (w := w) (by native_decide) ?_ ?_
  · native_decide
  · simp [encodeABIValue?, hlen, zeroBytes]

/-- ABI encoding of a single dynamic-array (static element type) constructor/calldata argument:
    a 32-byte offset (always `0x20`), a 32-byte length, then the statically-encoded elements.
    The workhorse for decoding the deployment shape of a `T[] memory` constructor parameter. -/
theorem encodeABIValues_single_dynArray_static
    {elemTy : ABIType} {vs : List Value}
    (hstatic : ABI.isDynamicABIType elemTy = false) :
    ABI.encodeABIValues? [.dynamicArray elemTy] [.array vs]
      = (ABI.encodeABIStaticArrayElems? elemTy vs).bind
          (fun e => some (ABI.natBytes 32 ++ (ABI.natBytes vs.length ++ e))) := by
  unfold ABI.encodeABIValues?
  cases h : ABI.encodeABIStaticArrayElems? elemTy vs with
  | none =>
      simp [ABI.abiTupleHeadSize?, ABI.isDynamicABIType, ABI.encodeABIValuesFrom?,
        ABI.encodeABIValue?, ABI.encodeABIArrayElems?, hstatic, h]
  | some e =>
      simp [ABI.abiTupleHeadSize?, ABI.isDynamicABIType, ABI.encodeABIValuesFrom?,
        ABI.encodeABIValue?, ABI.encodeABIArrayElems?, hstatic, h]

end Reasoning.Theory
