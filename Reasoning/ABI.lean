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
    have hdynFalse : types.any isDynamicABIType = false :=
      isABIScalarWordTypes_any_dynamic_false hscalar
    conv_lhs => rw [if_neg (by simp [hdynFalse])]
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
  have hnotHuge : ¬ ([abiBytes4].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
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
  have hnotHuge : ¬ ([abiBytes4].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
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
    have hHuge : [abiBytes4].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length := by
      have htlen : cd.toList.length = cd.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_drop, htlen]
      simp
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
  have hnotHuge : ¬ ([abiBytes4].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
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
  have hnotHuge : ¬ ([abiBytes32].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
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
  have hnotHuge : ¬ ([abiBytes32].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
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
    have hHuge : [abiBytes32].isEmpty = false ∧ 2 ^ 255 ≤ (cd.toList.drop 4).length := by
      have htlen : cd.toList.length = cd.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_drop, htlen]
      simp
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  simp only [Option.bind, bind]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
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

/-- ABI-encoding `false` is the one-word value `0` (for `bool`-returning functions). -/
theorem boolFalseReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool false) = some (UInt256.toByteArray ⟨0⟩) :=
  scalarReturnEncoding (t := .bool) (w := (⟨0⟩ : UInt256)) rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
        decide)
    (by simp [encodeABIValue?, encodeABIWord?, Bool.toUInt256_false]; rfl)

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
