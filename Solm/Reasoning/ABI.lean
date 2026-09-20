import EVMReasoning.ABI
import Solm.Semantics.ValueOps
import Solm.Semantics.Dispatch

/-! # ABI decoding facts phrased with Sol⁻'s `lookupNth?` (array element access), and the calldata
decoder bound to parameter names (`Solm.decodeCalldata`). -/


namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM

theorem decodeABIRawBoolArrayElems_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i word : Nat} {values : List ABIValue}
    (hdec : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset))
    (hlookup : lookupNth? values i = some (.rawBool word)) :
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
                  simp [lookupNth?] at hlookup
                  cases hlookup
                  simpa using hread
              | succ i =>
                  simp [lookupNth?] at hlookup
                  have htail := ih hrest hlookup
                  have hoff : start + 32 * (i + 1) = start + 32 + 32 * i := by omega
                  simpa [hoff, Nat.add_assoc] using htail

theorem decodeABIArrayStaticElems_uint256_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {value : UInt256}
    {values : List ABIValue}
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

theorem decodeABIArrayStaticElems_bytes32_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {value : UInt256}
    {values : List ABIValue}
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
    {start endOffset i : Nat} {values : List ABIValue} {value : UInt256}
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
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32)).bind
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_uint256_lookup_readNat hstatic hlookup

theorem decodeABIValue_dynamicArray_bool_lookup_readNat {bytes : List UInt8}
    {start endOffset i word : Nat} {values : List ABIValue}
    (hdec :
      decodeABIValue? (.dynamicArray (.elem .bool)) bytes start = some (.array values, endOffset))
    (hlookup : lookupNth? values i = some (.rawBool word)) :
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
    {start endOffset i : Nat} {values : List ABIValue} {value : UInt256}
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
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32)).bind
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_bytes32_lookup_readNat hstatic hlookup

theorem decodeABIArrayStaticElems_uint256_lookup_shape {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {values : List ABIValue}
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
    {bytes : List UInt8} {start endOffset i : Nat} {values : List ABIValue}
    (hdec : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset))
    (hbound : i < values.length) :
    ∃ word : Nat, lookupNth? values i = some (.rawBool word) := by
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
    {bytes : List UInt8} {start endOffset i : Nat} {values : List ABIValue}
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
    {start endOffset i : Nat} {values : List ABIValue}
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
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiUInt256 len 32 bytes (start + 32)).bind
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_uint256_lookup_shape hstatic hbound

theorem decodeABIValue_dynamicArray_bool_lookup_shape {bytes : List UInt8}
    {start endOffset i : Nat} {values : List ABIValue}
    (hdec :
      decodeABIValue? (.dynamicArray (.elem .bool)) bytes start = some (.array values, endOffset))
    (hbound : i < values.length) :
    ∃ word : Nat, lookupNth? values i = some (.rawBool word) := by
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
    {start endOffset i : Nat} {values : List ABIValue}
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
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? abiBytes32 len 32 bytes (start + 32)).bind
                fun p => some (ABIValue.array p.1, p.2)) =
                  some (ABIValue.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact decodeABIArrayStaticElems_bytes32_lookup_shape hstatic hbound

/-- A decoded `bool` word converts back to the ABI value it came from (both branches of
    `wordToElem` are `bool` constructors). -/
theorem wordToElem_bool_roundTrip (w : UInt256) :
    (Value.ofABI (wordToElem .bool w)).toABI? = some (wordToElem .bool w) := by
  by_cases h : (w.val == 0) = true <;> simp [wordToElem, h]

/-! ## Sol⁻ lists of decoded values -/

@[simp] theorem ofABIList_length (vs : List ABIValue) :
    (Value.ofABIList vs).length = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem lookupNth?_ofABIList (vs : List ABIValue) (i : Nat) :
    lookupNth? (Value.ofABIList vs) i = (lookupNth? vs i).map Value.ofABI := by
  induction vs generalizing i with
  | nil => cases i <;> simp [lookupNth?]
  | cons v vs ih => cases i <;> simp [lookupNth?, ih]

theorem ofABI_eq_int {a : ABIValue} {n : Int} (h : Value.ofABI a = .int n) : a = .int n := by
  cases a <;> simp at h
  subst h
  rfl

theorem ofABI_eq_fixedBytes {a : ABIValue} {n : Fin 32} {bs : List UInt8}
    (h : Value.ofABI a = .fixedBytes n bs) : a = .fixedBytes n bs := by
  cases a <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- Only the decoder's raw `bool` word converts to Sol⁻'s raw-bool marker. -/
theorem ofABI_eq_rawBoolMarker {a : ABIValue} {w : Nat}
    (h : Value.ofABI a = .tuple [.unit, .int w]) : a = .rawBool w := by
  cases a with
  | tuple vs =>
      simp at h
      cases vs with
      | nil => simp at h
      | cons v vs =>
          simp at h
          cases v <;> simp at h
  | rawBool w' =>
      simp at h
      subst h
      rfl
  | _ => simp at h

/-! ## Calldata bound to parameter names (`Solm.decodeCalldata`)

The store-shaped forms of the positional `decodeCalldataValues_*` facts. -/

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
  rw [decodeCalldataValues_scalarWords_eq hscalar]
  split
  · rfl
  · split
    · rfl
    · cases decodeScalarWords? types (cd.toList.drop 4) 0 <;> rfl

theorem decodeCalldataWithMode_legacyScalarWords_eq {names : List Solm.Ident}
    {types : List ABIType} {cd : ByteArray}
    (hscalar : types.all isABIScalarWordType = true) :
    decodeCalldataWithMode DecodeMode.legacySolc05 names types cd =
      if cd.toList.length < 4 then
        none
      else
        match decodeScalarWordsWithMode? DecodeMode.legacySolc05 types (cd.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues names values ∅
        | none => none := by
  unfold decodeCalldataWithMode decodeCalldata
  rw [decodeCalldataValues_legacyScalarWords_eq hscalar]
  split
  · rfl
  · cases decodeScalarWordsWithMode? DecodeMode.legacySolc05 types (cd.toList.drop 4) 0 <;> rfl

theorem decodeCalldataWithMode_vyperScalarWords_eq {names : List Solm.Ident}
    {types : List ABIType} {cd : ByteArray}
    (hscalar : types.all isABIScalarWordType = true) :
    decodeCalldataWithMode DecodeMode.vyper names types cd =
      if cd.toList.length < 4 then
        none
      else
        match decodeScalarWords? types (cd.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues names values ∅
        | none => none := by
  unfold decodeCalldataWithMode decodeCalldata
  rw [decodeCalldataValues_vyperScalarWords_eq hscalar]
  split
  · rfl
  · cases decodeScalarWords? types (cd.toList.drop 4) 0 <;> rfl

theorem decodeCalldata_legacyAddress_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiAddress] cd =
      some ((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_ok hsz36, decodeCalldata.insertValues]

theorem decodeCalldata_legacyAddress_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiAddress] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_none_short hsz4 hshort]

theorem decodeCalldata_legacyAddress_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiAddress, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_uint256_ok hsz68, decodeCalldata.insertValues]

theorem decodeCalldata_legacyAddress_uint256_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiAddress, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_uint256_none_short hsz4 hshort]

theorem decodeCalldata_legacyAddress_legacyAddress_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiAddress, abiAddress] cd =
      some (((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_legacyAddress_ok hsz68, decodeCalldata.insertValues]

theorem decodeCalldata_legacyAddress_legacyAddress_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiAddress, abiAddress] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_legacyAddress_none_short hsz4 hshort]

theorem decodeCalldata_legacyAddress_legacyAddress_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z] [abiAddress, abiAddress, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_legacyAddress_uint256_ok hsz100, decodeCalldata.insertValues]

theorem decodeCalldata_legacyAddress_legacyAddress_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z] [abiAddress, abiAddress, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_legacyAddress_legacyAddress_uint256_none_short hsz4 hshort]

theorem decodeCalldata_empty_ok {cd : ByteArray} (hsz4 : 4 ≤ cd.size) :
    decodeCalldata [] [] cd = some (∅ : Solm.Store) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_empty_ok hsz4, decodeCalldata.insertValues]

theorem decodeCalldataWithMode_empty_ok {mode : DecodeMode} {cd : ByteArray}
    (hsz4 : 4 ≤ cd.size) :
    decodeCalldataWithMode mode [] [] cd = some (∅ : Solm.Store) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_mode_empty_ok hsz4, decodeCalldata.insertValues]

theorem decodeCalldata_uint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_uint256_ok hsz36 hbig, decodeCalldata.insertValues]

theorem decodeCalldata_uint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hshort : cd.size < 36) :
    decodeCalldata [x] [abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_uint256_none_short hshort]

theorem decodeCalldata_uint256_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_uint256_none_huge hbig]

theorem decodeCalldata_string_none_total_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 ≤ cd.size) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_string_none_total_huge hbig]

theorem decodeCalldata_string_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_string_none_huge hbig]

theorem decodeCalldata_string_none_offset_huge {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size)
    (hoff : solcMaxU64 < (calldataWord cd 4).toNat) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_string_none_offset_huge hsz36 hoff]

theorem decodeCalldata_string_none_length_short {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hshort : cd.size < 4 + (calldataWord cd 4).toNat + 32) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_string_none_length_short hsz36 hhi hshort]

theorem decodeCalldata_string_none_length_huge {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenHuge : solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    decodeCalldata [x] [ABIType.string] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_string_none_length_huge hsz36 hhi hoffMax hlenWord hlenHuge]

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
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_string_none_payload_short hsz36 hhi hoffMax hlenWord hlenMax hpayload]

theorem decodeCalldata_bytes4_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((cd.toList.drop 4).take 32) 4 28 = some ()) :
    decodeCalldata [x] [abiBytes4] cd =
      some ((∅ : Solm.Store).insert x (.fixedBytes abiBytes4Width (calldataBytes4Arg cd))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes4_ok hsz36 hbig hpad, decodeCalldata.insertValues]

theorem decodeCalldata_bytes4_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [abiBytes4] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes4_none_short hsz4 hshort]

theorem decodeCalldata_bytes4_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [abiBytes4] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes4_none_huge hbig]

theorem decodeCalldata_bytes4_none_pad {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((cd.toList.drop 4).take 32) 4 28 = none) :
    decodeCalldata [x] [abiBytes4] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes4_none_pad hsz36 hbig hpad]

theorem decodeCalldata_bytes32_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x] [abiBytes32] cd =
      some ((∅ : Solm.Store).insert x (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes32_ok hsz36 hbig, decodeCalldata.insertValues]

theorem decodeCalldata_bytes32_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [abiBytes32] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes32_none_short hsz4 hshort]

theorem decodeCalldata_bytes32_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [abiBytes32] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes32_none_huge hbig]

theorem decodeCalldata_bytes32_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes32_address_ok hsz68 hbig hcanon, decodeCalldata.insertValues]

theorem decodeCalldata_bytes32_address_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes32_address_none_short hsz4 hshort]

theorem decodeCalldata_bytes32_address_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes32_address_none_huge hbig]

theorem decodeCalldata_bytes32_address_none_noncanon {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiBytes32, .elem .address] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_bytes32_address_none_noncanon hsz68 hbig hnc]

theorem decodeCalldata_addr_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_uint256_ok hsz68 hbig hcanon, decodeCalldata.insertValues]

theorem decodeCalldata_addr_uint256_none_noncanon {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_uint256_none_noncanon hsz68 hbig hnc]

theorem decodeCalldata_addr_uint256_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_uint256_none_short hsz4 hshort]

theorem decodeCalldata_addr_uint256_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [.elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_uint256_none_huge hbig]

theorem decodeCalldataWithMode_vyper_addr_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y] [.elem .address, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_addr_uint256_ok hsz68 hcanon, decodeCalldata.insertValues]

theorem decodeCalldataWithMode_vyper_addr_uint256_none_noncanon {cd : ByteArray}
    {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y] [.elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_addr_uint256_none_noncanon hsz68 hnc]

theorem decodeCalldataWithMode_vyper_addr_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.vyper [x, y] [.elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_addr_uint256_none_short hsz4 hshort]

theorem decodeCalldata_addr_bool_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hbool : calldataWord cd 36 = ⟨0⟩ ∨ calldataWord cd 36 = ⟨1⟩) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (Value.ofABI (wordToElem .bool (calldataWord cd 36)))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_bool_ok hsz68 hbig hcanon hbool, decodeCalldata.insertValues]

theorem decodeCalldata_addr_bool_none_noncanon_addr {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_bool_none_noncanon_addr hsz68 hbig hnc]

theorem decodeCalldata_addr_bool_none_noncanon_bool {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnz : calldataWord cd 36 ≠ ⟨0⟩) (hno : calldataWord cd 36 ≠ ⟨1⟩) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_bool_none_noncanon_bool hsz68 hbig hcanon hnz hno]

theorem decodeCalldata_addr_bool_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_bool_none_short hsz4 hshort]

theorem decodeCalldata_addr_bool_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_addr_bool_none_huge hbig]

theorem decodeCalldata_address_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [(.elem .address)] cd =
      some ((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_ok hsz36 hbig hcanon, decodeCalldata.insertValues]

theorem decodeCalldataWithMode_vyper_address_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x] [(.elem .address)] cd =
      some ((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_ok hsz36 hcanon, decodeCalldata.insertValues]

theorem decodeCalldata_address_none_noncanon {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [(.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_none_noncanon hsz36 hbig hnc]

theorem decodeCalldataWithMode_vyper_address_none_noncanon {cd : ByteArray}
    {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x] [(.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_none_noncanon hsz36 hnc]

theorem decodeCalldata_address_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [(.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_none_short hsz4 hshort]

theorem decodeCalldataWithMode_vyper_address_none_short {cd : ByteArray}
    {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.vyper [x] [(.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_none_short hsz4 hshort]

theorem decodeCalldata_address_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [(.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_none_huge hbig]

theorem decodeCalldata_address_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_ok hsz68 hbig hcanon0 hcanon1, decodeCalldata.insertValues]

theorem decodeCalldataWithMode_vyper_address_address_ok {cd : ByteArray}
    {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y] [(.elem .address), (.elem .address)] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_ok hsz68 hcanon0 hcanon1, decodeCalldata.insertValues]

theorem decodeCalldataWithMode_vyper_address_address_none_noncanon0 {cd : ByteArray}
    {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y] [(.elem .address), (.elem .address)] cd =
      none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_none_noncanon0 hsz68 hnc0]

theorem decodeCalldataWithMode_vyper_address_address_none_noncanon1 {cd : ByteArray}
    {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y] [(.elem .address), (.elem .address)] cd =
      none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_none_noncanon1 hsz68 hcanon0 hnc1]

theorem decodeCalldataWithMode_vyper_address_address_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.vyper [x, y] [(.elem .address), (.elem .address)] cd =
      none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_none_short hsz4 hshort]

theorem decodeCalldata_address_address_none_noncanon0 {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_none_noncanon0 hsz68 hbig hnc0]

theorem decodeCalldata_address_address_none_noncanon1 {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_none_noncanon1 hsz68 hbig hcanon0 hnc1]

theorem decodeCalldata_address_address_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_none_short hsz4 hshort]

theorem decodeCalldata_address_address_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [(.elem .address), (.elem .address)] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_none_huge hbig]

theorem decodeCalldata_address_uint256_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_uint256_uint256_ok hsz100 hbig hcanon0, decodeCalldata.insertValues]

theorem decodeCalldata_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_uint256_uint256_none_noncanon0 hsz100 hbig hnc0]

theorem decodeCalldata_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_uint256_uint256_none_short hsz4 hshort]

theorem decodeCalldata_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_uint256_uint256_none_huge hbig]

theorem decodeCalldata_address_address_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_ok hsz100 hbig hcanon0 hcanon1, decodeCalldata.insertValues]

theorem decodeCalldata_address_address_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_none_noncanon0 hsz100 hbig hnc0]

theorem decodeCalldata_address_address_uint256_none_noncanon1 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_none_noncanon1 hsz100 hbig hcanon0 hnc1]

theorem decodeCalldata_address_address_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_none_short hsz4 hshort]

theorem decodeCalldata_address_address_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [.elem .address, .elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_none_huge hbig]

theorem decodeCalldataWithMode_vyper_address_address_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y, z]
      [.elem .address, .elem .address, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_uint256_ok hsz100 hcanon0 hcanon1, decodeCalldata.insertValues]

theorem decodeCalldataWithMode_vyper_address_address_uint256_none_noncanon0
    {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y, z]
      [.elem .address, .elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_uint256_none_noncanon0 hsz100 hnc0]

theorem decodeCalldataWithMode_vyper_address_address_uint256_none_noncanon1
    {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper [x, y, z]
      [.elem .address, .elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_uint256_none_noncanon1 hsz100 hcanon0 hnc1]

theorem decodeCalldataWithMode_vyper_address_address_uint256_none_short
    {cd : ByteArray} {x y z : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.vyper [x, y, z]
      [.elem .address, .elem .address, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_vyper_address_address_uint256_none_short hsz4 hshort]

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
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_uint256_ok hsz132 hbig hcanon0 hcanon1, decodeCalldata.insertValues]

theorem decodeCalldata_address_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_uint256_none_noncanon0 hsz132 hbig hnc0]

theorem decodeCalldata_address_address_uint256_uint256_none_noncanon1 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_uint256_none_noncanon1 hsz132 hbig hcanon0 hnc1]

theorem decodeCalldata_address_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 132) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_uint256_none_short hsz4 hshort]

theorem decodeCalldata_address_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z w : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z, w]
      [.elem .address, .elem .address, abiUInt256, abiUInt256] cd = none := by
  simp [decodeCalldata, decodeCalldataWithMode, decodeCalldataValues_address_address_uint256_uint256_none_huge hbig]

end Reasoning.Theory
