import EVMReasoning.ABI
import Solm.Semantics.ValueOps

/-! # ABI decoding facts phrased with Sol⁻'s `lookupNth?` (array element access). -/


namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM

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

end Reasoning.Theory
