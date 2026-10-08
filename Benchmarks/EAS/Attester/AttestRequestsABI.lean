import Benchmarks.EAS.Attester.AttestCellABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

private theorem empty_toList : ByteArray.empty.toList = [] := by
  simp [byteArray_toList_eq]

def attestBatchRowValue (schema : UInt256) (n : Nat) (values : Nat → UInt256) : Value :=
  .tuple [wordBytes32Value schema, .array (attestArrayValues values 0 n)]

theorem attestBatchRowValue_encoding (schema : UInt256) (n : Nat)
    (values : Nat → UInt256) :
    encodeABIValue? (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)])
      (attestBatchRowValue schema n values) = some (wordBytes (attestBatchRowWords schema n
          values)).toList := by
  have ht (ts : List ABIType) (vs : List Value) :
      encodeABIValue? (.tuple ts) (.tuple vs) = encodeABIValues? ts vs := by
    simp only [encodeABIValue?]
  have hh : abiTupleHeadSize?
      [bytes32, .dynamicArray (attestationRequestDataTy)] = some 64 := by native_decide
  have hd := attestArrayValues_encoding values n
  have hb : encodeABIValue? bytes32 (wordBytes32Value schema) =
      some schema.toByteArray.toList := encodeABIValue_bytes32_word schema
  simp only [attestBatchRowValue, ht, encodeABIValues?, hh, encodeABIValuesFrom?, hb, hd,
    show isDynamicABIType bytes32 = false from rfl,
    show isDynamicABIType (.dynamicArray (attestationRequestDataTy)) = true from rfl,
    Bool.false_eq_true, if_false, if_true, bind, Option.bind,
    List.nil_append, List.append_nil, List.length_nil, Nat.add_zero,
    attestBatchRowWords, wordBytes_append, wordBytes, byteArray_toList_append,
    ByteArray.append_empty, List.append_assoc]
  simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]

def attestRequestsValues (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (i : Nat) : Nat → List Value
  | 0 => []
  | n + 1 => attestBatchRowValue (schemas i) (counts i) (values i) ::
      attestRequestsValues schemas counts values (i + 1) n

theorem attestRequestsValues_length (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (i n : Nat) :
    (attestRequestsValues schemas counts values i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [attestRequestsValues, List.length_cons, ih]

theorem attestRequestsValues_encoding_from (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (i n origin dst headSize : Nat)
    (head tail : List UInt8) (hpos : origin + 64 ≤ dst)
    (hoff : headSize + tail.length = dst - origin - 64) :
    encodeABIDynamicArrayElemsFrom?
      (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)])
      (attestRequestsValues schemas counts values i n) headSize head tail =
        some (head ++ (wordBytes (attestRequestsOffsetWords origin dst counts i n)).toList ++
          tail ++ (wordBytes (attestRequestsTailWords schemas counts values i n)).toList) := by
  induction n generalizing i dst head tail with
  | zero => simp only [attestRequestsValues, encodeABIDynamicArrayElemsFrom?,
      attestRequestsOffsetWords, attestRequestsTailWords, wordBytes,
      empty_toList, List.append_nil]
  | succ n ih =>
      have hlen : (wordBytes (attestBatchRowWords (schemas i) (counts i) (values i))).toList.length
          =
          96 + 288 * counts i := by
        rw [byteArray_toList_eq, Array.length_toList]
        change (wordBytes _).size = _
        rw [wordBytes_size, attestBatchRowWords_length]; omega
      rw [attestRequestsValues, encodeABIDynamicArrayElemsFrom?, attestBatchRowValue_encoding]
      simp only [bind, Option.bind]
      rw [ih (i + 1) (dst + 96 + 288 * counts i) _ _ (by omega)
        (by rw [List.length_append, hlen]; omega)]
      simp only [attestRequestsOffsetWords, attestRequestsTailWords, wordBytes, wordBytes_append,
        byteArray_toList_append, List.append_assoc, hoff]
      simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]

theorem attestRequestsValues_encoding (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (origin n : Nat) :
    encodeABIValues?
      [.dynamicArray (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)])]
      [.array (attestRequestsValues schemas counts values 0 n)] =
        some (wordBytes (attestRequestsABIWords origin n schemas counts values)).toList := by
  have hd : isDynamicABIType
      (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)]) = true := rfl
  have hh : abiTupleHeadSize?
      [.dynamicArray (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)])] =
        some 32 := by native_decide
  have he := attestRequestsValues_encoding_from schemas counts values 0 n origin
    (origin + 64 + 32 * n) (n * 32) [] [] (by omega) (by simp; omega)
  have hdata : encodeABIValue?
      (.dynamicArray (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)]))
      (.array (attestRequestsValues schemas counts values 0 n)) =
        some (natBytes n ++ (wordBytes
          (attestRequestsOffsetWords origin (origin + 64 + 32 * n) counts 0 n)).toList ++
          (wordBytes (attestRequestsTailWords schemas counts values 0 n)).toList) := by
    simp only [encodeABIValue?, encodeABIArrayElems?, hd, if_true,
      attestRequestsValues_length, he, bind, Option.bind, List.nil_append, List.append_assoc]
  simp only [encodeABIValues?, hh, encodeABIValuesFrom?, hdata,
    show isDynamicABIType
      (.dynamicArray (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)])) =
      true from rfl,
    if_true, bind, Option.bind, List.nil_append, List.append_nil, List.length_nil, Nat.add_zero,
    attestRequestsABIWords, wordBytes_append, wordBytes, ByteArray.append_empty,
    byteArray_toList_append, List.append_assoc]
  simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]

theorem attestRequestsValues_getElem (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (i n k : Nat) (hk : k < n) :
    (attestRequestsValues schemas counts values i n)[k]? =
      some (attestBatchRowValue (schemas (i + k)) (counts (i + k)) (values (i + k))) := by
  induction n generalizing i k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => simp only [attestRequestsValues, List.getElem?_cons_zero, Nat.add_zero]
      | succ k =>
          simpa only [attestRequestsValues, List.getElem?_cons_succ, Nat.add_assoc,
            Nat.add_comm 1 k] using ih (i + 1) k (by omega)

end Benchmarks.EAS.Attester
