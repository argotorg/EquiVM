import Benchmarks.EAS.Attester.PairRequestsRead
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

private theorem empty_toList : ByteArray.empty.toList = [] := by
  simp [byteArray_toList_eq]

-- LIBRARY CANDIDATE: ABI encoding of an array of (bytes32, (bytes32, uint256)[]) tuples.
def wordPairValue (p : UInt256 × UInt256) : Value :=
  .tuple [wordBytes32Value p.1, .int (Int.ofNat p.2.toNat)]

def pairSequenceValues (values : Nat → UInt256 × UInt256) (i : Nat) : Nat → List Value
  | 0 => []
  | n + 1 => wordPairValue (values i) :: pairSequenceValues values (i + 1) n

theorem pairSequenceValues_length (values : Nat → UInt256 × UInt256) (i n : Nat) :
    (pairSequenceValues values i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [pairSequenceValues, List.length_cons, ih]

theorem wordPairValue_encoding (p : UInt256 × UInt256) :
    encodeABIValue? (.tuple [abiBytes32, abiUInt256]) (wordPairValue p) =
      some (wordBytes [p.1, p.2]).toList := by
  have ht (ts : List ABIType) (vs : List Value) :
      encodeABIValue? (.tuple ts) (.tuple vs) = encodeABIValues? ts vs := by
    simp only [encodeABIValue?]
  have hh : abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 := by native_decide
  have hb := encodeABIValue_bytes32_word p.1
  have hu := encodeABIValue_uint256_word p.2
  simp only [wordPairValue, ht, encodeABIValues?, hh, encodeABIValuesFrom?, hb, hu,
    show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    Bool.false_eq_true, if_false, Option.bind_some, wordBytes, byteArray_toList_append,
    ByteArray.append_empty, List.nil_append, List.append_nil]
  rfl

theorem pairSequenceValues_encoding (values : Nat → UInt256 × UInt256) (i n : Nat) :
    encodeABIStaticArrayElems? (.tuple [abiBytes32, abiUInt256])
      (pairSequenceValues values i n) = some (wordBytes (pairSequenceWords values i n)).toList := by
  induction n generalizing i with
  | zero => simp only [pairSequenceValues, encodeABIStaticArrayElems?, pairSequenceWords,
      wordBytes, empty_toList]
  | succ n ih =>
      simp only [pairSequenceValues, encodeABIStaticArrayElems?, wordPairValue_encoding, ih,
        bind, Option.bind, pairSequenceWords, wordBytes, byteArray_toList_append,
        ByteArray.append_empty, List.append_assoc]

def pairRequestValue (schema : UInt256) (n : Nat) (values : Nat → UInt256 × UInt256) : Value :=
  .tuple [wordBytes32Value schema, .array (pairSequenceValues values 0 n)]

theorem pairRequestValue_encoding (schema : UInt256) (n : Nat)
    (values : Nat → UInt256 × UInt256) :
    encodeABIValue? (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])])
      (pairRequestValue schema n values) = some (wordBytes (pairRequestWords schema n
          values)).toList := by
  have ht (ts : List ABIType) (vs : List Value) :
      encodeABIValue? (.tuple ts) (.tuple vs) = encodeABIValues? ts vs := by
    simp only [encodeABIValue?]
  have hh : abiTupleHeadSize?
      [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])] = some 64 := by native_decide
  have hd : encodeABIValue? (.dynamicArray (.tuple [abiBytes32, abiUInt256]))
      (.array (pairSequenceValues values 0 n)) =
        some (natBytes n ++ (wordBytes (pairSequenceWords values 0 n)).toList) := by
    simp only [encodeABIValue?, encodeABIArrayElems?,
      show isDynamicABIType (.tuple [abiBytes32, abiUInt256]) = false from rfl,
      Bool.false_eq_true, if_false, pairSequenceValues_encoding, bind, Option.bind,
      pairSequenceValues_length]
  have hb := encodeABIValue_bytes32_word schema
  simp only [pairRequestValue, ht, encodeABIValues?, hh, encodeABIValuesFrom?, hb, hd,
    show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType (.dynamicArray (.tuple [abiBytes32, abiUInt256])) = true from rfl,
    Bool.false_eq_true, if_false, if_true, bind, Option.bind,
    List.nil_append, List.append_nil, List.length_nil, Nat.add_zero,
    pairRequestWords, wordBytes_append, wordBytes, byteArray_toList_append,
    ByteArray.append_empty, List.append_assoc]
  simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]

def pairRequestsValues (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) (i : Nat) : Nat → List Value
  | 0 => []
  | n + 1 => pairRequestValue (schemas i) (counts i) (values i) ::
      pairRequestsValues schemas counts values (i + 1) n

theorem pairRequestsValues_length (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) (i n : Nat) :
    (pairRequestsValues schemas counts values i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [pairRequestsValues, List.length_cons, ih]

theorem pairRequestsValues_encoding_from (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) (i n origin dst headSize : Nat)
    (head tail : List UInt8) (hpos : origin + 64 ≤ dst)
    (hoff : headSize + tail.length = dst - origin - 64) :
    encodeABIDynamicArrayElemsFrom?
      (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])])
      (pairRequestsValues schemas counts values i n) headSize head tail =
        some (head ++ (wordBytes (pairRequestsOffsetWords origin dst counts i n)).toList ++
          tail ++ (wordBytes (pairRequestsTailWords schemas counts values i n)).toList) := by
  induction n generalizing i dst head tail with
  | zero => simp only [pairRequestsValues, encodeABIDynamicArrayElemsFrom?,
      pairRequestsOffsetWords, pairRequestsTailWords, wordBytes,
      empty_toList, List.append_nil]
  | succ n ih =>
      have hlen : (wordBytes (pairRequestWords (schemas i) (counts i) (values i))).toList.length =
          96 + 64 * counts i := by
        rw [byteArray_toList_eq, Array.length_toList]
        change (wordBytes _).size = _
        rw [wordBytes_size, pairRequestWords_length]; omega
      rw [pairRequestsValues, encodeABIDynamicArrayElemsFrom?, pairRequestValue_encoding]
      simp only [bind, Option.bind]
      rw [ih (i + 1) (dst + 96 + 64 * counts i) _ _ (by omega)
        (by rw [List.length_append, hlen]; omega)]
      simp only [pairRequestsOffsetWords, pairRequestsTailWords, wordBytes, wordBytes_append,
        byteArray_toList_append, List.append_assoc, hoff]
      simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]

theorem pairRequestsValues_encoding (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) (origin n : Nat) :
    encodeABIValues?
      [.dynamicArray (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])])]
      [.array (pairRequestsValues schemas counts values 0 n)] =
        some (wordBytes (pairRequestsABIWords origin n schemas counts values)).toList := by
  have hd : isDynamicABIType
      (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])]) = true := rfl
  have hh : abiTupleHeadSize?
      [.dynamicArray (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])])] =
        some 32 := by native_decide
  have he := pairRequestsValues_encoding_from schemas counts values 0 n origin
    (origin + 64 + 32 * n) (n * 32) [] [] (by omega) (by simp; omega)
  have hdata : encodeABIValue?
      (.dynamicArray (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])]))
      (.array (pairRequestsValues schemas counts values 0 n)) =
        some (natBytes n ++ (wordBytes
          (pairRequestsOffsetWords origin (origin + 64 + 32 * n) counts 0 n)).toList ++
          (wordBytes (pairRequestsTailWords schemas counts values 0 n)).toList) := by
    simp only [encodeABIValue?, encodeABIArrayElems?, hd, if_true,
      pairRequestsValues_length, he, bind, Option.bind, List.nil_append, List.append_assoc]
  simp only [encodeABIValues?, hh, encodeABIValuesFrom?, hdata,
    show isDynamicABIType
      (.dynamicArray (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])])) =
      true from rfl,
    if_true, bind, Option.bind, List.nil_append, List.append_nil, List.length_nil, Nat.add_zero,
    pairRequestsABIWords, wordBytes_append, wordBytes, ByteArray.append_empty,
    byteArray_toList_append, List.append_assoc]
  simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]

theorem pairSequenceValues_getElem (values : Nat → UInt256 × UInt256) (i n k : Nat)
    (hk : k < n) : (pairSequenceValues values i n)[k]? = some (wordPairValue (values (i + k))) := by
  induction n generalizing i k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => simp only [pairSequenceValues, List.getElem?_cons_zero, Nat.add_zero]
      | succ k =>
          simpa only [pairSequenceValues, List.getElem?_cons_succ, Nat.add_assoc,
            Nat.add_comm 1 k] using ih (i + 1) k (by omega)

theorem pairRequestsValues_getElem (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) (i n k : Nat) (hk : k < n) :
    (pairRequestsValues schemas counts values i n)[k]? =
      some (pairRequestValue (schemas (i + k)) (counts (i + k)) (values (i + k))) := by
  induction n generalizing i k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => simp only [pairRequestsValues, List.getElem?_cons_zero, Nat.add_zero]
      | succ k =>
          simpa only [pairRequestsValues, List.getElem?_cons_succ, Nat.add_assoc,
            Nat.add_comm 1 k] using ih (i + 1) k (by omega)

end Reasoning.Theory
