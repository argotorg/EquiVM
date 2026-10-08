import Benchmarks.EAS.Attester.WordSequenceMemory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: canonical ABI encoding of a bytes32 array.
def wordArrayWords (values : Nat → UInt256) (i : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => values i :: wordArrayWords values (i + 1) n

def wordArrayValues (values : Nat → UInt256) (i n : Nat) : List Value :=
  (wordArrayWords values i n).map wordBytes32Value

theorem wordArrayWords_length (values : Nat → UInt256) (i n : Nat) :
    (wordArrayWords values i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [wordArrayWords, List.length_cons, ih]

theorem wordArrayValues_length (values : Nat → UInt256) (i n : Nat) :
    (wordArrayValues values i n).length = n := by
  simp only [wordArrayValues, List.length_map, wordArrayWords_length]

theorem wordArrayWords_getElem (values : Nat → UInt256) (i n k : Nat) (hk : k < n) :
    (wordArrayWords values i n)[k]? = some (values (i + k)) := by
  induction n generalizing i k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => simp only [wordArrayWords, List.getElem?_cons_zero, Nat.add_zero]
      | succ k =>
          simpa only [wordArrayWords, List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 k]
            using ih (i + 1) k (by omega)

theorem wordArrayValues_getElem (values : Nat → UInt256) (i n k : Nat) (hk : k < n) :
    (wordArrayValues values i n)[k]? = some (wordBytes32Value (values (i + k))) := by
  simp only [wordArrayValues, List.getElem?_map, wordArrayWords_getElem _ _ _ _ hk, Option.map_some]

theorem wordArrayValues_encoding (values : Nat → UInt256) (i n : Nat) :
    encodeABIStaticArrayElems? abiBytes32 (wordArrayValues values i n) =
      some (wordBytes (wordArrayWords values i n)).toList := by
  induction n generalizing i with
  | zero =>
      simp [wordArrayValues, wordArrayWords, encodeABIStaticArrayElems?, wordBytes,
        byteArray_toList_eq]
  | succ n ih =>
      rw [show wordArrayValues values i (n + 1) =
        wordBytes32Value (values i) :: wordArrayValues values (i + 1) n from rfl,
        encodeABIStaticArrayElems?, encodeABIValue_bytes32_word, ih]
      simp only [bind, Option.bind, wordArrayWords, wordBytes, byteArray_toList_append]

theorem wordArrayReturn_encoding (values : Nat → UInt256) (n : Nat) :
    encodeReturnValue? (.dynamicArray abiBytes32) (.array (wordArrayValues values 0 n)) =
      some (wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n)) := by
  have he : encodeABIValue? (.dynamicArray abiBytes32) (.array (wordArrayValues values 0 n)) =
      some (natBytes n ++ (wordBytes (wordArrayWords values 0 n)).toList) := by
    simp only [encodeABIValue?, encodeABIArrayElems?,
      show isDynamicABIType abiBytes32 = false from rfl, Bool.false_eq_true, if_false,
      wordArrayValues_encoding, wordArrayValues_length, bind, Option.bind]
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    show abiTupleHeadSize? [.dynamicArray abiBytes32] = some 32 by native_decide,
    show isDynamicABIType (.dynamicArray abiBytes32) = true from rfl,
    if_true, he, bind, Option.bind, List.length_nil, Nat.add_zero,
    List.nil_append, List.append_nil, wordBytes_append, wordBytes,
    list_toByteArray_append, byteArray_toList_toByteArray, natBytes_toByteArray,
    ByteArray.append_empty, ByteArray.append_assoc]
  rw [mk_toArray_eq, list_toByteArray_append, list_toByteArray_append,
    natBytes_toByteArray, natBytes_toByteArray, byteArray_toList_toByteArray]

end Reasoning.Theory
