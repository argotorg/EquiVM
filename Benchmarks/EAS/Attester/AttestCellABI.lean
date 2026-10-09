import Benchmarks.EAS.Attester.AttestABI
import Benchmarks.EAS.Attester.AttestRequestsRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestCellValue (input : UInt256) : Value :=
  .tuple [.address ⟨0, by decide⟩, .int 0, .bool true, wordBytes32Value ⟨0⟩,
    .bytes input.toByteArray, .int 0]

theorem attestCellValue_encoding (input : UInt256) :
    encodeABIValue? attestationRequestDataTy (attestCellValue input) =
      some (wordBytes (attestCellWords input)).toList := by
  have ht (ts : List ABIType) (vs : List Value) :
      encodeABIValue? (.tuple ts) (.tuple vs) = encodeABIValues? ts vs := by
    simp only [encodeABIValue?]
  have hb (w : UInt256) : encodeABIValue? bytes32 (wordBytes32Value w) =
      some w.toByteArray.toList := encodeABIValue_bytes32_word w
  have hzero : encodeABIValue? uint256 (.int 0) =
      some (⟨0⟩ : UInt256).toByteArray.toList := encodeABIValue_uint256_word ⟨0⟩
  have haddr : encodeABIValue? addr (.address ⟨0, by decide⟩) =
      some (⟨0⟩ : UInt256).toByteArray.toList := by native_decide
  have h64 : encodeABIValue? uint64 (.int 0) =
      some (⟨0⟩ : UInt256).toByteArray.toList := by native_decide
  have hbool : encodeABIValue? boolTy (.bool true) =
      some (⟨1⟩ : UInt256).toByteArray.toList := by native_decide
  have hbytes : encodeABIValue? bytesTy (.bytes input.toByteArray) =
      some (natBytes 32 ++ input.toByteArray.toList) := by
    simp [encodeABIValue?, bytesTy, toByteArray_size, padRightToWord, paddedSize, zeroBytes,
      byteArray_toList_eq]
  simp only [attestCellValue, attestationRequestDataTy, ht, encodeABIValues?,
    encodeABIValuesFrom?, hb, hzero, haddr, h64, hbool, hbytes,
    show abiTupleHeadSize? [addr, uint64, boolTy, bytes32, bytesTy, uint256] =
      some 192 by native_decide,
    show isDynamicABIType addr = false from rfl,
    show isDynamicABIType uint64 = false from rfl,
    show isDynamicABIType boolTy = false from rfl,
    show isDynamicABIType bytes32 = false from rfl,
    show isDynamicABIType bytesTy = true from rfl,
    show isDynamicABIType uint256 = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, if_true, List.nil_append, List.append_nil,
    List.length_nil, Nat.add_zero, attestCellWords, wordBytes, byteArray_toList_append,
    ByteArray.append_empty, List.append_assoc]
  simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]
  rfl

def attestArrayValues (values : Nat → UInt256) (i : Nat) : Nat → List Value
  | 0 => []
  | n + 1 => attestCellValue (values i) :: attestArrayValues values (i + 1) n

theorem attestArrayValues_length (values : Nat → UInt256) (i n : Nat) :
    (attestArrayValues values i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [attestArrayValues, List.length_cons, ih]

theorem attestArrayValues_encoding_from (values : Nat → UInt256) (i n origin dst headSize : Nat)
    (head tail : List UInt8) (hpos : origin + 96 ≤ dst)
    (hoff : headSize + tail.length = dst - origin - 96) :
    encodeABIDynamicArrayElemsFrom? attestationRequestDataTy
      (attestArrayValues values i n) headSize head tail =
        some (head ++ (wordBytes (attestArrayOffsetWords origin dst n)).toList ++
          tail ++ (wordBytes (attestArrayTailWords values i n)).toList) := by
  induction n generalizing i dst head tail with
  | zero =>
      have hempty : ByteArray.empty.toList = [] := by simp [byteArray_toList_eq]
      simp only [attestArrayValues, encodeABIDynamicArrayElemsFrom?, attestArrayOffsetWords,
        attestArrayTailWords, wordBytes, hempty, List.append_nil]
  | succ n ih =>
      have hlen : (wordBytes (attestCellWords (values i))).toList.length = 256 := by
        rw [byteArray_toList_eq, Array.length_toList]
        change (wordBytes _).size = _
        rw [wordBytes_size]
        rfl
      rw [attestArrayValues, encodeABIDynamicArrayElemsFrom?, attestCellValue_encoding]
      simp only [bind, Option.bind]
      rw [ih (i + 1) (dst + 256) _ _ (by omega)
        (by rw [List.length_append, hlen]; omega)]
      simp only [attestArrayOffsetWords, attestArrayTailWords, wordBytes, wordBytes_append,
        byteArray_toList_append, List.append_assoc, hoff]
      simp only [natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]

theorem attestArrayValues_encoding (values : Nat → UInt256) (n : Nat) :
    encodeABIValue? (.dynamicArray attestationRequestDataTy) (.array (attestArrayValues values 0 n))
        =
      some (natBytes n ++ (wordBytes (attestArrayOffsetWords 0 (96 + 32 * n) n)).toList ++
        (wordBytes (attestArrayTailWords values 0 n)).toList) := by
  have he := attestArrayValues_encoding_from values 0 n 0 (96 + 32 * n) (n * 32) [] []
    (by omega) (by simp; omega)
  simp only [encodeABIValue?, encodeABIArrayElems?,
    show isDynamicABIType attestationRequestDataTy = true from rfl, if_true,
    attestArrayValues_length, he, bind, Option.bind, List.nil_append, List.append_assoc]

theorem attestArrayValues_getElem (values : Nat → UInt256) (i n k : Nat) (hk : k < n) :
    (attestArrayValues values i n)[k]? = some (attestCellValue (values (i + k))) := by
  induction n generalizing i k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => simp only [attestArrayValues, List.getElem?_cons_zero, Nat.add_zero]
      | succ k =>
          simpa only [attestArrayValues, List.getElem?_cons_succ, Nat.add_assoc,
            Nat.add_comm 1 k] using ih (i + 1) k (by omega)

end Benchmarks.EAS.Attester
