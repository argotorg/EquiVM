import Benchmarks.EAS.Attester.AttestMemory
import Benchmarks.EAS.Attester.ABIHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestRequest (schema input : UInt256) : Value :=
  .tuple [wordBytes32Value schema,
    .tuple [.address ⟨0, by decide⟩, .int 0, .bool true, wordBytes32Value ⟨0⟩,
      .bytes input.toByteArray, .int 0]]

def attestRequestWords (schema input : UInt256) : List UInt256 :=
  [⟨32⟩, schema, ⟨64⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨192⟩, ⟨0⟩, ⟨32⟩, input]

theorem attestMemory_readSelector (schema input : UInt256) :
    (attestMemory schema input).readWithPadding 448 4 = attestSelector := by
  let pre := writeCascade (attestMemory0 schema input)
    [(384, ⟨32⟩), (64, ⟨448⟩), (320, ⟨384⟩), (352, ⟨0⟩), (160, ⟨192⟩)]
  have heq : attestMemory schema input = writeCascade pre
      [(448, ⟨0xf17325e700000000000000000000000000000000000000000000000000000000⟩),
        (452, ⟨32⟩), (484, schema), (516, ⟨64⟩), (548, ⟨0⟩), (580, ⟨0⟩), (612, ⟨1⟩),
        (644, ⟨0⟩), (676, ⟨192⟩), (740, ⟨32⟩), (772, input), (804, ⟨0⟩), (708, ⟨0⟩)] := by
    simp only [attestMemory, attestMemory4, attestMemory3, attestMemory2, attestMemory1,
      pre, writeCascade]
  have hpre : pre.size = 448 := by
    simp only [pre, attestMemory0, writeCascade, writeWord_sparse_size, solcFreePtrMem_size]
    rfl
  rw [heq, writeCascade_read_window_of_head (start := 0) (len := 4)]
  · decide +kernel
  · rw [hpre]; exact USize.size_pos
  · simp only [hpre, WindowDisjointFromWrites]
    native_decide
  all_goals decide +kernel

set_option maxHeartbeats 1000000 in
theorem attestMemory_readWords (schema input : UInt256) :
    (attestMemory schema input).readWithPadding 452 352 =
      ((attestRequestWords schema input).map UInt256.toByteArray).foldr (· ++ ·) ByteArray.empty :=
          by
  apply readWithPadding_words (words := attestRequestWords schema input)
  · simp only [attestMemory_size, attestRequestWords, List.length_cons, List.length_nil]; decide
  intro i
  change Fin 11 at i
  fin_cases i <;> simp only [attestRequestWords, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals apply readWord_of_memLoad
  all_goals try (rw [attestMemory_size]; decide)
  all_goals try decide
  all_goals
    simp only [attestMemory, attestMemory4, attestMemory3, attestMemory2, attestMemory1,
      attestMemory0, writeCascade, Reasoning.Theory.writeWord]
    simp (disch := (first | decide +kernel |
      (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
      [memLoad_write_same, memLoad_write_disjoint]
    rfl

theorem attestMemory_read (schema input : UInt256) :
    (attestMemory schema input).readWithPadding 448 356 = attestSelector ++
      ((attestRequestWords schema input).map UInt256.toByteArray).foldr (· ++ ·) ByteArray.empty :=
          by
  rw [show 356 = 4 + 352 by rfl, readWithPadding_split _ _ _ _
    (by rw [attestMemory_size]; decide), attestMemory_readSelector, attestMemory_readWords]

theorem encodeInput (input : UInt256) :
    config.externalABI.encode? "__abi_encode_uint256" [.int (Int.ofNat input.toNat)] =
      some (abiEncodeUint256Selector ++ input.toByteArray) := by
  change encodeCallWithSelector? abiEncodeUint256Selector [uint256] [_] = _
  have hu : encodeABIValue? uint256 (.int (Int.ofNat input.toNat)) =
      some input.toByteArray.toList := encodeABIValue_uint256_word input
  simp only [encodeCallWithSelector?, encodeABIValues?, encodeABIValuesFrom?, hu,
    show abiTupleHeadSize? [uint256] = some 32 by native_decide,
    show isDynamicABIType uint256 = false by rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    byteArray_toList_toByteArray]

theorem attestRequest_encoding (schema input : UInt256) :
    config.externalABI.encode? "attest" [attestRequest schema input] =
      some ((attestMemory schema input).readWithPadding 448 356) := by
  rw [attestMemory_read]
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
  change encodeCallWithSelector? attestSelector [attestationRequestTy]
    [attestRequest schema input] = _
  simp only [encodeCallWithSelector?, attestRequest, attestationRequestTy,
    attestationRequestDataTy, encodeABIValues?, encodeABIValuesFrom?, ht, hb, hzero,
    haddr, h64, hbool, hbytes,
    show abiTupleHeadSize? [.tuple [bytes32, .tuple [addr, uint64, boolTy, bytes32, bytesTy,
        uint256]]] =
      some 32 by native_decide,
    show abiTupleHeadSize? [bytes32, .tuple [addr, uint64, boolTy, bytes32, bytesTy, uint256]] =
      some 64 by native_decide,
    show abiTupleHeadSize? [addr, uint64, boolTy, bytes32, bytesTy,
        uint256] = some 192 by native_decide,
    show isDynamicABIType (.tuple [bytes32, .tuple [addr, uint64, boolTy, bytes32, bytesTy,
        uint256]]) =
      true by rfl,
    show isDynamicABIType (.tuple [addr, uint64, boolTy, bytes32, bytesTy, uint256]) = true by rfl,
    show isDynamicABIType addr = false by rfl,
    show isDynamicABIType uint64 = false by rfl,
    show isDynamicABIType boolTy = false by rfl,
    show isDynamicABIType bytes32 = false by rfl,
    show isDynamicABIType bytesTy = true by rfl,
    show isDynamicABIType uint256 = false by rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, if_true, List.nil_append, List.append_nil,
    List.length_nil, Nat.add_zero, attestRequestWords, List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, list_toByteArray_append, byteArray_toList_toByteArray]
  simp only [natBytes_toByteArray, ByteArray.append_assoc, ByteArray.append_empty]
  rfl

end Benchmarks.EAS.Attester
