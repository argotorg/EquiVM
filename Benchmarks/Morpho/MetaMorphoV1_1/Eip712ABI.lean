import Benchmarks.Morpho.MetaMorphoV1_1.Eip712Source
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderMemory
import Benchmarks.EAS.Attester.WordSequenceMemory
import Reasoning.ABIViews

/-! The seven-field ABI return encoding of `eip712Domain`. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def eip712FieldsWord : UInt256 := UInt256.shiftLeft (UInt256.ofNat 15) (UInt256.ofNat 248)

def eip712HeadWords (I : ExecutionEnv) (name version : ByteArray) : List UInt256 :=
  [eip712FieldsWord, ⟨224⟩, UInt256.ofNat (256 + paddedSize name.size),
   UInt256.ofNat Ethereum.chainId, UInt256.ofNat I.codeOwner.val, ⟨0⟩,
   UInt256.ofNat (288 + paddedSize name.size + paddedSize version.size)]

def eip712ReturnBytes (I : ExecutionEnv) (name version : ByteArray) : ByteArray :=
  wordBytes (eip712HeadWords I name version) ++
    (stringPayloadBytes name ++ (stringPayloadBytes version ++ (⟨0⟩ : UInt256).toByteArray))

-- LIBRARY CANDIDATE: the size and ABI value encoding of an individual dynamic string tail.
theorem stringPayloadBytes_size (bytes : ByteArray) :
    (stringPayloadBytes bytes).size = 32 + paddedSize bytes.size := by
  have h : bytes.size ≤ paddedSize bytes.size := by unfold paddedSize; omega
  simp only [stringPayloadBytes, ByteArray.size_append, toByteArray_size,
    ByteArray_zeroes_size]
  omega

theorem encodeABIStringPayload (bytes : ByteArray) :
    encodeABIValue? .string (.bytes bytes) = some (stringPayloadBytes bytes).toList := by
  have h : (natBytes bytes.size ++ padRightToWord bytes.toList).toByteArray =
      stringPayloadBytes bytes := by
    rw [List.toByteArray_append, natBytes_toByteArray, padRightToWord_toByteArray]
    rfl
  rw [encodeABIValue?]
  congr 1
  simpa [byteArray_toList_eq] using congrArg ByteArray.toList h

theorem eip712ReturnEncoding (evm : State) (v : MetaMorphoV1_1Immutables) :
    encodeReturnValues? eip712DomainTransition.returnType (eip712ReturnValues evm v) =
      some (eip712ReturnBytes evm.executionEnv
        (domainStringBytes v false evm) (domainStringBytes v true evm)) := by
  have hf : encodeABIValue? (.elem (.bytes 0)) (.fixedBytes 0 [15]) =
      some eip712FieldsWord.toByteArray.toList := by native_decide
  have hz : encodeABIValue? abiBytes32 (.fixedBytes 31 (List.replicate 32 0)) =
      some (⟨0⟩ : UInt256).toByteArray.toList := by native_decide
  have hc : encodeABIValue? abiUInt256 (.int (Int.ofNat Ethereum.chainId)) =
      some (UInt256.ofNat Ethereum.chainId).toByteArray.toList := by
    exact encodeABIValue_uint256_word (UInt256.ofNat Ethereum.chainId)
  have he : encodeABIValue? (.dynamicArray abiUInt256) (.array []) = some (natBytes 0) := by
    simp only [encodeABIValue?, encodeABIArrayElems?, isDynamicABIType,
      Bool.false_eq_true, if_false, encodeABIStaticArrayElems?, bind, Option.bind,
      List.length_nil, List.append_nil]
  have ht : eip712DomainTransition.returnType =
      [.elem (.bytes 0), .string, .string, abiUInt256, abiAddress, abiBytes32,
        .dynamicArray abiUInt256] := rfl
  have hh : abiTupleHeadSize? eip712DomainTransition.returnType = some 224 := by
    rw [ht]
    simp only [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
      if_true, Bool.false_eq_true, if_false]
  have hl (bytes : ByteArray) : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [encodeReturnValues?, encodeABIValues?, hh]
  simp only [ht, eip712ReturnValues, encodeABIValuesFrom?, hf, hz, hc, he,
    encodeABIStringPayload, encodeABIValue_this_address, isDynamicABIType,
    bind, Option.bind, if_true, Bool.false_eq_true, if_false, List.nil_append,
    List.append_nil, List.length_nil, List.length_append, hl, Nat.add_zero,
    stringPayloadBytes_size]
  rw [mk_toArray_eq]
  simp only [List.toByteArray_append, natBytes_toByteArray, byteArray_toList_toByteArray]
  simp only [eip712ReturnBytes, eip712HeadWords, wordBytes, ByteArray.append_empty,
    ByteArray.append_assoc]
  rw [show 224 + (32 + paddedSize (domainStringBytes v false evm).size) =
      256 + paddedSize (domainStringBytes v false evm).size by omega,
    show 224 + (32 + paddedSize (domainStringBytes v false evm).size +
        (32 + paddedSize (domainStringBytes v true evm).size)) =
      288 + paddedSize (domainStringBytes v false evm).size +
        paddedSize (domainStringBytes v true evm).size by omega]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
