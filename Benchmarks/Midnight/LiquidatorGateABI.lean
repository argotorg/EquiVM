import Benchmarks.Midnight.SafeTransferABI
import Benchmarks.Midnight.BoolDecode

/-! The liquidator gate's address argument and canonical boolean reply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidatorGateSelector : ByteArray := ⟨#[0xb9, 0xf4, 0xff, 0x55]⟩

def liquidatorGateSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 3119841109) (UInt256.ofNat 224)

def liquidatorGateCalldata (caller : AccountAddress) : ByteArray :=
  liquidatorGateSelector ++ (UInt256.ofNat caller.val).toByteArray

theorem liquidatorGateSelectorWord_bytes :
    liquidatorGateSelectorWord.toByteArray.extract 0 4 = liquidatorGateSelector := by
  decide +kernel

theorem encodeLiquidatorGate (caller : AccountAddress) :
    config.externalABI.encode? "canLiquidate" [.address caller] =
      some (liquidatorGateCalldata caller) := by
  have ha := encodeABIValue_accountAddress caller
  simp only [config, externalABI, Model.abiValues, Model.abiValue, String.reduceEq,
    if_false, if_true, encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?,
    staticABIEncodedSize?, isDynamicABIType, Bool.false_eq_true, bind, Option.bind,
    encodeABIValuesFrom?, ha, List.nil_append, List.append_nil,
    liquidatorGateCalldata, liquidatorGateSelector, List.toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray]

-- LIBRARY CANDIDATE: decoding a bool from a bounded one-word return-data slice.
theorem decodeReturnBoolSlice (out : ByteArray) :
    decodeReturnValues? [(.elem .bool)] (out.extract 0 32) =
      if 32 ≤ out.size ∧ (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) then
        some [wordToElem .bool (calldataWord out 0)] else none := by
  have hl : (out.extract 0 32).toList.length = min 32 out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (out.extract 0 32).size = _
    rw [ByteArray.size_extract]
    omega
  have he : (out.extract 0 32).toList = out.toList.take 32 := by
    simp only [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by rw [hl]; omega)]
  by_cases hs : 32 ≤ out.size
  · have hlen : ((out.extract 0 32).toList.drop 0 |>.take 32).length = 32 := by
      simp only [List.drop_zero, List.length_take, hl]
      omega
    have hw : bytesToWord ((out.extract 0 32).toList.drop 0 |>.take 32) =
        calldataWord out 0 := by
      simpa only [he, List.drop_zero, List.take_take, Nat.min_self] using
        decode_word_at_eq_any out 0 hs
    simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, hlen,
      if_true, bind, Option.bind, hw, decodeABIWord_bool, hs, true_and]
    by_cases hc : calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩ <;>
      simp only [hc, if_true, if_false] <;> rfl
  · have hlen : ((out.extract 0 32).toList.drop 0 |>.take 32).length ≠ 32 := by
      simp only [List.drop_zero, List.length_take, hl]
      omega
    simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?,
      if_neg hlen, bind, Option.bind, hs, false_and, if_false]

theorem decodeLiquidatorGate (out : ByteArray) :
    config.externalABI.decode? "canLiquidate" out =
      if 32 ≤ out.size ∧ (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) then
        some [wordToElem .bool (calldataWord out 0)] else none :=
  decodeReturnBoolSlice out

end Benchmarks.Midnight
