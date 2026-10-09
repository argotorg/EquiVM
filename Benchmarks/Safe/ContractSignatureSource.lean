import Benchmarks.Safe.WordCallResult
import Benchmarks.Safe.Bytes32ReturnDecoder
import Benchmarks.Safe.PreModuleCallEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def signatureMagicWord : UInt256 := UInt256.shiftLeft ⟨371636862⟩ ⟨224⟩

def contractSignatureCallBytes (hash : UInt256) (signature : ByteArray) : ByteArray :=
  isValidSignatureSelector ++ wordBytes [hash, ⟨64⟩, UInt256.ofNat signature.size] ++
    signature ++ ByteArray.zeroes (ABI.paddedSize signature.size - signature.size)

theorem contractSignatureCallEncoding (hash : UInt256) (signature : ByteArray) :
    config.externalABI.encode? "isValidSignature" [wordBytes32Value hash, .bytes signature] =
      some (contractSignatureCallBytes hash signature) := by
  have hh := encodeABIValue_bytes32_word hash
  change ABI.encodeCallWithSelector? isValidSignatureSelector [bytes32, bytesTy] _ = _
  simp only [bytes32, bytes32Width, bytesTy, wordBytes32Value, abiBytes32, abiBytes32Width]
    at hh ⊢
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, encodeABIValuesFrom?, hh, bind, Option.bind, pure,
    Bool.false_eq_true, Bool.true_eq, ite_false, ite_true, List.nil_append, List.append_nil,
    List.length_nil, Nat.add_zero]
  simp only [encodeABIValue?, bind, Option.bind, pure, List.nil_append, List.append_nil,
    list_toByteArray_append, natBytes_toByteArray, padRightToWord_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray, byteArray_toList_toByteArray]
  simp only [contractSignatureCallBytes, wordBytes, ByteArray.append_empty,
    ByteArray.append_assoc]
  rfl

def contractSignatureArgs (owner : EVM.Address) (hash : UInt256) (signature : ByteArray) :
    Store :=
  (((∅ : Store).insert "signature" (.bytes signature)).insert
    "dataHash" (wordBytes32Value hash)).insert "owner" (.address owner)

def contractSignatureFrame (owner : EVM.Address) (hash : UInt256) (signature : ByteArray) :
    Frame := { contract := contract, locals := contractSignatureArgs owner hash signature }

def contractSignatureFinalFrame (owner : EVM.Address) (hash : UInt256) (signature : ByteArray)
    (z : Bool) (out : ByteArray) : Frame :=
  { contractSignatureFrame owner hash signature with
    locals := ((contractSignatureArgs owner hash signature).insert "sigSuccess" (.bool z)).insert
      "sigResult" (.bytes out) }

def contractSignatureResult (z : Bool) (out : ByteArray) : Bool :=
  z && (decide (out.size = 32) && decide (calldataWord out 0 = signatureMagicWord))

theorem evalContractSignatureResult (evm : EVM.State) (owner : EVM.Address) (hash : UInt256)
    (signature : ByteArray) (z : Bool) (out : ByteArray) :
    evalExpr? config (contractSignatureFinalFrame owner hash signature z out) evm
      (andE (.var "sigSuccess") (andE (eqE (localLength "sigResult") (.intLit 32))
        (eqE (.abiDecode bytes32 (.var "sigResult")) eip1271MagicBytes32))) =
      .ok (.bool (contractSignatureResult z out)) := by
  apply evalWordCallResult
    (by simp [contractSignatureFinalFrame, Std.HashMap.getElem_insert])
    (by simp [contractSignatureFinalFrame, Std.HashMap.getElem_insert])
  intro ho
  have hd := decodeBytes32ReturnLong (out := out) (by omega) (by rw [ho]; decide)
  change ABI.decodeReturnValueWithMode? config.abiDecodeMode bytes32 out =
    some (wordBytes32Value (calldataWord out 0)) at hd
  have hm : eip1271MagicBytes32 =
      .fixedBytesLit bytes32Width (EVM.Word.toBytesBE signatureMagicWord) := by native_decide
  simp only [eqE, evalExpr?, contractSignatureFinalFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert_self,
    String.reduceEq, if_true, EvalResult.ofOption, bind, EvalResult.bind, pure, hd, hm]
  change EvalResult.ok (Value.bool (wordBytes32Value (calldataWord out 0) ==
    wordBytes32Value signatureMagicWord)) = _
  rw [wordBytes32Value_beq]

theorem safeContractSignatureSource {evm evm' : EVM.State} {owner : EVM.Address}
    {hash : UInt256} {signature out : ByteArray} {z : Bool}
    (hc : callViaEVM evm (EVM.address owner) 0 (contractSignatureCallBytes hash signature)
      (z, evm', out) false) :
    ExecFuncBody config (contractSignatureFrame owner hash signature) evm
      validateContractSignatureFunction.body
      (.returned (contractSignatureFinalFrame owner hash signature z out) evm'
        (some [.bool (contractSignatureResult z out)])) := by
  apply ExecFuncBody.execBlockRet
  refine .consNormal ?_ (.consReturn (.return (evalExprs?_singleton
    (evalContractSignatureResult evm' owner hash signature z out))))
  have ht : evalExpr? config (contractSignatureFrame owner hash signature) evm (.var "owner") =
      .ok (.address owner) := by
    simp [evalExpr?, contractSignatureFrame, contractSignatureArgs, Std.HashMap.getElem_insert,
      EvalResult.ofOption, pure]
  have hv : evalExpr? config (contractSignatureFrame owner hash signature) evm (.intLit 0) =
      .ok (.int 0) := by simp [evalExpr?, pure]
  have hd : evalExpr? config (contractSignatureFrame owner hash signature) evm
      (.abiEncodeCall "isValidSignature" [.var "dataHash", .var "signature"]) =
      .ok (.bytes (contractSignatureCallBytes hash signature)) := by
    simp [evalExpr?, evalExprList?, contractSignatureFrame, contractSignatureArgs,
      Std.HashMap.getElem_insert, EvalResult.ofOption, EvalResult.bind, bind, pure,
      contractSignatureCallEncoding]
  cases z
  · exact .lowLevelCallFailure ht hv hd hc
  · exact .lowLevelCallSuccess ht hv hd hc

end Benchmarks.Safe
