import Benchmarks.Safe.V2_0e91d99.WordCallResult
import Benchmarks.Safe.V2_0e91d99.Bytes4ReturnDecoder
import Benchmarks.Safe.V2_0e91d99.PreModuleCallEncoding

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99

set_option maxHeartbeats 1000000

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

theorem signatureMagicWord_canonical :
    signatureMagicWord = UInt256.land signatureMagicWord bytes4Mask := by native_decide

theorem signatureMagicWord_value :
    bytes4WordValue signatureMagicWord = .fixedBytes bytes4Width [0x16, 0x26, 0xba, 0x7e] := by
  native_decide

def contractSignatureFinalFrame (owner : EVM.Address) (hash : UInt256) (signature : ByteArray)
    (_z : Bool) (out : ByteArray) : Frame :=
  { contractSignatureFrame owner hash signature with
    locals := (contractSignatureArgs owner hash signature).insert
      "sigResult" (bytes4WordValue (calldataWord out 0)) }

def contractSignatureResult (z : Bool) (out : ByteArray) : Bool :=
  z && (decide (32 ≤ out.size) && decide (calldataWord out 0 = signatureMagicWord))

def contractSignatureDecoded (z : Bool) (out : ByteArray) : Bool :=
  z && (decide (32 ≤ out.size) &&
    decide (calldataWord out 0 = UInt256.land (calldataWord out 0) bytes4Mask))

theorem contractSignatureResult_of_not_decoded {z : Bool} {out : ByteArray}
    (hd : contractSignatureDecoded z out = false) : contractSignatureResult z out = false := by
  cases z <;> simp only [contractSignatureDecoded, contractSignatureResult, Bool.false_and,
    Bool.true_and] at hd ⊢
  by_cases hl : 32 ≤ out.size
  · simp only [hl, decide_true, Bool.true_and] at hd ⊢
    apply decide_eq_false (fun he ↦ ?_)
    rw [he] at hd
    have hm := signatureMagicWord_canonical
    rw [decide_eq_true hm] at hd
    contradiction
  · simp only [hl, decide_false, Bool.false_and]

theorem evalContractSignatureResult (evm : EVM.State) (owner : EVM.Address) (hash : UInt256)
    (signature : ByteArray) (out : ByteArray) (hl : 32 ≤ out.size)
    (hd : calldataWord out 0 = UInt256.land (calldataWord out 0) bytes4Mask) :
    evalExpr? config (contractSignatureFinalFrame owner hash signature true out) evm
      (eqE (.var "sigResult") (fixedBytes4Lit 0x16 0x26 0xba 0x7e)) =
      .ok (.bool (contractSignatureResult true out)) := by
  simp only [eqE, evalExpr?, contractSignatureFinalFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert_self, fixedBytes4Lit, EvalResult.ofOption,
    bind, EvalResult.bind, pure]
  change EvalResult.ok (Value.bool (bytes4WordValue (calldataWord out 0) ==
    .fixedBytes bytes4Width [0x16, 0x26, 0xba, 0x7e])) = _
  rw [← signatureMagicWord_value, bytes4WordValue_beq hd signatureMagicWord_canonical]
  simp only [contractSignatureResult, hl, decide_true, Bool.true_and]

theorem safeContractSignatureSource {evm evm' : EVM.State} {owner : EVM.Address}
    {hash : UInt256} {signature out : ByteArray} {z : Bool} (hb : out.size < 2 ^ 255)
    (hc : callViaEVM fork evm (EVM.address owner) 0 (contractSignatureCallBytes hash signature)
      (z, evm', out) false) :
    ExecFuncBody fork config (contractSignatureFrame owner hash signature) evm
      validateContractSignatureFunction.body
      (if contractSignatureDecoded z out then
        .returned (contractSignatureFinalFrame owner hash signature z out) evm'
          (some [.bool (contractSignatureResult z out)]) else .reverted) := by
  have ht : evalExpr? config (contractSignatureFrame owner hash signature) evm (.var "owner") =
      .ok (.address owner) := by
    simp [evalExpr?, contractSignatureFrame, contractSignatureArgs, Std.HashMap.getElem_insert,
      EvalResult.ofOption, pure]
  have hv : evalExpr? config (contractSignatureFrame owner hash signature) evm (.intLit 0) =
      .ok (.int 0) := by simp [evalExpr?, pure]
  have ha : evalExprs? config (contractSignatureFrame owner hash signature) evm
      [.var "dataHash", .var "signature"] =
      .ok [wordBytes32Value hash, .bytes signature] := by
    simp [evalExprs?, evalExpr?, contractSignatureFrame, contractSignatureArgs,
      Std.HashMap.getElem_insert, EvalResult.ofOption, EvalResult.bind, bind, pure]
  have hcall : typedCallViaEVM fork config evm (EVM.address owner) "isValidSignature" 0
      [wordBytes32Value hash, .bytes signature] (z, evm', out) false := by
    exact ⟨_, contractSignatureCallEncoding _ _, hc⟩
  cases z with
  | false =>
      simp only [contractSignatureDecoded, Bool.false_and, Bool.false_eq_true, if_false]
      exact .execBlockRevert (.consRevert (.externalCallFailure (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ht hv ha hcall))
  | true =>
      by_cases hl : 32 ≤ out.size
      swap
      · simp only [contractSignatureDecoded, hl, decide_false, Bool.false_and, Bool.and_false,
          Bool.false_eq_true, if_false]
        apply ExecFuncBody.execBlockRevert
        apply ExecBlock.consRevert
        apply ExecStmt.externalCallReturnDecodeRevert (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ht hv ha hcall
        change (ABI.decodeReturnValueWithMode? .modern abiBytes4 out).map (fun v ↦ [v]) = none
        rw [decodeBytes4ReturnShort (by omega)]; rfl
      by_cases hd : calldataWord out 0 = UInt256.land (calldataWord out 0) bytes4Mask
      · simp only [contractSignatureDecoded, hl, decide_eq_true hd, decide_true,
          Bool.and_self, if_true]
        apply ExecFuncBody.execBlockRet
        refine .consNormal ?_ (.consReturn (.return (evalExprs?_singleton
          (evalContractSignatureResult evm' owner hash signature out hl hd))))
        apply ExecStmt.externalCallSuccess (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := [bytes4WordValue (calldataWord out 0)])
          ht hv ha hcall
        change (ABI.decodeReturnValueWithMode? .modern abiBytes4 out).map (fun v ↦ [v]) =
          some [bytes4WordValue (calldataWord out 0)]
        rw [decodeBytes4ReturnLong hl hb, if_pos hd, bytes4WordValue_calldata hl]
        rfl
      · simp only [contractSignatureDecoded, hd, decide_false, Bool.and_false,
          Bool.false_eq_true, if_false]
        apply ExecFuncBody.execBlockRevert
        apply ExecBlock.consRevert
        apply ExecStmt.externalCallReturnDecodeRevert (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ht hv ha hcall
        change (ABI.decodeReturnValueWithMode? .modern abiBytes4 out).map (fun v ↦ [v]) = none
        rw [decodeBytes4ReturnLong hl hb, if_neg hd]; rfl

end Benchmarks.Safe.V2_0e91d99
