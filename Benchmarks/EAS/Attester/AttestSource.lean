import Benchmarks.EAS.Attester.AttestABI
import Reasoning.ExternalCall
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestLocals (schema input : UInt256) : Store :=
  ((∅ : Store).insert "schema" (wordBytes32Value schema)).insert "input" (.int input.toNat)

theorem attesterAttestDecode {cd : ByteArray} (hlen : 68 ≤ cd.size)
    (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (attestTransition.params.map Param.name)
      (transitionSignature attestTransition).paramTypes cd =
        some (attestLocals (calldataWord cd 4) (calldataWord cd 36)) := by
  have hlenList : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h0 := decodeABIValue_bytes32_ok (bytes := cd.toList.drop 4) (start := 0)
    (by simp only [List.drop_zero, List.length_take, List.length_drop, hlenList]; omega)
  have h32 := decodeABIValue_uint256_ok (bytes := cd.toList.drop 4) (start := 32)
    (by simp only [List.length_take, List.length_drop, hlenList]; omega)
  have hd := decodeCalldata_twoWords_ok (x := "schema") (y := "input")
    (by rfl) (by rfl) (by rfl) (by rfl) hlen hhi h0 h32
  simpa only [List.drop_zero, List.drop_drop, Nat.reduceAdd,
    calldata_bytes32_value (cd := cd) (off := 4) (by omega) (by decide),
    decode_word_at_eq cd 36 (by omega) (by decide)] using hd

theorem attesterAttestDecodeShort {cd : ByteArray} (hshort : cd.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (attestTransition.params.map Param.name)
      (transitionSignature attestTransition).paramTypes cd = none :=
  decodeCalldata_head_none_short (headSize := 64) (by native_decide) hshort

theorem attesterAttestDecodeHuge {cd : ByteArray} (hhi : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (attestTransition.params.map Param.name)
      (transitionSignature attestTransition).paramTypes cd = none :=
  decodeCalldata_nonempty_none_huge hhi

def attestFrame (imms : Store) (schema input : UInt256) : Frame :=
  ⟨contract, attestLocals schema input, imms⟩

def attestEasFrame (imms : Store) (eas : EVM.Address) (schema input : UInt256) : Frame :=
  { attestFrame imms schema input with
    locals := (attestLocals schema input).insert "eas" (.address eas) }

def attestEncodedFrame (imms : Store) (eas : EVM.Address) (schema input : UInt256) : Frame :=
  { attestEasFrame imms eas schema input with
    locals := (attestEasFrame imms eas schema input).locals.insert "encodedCall"
      (.bytes (abiEncodeUint256Selector ++ input.toByteArray)) }

def attestCallFrame (imms : Store) (eas : EVM.Address) (schema input : UInt256) : Frame :=
  { attestEncodedFrame imms eas schema input with
    locals := (attestEncodedFrame imms eas schema input).locals.insert "encodedInput" (.bytes
        input.toByteArray) }

theorem encodedInput_extract (input : UInt256) :
    (abiEncodeUint256Selector ++ input.toByteArray).extract 4 36 = input.toByteArray := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.data_append, abiEncodeUint256Selector, selectorBytes,
    Array.extract_append, toByteArray_size]

theorem attestSourcePrefix {imms : Store} {eas : EVM.Address} {schema input : UInt256}
    {evm : State} {result : ExecResult} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hrest : ExecBlock config (attestCallFrame imms eas schema input) evm
      (attestTransition.body.drop 4) result) :
    ExecBlock config (attestFrame imms schema input) evm attestTransition.body result := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .address eas) ?_) ?_
  · change evalExpr? config (attestFrame imms schema input) evm (.immutable "_eas") = _
    simp only [evalExpr?, attestFrame, hget, EvalResult.ofOption]
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (value := .bytes (abiEncodeUint256Selector ++ input.toByteArray)) ?_) ?_
  · change evalExpr? config (attestEasFrame imms eas schema input) evm
      (.abiEncodeCall "__abi_encode_uint256" [.var "input"]) = _
    simp [evalExpr?, evalExprs?, evalExprList?, attestEasFrame, attestLocals, EvalResult.ofOption,
      bind, pure, EvalResult.bind, Std.HashMap.getElem_insert]
    have hinp : config.externalABI.encode? "__abi_encode_uint256" [.int (input.toNat : Int)] =
        some (abiEncodeUint256Selector ++ input.toByteArray) := by simpa using encodeInput input
    rw [hinp]
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes input.toByteArray) ?_) hrest
  change evalExpr? config (attestEncodedFrame imms eas schema input) evm
    (.bytesSlice (.var "encodedCall") (.intLit 4) (.intLit 36)) = _
  simp [evalExpr?, sliceBytes?, attestEncodedFrame, EvalResult.ofOption, bind, pure,
      EvalResult.bind,
    ByteArray.size_append, toByteArray_size, show abiEncodeUint256Selector.size = 4 from rfl,
    encodedInput_extract]

def attestArgExpr : Expr :=
  .tupleLit [.var "schema", .tupleLit [.cast (.intLit 0) (.elem .address), .intLit 0,
    .boolLit true, .fixedBytesLit abiBytes32Width (List.replicate 32 0),
    .var "encodedInput", .intLit 0]]

theorem attestSourceReceiver {imms : Store} {eas : EVM.Address} {schema input : UInt256}
    {evm : State} :
    evalExpr? config (attestCallFrame imms eas schema input) evm (.var "eas") =
      .ok (.address eas) := by
  simp [evalExpr?, attestCallFrame, attestEncodedFrame, attestEasFrame, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem attestSourceArgs {imms : Store} {eas : EVM.Address} {schema input : UInt256}
    {evm : State} :
    evalExprs? config (attestCallFrame imms eas schema input) evm [attestArgExpr] =
      .ok [attestRequest schema input] := by
  simp [evalExprs?, evalExprList?, evalExpr?, attestArgExpr, attestCallFrame, attestEncodedFrame,
    attestEasFrame, attestLocals, attestRequest, EvalResult.ofOption,
    EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
  rw [show castValue? (.int 0) (.elem .address) = some (.address ⟨0, by decide⟩) by native_decide]
  rw [show wordBytes32Value (⟨0⟩ : UInt256) =
    .fixedBytes abiBytes32Width (List.replicate 32 0) by native_decide]
  rfl

theorem attestSourceFailure {imms : Store} {eas : EVM.Address} {schema input : UInt256}
    {evm evm' : State} {out : ByteArray} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hcall : typedCallViaEVM config evm eas "attest" 0 [attestRequest schema input]
      (false, evm', out)) :
    ExecTransitionBody config contract evm (attestLocals schema input) attestTransition.body
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply attestSourcePrefix hvalue hget
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) attestSourceReceiver
    (by simp only [evalExpr?, pure]) attestSourceArgs
    (by simpa only [address_of_val] using hcall))

theorem attestSourceDecodeFailure {imms : Store} {eas : EVM.Address} {schema input : UInt256}
    {evm evm' : State} {out : ByteArray} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hcall : typedCallViaEVM config evm eas "attest" 0 [attestRequest schema input]
      (true, evm', out)) (hdec : config.externalABI.decode? "attest" out = none) :
    ExecTransitionBody config contract evm (attestLocals schema input) attestTransition.body
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply attestSourcePrefix hvalue hget
  exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0)
    attestSourceReceiver (by simp only [evalExpr?, pure]) attestSourceArgs
    (by simpa only [address_of_val] using hcall) hdec)

def attestFinalFrame (imms : Store) (eas : EVM.Address) (schema input uid : UInt256) : Frame :=
  { attestCallFrame imms eas schema input with
    locals := (attestCallFrame imms eas schema input).locals.insert "uid" (wordBytes32Value uid) }

theorem attestSourceSuccess {imms : Store} {eas : EVM.Address} {schema input uid : UInt256}
    {evm evm' : State} {out : ByteArray} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hcall : typedCallViaEVM config evm eas "attest" 0 [attestRequest schema input]
      (true, evm', out))
    (hdec : config.externalABI.decode? "attest" out = some [wordBytes32Value uid]) :
    ExecTransitionBody config contract evm (attestLocals schema input) attestTransition.body
      (.returned (attestFinalFrame imms eas schema input uid) evm'
        (some [wordBytes32Value uid])) imms := by
  apply ExecFuncBody.execBlockRet
  apply attestSourcePrefix hvalue hget
  refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0)
    attestSourceReceiver (by simp only [evalExpr?, pure]) attestSourceArgs
    (by simpa only [address_of_val] using hcall) hdec) ?_
  refine ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExprList?, evalExpr?, EvalResult.ofOption, bind, pure, EvalResult.bind,
    collapseReturns]

theorem attestDecodeReturn_ok {out : ByteArray} (hlen : 32 ≤ out.size)
    (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "attest" out = some [wordBytes32Value (calldataWord out 0)] := by
  have hl : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hd := decodeABIValues_bytes32_ok (mode := .modern) (bytes := out.toList)
    (by simp only [List.length_take, hl]; omega)
  have hw := calldata_bytes32_value (cd := out) (off := 0) hlen (by decide)
  simp only [List.drop_zero] at hw
  change (decodeReturnValue? bytes32 out).map (fun v ↦ [v]) = _
  simp only [decodeReturnValue?, decodeReturnValues?, List.isEmpty_cons, Bool.false_eq_true,
    true_and, hl, Nat.not_le.mpr hhi, if_false,
    show abiTupleHeadSize? [bytes32] = some 32 by native_decide,
    bind, Option.bind]
  rw [show bytes32 = abiBytes32 from rfl, hd]
  simp only [hw, Option.map_some]

theorem attestDecodeReturn_short {out : ByteArray} (hshort : out.size < 32) :
    config.externalABI.decode? "attest" out = none := by
  have hl : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hd := decodeABIValues_bytes32_none_short (mode := .modern) (bytes := out.toList)
    (by rw [hl]; exact hshort)
  change (decodeReturnValue? bytes32 out).map (fun v ↦ [v]) = _
  simp only [decodeReturnValue?, decodeReturnValues?, List.isEmpty_cons, Bool.false_eq_true,
    true_and, hl, show ¬ 2 ^ 255 ≤ out.size by omega, if_false,
    show abiTupleHeadSize? [bytes32] = some 32 by native_decide,
    bind, Option.bind]
  rw [show bytes32 = abiBytes32 from rfl, hd]; rfl

end Benchmarks.EAS.Attester
