import Benchmarks.UniswapV3.Pool.Calls
import Benchmarks.UniswapV3.Pool.SourceExpressions
import Benchmarks.UniswapV3.Pool.TupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

abbrev safeTransferFunction : FunctionDecl := contract.functions[15]!

theorem safeTransferLookup :
    lookupCallable? contract "TransferHelper_safeTransfer" = some safeTransferFunction.toCallable := rfl

def safeTransferCalldata (recipient : AccountAddress) (value : UInt256) : ByteArray :=
  selectorBytes 0xa9 0x05 0x9c 0xbb ++ (EVM.word recipient.val).toByteArray ++ value.toByteArray

theorem safeTransferEncode (recipient : AccountAddress) (value : UInt256) :
    externalABI.encode? "transfer" [.address recipient, .int (Int.ofNat value.toNat)] =
      some (safeTransferCalldata recipient value) := by
  have h := staticWordsReturnEncoding
    [(.elem .address, .address recipient, EVM.word recipient.val),
     (.elem (.int (.uint ⟨256, by decide⟩)), .int (Int.ofNat value.toNat), value)] 64
    (by simp only [List.map_cons, List.map_nil, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType, bind, Option.bind]; rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · simp [encodeABIValue?, encodeABIWord?]
        · exact encodeABIValue_uint ⟨256, by decide⟩ value value.val.isLt)
  have hargs : encodeReturnValues? [.elem .address, .elem (.int (.uint ⟨256, by decide⟩))]
      [.address recipient, .int (Int.ofNat value.toNat)] =
      some ((EVM.word recipient.val).toByteArray ++ value.toByteArray) := by
    simpa only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray] using h
  have hcall := encodeCall_of_encodeReturn (selectorBytes 0xa9 0x05 0x9c 0xbb) hargs
  simpa only [externalABI, safeTransferCalldata, ByteArray.append_assoc] using hcall

def safeTransferLocals (token recipient : AccountAddress) (value : UInt256) : Store :=
  (((∅ : Store).insert "value" (.int (Int.ofNat value.toNat))).insert "to" (.address recipient)).insert
    "token" (.address token)

theorem safeTransferBind (token recipient : AccountAddress) (value : UInt256) :
    bindParams? safeTransferFunction.params
      [.address token, .address recipient, .int (Int.ofNat value.toNat)] =
      some (safeTransferLocals token recipient value) := rfl

def safeTransferFrame (imms : Store) (token recipient : AccountAddress) (value : UInt256) : Frame :=
  { contract := contract, locals := safeTransferLocals token recipient value, immutables := imms }

def safeTransferCallFrame (imms : Store) (token recipient : AccountAddress) (value : UInt256)
    (ok : Bool) (out : ByteArray) : Frame :=
  { (safeTransferFrame imms token recipient value) with
    locals := ((safeTransferLocals token recipient value).insert "success" (.bool ok)).insert "data" (.bytes out) }

theorem safeTransferCall (imms : Store) (evm evm' : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata recipient value) (ok, evm', out) true) :
    ExecStmt config (safeTransferFrame imms token recipient value) evm
      (.lowLevelCall (.var "token") (.intLit 0)
        (.abiEncodeCall "transfer" [.var "to", .var "value"]) "success" "data" true)
      (.ok (safeTransferCallFrame imms token recipient value ok out) evm') := by
  apply lowLevelCallWithPermSource (target := token) (calldata := safeTransferCalldata recipient value)
    (value := 0) _ (by simp only [evalExpr?, pure]) _ hcall
  · exact evalExpr_var_get (by simp [safeTransferFrame, safeTransferLocals])
  · have hr : evalExpr? config (safeTransferFrame imms token recipient value) evm (.var "to") =
        .ok (.address recipient) := evalExpr_var_get (by
      simp [safeTransferFrame, safeTransferLocals, Std.HashMap.getElem_insert])
    have hv : evalExpr? config (safeTransferFrame imms token recipient value) evm (.var "value") =
        .ok (.int (Int.ofNat value.toNat)) := evalExpr_var_get (by simp [safeTransferFrame, safeTransferLocals, Std.HashMap.getElem_insert])
    simp only [evalExpr?, evalExprList?, hr, hv, bind, EvalResult.bind, pure]
    change (do let bytes ← EvalResult.ofOption .typeError
                (externalABI.encode? "transfer" [.address recipient, .int (Int.ofNat value.toNat)])
               pure (Value.bytes bytes)) = _
    rw [safeTransferEncode]
    rfl

def safeTransferEmptyExpr : Expr :=
  .binary .eq (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)

def safeTransferCondition : Expr :=
  .binary .and (.var "success")
    (.binary .or safeTransferEmptyExpr (.abiDecode abiBool (.var "data")))

theorem evalSafeTransferSuccess (imms : Store) (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (ok : Bool) (out : ByteArray) :
    evalExpr? config (safeTransferCallFrame imms token recipient value ok out) evm (.var "success") =
      .ok (.bool ok) := evalExpr_var_get (by
    simp [safeTransferCallFrame, Std.HashMap.getElem_insert])

theorem evalSafeTransferData (imms : Store) (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (ok : Bool) (out : ByteArray) :
    evalExpr? config (safeTransferCallFrame imms token recipient value ok out) evm (.var "data") =
      .ok (.bytes out) := evalExpr_var_get (by simp [safeTransferCallFrame])

theorem evalSafeTransferEmpty (imms : Store) (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (ok : Bool) (out : ByteArray) :
    evalExpr? config (safeTransferCallFrame imms token recipient value ok out) evm safeTransferEmptyExpr =
      .ok (.bool (decide (out.size = 0))) :=
  evalExpr_nat_eq_zero (evalExpr_localBytesLength (by simp [safeTransferCallFrame]))

theorem evalSafeTransferConditionFalse (imms : Store) (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray) :
    evalExpr? config (safeTransferCallFrame imms token recipient value false out) evm safeTransferCondition =
      .ok (.bool false) := by
  simp only [safeTransferCondition, evalExpr?, evalSafeTransferSuccess, bind, EvalResult.bind, pure]

theorem evalSafeTransferConditionEmpty (imms : Store) (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray) (hempty : out.size = 0) :
    evalExpr? config (safeTransferCallFrame imms token recipient value true out) evm safeTransferCondition =
      .ok (.bool true) := by
  have he := evalSafeTransferEmpty imms evm token recipient value true out
  rw [hempty] at he
  simp only [safeTransferCondition, evalExpr?, evalSafeTransferSuccess, he, bind, EvalResult.bind, pure,
    decide_true]

theorem evalSafeTransferConditionBool (imms : Store) (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray) (result : Bool)
    (hne : out.size ≠ 0)
    (hdecode : decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool result)) :
    evalExpr? config (safeTransferCallFrame imms token recipient value true out) evm safeTransferCondition =
      .ok (.bool result) := by
  have he := evalSafeTransferEmpty imms evm token recipient value true out
  rw [show decide (out.size = 0) = false by simp [hne]] at he
  have hd : evalExpr? config (safeTransferCallFrame imms token recipient value true out) evm
      (.abiDecode abiBool (.var "data")) = .ok (.bool result) := by
    simp only [evalExpr?, evalSafeTransferData, hdecode, bind, EvalResult.bind, pure]
  exact evalExpr_bool_and (evalSafeTransferSuccess imms evm token recipient value true out)
    (evalExpr_bool_or he hd)

theorem evalSafeTransferConditionRevert (imms : Store) (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray) (hne : out.size ≠ 0)
    (hdecode : decodeReturnValueWithMode? config.abiDecodeMode abiBool out = none) :
    evalExpr? config (safeTransferCallFrame imms token recipient value true out) evm safeTransferCondition =
      .revert := by
  have he := evalSafeTransferEmpty imms evm token recipient value true out
  rw [show decide (out.size = 0) = false by simp [hne]] at he
  simp only [safeTransferCondition, evalExpr?, evalSafeTransferSuccess, he,
    evalSafeTransferData, hdecode, bind, EvalResult.bind, pure]

theorem safeTransferRevertsCall (imms : Store) (evm evm' : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata recipient value) (false, evm', out) true) :
    ExecFuncBody config (safeTransferFrame imms token recipient value) evm safeTransferFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (safeTransferCall imms evm evm' token recipient value false out hcall)
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalSafeTransferConditionFalse imms evm' token recipient value out))

theorem safeTransferRevertsDecode (imms : Store) (evm evm' : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata recipient value) (true, evm', out) true)
    (hne : out.size ≠ 0)
    (hdecode : decodeReturnValueWithMode? config.abiDecodeMode abiBool out = none) :
    ExecFuncBody config (safeTransferFrame imms token recipient value) evm safeTransferFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (safeTransferCall imms evm evm' token recipient value true out hcall)
  exact ExecBlock.consRevert (ExecStmt.requireRevert
    (evalSafeTransferConditionRevert imms evm' token recipient value out hne hdecode))

theorem safeTransferRevertsFalse (imms : Store) (evm evm' : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata recipient value) (true, evm', out) true)
    (hne : out.size ≠ 0)
    (hdecode : decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool false)) :
    ExecFuncBody config (safeTransferFrame imms token recipient value) evm safeTransferFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (safeTransferCall imms evm evm' token recipient value true out hcall)
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalSafeTransferConditionBool imms evm' token recipient value out false hne hdecode))

theorem safeTransferReturns (imms : Store) (evm evm' : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata recipient value) (true, evm', out) true)
    (hgood : out.size = 0 ∨
      decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool true)) :
    ExecFuncBody config (safeTransferFrame imms token recipient value) evm safeTransferFunction.body
      (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) := by
  apply ExecFuncBody.execBlockOK
  apply ExecBlock.consNormal (safeTransferCall imms evm evm' token recipient value true out hcall)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  by_cases hempty : out.size = 0
  · exact evalSafeTransferConditionEmpty imms evm' token recipient value out hempty
  · exact evalSafeTransferConditionBool imms evm' token recipient value out true hempty
      (hgood.resolve_left hempty)

end Benchmarks.UniswapV3.Pool
