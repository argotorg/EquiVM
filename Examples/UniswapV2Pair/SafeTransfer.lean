import Examples.UniswapV2Pair.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-!
# `_safeTransfer` source-side helpers

The Solidity helper is a low-level `token.call(abi.encodeWithSelector(SELECTOR, recipient, value))`
followed by the Uniswap return-data predicate:

`success && (data.length == 0 || abi.decode(data, (bool)))`.

These lemmas keep callers such as `skim`, `burn`, and `swap` at the internal-call boundary rather
than inlining `_safeTransfer` into each external proof.
-/

abbrev safeTransferUintValue (value : UInt256) : Value :=
  .int (Int.ofNat value.toNat)

abbrev safeTransferArgs (token recipient : AccountAddress) (value : UInt256) : List Value :=
  [.address token, .address recipient, safeTransferUintValue value]

abbrev transferCallArgs (recipient : AccountAddress) (value : UInt256) : List Value :=
  [.address recipient, safeTransferUintValue value]

abbrev safeTransferCalleeStore (token recipient : AccountAddress) (value : UInt256) : Store :=
  (((∅ : Store).insert "value" (safeTransferUintValue value)).insert "to" (.address recipient)).insert
    "token" (.address token)

abbrev safeTransferCallStore (token recipient : AccountAddress) (value : UInt256)
    (success : Bool) (out : ByteArray) : Store :=
  ((safeTransferCalleeStore token recipient value).insert "_success" (.bool success)).insert "_data"
    (.bytes out)

def transferCalldata? (recipient : AccountAddress) (value : UInt256) : Option ByteArray :=
  config.externalABI.encode? "transfer" (transferCallArgs recipient value)

theorem safeTransferCalleeStore_token (token recipient : AccountAddress) (value : UInt256) :
    (safeTransferCalleeStore token recipient value).get? "token" = some (.address token) := by
  rw [safeTransferCalleeStore, store_get_self]

theorem safeTransferCalleeStore_to (token recipient : AccountAddress) (value : UInt256) :
    (safeTransferCalleeStore token recipient value).get? "to" = some (.address recipient) := by
  rw [safeTransferCalleeStore, store_get_ne _ _ (by decide), store_get_self]

theorem safeTransferCalleeStore_value (token recipient : AccountAddress) (value : UInt256) :
    (safeTransferCalleeStore token recipient value).get? "value" =
      some (safeTransferUintValue value) := by
  rw [safeTransferCalleeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem safeTransferCallStore_success (token recipient : AccountAddress) (value : UInt256)
    (success : Bool) (out : ByteArray) :
    (safeTransferCallStore token recipient value success out).get? "_success" =
      some (.bool success) := by
  rw [safeTransferCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem safeTransferCallStore_data (token recipient : AccountAddress) (value : UInt256)
    (success : Bool) (out : ByteArray) :
    (safeTransferCallStore token recipient value success out).get? "_data" = some (.bytes out) := by
  rw [safeTransferCallStore, store_get_self]

theorem evalExpr_safeTransfer_receiver (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) :
    evalExpr? config { contract := contract, locals := safeTransferCalleeStore token recipient value }
      evm (.var "token") = .ok (.address token) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [safeTransferCalleeStore_token]

theorem evalExpr_safeTransfer_value (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) :
    evalExpr? config { contract := contract, locals := safeTransferCalleeStore token recipient value }
      evm (.intLit 0) = .ok (.int 0) := by
  simp only [evalExpr?]
  rfl

theorem evalExpr_safeTransfer_calldata (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) {calldata : ByteArray}
    (hdata : transferCalldata? recipient value = some calldata) :
    evalExpr? config { contract := contract, locals := safeTransferCalleeStore token recipient value }
      evm (transferCalldataExpr (.var "to") (.var "value")) = .ok (.bytes calldata) := by
  simp only [transferCalldataExpr, evalExpr?, Solm.evalExprList?.eq_def, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  rw [safeTransferCalleeStore_to, safeTransferCalleeStore_value]
  simp
  rw [show config.externalABI.encode? "transfer" (transferCallArgs recipient value) =
    some calldata from by simpa [transferCalldata?, transferCallArgs] using hdata]

theorem bindParams_safeTransfer (token recipient : AccountAddress) (value : UInt256) :
    bindParams? safeTransferFunction.params (safeTransferArgs token recipient value) =
      some (safeTransferCalleeStore token recipient value) := by
  simp [safeTransferFunction, safeTransferArgs, safeTransferCalleeStore, safeTransferUintValue,
    bindParams?]

theorem lookupCallable_safeTransfer :
    lookupCallable? contract "_safeTransfer" = some safeTransferFunction.toCallable := by
  rfl

theorem evalExpr_safeTransferReturnOk_false (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) (out : ByteArray) :
    evalExpr? config
      { contract := contract, locals := safeTransferCallStore token recipient value false out } evm
      safeTransferReturnOkExpr = .ok (.bool false) := by
  simp only [safeTransferReturnOkExpr, evalExpr?, EvalResult.ofOption]
  rw [safeTransferCallStore_success]
  simp [EvalResult.bind, bind, pure]

theorem evalExpr_safeTransferReturnOk_empty (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) {out : ByteArray}
    (hout : out.size = 0) :
    evalExpr? config
      { contract := contract, locals := safeTransferCallStore token recipient value true out } evm
      safeTransferReturnOkExpr = .ok (.bool true) := by
  simp only [safeTransferReturnOkExpr, evalExpr?, EvalResult.ofOption]
  rw [safeTransferCallStore_success, safeTransferCallStore_data]
  simp [readLocalPath?, evalBinaryOp?, EvalResult.bind, bind, pure, hout]

theorem evalExpr_safeTransferReturnOk_decodeRevert (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) {out : ByteArray}
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = none) :
    evalExpr? config
      { contract := contract, locals := safeTransferCallStore token recipient value true out } evm
      safeTransferReturnOkExpr = .revert := by
  have hint : Int.ofNat out.size ≠ 0 := by
    intro hi
    exact hsize (Nat.cast_eq_zero.mp hi)
  have hneq : (Value.int (Int.ofNat out.size) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    injection h with hi
    exact hint hi
  simp only [safeTransferReturnOkExpr, evalExpr?, EvalResult.ofOption]
  rw [safeTransferCallStore_success, safeTransferCallStore_data]
  simp only [readLocalPath?, evalBinaryOp?, EvalResult.bind, bind, pure, hneq, hdec]

theorem evalExpr_safeTransferReturnOk_decodeFalse (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) {out : ByteArray}
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = some (.bool false)) :
    evalExpr? config
      { contract := contract, locals := safeTransferCallStore token recipient value true out } evm
      safeTransferReturnOkExpr = .ok (.bool false) := by
  have hint : Int.ofNat out.size ≠ 0 := by
    intro hi
    exact hsize (Nat.cast_eq_zero.mp hi)
  have hneq : (Value.int (Int.ofNat out.size) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    injection h with hi
    exact hint hi
  simp only [safeTransferReturnOkExpr, evalExpr?, EvalResult.ofOption]
  rw [safeTransferCallStore_success, safeTransferCallStore_data]
  simp only [readLocalPath?, evalBinaryOp?, EvalResult.bind, bind, pure, hneq, hdec]

theorem evalExpr_safeTransferReturnOk_decodeTrue (evm : EVM.State)
    (token recipient : AccountAddress) (value : UInt256) {out : ByteArray}
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = some (.bool true)) :
    evalExpr? config
      { contract := contract, locals := safeTransferCallStore token recipient value true out } evm
      safeTransferReturnOkExpr = .ok (.bool true) := by
  have hint : Int.ofNat out.size ≠ 0 := by
    intro hi
    exact hsize (Nat.cast_eq_zero.mp hi)
  have hneq : (Value.int (Int.ofNat out.size) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    injection h with hi
    exact hint hi
  simp only [safeTransferReturnOkExpr, evalExpr?, EvalResult.ofOption]
  rw [safeTransferCallStore_success, safeTransferCallStore_data]
  simp only [readLocalPath?, evalBinaryOp?, EvalResult.bind, bind, pure, hneq, hdec]

theorem safeTransferFunctionBodyReverts_callFailure
    (evm evm' : EVM.State) (token recipient : AccountAddress) (value : UInt256)
    {calldata out : ByteArray}
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (false, evm', out)) :
    ExecFuncBody config
      { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
      safeTransferFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
    [ .lowLevelCall (.var "token") (.intLit 0)
        (transferCalldataExpr (.var "to") (.var "value")) "_success" "_data",
      .require safeTransferReturnOkExpr ] .reverted
  exact lowLevelCallFailureThenRequireFalse
    (C := contract) (locals := safeTransferCalleeStore token recipient value)
    (receiver := .var "token") (eth := .intLit 0)
    (cdata := transferCalldataExpr (.var "to") (.var "value"))
    (requireCond := safeTransferReturnOkExpr)
    (okVar := "_success") (dataVar := "_data")
    (target := token) (sendVal := 0) (calldata := calldata) (out := out)
    (evalExpr_safeTransfer_receiver evm token recipient value)
    (evalExpr_safeTransfer_value evm token recipient value)
    (evalExpr_safeTransfer_calldata evm token recipient value hdata)
    hcall
    (evalExpr_safeTransferReturnOk_false evm' token recipient value out)

theorem safeTransferFunctionBodyReverts_decode
    (evm evm' : EVM.State) (token recipient : AccountAddress) (value : UInt256)
    {calldata out : ByteArray}
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = none) :
    ExecFuncBody config
      { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
      safeTransferFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
    [ .lowLevelCall (.var "token") (.intLit 0)
        (transferCalldataExpr (.var "to") (.var "value")) "_success" "_data",
      .require safeTransferReturnOkExpr ] .reverted
  refine ExecBlock.consNormal
    (solm' := { contract := contract, locals := safeTransferCallStore token recipient value true out })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess
      (evalExpr_safeTransfer_receiver evm token recipient value)
      (evalExpr_safeTransfer_value evm token recipient value)
      (evalExpr_safeTransfer_calldata evm token recipient value hdata)
      hcall
  · exact ExecBlock.consRevert
      (ExecStmt.requireRevert
        (evalExpr_safeTransferReturnOk_decodeRevert evm' token recipient value hsize hdec))

theorem safeTransferFunctionBodyReverts_decodeFalse
    (evm evm' : EVM.State) (token recipient : AccountAddress) (value : UInt256)
    {calldata out : ByteArray}
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = some (.bool false)) :
    ExecFuncBody config
      { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
      safeTransferFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
    [ .lowLevelCall (.var "token") (.intLit 0)
        (transferCalldataExpr (.var "to") (.var "value")) "_success" "_data",
      .require safeTransferReturnOkExpr ] .reverted
  refine ExecBlock.consNormal
    (solm' := { contract := contract, locals := safeTransferCallStore token recipient value true out })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess
      (evalExpr_safeTransfer_receiver evm token recipient value)
      (evalExpr_safeTransfer_value evm token recipient value)
      (evalExpr_safeTransfer_calldata evm token recipient value hdata)
      hcall
  · exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_safeTransferReturnOk_decodeFalse evm' token recipient value hsize hdec))

theorem safeTransferFunctionBodyReturns_empty
    (evm evm' : EVM.State) (token recipient : AccountAddress) (value : UInt256)
    {calldata out : ByteArray}
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hout : out.size = 0) :
    ExecFuncBody config
      { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
      safeTransferFunction.body
      (.returned
        { contract := contract, locals := safeTransferCallStore token recipient value true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config
    { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
    [ .lowLevelCall (.var "token") (.intLit 0)
        (transferCalldataExpr (.var "to") (.var "value")) "_success" "_data",
      .require safeTransferReturnOkExpr ]
    (.ok { contract := contract, locals := safeTransferCallStore token recipient value true out } evm')
  refine ExecBlock.consNormal
    (solm' := { contract := contract, locals := safeTransferCallStore token recipient value true out })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess
      (evalExpr_safeTransfer_receiver evm token recipient value)
      (evalExpr_safeTransfer_value evm token recipient value)
      (evalExpr_safeTransfer_calldata evm token recipient value hdata)
      hcall
  · exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_safeTransferReturnOk_empty evm' token recipient value hout))
      ExecBlock.nil

theorem safeTransferFunctionBodyReturns_decodeTrue
    (evm evm' : EVM.State) (token recipient : AccountAddress) (value : UInt256)
    {calldata out : ByteArray}
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = some (.bool true)) :
    ExecFuncBody config
      { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
      safeTransferFunction.body
      (.returned
        { contract := contract, locals := safeTransferCallStore token recipient value true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config
    { contract := contract, locals := safeTransferCalleeStore token recipient value } evm
    [ .lowLevelCall (.var "token") (.intLit 0)
        (transferCalldataExpr (.var "to") (.var "value")) "_success" "_data",
      .require safeTransferReturnOkExpr ]
    (.ok { contract := contract, locals := safeTransferCallStore token recipient value true out } evm')
  refine ExecBlock.consNormal
    (solm' := { contract := contract, locals := safeTransferCallStore token recipient value true out })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess
      (evalExpr_safeTransfer_receiver evm token recipient value)
      (evalExpr_safeTransfer_value evm token recipient value)
      (evalExpr_safeTransfer_calldata evm token recipient value hdata)
      hcall
  · exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_safeTransferReturnOk_decodeTrue evm' token recipient value hsize hdec))
      ExecBlock.nil

theorem safeTransferInternalCallReverts_callFailure
    (caller : Frame) (evm evm' : EVM.State)
    {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (token recipient : AccountAddress) (value : UInt256) {calldata out : ByteArray}
    (hcaller : caller.contract = contract)
    (hargs :
      evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] =
        .ok (safeTransferArgs token recipient value))
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (false, evm', out)) :
    ExecStmt config caller evm
      (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := caller) (evm := evm) (name := "_safeTransfer")
    (retVar := retVar) (args := [tokenExpr, toExpr, valueExpr])
    (argVals := safeTransferArgs token recipient value) (callee := safeTransferFunction)
    (locals := safeTransferCalleeStore token recipient value)
    hargs (by simpa [hcaller] using lookupCallable_safeTransfer)
    (bindParams_safeTransfer token recipient value)
    (by
      simpa [hcaller] using
        (safeTransferFunctionBodyReverts_callFailure evm evm' token recipient value hdata hcall))

theorem safeTransferInternalCallReverts_decode
    (caller : Frame) (evm evm' : EVM.State)
    {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (token recipient : AccountAddress) (value : UInt256) {calldata out : ByteArray}
    (hcaller : caller.contract = contract)
    (hargs :
      evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] =
        .ok (safeTransferArgs token recipient value))
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = none) :
    ExecStmt config caller evm
      (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := caller) (evm := evm) (name := "_safeTransfer")
    (retVar := retVar) (args := [tokenExpr, toExpr, valueExpr])
    (argVals := safeTransferArgs token recipient value) (callee := safeTransferFunction)
    (locals := safeTransferCalleeStore token recipient value)
    hargs (by simpa [hcaller] using lookupCallable_safeTransfer)
    (bindParams_safeTransfer token recipient value)
    (by
      simpa [hcaller] using
        (safeTransferFunctionBodyReverts_decode evm evm' token recipient value hdata hcall hsize
          hdec))

theorem safeTransferInternalCallReverts_decodeFalse
    (caller : Frame) (evm evm' : EVM.State)
    {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (token recipient : AccountAddress) (value : UInt256) {calldata out : ByteArray}
    (hcaller : caller.contract = contract)
    (hargs :
      evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] =
        .ok (safeTransferArgs token recipient value))
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hsize : out.size ≠ 0)
    (hdec :
      ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = some (.bool false)) :
    ExecStmt config caller evm
      (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := caller) (evm := evm) (name := "_safeTransfer")
    (retVar := retVar) (args := [tokenExpr, toExpr, valueExpr])
    (argVals := safeTransferArgs token recipient value) (callee := safeTransferFunction)
    (locals := safeTransferCalleeStore token recipient value)
    hargs (by simpa [hcaller] using lookupCallable_safeTransfer)
    (bindParams_safeTransfer token recipient value)
    (by
      simpa [hcaller] using
        (safeTransferFunctionBodyReverts_decodeFalse evm evm' token recipient value hdata hcall
          hsize hdec))

theorem safeTransferInternalCallReturns_empty
    (caller : Frame) (evm evm' : EVM.State)
    {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (token recipient : AccountAddress) (value : UInt256) {calldata out : ByteArray}
    (hcaller : caller.contract = contract)
    (hargs :
      evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] =
        .ok (safeTransferArgs token recipient value))
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hout : out.size = 0) :
    ExecStmt config caller evm
      (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
      (.ok (resumeAfterInternalCall caller retVar none) evm') := by
  exact internalCallFunctionReturn
    (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm')
    (name := "_safeTransfer") (retVar := retVar)
    (args := [tokenExpr, toExpr, valueExpr])
    (argVals := safeTransferArgs token recipient value) (callee := safeTransferFunction)
    (locals := safeTransferCalleeStore token recipient value)
    (calleeSolm :=
      { contract := contract, locals := safeTransferCallStore token recipient value true out })
    (value := none)
    hargs (by simpa [hcaller] using lookupCallable_safeTransfer)
    (bindParams_safeTransfer token recipient value)
    (by
      simpa [hcaller] using
        (safeTransferFunctionBodyReturns_empty evm evm' token recipient value hdata hcall hout))

theorem safeTransferInternalCallReturns_decodeTrue
    (caller : Frame) (evm evm' : EVM.State)
    {tokenExpr toExpr valueExpr : Expr} {retVar : Ident}
    (token recipient : AccountAddress) (value : UInt256) {calldata out : ByteArray}
    (hcaller : caller.contract = contract)
    (hargs :
      evalExprs? config caller evm [tokenExpr, toExpr, valueExpr] =
        .ok (safeTransferArgs token recipient value))
    (hdata : transferCalldata? recipient value = some calldata)
    (hcall : callViaEVM evm (EVM.address token) 0 calldata (true, evm', out))
    (hsize : out.size ≠ 0)
    (hdec : ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out = some (.bool true)) :
    ExecStmt config caller evm
      (.internalCall "_safeTransfer" [tokenExpr, toExpr, valueExpr] retVar)
      (.ok (resumeAfterInternalCall caller retVar none) evm') := by
  exact internalCallFunctionReturn
    (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm')
    (name := "_safeTransfer") (retVar := retVar)
    (args := [tokenExpr, toExpr, valueExpr])
    (argVals := safeTransferArgs token recipient value) (callee := safeTransferFunction)
    (locals := safeTransferCalleeStore token recipient value)
    (calleeSolm :=
      { contract := contract, locals := safeTransferCallStore token recipient value true out })
    (value := none)
    hargs (by simpa [hcaller] using lookupCallable_safeTransfer)
    (bindParams_safeTransfer token recipient value)
    (by
      simpa [hcaller] using
        (safeTransferFunctionBodyReturns_decodeTrue evm evm' token recipient value hdata hcall hsize
          hdec))

end UniswapV2Pair
