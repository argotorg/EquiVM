import Benchmarks.Midnight.SafeTransferABI
import Benchmarks.Midnight.SafeTransferSourceTail

/-! Source execution of the internal safe-transfer functions, including the external call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def safeTransferArguments (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) : List Value :=
  .address token :: safeTransferCallArgs isFrom sender recipient value

def safeTransferLocals (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) : Store :=
  let rest := ((∅ : Store).insert "value" (.int (Int.ofNat value.toNat))).insert
    "to" (.address recipient)
  (if isFrom then rest.insert "from" (.address sender) else rest).insert "token" (.address token)

def safeTransferFrame (isFrom : Bool) (imms : Store) (token sender recipient : AccountAddress)
    (value : UInt256) : Frame :=
  { contract := contract, locals := safeTransferLocals isFrom token sender recipient value,
    immutables := imms }

def safeTransferPayloadFrame (isFrom : Bool) (imms : Store)
    (token sender recipient : AccountAddress) (value : UInt256) : Frame :=
  let frame := safeTransferFrame isFrom imms token sender recipient value
  { frame with
    locals := frame.locals.insert "payload"
      (.bytes (safeTransferCalldata isFrom sender recipient value)) }

def safeTransferCallFrame (isFrom : Bool) (imms : Store)
    (token sender recipient : AccountAddress) (value : UInt256) (success : Bool)
    (out : ByteArray) : Frame :=
  let frame := safeTransferPayloadFrame isFrom imms token sender recipient value
  { frame with
    locals := (frame.locals.insert "success" (.bool success)).insert
      "returndata" (.bytes out) }

def safeTransferPayloadExpr (isFrom : Bool) : Expr :=
  if isFrom then .abiEncodeCall "transferFrom" [.var "from", .var "to", .var "value"]
  else .abiEncodeCall "transfer" [.var "to", .var "value"]

theorem safeTransferLookup (isFrom : Bool) :
    lookupCallable? contract
      (if isFrom then "SafeTransferLib_safeTransferFrom" else "SafeTransferLib_safeTransfer") =
      some (safeTransferFunctionFor isFrom).toCallable := by
  cases isFrom <;> rfl

theorem safeTransferBind (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) :
    bindParams? (safeTransferFunctionFor isFrom).params
      (safeTransferArguments isFrom token sender recipient value) =
      some (safeTransferLocals isFrom token sender recipient value) := by
  cases isFrom <;> rfl

theorem safeTransferBody_shape (isFrom : Bool) :
    (safeTransferFunctionFor isFrom).body =
      [.require (.binary .gt (.extCodeSize (.var "token")) (.intLit 0)),
       .letDecl "payload" (some .bytes) (safeTransferPayloadExpr isFrom),
       .lowLevelCall (.var "token") (.intLit 0) (.var "payload") "success" "returndata" true] ++
      safeTransferTail := by
  cases isFrom <;> rfl

theorem safeTransferToken_get (isFrom : Bool) (imms : Store)
    (token sender recipient : AccountAddress) (value : UInt256) :
    (safeTransferFrame isFrom imms token sender recipient value).locals.get? "token" =
      some (.address token) := by
  simp [safeTransferFrame, safeTransferLocals]

theorem safeTransferPayload_eval (isFrom : Bool) (imms : Store) (evm : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) :
    evalExpr? config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferPayloadExpr isFrom) =
      .ok (.bytes (safeTransferCalldata isFrom sender recipient value)) := by
  have hr : (safeTransferFrame isFrom imms token sender recipient value).locals.get? "to" =
      some (.address recipient) := by
    cases isFrom <;> simp [safeTransferFrame, safeTransferLocals, Std.HashMap.getElem_insert]
  have hv : (safeTransferFrame isFrom imms token sender recipient value).locals.get? "value" =
      some (.int (Int.ofNat value.toNat)) := by
    cases isFrom <;> simp [safeTransferFrame, safeTransferLocals, Std.HashMap.getElem_insert]
  have hf : (safeTransferFrame true imms token sender recipient value).locals.get? "from" =
      some (.address sender) := by
    simp [safeTransferFrame, safeTransferLocals, Std.HashMap.getElem_insert]
  cases isFrom <;>
    simp only [safeTransferPayloadExpr, Bool.false_eq_true, ↓reduceIte, evalExpr?, evalExprList?,
      hr, hv, hf, EvalResult.ofOption, bind, EvalResult.bind, pure]
  · change (do
        let bytes ← EvalResult.ofOption .typeError
          (config.externalABI.encode? "transfer" (safeTransferCallArgs false sender recipient value))
        pure (Value.bytes bytes)) = _
    simp only [show config.externalABI.encode? "transfer"
      (safeTransferCallArgs false sender recipient value) =
        some (safeTransferCalldata false sender recipient value) from
          encodeSafeTransfer false sender recipient value]
    rfl
  · change (do
        let bytes ← EvalResult.ofOption .typeError
          (config.externalABI.encode? "transferFrom" (safeTransferCallArgs true sender recipient value))
        pure (Value.bytes bytes)) = _
    simp only [show config.externalABI.encode? "transferFrom"
      (safeTransferCallArgs true sender recipient value) =
        some (safeTransferCalldata true sender recipient value) from
          encodeSafeTransfer true sender recipient value]
    rfl

theorem safeTransferCode_eval (isFrom : Bool) (imms : Store) (evm : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) :
    evalExpr? config (safeTransferFrame isFrom imms token sender recipient value) evm
      (.binary .gt (.extCodeSize (.var "token")) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat))) := by
  apply evalExpr_codeGuard_of_accounts_eq rfl
  · exact (accountAddress_roundtrip token).symm
  · simp only [evalExpr?, safeTransferToken_get, EvalResult.ofOption]

theorem safeTransferCall (isFrom : Bool) (imms : Store) (evm evm' : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) (success : Bool) (out : ByteArray)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (success, evm', out) true) :
    ExecStmt config (safeTransferPayloadFrame isFrom imms token sender recipient value) evm
      (.lowLevelCall (.var "token") (.intLit 0) (.var "payload") "success" "returndata" true)
      (.ok (safeTransferCallFrame isFrom imms token sender recipient value success out) evm') := by
  apply lowLevelCallSource (hperm := Or.inl rfl) (value := 0)
    (target := token) _ (by simp only [evalExpr?, pure]) _ hcall
  · simp only [evalExpr?, safeTransferPayloadFrame,
      store_get_ne _ _ (by decide : ("payload" == "token") = false),
      safeTransferToken_get, EvalResult.ofOption]
  · simp only [evalExpr?, safeTransferPayloadFrame, store_get_self, EvalResult.ofOption]

theorem safeTransferRun (isFrom : Bool) (imms : Store) (evm evm' : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) (success : Bool) (out : ByteArray)
    (hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (success, evm', out) true) {result : ExecResult}
    (htail : ExecBlock config (safeTransferCallFrame isFrom imms token sender recipient value
      success out) evm' safeTransferTail result) :
    ExecBlock config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body result := by
  rw [safeTransferBody_shape]
  apply ExecBlock.consNormal (ExecStmt.requireTrue
    ((safeTransferCode_eval isFrom imms evm token sender recipient value).trans
      (by rw [decide_eq_true hcode])))
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (safeTransferPayload_eval isFrom imms evm token sender recipient value))
  exact .consNormal (safeTransferCall isFrom imms evm evm' token sender recipient value
    success out hcall) htail

theorem safeTransferRevertsCode (isFrom : Bool) (imms : Store) (evm : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256)
    (hcode : (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat = 0) :
    ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [safeTransferBody_shape]
  exact .consRevert (.requireFalse
    ((safeTransferCode_eval isFrom imms evm token sender recipient value).trans
      (by rw [hcode]; rfl)))

theorem safeTransferCallFrame_data (isFrom : Bool) (imms : Store)
    (token sender recipient : AccountAddress) (value : UInt256) (success : Bool) (out : ByteArray) :
    (safeTransferCallFrame isFrom imms token sender recipient value success out).locals.get?
      "returndata" = some (.bytes out) := by
  simp only [safeTransferCallFrame, store_get_self]

theorem safeTransferCallFrame_success (isFrom : Bool) (imms : Store)
    (token sender recipient : AccountAddress) (value : UInt256) (success : Bool) (out : ByteArray) :
    (safeTransferCallFrame isFrom imms token sender recipient value success out).locals.get?
      "success" = some (.bool success) := by
  simp only [safeTransferCallFrame,
    store_get_ne _ _ (by decide : ("returndata" == "success") = false),
    store_get_self]

theorem safeTransferRevertsCall (isFrom : Bool) (imms : Store) (evm evm' : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) (out : ByteArray)
    (hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (false, evm', out) true) :
    ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safeTransferRun isFrom imms evm evm' token sender recipient value false out hcode hcall
  exact safeTransferTail_callFailure (safeTransferCallFrame_data ..) (safeTransferCallFrame_success ..)

theorem safeTransferRevertsSize (isFrom : Bool) (imms : Store) (evm evm' : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) (success : Bool) (out : ByteArray)
    (hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (success, evm', out) true) (hb : 2 ^ 64 ≤ out.size) :
    ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safeTransferRun isFrom imms evm evm' token sender recipient value success out hcode hcall
  exact safeTransferTail_oversize (safeTransferCallFrame_data ..) hb

theorem safeTransferRevertsDecode (isFrom : Bool) (imms : Store) (evm evm' : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) (out : ByteArray)
    (hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (true, evm', out) true) (hne : out.size ≠ 0)
    (hd : config.externalABI.decodeValue? abiBool out = none ∨
      config.externalABI.decodeValue? abiBool out = some (.bool false)) :
    ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safeTransferRun isFrom imms evm evm' token sender recipient value true out hcode hcall
  exact safeTransferTail_decodeFailure (safeTransferCallFrame_data ..)
    (safeTransferCallFrame_success ..) hne hd

theorem safeTransferReturns (isFrom : Bool) (imms : Store) (evm evm' : EVM.State)
    (token sender recipient : AccountAddress) (value : UInt256) (out : ByteArray)
    (hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (true, evm', out) true) (hb : out.size < 2 ^ 64)
    (hd : out.size = 0 ∨ config.externalABI.decodeValue? abiBool out = some (.bool true)) :
    ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body
      (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
        none) := by
  apply ExecFuncBody.execBlockOK
  apply safeTransferRun isFrom imms evm evm' token sender recipient value true out hcode hcall
  exact safeTransferTail_success (safeTransferCallFrame_data ..)
    (safeTransferCallFrame_success ..) hb hd

end Benchmarks.Midnight
