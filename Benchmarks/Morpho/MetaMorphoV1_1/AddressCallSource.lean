import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifySource
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnSource

/-! The zero-value Address call, its explicit buffer reservation, and target validation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def addressCallFrame (imms : Store) (target : AccountAddress) (data : ByteArray)
    (ptr : UInt256) : Frame :=
  ⟨contract, (((∅ : Store).insert cursorName (uint256Value ptr)).insert "data" (.bytes data)).insert
    "target" (.address target), imms⟩

def addressCallRawFrame (imms : Store) (target : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) : Frame :=
  { addressCallFrame imms target data ptr with
    locals := ((addressCallFrame imms target data ptr).locals.insert "success" (.bool ok)).insert
      "returndata" (.bytes out) }

def addressCallReserveFrame (imms : Store) (target : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) : Frame :=
  callReturnFrame (addressCallRawFrame imms target data ptr ok out) ptr out

def addressCallResultFrame (imms : Store) (target : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (out : ByteArray) : Frame :=
  { addressCallReserveFrame imms target data ptr true out with
    locals := (addressCallReserveFrame imms target data ptr true out).locals.insert "__c0"
      (.bytes out) }

theorem addressCallPrefix {evm evm' : State} (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray) {result : ExecResult}
    (hcall : callViaEVM evm target 0 data (ok, evm', out))
    (htail : ExecBlock config (addressCallRawFrame imms target data ptr ok out) evm'
      (allocatedAddressCallFunction.body.drop 2) result) :
    ExecBlock config (addressCallFrame imms target data ptr) evm
      allocatedAddressCallFunction.body result := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
  · apply ExecBlock.consNormal _ htail
    exact lowLevelCallSource
      (by simp only [evalExpr?, addressCallFrame, store_get_self, EvalResult.ofOption])
      (by simp only [evalExpr?, pure])
      (by simp [evalExpr?, addressCallFrame, Std.HashMap.getElem_insert, EvalResult.ofOption])
      hcall
  · simpa only [decide_true] using naturalGeSource
      (show evalExpr? config (addressCallFrame imms target data ptr) evm (.env .selfbalance) =
        .ok (.int (Int.ofNat
          ((evm.lookupAccount evm.executionEnv.codeOwner).option (⟨0⟩ : UInt256)
            (fun acc : Account ↦ acc.balance)).toNat))
        by simp only [evalExpr?, envValue, pure]; rfl)
      (show evalExpr? config (addressCallFrame imms target data ptr) evm (.intLit 0) =
        .ok (.int (Int.ofNat 0)) by simp only [evalExpr?, pure]; rfl)

theorem addressCallRawFrame_cursor (imms : Store) (target : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) :
    (addressCallRawFrame imms target data ptr ok out).locals.get? cursorName =
      some (uint256Value ptr) := by
  simp [addressCallRawFrame, addressCallFrame, cursorName, Std.HashMap.getElem_insert]

theorem addressCallReserveSource (evm : State) (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hfit : callReturnFits ptr out) :
    ExecStmt config (addressCallRawFrame imms target data ptr ok out) evm reserveCallReturn
      (.ok (addressCallReserveFrame imms target data ptr ok out) evm) :=
  reserveCallReturnReturns allocateFunction_lookup
    (addressCallRawFrame_cursor imms target data ptr ok out) (store_get_self _ _ _) hfit

theorem addressCallVerifyArgs (evm : State) (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray) :
    evalExprs? config (addressCallReserveFrame imms target data ptr ok out) evm
      [.var "target", .var "success", .var "returndata"] =
        .ok [.address target, .bool ok, .bytes out] := by
  simp only [evalExprs?, evalExpr?, addressCallReserveFrame,
    callReturnFrame_get _ _ _ _ (show (cursorName == "target") = false by decide),
    callReturnFrame_get _ _ _ _ (show (cursorName == "success") = false by decide),
    callReturnFrame_get _ _ _ _ (show (cursorName == "returndata") = false by decide)]
  simp [addressCallRawFrame, addressCallFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem addressCallPostReturns (evm : State) (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hfit : callReturnFits ptr out) (hvalid : addressReturnValid evm target out) :
    ExecBlock config (addressCallRawFrame imms target data ptr true out) evm
      addressCallReturnBody
      (.returned (addressCallResultFrame imms target data ptr out) evm
        (some [.bytes out, uint256Value (callReturnCursor ptr out)])) := by
  apply ExecBlock.consNormal (addressCallReserveSource evm imms target data ptr true out hfit)
  apply ExecBlock.consNormal (addressVerifyCallReturns evm _ imms target out _ "__c0"
    (addressCallVerifyArgs evm imms target data ptr true out) hvalid)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  change evalExprs? config (addressCallResultFrame imms target data ptr out) evm _ = _
  have hc := callReturnFrame_cursor _ _ out
    (addressCallRawFrame_cursor imms target data ptr true out)
  change (addressCallReserveFrame imms target data ptr true out).locals.get? cursorName =
    some (uint256Value (callReturnCursor ptr out)) at hc
  simp only [evalExprs?, evalExpr?, store_get_self,
    addressCallResultFrame,
    store_get_ne _ _ (show ("__c0" == cursorName) = false by decide),
    hc, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem addressCallPostRevertsAllocation (evm : State) (imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hbad : ¬ callReturnFits ptr out) :
    ExecBlock config (addressCallRawFrame imms target data ptr ok out) evm
      addressCallReturnBody .reverted :=
  ExecBlock.consRevert (reserveCallReturnReverts allocateFunction_lookup
    (addressCallRawFrame_cursor imms target data ptr ok out) (store_get_self _ _ _) hbad)

theorem addressCallPostRevertsVerify (evm : State) (imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hfit : callReturnFits ptr out) (hbad : ok = false ∨ ¬ addressReturnValid evm target out) :
    ExecBlock config (addressCallRawFrame imms target data ptr ok out) evm
      addressCallReturnBody .reverted :=
  ExecBlock.consNormal (addressCallReserveSource evm imms target data ptr ok out hfit)
    (ExecBlock.consRevert (addressVerifyCallReverts evm _ imms target ok out _ "__c0"
      (addressCallVerifyArgs evm imms target data ptr ok out) hbad))

theorem addressCallBodyReturns {evm evm' : State} (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hcall : callViaEVM evm target 0 data (true, evm', out))
    (hfit : callReturnFits ptr out) (hvalid : addressReturnValid evm' target out) :
    ExecFuncBody config (addressCallFrame imms target data ptr) evm
      allocatedAddressCallFunction.body
      (.returned (addressCallResultFrame imms target data ptr out) evm'
        (some [.bytes out, uint256Value (callReturnCursor ptr out)])) := by
  apply ExecFuncBody.execBlockRet
  apply addressCallPrefix imms target data ptr true out hcall
  exact addressCallPostReturns evm' imms target data ptr out hfit hvalid

theorem addressCallBodyRevertsAllocation {evm evm' : State} (imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm target 0 data (ok, evm', out)) (hbad : ¬ callReturnFits ptr out) :
    ExecFuncBody config (addressCallFrame imms target data ptr) evm
      allocatedAddressCallFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply addressCallPrefix imms target data ptr ok out hcall
  exact addressCallPostRevertsAllocation evm' imms target data ptr ok out hbad

theorem addressCallBodyRevertsVerify {evm evm' : State} (imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm target 0 data (ok, evm', out)) (hfit : callReturnFits ptr out)
    (hbad : ok = false ∨ ¬ addressReturnValid evm' target out) :
    ExecFuncBody config (addressCallFrame imms target data ptr) evm
      allocatedAddressCallFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply addressCallPrefix imms target data ptr ok out hcall
  exact addressCallPostRevertsVerify evm' imms target data ptr ok out hfit hbad

theorem addressCallStatementReturns {evm evm' : State} (locals imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address target, .bytes data, uint256Value ptr])
    (hcall : callViaEVM evm target 0 data (true, evm', out)) (hfit : callReturnFits ptr out)
    (hvalid : addressReturnValid evm' target out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall allocatedAddressCallFunction.name args retVar)
      (.ok ⟨contract, locals.insert retVar
        (.tuple [.bytes out, uint256Value (callReturnCursor ptr out)]), imms⟩ evm') :=
  internalCallFunctionReturn (callee := allocatedAddressCallFunction) hargs rfl rfl
    (addressCallBodyReturns imms target data ptr out hcall hfit hvalid)

theorem addressCallStatementReverts {evm evm' : State} (locals imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address target, .bytes data, uint256Value ptr])
    (hcall : callViaEVM evm target 0 data (ok, evm', out))
    (hbad : ¬ callReturnFits ptr out ∨ ok = false ∨ ¬ addressReturnValid evm' target out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall allocatedAddressCallFunction.name args retVar) .reverted := by
  apply internalCallFunctionRevert (callee := allocatedAddressCallFunction) hargs rfl rfl
  by_cases hfit : callReturnFits ptr out
  · exact addressCallBodyRevertsVerify imms target data ptr ok out hcall hfit
      (hbad.resolve_left (not_not_intro hfit))
  · exact addressCallBodyRevertsAllocation imms target data ptr ok out hcall hfit

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
