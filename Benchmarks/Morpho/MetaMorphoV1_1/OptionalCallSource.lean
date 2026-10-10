import Benchmarks.Morpho.MetaMorphoV1_1.AddressCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalReturnSource

/-! Compose the allocated Address call with SafeERC20's optional-return check. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def optionalCallFrame (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) : Frame :=
  ⟨contract, (((∅ : Store).insert cursorName (uint256Value ptr)).insert "data" (.bytes data)).insert
    "token" (.address token), imms⟩

def optionalAddressFrame (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (out : ByteArray) : Frame :=
  { optionalCallFrame imms token data ptr with
    locals := (optionalCallFrame imms token data ptr).locals.insert "__solcAddressResult"
      (.tuple [.bytes out, uint256Value (callReturnCursor ptr out)]) }

def optionalDataFrame (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (out : ByteArray) : Frame :=
  { optionalAddressFrame imms token data ptr out with
    locals := (optionalAddressFrame imms token data ptr out).locals.insert "returndata" (.bytes out) }

def optionalResultFrame (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (out : ByteArray) : Frame :=
  { optionalDataFrame imms token data ptr out with
    locals := (optionalDataFrame imms token data ptr out).locals.insert cursorName
      (uint256Value (callReturnCursor ptr out)) }

theorem optionalCallArgs (evm : State) (imms : Store) (token : AccountAddress)
    (data : ByteArray) (ptr : UInt256) :
    evalExprs? config (optionalCallFrame imms token data ptr) evm
      [.var "token", .var "data", .var cursorName] =
        .ok [.address token, .bytes data, uint256Value ptr] := by
  simp [evalExprs?, evalExpr?, optionalCallFrame, Std.HashMap.getElem_insert, cursorName,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem optionalCallPrefix {evm evm' : State} (imms : Store) (token : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (out : ByteArray) {result : ExecResult}
    (hcall : callViaEVM evm token 0 data (true, evm', out)) (hfit : callReturnFits ptr out)
    (hvalid : addressReturnValid evm' token out)
    (htail : ExecBlock config (optionalResultFrame imms token data ptr out) evm'
      (allocatedOptionalReturnFunction.body.drop 3) result) :
    ExecBlock config (optionalCallFrame imms token data ptr) evm
      allocatedOptionalReturnFunction.body result := by
  apply ExecBlock.consNormal (addressCallStatementReturns _ imms token data ptr out _
    "__solcAddressResult" (optionalCallArgs evm imms token data ptr) hcall hfit hvalid)
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
    simp [evalExpr?, optionalDataFrame, optionalAddressFrame, Std.HashMap.getElem_insert,
      EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]
  · simp [evalExpr?, EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]

theorem optionalResultFrame_data (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (out : ByteArray) :
    (optionalResultFrame imms token data ptr out).locals.get? "returndata" = some (.bytes out) := by
  simp [optionalResultFrame, optionalDataFrame, cursorName, Std.HashMap.getElem_insert]

theorem optionalCallBodyReturns {evm evm' : State} (imms : Store) (token : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hcall : callViaEVM evm token 0 data (true, evm', out)) (hfit : callReturnFits ptr out)
    (hvalid : addressReturnValid evm' token out) (hbool : optionalReturnValid out) :
    ExecFuncBody config (optionalCallFrame imms token data ptr) evm
      allocatedOptionalReturnFunction.body
      (.returned (optionalResultFrame imms token data ptr out) evm'
        (some [uint256Value (callReturnCursor ptr out)])) := by
  apply ExecFuncBody.execBlockRet
  apply optionalCallPrefix imms token data ptr out hcall hfit hvalid
  have hs : out.size < 2 ^ 255 := by rcases hfit with hz | ⟨hs, _⟩ <;> omega
  apply ExecBlock.consNormal (optionalReturnSourcePasses
    (optionalResultFrame_data imms token data ptr out) hs hbool)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, optionalResultFrame, store_get_self, EvalResult.ofOption]

theorem optionalCallBodyRevertsAddress {evm evm' : State} (imms : Store)
    (token : AccountAddress) (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm token 0 data (ok, evm', out))
    (hbad : ¬ callReturnFits ptr out ∨ ok = false ∨ ¬ addressReturnValid evm' token out) :
    ExecFuncBody config (optionalCallFrame imms token data ptr) evm
      allocatedOptionalReturnFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (addressCallStatementReverts _ imms token data ptr ok out _
    "__solcAddressResult" (optionalCallArgs evm imms token data ptr) hcall hbad)

theorem optionalCallBodyRevertsBool {evm evm' : State} (imms : Store)
    (token : AccountAddress) (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hcall : callViaEVM evm token 0 data (true, evm', out)) (hfit : callReturnFits ptr out)
    (hvalid : addressReturnValid evm' token out) (hbad : ¬ optionalReturnValid out) :
    ExecFuncBody config (optionalCallFrame imms token data ptr) evm
      allocatedOptionalReturnFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply optionalCallPrefix imms token data ptr out hcall hfit hvalid
  have hs : out.size < 2 ^ 255 := by rcases hfit with hz | ⟨hs, _⟩ <;> omega
  exact ExecBlock.consRevert (optionalReturnSourceReverts
    (optionalResultFrame_data imms token data ptr out) hs hbad)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
