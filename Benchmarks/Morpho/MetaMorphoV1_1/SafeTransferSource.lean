import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferABI

/-! Source composition for the transfer request allocation and optional-return call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def safeTransferFrame (imms : Store) (token recipient : AccountAddress) (amount ptr : UInt256) :
    Frame :=
  ⟨contract, ((((∅ : Store).insert cursorName (uint256Value ptr)).insert
    "value" (uint256Value amount)).insert "to" (.address recipient)).insert
    "token" (.address token), imms⟩

def safeTransferDataFrame (imms : Store) (token recipient : AccountAddress)
    (amount ptr : UInt256) : Frame :=
  { safeTransferFrame imms token recipient amount ptr with
    locals := (safeTransferFrame imms token recipient amount ptr).locals.insert "data"
      (.bytes (safeTransferCalldata recipient amount)) }

def safeTransferAllocatedFrame (imms : Store) (token recipient : AccountAddress)
    (amount ptr : UInt256) : Frame :=
  { safeTransferDataFrame imms token recipient amount ptr with
    locals := (safeTransferDataFrame imms token recipient amount ptr).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨100⟩)) }

def safeTransferResultFrame (imms : Store) (token recipient : AccountAddress)
    (amount ptr cursor : UInt256) : Frame :=
  { safeTransferAllocatedFrame imms token recipient amount ptr with
    locals := (safeTransferAllocatedFrame imms token recipient amount ptr).locals.insert "__c0"
      (uint256Value cursor) }

theorem safeTransferEncodeSource (evm : State) (imms : Store) (token recipient : AccountAddress)
    (amount ptr : UInt256) :
    evalExpr? config (safeTransferFrame imms token recipient amount ptr) evm
      (.abiEncodeCall "transfer" [.var "to", .var "value"]) =
      .ok (.bytes (safeTransferCalldata recipient amount)) := by
  simp [evalExpr?, evalExprList?, safeTransferFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure, safeTransferEncode]

theorem safeTransferCursorSource (evm : State) (imms : Store) (token recipient : AccountAddress)
    (amount ptr : UInt256) :
    evalExpr? config (safeTransferDataFrame imms token recipient amount ptr) evm
      (.var cursorName) = .ok (uint256Value ptr) := by
  simp [evalExpr?, safeTransferDataFrame, safeTransferFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem safeTransferOptionalArgs (evm : State) (imms : Store) (token recipient : AccountAddress)
    (amount ptr : UInt256) :
    evalExprs? config (safeTransferAllocatedFrame imms token recipient amount ptr) evm
      [.var "token", .var "data", .var cursorName] =
      .ok [.address token, .bytes (safeTransferCalldata recipient amount),
        uint256Value (nextCursor ptr ⟨100⟩)] := by
  simp [evalExprs?, evalExpr?, safeTransferAllocatedFrame, safeTransferDataFrame,
    safeTransferFrame, cursorName, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem safeTransferPrefix (evm : State) (imms : Store) (token recipient : AccountAddress)
    (amount ptr : UInt256) {result : ExecResult} (hfit : allocationFits ptr ⟨100⟩)
    (htail : ExecBlock config (safeTransferAllocatedFrame imms token recipient amount ptr) evm
      (allocatedSafeTransferFunction.body.drop 2) result) :
    ExecBlock config (safeTransferFrame imms token recipient amount ptr) evm
      allocatedSafeTransferFunction.body result := by
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (safeTransferEncodeSource evm imms token recipient amount ptr))
  apply ExecBlock.consNormal _ htail
  exact allocateCallReturns cursorName allocateFunction_lookup
    (safeTransferCursorSource evm imms token recipient amount ptr)
    (by simp [evalExpr?, pure, uint256Value]; decide) hfit

theorem safeTransferBodyReturns {evm evm' : State} (imms : Store)
    (token recipient : AccountAddress) (amount ptr cursor : UInt256) {frame' : Frame}
    (hfit : allocationFits ptr ⟨100⟩)
    (hcall : ExecFuncBody config
      (optionalCallFrame imms token (safeTransferCalldata recipient amount) (nextCursor ptr ⟨100⟩))
      evm allocatedOptionalReturnFunction.body
      (.returned frame' evm' (some [uint256Value cursor]))) :
    ExecFuncBody config (safeTransferFrame imms token recipient amount ptr) evm
      allocatedSafeTransferFunction.body
      (.returned (safeTransferResultFrame imms token recipient amount ptr cursor) evm'
        (some [uint256Value cursor])) := by
  apply ExecFuncBody.execBlockRet
  apply safeTransferPrefix evm imms token recipient amount ptr hfit
  apply ExecBlock.consNormal (internalCallFunctionReturn
    (callee := allocatedOptionalReturnFunction)
    (safeTransferOptionalArgs evm imms token recipient amount ptr) rfl rfl hcall)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  change evalExprs? config
    (safeTransferResultFrame imms token recipient amount ptr cursor) evm' _ = _
  simp only [evalExprs?, evalExpr?, safeTransferResultFrame, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem safeTransferBodyRevertsCall (evm : State) (imms : Store)
    (token recipient : AccountAddress) (amount ptr : UInt256)
    (hfit : allocationFits ptr ⟨100⟩)
    (hcall : ExecFuncBody config
      (optionalCallFrame imms token (safeTransferCalldata recipient amount) (nextCursor ptr ⟨100⟩))
      evm allocatedOptionalReturnFunction.body .reverted) :
    ExecFuncBody config (safeTransferFrame imms token recipient amount ptr) evm
      allocatedSafeTransferFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safeTransferPrefix evm imms token recipient amount ptr hfit
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedOptionalReturnFunction)
    (safeTransferOptionalArgs evm imms token recipient amount ptr) rfl rfl hcall)

theorem safeTransferBodyRevertsAllocation (evm : State) (imms : Store)
    (token recipient : AccountAddress) (amount ptr : UInt256)
    (hbad : ¬ allocationFits ptr ⟨100⟩) :
    ExecFuncBody config (safeTransferFrame imms token recipient amount ptr) evm
      allocatedSafeTransferFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (safeTransferEncodeSource evm imms token recipient amount ptr))
  exact ExecBlock.consRevert (allocateCallReverts cursorName allocateFunction_lookup
    (safeTransferCursorSource evm imms token recipient amount ptr)
    (by simp [evalExpr?, pure, uint256Value]; decide) hbad)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
