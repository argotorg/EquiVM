import Benchmarks.Morpho.MorphoBlue.SafeTransferFunctionRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoSafeTransferInternalOk (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (cursor : Nat) (locals imms : Store) (evm evm' : EVM.State)
    (frame' : Frame) (result : Option (List Value)) (args : List Expr) (retVar : Ident)
    (ha : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok (safeTransferArgs isFrom token sender recipient value cursor))
    (hb : ExecFuncBody config (safeTransferStart isFrom token sender recipient value cursor imms)
      evm (safeTransferFunctionFor isFrom).body (.returned frame' evm' result)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall (if isFrom then "SafeTransferLib_safeTransferFrom" else "SafeTransferLib_safeTransfer") args retVar)
      (.ok (resumeAfterInternalCall { contract := contract, locals := locals, immutables := imms }
        retVar result) evm') := by
  exact internalCallFunctionReturn (callee := safeTransferFunctionFor isFrom) ha
    (safeTransfer_lookup isFrom) (safeTransfer_bind isFrom token sender recipient value cursor) hb

theorem morphoSafeTransferInternalRevert (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (cursor : Nat) (locals imms : Store) (evm : EVM.State)
    (args : List Expr) (retVar : Ident)
    (ha : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok (safeTransferArgs isFrom token sender recipient value cursor))
    (hb : ExecFuncBody config (safeTransferStart isFrom token sender recipient value cursor imms)
      evm (safeTransferFunctionFor isFrom).body .reverted) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall (if isFrom then "SafeTransferLib_safeTransferFrom" else "SafeTransferLib_safeTransfer") args retVar)
      .reverted := by
  exact internalCallFunctionRevert (callee := safeTransferFunctionFor isFrom) ha
    (safeTransfer_lookup isFrom) (safeTransfer_bind isFrom token sender recipient value cursor) hb

end Benchmarks.Morpho.MorphoBlue
