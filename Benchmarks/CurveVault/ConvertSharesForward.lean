import Benchmarks.CurveVault.ConvertSharesInternal
import Benchmarks.CurveVault.ConversionArguments

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultSharesForwardBody (isFloor : Bool) : List Stmt :=
  [.internalCall "_convert_to_shares" [.var "_assets", .boolLit isFloor, .intLit (2 ^ 256 - 1)] "__c0",
    .return [.var "__c0"]]

theorem vaultSharesForwardReturns {evm evm' : State} {locals : Store}
    {callee : Frame} {assets value : UInt256} {isFloor : Bool}
    (ha : locals.get? "_assets" = some (.int (Int.ofNat assets.toNat)))
    (hbody : ExecFuncBody fork config
      {contract := contract, locals := vaultConversionLocals "_assets" assets isFloor vaultMaxWord}
      evm vaultConvertSharesFunction.body (.returned callee evm' (some [.int (Int.ofNat value.toNat)]))) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm (vaultSharesForwardBody isFloor)
      (.returned {contract := contract, locals := locals.insert "__c0" (.int (Int.ofNat value.toNat))}
        evm' (some [.int (Int.ofNat value.toNat)])) := by
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (callee := vaultConvertSharesFunction) (name := "_convert_to_shares")
    (args := [.var "_assets", .boolLit isFloor, .intLit (2 ^ 256 - 1)])
    (argVals := [.int (Int.ofNat assets.toNat), .bool isFloor, .int (Int.ofNat vaultMaxWord.toNat)])
    (retVar := "__c0") (by simp [evalExprs?, heval, evalExpr?, bind, pure, EvalResult.bind]; rfl)
    rfl rfl hbody
  exact ExecFuncBody.execBlockRet <| ExecBlock.consNormal hcall <|
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
      simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption])))

theorem vaultSharesForwardReverts {evm : State} {locals : Store} {assets : UInt256} {isFloor : Bool}
    (ha : locals.get? "_assets" = some (.int (Int.ofNat assets.toNat)))
    (hbody : ExecFuncBody fork config
      {contract := contract, locals := vaultConversionLocals "_assets" assets isFloor vaultMaxWord}
      evm vaultConvertSharesFunction.body .reverted) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm (vaultSharesForwardBody isFloor) .reverted := by
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  exact ExecFuncBody.execBlockRevert <| ExecBlock.consRevert <|
    internalCallFunctionRevert (callee := vaultConvertSharesFunction)
      (argVals := [.int (Int.ofNat assets.toNat), .bool isFloor, .int (Int.ofNat vaultMaxWord.toNat)])
      (by simp [evalExprs?, heval, evalExpr?, bind, pure, EvalResult.bind]; rfl) rfl rfl hbody
end Benchmarks.CurveVault
