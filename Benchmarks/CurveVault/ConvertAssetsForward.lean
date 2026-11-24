import Benchmarks.CurveVault.ConvertAssetsInternal
import Benchmarks.CurveVault.ConversionArguments

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAssetsForwardBody (isFloor : Bool) : List Stmt :=
  [.internalCall "_convert_to_assets" [.var "_shares", .boolLit isFloor, .intLit (2 ^ 256 - 1)] "__c0",
    .return [.var "__c0"]]

theorem vaultAssetsForwardReturns {evm evm' : State} {locals : Store}
    {callee : Frame} {shares value : UInt256} {isFloor : Bool}
    (ha : locals.get? "_shares" = some (.int (Int.ofNat shares.toNat)))
    (hbody : ExecFuncBody fork config
      {contract := contract, locals := vaultConversionLocals "_shares" shares isFloor vaultMaxWord}
      evm vaultConvertAssetsFunction.body (.returned callee evm' (some [.int (Int.ofNat value.toNat)]))) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm (vaultAssetsForwardBody isFloor)
      (.returned {contract := contract, locals := locals.insert "__c0" (.int (Int.ofNat value.toNat))}
        evm' (some [.int (Int.ofNat value.toNat)])) := by
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (callee := vaultConvertAssetsFunction) (name := "_convert_to_assets")
    (args := [.var "_shares", .boolLit isFloor, .intLit (2 ^ 256 - 1)])
    (argVals := [.int (Int.ofNat shares.toNat), .bool isFloor, .int (Int.ofNat vaultMaxWord.toNat)])
    (retVar := "__c0") (by simp [evalExprs?, heval, evalExpr?, bind, pure, EvalResult.bind]; rfl)
    rfl rfl hbody
  exact ExecFuncBody.execBlockRet <| ExecBlock.consNormal hcall <|
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
      simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption])))

theorem vaultAssetsForwardReverts {evm : State} {locals : Store} {shares : UInt256} {isFloor : Bool}
    (ha : locals.get? "_shares" = some (.int (Int.ofNat shares.toNat)))
    (hbody : ExecFuncBody fork config
      {contract := contract, locals := vaultConversionLocals "_shares" shares isFloor vaultMaxWord}
      evm vaultConvertAssetsFunction.body .reverted) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm (vaultAssetsForwardBody isFloor) .reverted := by
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  exact ExecFuncBody.execBlockRevert <| ExecBlock.consRevert <|
    internalCallFunctionRevert (callee := vaultConvertAssetsFunction)
      (argVals := [.int (Int.ofNat shares.toNat), .bool isFloor, .int (Int.ofNat vaultMaxWord.toNat)])
      (by simp [evalExprs?, heval, evalExpr?, bind, pure, EvalResult.bind]; rfl) rfl rfl hbody
end Benchmarks.CurveVault
