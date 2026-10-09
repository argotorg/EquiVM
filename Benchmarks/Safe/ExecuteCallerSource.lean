import Benchmarks.Safe.ExecuteSource
import Benchmarks.Safe.InternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeInternalExecute {caller : Frame} {evm : EVM.State}
    {targetExpr valueExpr dataExpr operationExpr gasExpr : Expr}
    {target : EVM.Address} {value operation txGas : UInt256} {payload : ByteArray}
    {retVar : Ident} {result : ExecResult}
    (hc : caller.contract = contract) (hi : caller.immutables = ∅)
    (ht : evalExpr? config caller evm targetExpr = .ok (.address target))
    (hv : evalExpr? config caller evm valueExpr = .ok (uint256Value value))
    (hd : evalExpr? config caller evm dataExpr = .ok (.bytes payload))
    (ho : evalExpr? config caller evm operationExpr = .ok (uint256Value operation))
    (hg : evalExpr? config caller evm gasExpr = .ok (uint256Value txGas))
    (hb : ExecFuncBody config (executeFrame target value payload operation txGas) evm
      executeFunction.body result) :
    ExecStmt config caller evm
      (.internalCall "execute" [targetExpr, valueExpr, dataExpr, operationExpr, gasExpr] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := executeFunction)
    (argVals := [.address target, uint256Value value, .bytes payload,
      uint256Value operation, uint256Value txGas])
    (locals := executeArgs target value payload operation txGas)
  · simp only [evalExprs?, ht, hv, hd, ho, hg, EvalResult.bind, bind, pure]
  · rw [hc]; rfl
  · rfl
  · convert hb using 1
    simp only [executeFrame, hc, hi]

end Benchmarks.Safe
