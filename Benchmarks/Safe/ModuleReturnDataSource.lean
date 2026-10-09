import Benchmarks.Safe.ModuleCallerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def moduleReturnDataFrame (target guard : EVM.Address) (value operation hash : UInt256)
    (payload : ByteArray) (z : Bool) (out : ByteArray) : Frame :=
  executeCallFrame (moduleAfterPre target value payload operation guard hash) z out

theorem safeModuleExecuteLocals (target guard : EVM.Address) (value operation hash : UInt256)
    (payload : ByteArray) :
    ExecuteLocals (moduleAfterPre target value payload operation guard hash)
      target value payload operation := by
  constructor <;>
    simp [moduleAfterPre, moduleFrame, moduleArgs, resumeAfterInternalCall,
      Std.HashMap.getElem_insert]

theorem safeModuleReturnDataPost {evm : EVM.State} {target guard : EVM.Address}
    {payload out : ByteArray} {value operation hash : UInt256} {z : Bool} {result : ExecResult}
    (hbody : ExecFuncBody config (postModuleFrame guard hash z) evm
      postModuleExecutionFunction.body result) :
    ExecStmt config (moduleReturnDataFrame target guard value operation hash payload z out) evm
      modulePostCall
      (internalCallResult (moduleReturnDataFrame target guard value operation hash payload z out)
        "_post" result) := by
  apply internalCallFunctionResult (callee := postModuleExecutionFunction)
    (argVals := [.address guard, .fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z])
    (locals := postModuleArgs guard hash z)
  · simp [moduleReturnDataFrame, executeCallFrame, moduleAfterPre, moduleFrame, moduleArgs,
      resumeAfterInternalCall, collapseReturns, tuple0, tuple1, tupleGetValue?, evalExprs?,
      evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · exact hbody

theorem safeModuleReturnDataReturn (evm : EVM.State) (target guard : EVM.Address)
    (value operation hash : UInt256) (payload : ByteArray) (z : Bool) (out : ByteArray) :
    ExecBlock config
      (resumeAfterInternalCall
        (moduleReturnDataFrame target guard value operation hash payload z out) "_post" none)
      evm [.return [.var "success", .var "returnData"]]
      (.returned
        (resumeAfterInternalCall
          (moduleReturnDataFrame target guard value operation hash payload z out) "_post" none)
        evm (some [.bool z, .bytes out])) := by
  exact .consReturn (.return (by
    simp [moduleReturnDataFrame, executeCallFrame, resumeAfterInternalCall, collapseReturns,
      evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      Std.HashMap.getElem_insert]))

end Benchmarks.Safe
