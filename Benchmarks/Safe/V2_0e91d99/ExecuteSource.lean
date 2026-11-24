import Benchmarks.Safe.V2_0e91d99.ExecuteCallSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99

def executeArgs (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation txGas : UInt256) : Store :=
  (((((∅ : Store).insert "txGas" (.int (Int.ofNat txGas.toNat))).insert
    "operation" (.int (Int.ofNat operation.toNat))).insert "data" (.bytes payload)).insert
      "value" (.int (Int.ofNat value.toNat))).insert "to" (.address target)

def executeFrame (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation txGas : UInt256) : Frame :=
  { contract := contract, locals := executeArgs target value payload operation txGas }

def executeFinalFrame (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation txGas : UInt256) (z : Bool) (out : ByteArray) : Frame :=
  { executeFrame target value payload operation txGas with
    locals := ((executeArgs target value payload operation txGas).insert "success" (.bool z)).insert
      "returnData" (.bytes out) }

theorem safeExecuteLocals (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation txGas : UInt256) :
    ExecuteLocals (executeFrame target value payload operation txGas)
      target value payload operation := by
  constructor <;> simp [executeFrame, executeArgs, Std.HashMap.getElem_insert]

theorem safeExecuteCondition (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation txGas : UInt256) :
    evalExpr? config (executeFrame target value payload operation txGas) evm
      (eqE (.var "operation") (.intLit 1)) =
        .ok (.bool (decide (operation = ⟨1⟩))) := by
  exact safeExecuteCallCondition (safeExecuteLocals target value payload operation txGas)

theorem safeExecuteReturn (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation txGas : UInt256) (z : Bool) (out : ByteArray) :
    ExecBlock fork config (executeFinalFrame target value payload operation txGas z out) evm
      [.return [.var "success"]]
      (.returned (executeFinalFrame target value payload operation txGas z out) evm
        (some [.bool z])) := by
  exact .consReturn (.return (by
    simp [executeFinalFrame, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind,
      bind, pure, Std.HashMap.getElem_insert]))

theorem safeExecuteDelegateSource {evm evm' : EVM.State} {target : EVM.Address}
    {value operation txGas : UInt256} {payload out : ByteArray} {z : Bool}
    (hop : operation = ⟨1⟩)
    (hcall : delegateCallViaEVM fork evm (EVM.address target) payload (z, evm', out)) :
    ExecFuncBody fork config (executeFrame target value payload operation txGas) evm
      executeFunction.body
      (.returned (executeFinalFrame target value payload operation txGas z out) evm'
        (some [.bool z])) := by
  exact .execBlockRet (.consNormal
    (safeExecuteCallStatement (fork := fork) (hperm := Or.inl hop) (safeExecuteLocals target value payload operation txGas)
      (Or.inl ⟨hop, hcall⟩)) (safeExecuteReturn evm' target value payload operation txGas z out))

theorem safeExecuteCallSource {evm evm' : EVM.State} {target : EVM.Address}
    {value operation txGas : UInt256} {payload out : ByteArray} {z : Bool}
    (hop : operation ≠ ⟨1⟩)
    (hcall : callViaEVM fork evm (EVM.address target) (Int.ofNat value.toNat) payload (z, evm', out))
    (hperm : value = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    ExecFuncBody fork config (executeFrame target value payload operation txGas) evm
      executeFunction.body
      (.returned (executeFinalFrame target value payload operation txGas z out) evm'
        (some [.bool z])) := by
  exact .execBlockRet (.consNormal
    (safeExecuteCallStatement (fork := fork) (hperm := Or.inr hperm) (safeExecuteLocals target value payload operation txGas)
      (Or.inr ⟨hop, hcall⟩)) (safeExecuteReturn evm' target value payload operation txGas z out))

theorem safeExecuteCallStaticSource {evm : EVM.State} {target : EVM.Address}
    {value operation txGas : UInt256} {payload : ByteArray}
    (hop : operation ≠ ⟨1⟩) (hp : evm.executionEnv.perm = false) (hv : value ≠ ⟨0⟩) :
    ExecFuncBody fork config (executeFrame target value payload operation txGas) evm
      executeFunction.body .staticViolation := by
  exact .execBlockStatic (.consStatic
    (safeExecuteCallStatementStatic (safeExecuteLocals target value payload operation txGas)
      hop hp hv))

end Benchmarks.Safe.V2_0e91d99
