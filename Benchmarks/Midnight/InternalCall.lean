import Benchmarks.Midnight.Entry

variable {fork : Ethereum.Fork}

/-! Source composition for entry guards and single-result internal calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem guardedBodyBlock {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {body : List Stmt} {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecBlock fork cfg (calldataFrame C locals imms evm) evm body result) :
    ExecBlock fork cfg { contract := C, locals := locals, immutables := imms } evm
      (entryPrefix ++ body) result := by
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (value := .bytes evm.executionEnv.calldata)
      (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_).run hbody
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_true hhi))

theorem returnInternalResult {cfg : Config} {frame : Frame} {evm : EVM.State}
    (name : Ident) (value : Value) :
    ExecBlock fork cfg (resumeAfterInternalCall frame name (some [value])) evm [.return [.var name]]
      (.returned (resumeAfterInternalCall frame name (some [value])) evm (some [value])) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, collapseReturns, store_get_self,
    EvalResult.ofOption, bind, pure, EvalResult.bind]

end Benchmarks.Midnight
