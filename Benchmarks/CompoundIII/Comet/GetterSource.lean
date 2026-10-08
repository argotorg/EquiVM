import Benchmarks.CompoundIII.Comet.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def calldataLocalFrame (frame : Frame) (evm : EVM.State) : Frame :=
  { frame with locals := frame.locals.insert "__calldata" (.bytes evm.executionEnv.calldata) }

def calldataBoundExpr : Expr :=
  .binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩) (.intLit (2 ^ 255 + 4))

def calldataPrologue (body : List Stmt) : List Stmt :=
  .require (.binary .eq (.env .callvalue) (.intLit 0)) ::
  .letDecl "__calldata" (some .bytes) (.env .msgData) :: .require calldataBoundExpr :: body

-- LIBRARY CANDIDATE: Reasoning.SolmBody — the source counterpart of solc's
-- nonpayability and signed calldata-size checks, parameterized by the remaining body.
theorem calldataBound_eval (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg (calldataLocalFrame frame evm) evm calldataBoundExpr =
      .ok (.bool (decide (evm.executionEnv.calldata.size < 2 ^ 255 + 4))) := by
  simp [calldataLocalFrame, calldataBoundExpr, evalExpr?, readLocalPath?, evalBinaryOp?,
    pure, Bind.bind, EvalResult.bind]

theorem calldataPrologue_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {body : List Stmt} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock cfg evm frame (calldataPrologue body) (calldataLocalFrame frame evm) body := by
  exact ((ABlock.start.requireStep (evalCallvalueEq_true hvalue)).letStep
    (show evalExpr? cfg frame evm (.env .msgData) = .ok (.bytes evm.executionEnv.calldata)
      by simp only [evalExpr?, envValue, pure])).requireStep (by
        simpa only [calldataLocalFrame, decide_eq_true hsize] using
          calldataBound_eval cfg frame evm)

theorem calldataPrologue_nonpayable {cfg : Config} {frame : Frame} {evm : EVM.State}
    {body : List Stmt} (hvalue : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecFuncBody cfg frame evm (calldataPrologue body) .reverted := by
  exact .execBlockRevert (ABlock.start.requireRevert (evalCallvalueEq_false hvalue))

theorem calldataPrologue_huge {cfg : Config} {frame : Frame} {evm : EVM.State}
    {body : List Stmt} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : ¬ evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecFuncBody cfg frame evm (calldataPrologue body) .reverted := by
  exact .execBlockRevert <|
    ((ABlock.start.requireStep (evalCallvalueEq_true hvalue)).letStep
      (show evalExpr? cfg frame evm (.env .msgData) = .ok (.bytes evm.executionEnv.calldata)
        by simp only [evalExpr?, envValue, pure])).requireRevert (by
          simpa only [calldataLocalFrame, decide_eq_false hsize] using
            calldataBound_eval cfg frame evm)

theorem immutableGetter_returns {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {value : Value} (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hget : frame.immutables.get? name = some value) :
    ExecFuncBody cfg frame evm (calldataPrologue [.return [.immutable name]])
      (.returned (calldataLocalFrame frame evm) evm (some [value])) := by
  exact .execBlockRet <| (calldataPrologue_ok hvalue hsize).returns (by
    simp only [evalExpr?, calldataLocalFrame, hget, EvalResult.ofOption])

end Benchmarks.CompoundIII.Comet
