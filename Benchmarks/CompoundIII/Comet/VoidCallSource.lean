import Benchmarks.CompoundIII.Comet.InternalOutcome
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: terminal source outcomes of a function with an explicit void return.
def explicitVoidSourceResult (cfg : Config) (frame : Frame) (evm : EVM.State)
    (body : List Stmt) : InternalOutcome → Prop
  | .ok evm' => ∃ final, ExecFuncBody cfg frame evm body (.returned final evm' (some []))
  | .reverted => ExecFuncBody cfg frame evm body .reverted
  | .staticViolation => ExecFuncBody cfg frame evm body .staticViolation

-- LIBRARY CANDIDATE: lift a void call through the nonpayable/calldata prologue.
theorem voidCallPrologue_source {cfg frame evm stmt final ret result}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (hc : ExecStmt cfg (calldataLocalFrame frame evm) evm stmt (internalStmtResult final ret result)) :
    explicitVoidSourceResult cfg frame evm (calldataPrologue [stmt, .return []]) result := by
  cases result with
  | ok evm' =>
    exact ⟨_, ExecFuncBody.execBlockRet ((calldataPrologue_ok hv hhi).run
      (ExecBlock.consNormal hc (ExecBlock.consReturn (ExecStmt.return rfl))))⟩
  | reverted =>
    exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run (ExecBlock.consRevert hc))
  | staticViolation =>
    exact ExecFuncBody.execBlockStatic ((calldataPrologue_ok hv hhi).run (ExecBlock.consStatic hc))

end Benchmarks.CompoundIII.Comet
