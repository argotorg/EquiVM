import Benchmarks.CompoundIII.Comet.VoidCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: ABI equivalence of the constant Boolean success return.
theorem boolTrueReturnEquiv :
    returnEquiv (UInt256.ofNat 1).toByteArray (some [.bool true]) [.elem .bool] :=
  returnEquiv.returned rfl boolTrueReturnEncoding

-- GENERALIZES explicitVoidSourceResult to a fixed list of return values.
def explicitSourceResult (cfg : Config) (frame : Frame) (evm : EVM.State)
    (body : List Stmt) (values : List Value) : InternalOutcome → Prop
  | .ok evm' => ∃ final, ExecFuncBody cfg frame evm body (.returned final evm' (some values))
  | .reverted => ExecFuncBody cfg frame evm body .reverted
  | .staticViolation => ExecFuncBody cfg frame evm body .staticViolation

-- GENERALIZES voidCallPrologue_source to a post-call return expression list.
theorem callReturnPrologue_source {cfg frame evm stmt final ret result exprs values}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (he : ∀ evm', evalExprs? cfg { final with locals := final.locals.insert ret .unit }
      evm' exprs = .ok values)
    (hc : ExecStmt cfg (calldataLocalFrame frame evm) evm stmt (internalStmtResult final ret result)) :
    explicitSourceResult cfg frame evm (calldataPrologue [stmt, .return exprs]) values result := by
  cases result with
  | ok evm' =>
    exact ⟨_, ExecFuncBody.execBlockRet ((calldataPrologue_ok hv hhi).run
      (ExecBlock.consNormal hc (ExecBlock.consReturn (ExecStmt.return (he evm')))))⟩
  | reverted =>
    exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run (ExecBlock.consRevert hc))
  | staticViolation =>
    exact ExecFuncBody.execBlockStatic ((calldataPrologue_ok hv hhi).run (ExecBlock.consStatic hc))

end Benchmarks.CompoundIII.Comet
