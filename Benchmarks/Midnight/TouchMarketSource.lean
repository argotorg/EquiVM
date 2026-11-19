import Benchmarks.Midnight.TouchMarketSourceBase
import Benchmarks.Midnight.MarketOnlyDecode

/-! The public touchMarket wrapper and propagation of its internal result. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def touchMarketExternalFrame (evm : EVM.State) (m : MarketData) : Frame :=
  calldataFrame contract (marketOnlyArguments m) ∅ evm

theorem evalTouchMarketCallArgs (evm : EVM.State) (m : MarketData) :
    evalExprs? config (touchMarketExternalFrame evm m) evm [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp only [evalExprs?, evalExpr?, touchMarketExternalFrame, calldataFrame,
    marketOnlyArguments, store_get_ne _ _ (show ("__calldata" == "market") = false from rfl),
    store_get_self, EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem touchMarketBodyReturns {evm evm' : EVM.State} {m : MarketData} {frame : Frame}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecFuncBody config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      (.returned frame evm' (some [wordBytes32Value m.id]))) :
    ExecTransitionBody config contract evm (marketOnlyArguments m) touchMarketTransition.body
      (.returned (resumeAfterInternalCall (touchMarketExternalFrame evm m) "__r"
        (some [wordBytes32Value m.id])) evm' (some [wordBytes32Value m.id])) := by
  apply ExecFuncBody.execBlockRet
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (evalTouchMarketCallArgs evm m) rfl rfl hbody)
  exact returnInternalResult "__r" (wordBytes32Value m.id)

theorem touchMarketBodyReverts {evm : EVM.State} {m : MarketData}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecFuncBody config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body .reverted) :
    ExecTransitionBody config contract evm (marketOnlyArguments m) touchMarketTransition.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (evalTouchMarketCallArgs evm m) rfl rfl hbody)

theorem touchMarketBodyStatic {evm : EVM.State} {m : MarketData}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecFuncBody config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      .staticViolation) :
    ExecTransitionBody config contract evm (marketOnlyArguments m) touchMarketTransition.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consStatic
  apply ExecStmt.internalCallStatic
  · exact evalTouchMarketCallArgs evm m
  · rfl
  · rfl
  · exact hbody

end Benchmarks.Midnight
