import Benchmarks.Midnight.HealthSource
import Benchmarks.Midnight.MarketAccountDecode

/-! The external health wrapper calls the internal predicate and returns its Boolean. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def isHealthyExternalFrame (evm : EVM.State) (m : MarketData) (id user : UInt256) : Frame :=
  calldataFrame contract (marketIdAccountArguments "borrower" m id
    (AccountAddress.ofNat user.toNat)) ∅ evm

theorem evalIsHealthyCallArgs (evm : EVM.State) (m : MarketData) (id user : UInt256) :
    evalExprs? config (isHealthyExternalFrame evm m id user) evm
      [.var "market", .var "id", .var "borrower"] =
      .ok [Model.marketValue m.value, wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)] := by
  simp [evalExprs?, evalExpr?, isHealthyExternalFrame, calldataFrame, marketIdAccountArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem isHealthyBodyReverts {evm : EVM.State} {m : MarketData} {id user : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecFuncBody config (healthCallFrame ∅ m id user) evm healthFunction.body .reverted) :
    ExecTransitionBody config contract evm
      (marketIdAccountArguments "borrower" m id (AccountAddress.ofNat user.toNat))
      isHealthyTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := healthFunction)
    (locals := healthArguments m id user) (evalIsHealthyCallArgs evm m id user) rfl rfl hbody)

theorem isHealthyBodyReturns {evm evm' : EVM.State} {m : MarketData} {id user : UInt256}
    {frame : Frame} {value : Bool}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecFuncBody config (healthCallFrame ∅ m id user) evm healthFunction.body
      (.returned frame evm' (some [.bool value]))) :
    ExecTransitionBody config contract evm
      (marketIdAccountArguments "borrower" m id (AccountAddress.ofNat user.toNat))
      isHealthyTransition.body
      (.returned (resumeAfterInternalCall (isHealthyExternalFrame evm m id user) "__r"
        (some [.bool value])) evm' (some [.bool value])) := by
  apply ExecFuncBody.execBlockRet
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := healthFunction)
    (locals := healthArguments m id user) (evalIsHealthyCallArgs evm m id user) rfl rfl hbody)
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, collapseReturns, store_get_self,
    bind, pure, EvalResult.bind, EvalResult.ofOption]

end Benchmarks.Midnight
