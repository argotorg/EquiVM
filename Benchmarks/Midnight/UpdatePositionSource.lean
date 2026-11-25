import Benchmarks.Midnight.TouchMarketSource
import Benchmarks.Midnight.PositionUpdateTrace
import Benchmarks.Midnight.MarketUserDecode

variable {fork : Ethereum.Fork}

/-! The public position update sequences market initialization and position accounting. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def updatePositionExternalFrame (evm : EVM.State) (m : MarketData) (user : UInt256) : Frame :=
  calldataFrame contract (marketUserArguments m (AccountAddress.ofNat user.toNat)) ∅ evm

def updatePositionAfterTouchFrame (evm : EVM.State) (m : MarketData) (user : UInt256) : Frame :=
  resumeAfterInternalCall (updatePositionExternalFrame evm m user) "id"
    (some [wordBytes32Value m.id])

theorem evalUpdatePositionTouchArgs (evm : EVM.State) (m : MarketData) (user : UInt256) :
    evalExprs? config (updatePositionExternalFrame evm m user) evm [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp [evalExprs?, evalExpr?, updatePositionExternalFrame, calldataFrame, marketUserArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem evalUpdatePositionCallArgs (evm evm' : EVM.State) (m : MarketData) (user : UInt256) :
    evalExprs? config (updatePositionAfterTouchFrame evm m user) evm'
      [.var "market", .var "id", .var "user"] =
      .ok [Model.marketValue m.value, wordBytes32Value m.id,
        .address (AccountAddress.ofNat user.toNat)] := by
  simp [evalExprs?, evalExpr?, updatePositionAfterTouchFrame, updatePositionExternalFrame,
    resumeAfterInternalCall, collapseReturns, calldataFrame, marketUserArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem updatePositionAfterTouchSource {evm evm' : EVM.State} {m : MarketData} {user : UInt256}
    {frame : Frame} {result}
    (htouch : ExecFuncBody fork config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      (.returned frame evm' (some [wordBytes32Value m.id])))
    (htail : ExecBlock fork config (updatePositionAfterTouchFrame evm m user) evm'
      (updatePositionTransition.body.drop 4) result) :
    ExecBlock fork config (updatePositionExternalFrame evm m user) evm
      (updatePositionTransition.body.drop 3) result := by
  exact ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (evalUpdatePositionTouchArgs evm m user) rfl rfl htouch) htail

theorem updatePositionTouchReverts {evm : EVM.State} {m : MarketData} {user : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecFuncBody fork config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body .reverted) :
    ExecTransitionBody fork config contract evm (marketUserArguments m (AccountAddress.ofNat user.toNat))
      updatePositionTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (evalUpdatePositionTouchArgs evm m user) rfl rfl hbody)

theorem updatePositionTouchStatic {evm : EVM.State} {m : MarketData} {user : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbody : ExecFuncBody fork config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      .staticViolation) :
    ExecTransitionBody fork config contract evm (marketUserArguments m (AccountAddress.ofNat user.toNat))
      updatePositionTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consStatic
  exact ExecStmt.internalCallStatic (evalUpdatePositionTouchArgs evm m user) rfl rfl hbody

theorem updatePositionBodyReverts {evm evm' : EVM.State} {m : MarketData} {user : UInt256}
    {frame : Frame}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (htouch : ExecFuncBody fork config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      (.returned frame evm' (some [wordBytes32Value m.id])))
    (hbody : ExecFuncBody fork config (positionViewCallFrame ∅ m m.id user) evm'
      positionUpdateFunction.body .reverted) :
    ExecTransitionBody fork config contract evm (marketUserArguments m (AccountAddress.ofNat user.toNat))
      updatePositionTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply updatePositionAfterTouchSource htouch
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := positionUpdateFunction)
    (locals := positionViewArguments m m.id user) (evalUpdatePositionCallArgs evm evm' m user)
    rfl rfl hbody)

theorem updatePositionBodyStatic {evm evm' : EVM.State} {m : MarketData} {user : UInt256}
    {frame : Frame}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (htouch : ExecFuncBody fork config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      (.returned frame evm' (some [wordBytes32Value m.id])))
    (hbody : ExecFuncBody fork config (positionViewCallFrame ∅ m m.id user) evm'
      positionUpdateFunction.body .staticViolation) :
    ExecTransitionBody fork config contract evm (marketUserArguments m (AccountAddress.ofNat user.toNat))
      updatePositionTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  apply updatePositionAfterTouchSource htouch
  apply ExecBlock.consStatic
  exact ExecStmt.internalCallStatic (evalUpdatePositionCallArgs evm evm' m user) rfl rfl hbody

theorem updatePositionBodyReturns {evm evm' evm'' : EVM.State} {m : MarketData}
    {user credit pending fee : UInt256} {touchFrame updateFrame : Frame}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (htouch : ExecFuncBody fork config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      (.returned touchFrame evm' (some [wordBytes32Value m.id])))
    (hbody : ExecFuncBody fork config (positionViewCallFrame ∅ m m.id user) evm'
      positionUpdateFunction.body (.returned updateFrame evm''
        (some [.int credit.toNat, .int pending.toNat, .int fee.toNat]))) :
    ExecTransitionBody fork config contract evm (marketUserArguments m (AccountAddress.ofNat user.toNat))
      updatePositionTransition.body
      (.returned (resumeAfterInternalCall (updatePositionAfterTouchFrame evm m user) "__c1"
        (some [.int credit.toNat, .int pending.toNat, .int fee.toNat])) evm''
        (some [.int credit.toNat, .int pending.toNat, .int fee.toNat])) := by
  apply ExecFuncBody.execBlockRet
  apply guardedBodyBlock hwv hhi
  apply updatePositionAfterTouchSource htouch
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := positionUpdateFunction)
    (locals := positionViewArguments m m.id user) (evalUpdatePositionCallArgs evm evm' m user)
    rfl rfl hbody)
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, collapseReturns, store_get_self,
    tupleGetValue?, bind, pure, EvalResult.bind, EvalResult.ofOption,
    List.getElem?_cons_zero, List.getElem?_cons_succ]

end Benchmarks.Midnight
