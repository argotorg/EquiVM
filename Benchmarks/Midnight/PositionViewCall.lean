import Benchmarks.Midnight.PositionViewSource
import Benchmarks.Midnight.MarketEntryDecode

variable {fork : Ethereum.Fork}

/-! The external wrapper calling the internal position-view function. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def positionViewExternalFrame (evm : EVM.State) (m : MarketData) (id user : UInt256) : Frame :=
  calldataFrame contract (marketIdUserArguments m id (AccountAddress.ofNat user.toNat)) ∅ evm

theorem evalPositionViewCallArgs (evm : EVM.State) (m : MarketData) (id user : UInt256) :
    evalExprs? config (positionViewExternalFrame evm m id user) evm
      [.var "market", .var "id", .var "user"] =
      .ok [Model.marketValue m.value, wordBytes32Value id, .address (AccountAddress.ofNat user.toNat)] := by
  simp [evalExprs?, evalExpr?, positionViewExternalFrame, calldataFrame, marketIdUserArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem positionViewBodyReturns (evm : EVM.State) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hsafe : PositionViewSourceSafe evm m id user) :
    ExecTransitionBody fork config contract evm
      (marketIdUserArguments m id (AccountAddress.ofNat user.toNat)) updatePositionViewTransition.body
      (.returned (resumeAfterInternalCall (positionViewExternalFrame evm m id user) "result"
        (some (positionViewReturnValues (positionPostCredit evm id user) (positionPostPending evm id user)
          (positionViewFee evm m id user)))) evm
        (some (positionViewReturnValues (positionPostCredit evm id user) (positionPostPending evm id user)
          (positionViewFee evm m id user)))) := by
  apply ExecFuncBody.execBlockRet
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := positionViewFunction)
    (locals := positionViewArguments m id user) (evalPositionViewCallArgs evm m id user) rfl rfl
    (positionViewInternalReturns evm ∅ m id user hcanon hsafe))
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, collapseReturns,
    positionViewReturnValues, store_get_self, tupleGetValue?, bind, pure, EvalResult.bind,
    EvalResult.ofOption, List.getElem?_cons_zero, List.getElem?_cons_succ]

theorem positionViewBodyReverts (evm : EVM.State) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hbad : ¬ PositionViewSourceSafe evm m id user) :
    ExecTransitionBody fork config contract evm
      (marketIdUserArguments m id (AccountAddress.ofNat user.toNat)) updatePositionViewTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := positionViewFunction)
    (locals := positionViewArguments m id user) (evalPositionViewCallArgs evm m id user) rfl rfl
    (positionViewInternalReverts evm ∅ m id user hcanon hbad))

end Benchmarks.Midnight
