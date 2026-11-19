import Benchmarks.Midnight.WithdrawReadSource
import Benchmarks.Midnight.MarketIndexAmountReceiverDecode
import Benchmarks.Midnight.TouchMarketSource
import Benchmarks.Midnight.Authorization

/-! Source authorization and market initialization for collateral withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawExternalFrame (origin : EVM.State) (m : MarketData) (user index assets : UInt256) (receiver : AccountAddress) : Frame :=
  calldataFrame contract (marketIndexAmountReceiverArguments m index assets
    (AccountAddress.ofNat user.toNat) receiver) ∅ origin

def withdrawAfterTouchFrame (origin : EVM.State) (m : MarketData) (user index assets : UInt256) (receiver : AccountAddress) : Frame :=
  resumeAfterInternalCall (withdrawExternalFrame origin m user index assets receiver) "id"
    (some [wordBytes32Value m.id])

theorem withdrawAfterTouch_get (origin : EVM.State) (m : MarketData) (user index assets : UInt256) (receiver : AccountAddress) :
    SupplyTouchSourceFrame (withdrawAfterTouchFrame origin m user index assets receiver) m user index assets := by
  constructor <;>
    simp [withdrawAfterTouchFrame, resumeAfterInternalCall, collapseReturns, withdrawExternalFrame,
      calldataFrame, marketIndexAmountReceiverArguments, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]

theorem withdrawAfterTouch_receiver (origin : EVM.State) (m : MarketData)
    (user index assets : UInt256) (receiver : AccountAddress) :
    (withdrawAfterTouchFrame origin m user index assets receiver).locals.get? "receiver" =
      some (.address receiver) := by
  simp [withdrawAfterTouchFrame, resumeAfterInternalCall, collapseReturns, withdrawExternalFrame,
    calldataFrame, marketIndexAmountReceiverArguments, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert]

theorem withdrawAuthEval (origin : EVM.State) (m : MarketData) (user index assets : UInt256) (receiver : AccountAddress)
    (hcanon : user.toNat < EVM.addressModulus) :
    evalExpr? config (withdrawExternalFrame origin m user index assets receiver) origin onBehalfGuard =
      .ok (.bool (decide (onBehalfAllowed origin user))) := by
  apply evalOnBehalfGuard origin user hcanon rfl
  · simp [withdrawExternalFrame, calldataFrame, marketIndexAmountReceiverArguments]
  · simp [withdrawExternalFrame, calldataFrame, marketIndexAmountReceiverArguments, Std.HashMap.getElem_insert]

theorem withdrawTouchArgs (origin : EVM.State) (m : MarketData) (user index assets : UInt256) (receiver : AccountAddress) :
    evalExprs? config (withdrawExternalFrame origin m user index assets receiver) origin [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp [evalExprs?, evalExpr?, withdrawExternalFrame, calldataFrame, marketIndexAmountReceiverArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert]

theorem withdrawAfterAuthSource {origin : EVM.State} {m : MarketData} {user index assets : UInt256} {receiver : AccountAddress}
    {result : ExecResult} (hcanon : user.toNat < EVM.addressModulus)
    (hwv : origin.executionEnv.weiValue = ⟨0⟩)
    (hlimit : origin.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed origin user)
    (htail : ExecBlock config (withdrawExternalFrame origin m user index assets receiver) origin
      (withdrawCollateralTransition.body.drop 4) result) :
    ExecBlock config { contract := contract, locals := (marketIndexAmountReceiverArguments m index assets
      (AccountAddress.ofNat user.toNat) receiver), immutables := ∅ } origin
      withdrawCollateralTransition.body result := by
  apply guardedBodyBlock hwv hlimit
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  exact (withdrawAuthEval origin m user index assets receiver hcanon).trans
    (by rw [decide_eq_true hauth])

theorem withdrawAfterTouchSource {origin evm : EVM.State} {m : MarketData} {user index assets : UInt256} {receiver : AccountAddress}
    {callee : Frame} {result : ExecResult}
    (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
      (.returned callee evm (some [wordBytes32Value m.id])))
    (htail : ExecBlock config (withdrawAfterTouchFrame origin m user index assets receiver) evm
      (withdrawCollateralTransition.body.drop 5) result) :
    ExecBlock config (withdrawExternalFrame origin m user index assets receiver) origin
      (withdrawCollateralTransition.body.drop 4) result :=
  ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (withdrawTouchArgs origin m user index assets receiver) rfl rfl htouch) htail

end Benchmarks.Midnight
