import Benchmarks.Midnight.WithdrawUnitsSourceFrame
import Benchmarks.Midnight.PositionUpdateSource
import Benchmarks.Midnight.MarketUnitsReceiverDecode
import Benchmarks.Midnight.TouchMarketSource
import Benchmarks.Midnight.Authorization

variable {fork : Ethereum.Fork}

/-! Source authorization and market initialization for unit withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawUnitsExternalFrame (origin : EVM.State) (m : MarketData) (user units : UInt256) (receiver : AccountAddress) : Frame :=
  calldataFrame contract (marketUnitsReceiverArguments m units
    (AccountAddress.ofNat user.toNat) receiver) ∅ origin

def withdrawUnitsAfterTouchFrame (origin : EVM.State) (m : MarketData) (user units : UInt256) (receiver : AccountAddress) : Frame :=
  resumeAfterInternalCall (withdrawUnitsExternalFrame origin m user units receiver) "id"
    (some [wordBytes32Value m.id])

theorem withdrawUnitsAuthEval (origin : EVM.State) (m : MarketData) (user units : UInt256) (receiver : AccountAddress)
    (hcanon : user.toNat < EVM.addressModulus) :
    evalExpr? config (withdrawUnitsExternalFrame origin m user units receiver) origin onBehalfGuard =
      .ok (.bool (decide (onBehalfAllowed origin user))) := by
  apply evalOnBehalfGuard origin user hcanon rfl
  · simp [withdrawUnitsExternalFrame, calldataFrame, marketUnitsReceiverArguments]
  · simp [withdrawUnitsExternalFrame, calldataFrame, marketUnitsReceiverArguments, Std.HashMap.getElem_insert]

theorem withdrawUnitsTouchArgs (origin : EVM.State) (m : MarketData) (user units : UInt256) (receiver : AccountAddress) :
    evalExprs? config (withdrawUnitsExternalFrame origin m user units receiver) origin [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp [evalExprs?, evalExpr?, withdrawUnitsExternalFrame, calldataFrame, marketUnitsReceiverArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert]

theorem withdrawUnitsAfterAuthSource {origin : EVM.State} {m : MarketData} {user units : UInt256} {receiver : AccountAddress}
    {result : ExecResult} (hcanon : user.toNat < EVM.addressModulus)
    (hwv : origin.executionEnv.weiValue = ⟨0⟩)
    (hlimit : origin.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed origin user)
    (htail : ExecBlock fork config (withdrawUnitsExternalFrame origin m user units receiver) origin
      (withdrawTransition.body.drop 4) result) :
    ExecBlock fork config { contract := contract, locals := (marketUnitsReceiverArguments m units
      (AccountAddress.ofNat user.toNat) receiver), immutables := ∅ } origin
      withdrawTransition.body result := by
  apply guardedBodyBlock hwv hlimit
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  exact (withdrawUnitsAuthEval origin m user units receiver hcanon).trans
    (by rw [decide_eq_true hauth])

theorem withdrawUnitsAfterTouchSource {origin evm : EVM.State} {m : MarketData} {user units : UInt256} {receiver : AccountAddress}
    {callee : Frame} {result : ExecResult}
    (htouch : ExecFuncBody fork config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
      (.returned callee evm (some [wordBytes32Value m.id])))
    (htail : ExecBlock fork config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
      (withdrawTransition.body.drop 5) result) :
    ExecBlock fork config (withdrawUnitsExternalFrame origin m user units receiver) origin
      (withdrawTransition.body.drop 4) result :=
  ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (withdrawUnitsTouchArgs origin m user units receiver) rfl rfl htouch) htail

end Benchmarks.Midnight
