import Benchmarks.Midnight.SupplyReadSource
import Benchmarks.Midnight.MarketIndexAmountDecode
import Benchmarks.Midnight.TouchMarketSource
import Benchmarks.Midnight.Authorization

/-! Source authorization and market initialization for collateral supply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def supplyExternalFrame (origin : EVM.State) (m : MarketData) (user index assets : UInt256) : Frame :=
  calldataFrame contract (marketIndexAmountArguments m index assets
    (AccountAddress.ofNat user.toNat)) ∅ origin

def supplyAfterTouchFrame (origin : EVM.State) (m : MarketData) (user index assets : UInt256) : Frame :=
  resumeAfterInternalCall (supplyExternalFrame origin m user index assets) "id"
    (some [wordBytes32Value m.id])

theorem supplyAfterTouch_get (origin : EVM.State) (m : MarketData) (user index assets : UInt256) :
    SupplyTouchSourceFrame (supplyAfterTouchFrame origin m user index assets) m user index assets := by
  constructor <;>
    simp [supplyAfterTouchFrame, resumeAfterInternalCall, collapseReturns, supplyExternalFrame,
      calldataFrame, marketIndexAmountArguments, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]

theorem supplyAuthEval (origin : EVM.State) (m : MarketData) (user index assets : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) :
    evalExpr? config (supplyExternalFrame origin m user index assets) origin onBehalfGuard =
      .ok (.bool (decide (onBehalfAllowed origin user))) := by
  apply evalOnBehalfGuard origin user hcanon rfl
  · simp [supplyExternalFrame, calldataFrame, marketIndexAmountArguments]
  · simp [supplyExternalFrame, calldataFrame, marketIndexAmountArguments, Std.HashMap.getElem_insert]

theorem supplyTouchArgs (origin : EVM.State) (m : MarketData) (user index assets : UInt256) :
    evalExprs? config (supplyExternalFrame origin m user index assets) origin [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp [evalExprs?, evalExpr?, supplyExternalFrame, calldataFrame, marketIndexAmountArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert]

theorem supplyAfterAuthSource {origin : EVM.State} {m : MarketData} {user index assets : UInt256}
    {result : ExecResult} (hcanon : user.toNat < EVM.addressModulus)
    (hwv : origin.executionEnv.weiValue = ⟨0⟩)
    (hlimit : origin.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed origin user)
    (htail : ExecBlock config (supplyExternalFrame origin m user index assets) origin
      (supplyCollateralTransition.body.drop 4) result) :
    ExecBlock config { contract := contract, locals := (marketIndexAmountArguments m index assets
      (AccountAddress.ofNat user.toNat)), immutables := ∅ } origin
      supplyCollateralTransition.body result := by
  apply guardedBodyBlock hwv hlimit
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  simpa only [decide_eq_true hauth] using supplyAuthEval origin m user index assets hcanon

theorem supplyAfterTouchSource {origin evm : EVM.State} {m : MarketData} {user index assets : UInt256}
    {callee : Frame} {result : ExecResult}
    (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
      (.returned callee evm (some [wordBytes32Value m.id])))
    (htail : ExecBlock config (supplyAfterTouchFrame origin m user index assets) evm
      (supplyCollateralTransition.body.drop 5) result) :
    ExecBlock config (supplyExternalFrame origin m user index assets) origin
      (supplyCollateralTransition.body.drop 4) result :=
  ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (supplyTouchArgs origin m user index assets) rfl rfl htouch) htail

end Benchmarks.Midnight
