import Benchmarks.Midnight.MarketAmountDecode
import Benchmarks.Midnight.TouchMarketSource
import Benchmarks.Midnight.RoleSource
import Benchmarks.Midnight.ClaimFeeState

/-! Source frames through market initialization and claim authorization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def claimFeeExternalFrame (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) : Frame :=
  calldataFrame contract
    (marketAmountAccountArguments "receiver" m amount (AccountAddress.ofNat receiver.toNat)) ∅ evm

def claimFeeAfterTouchFrame (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) : Frame :=
  resumeAfterInternalCall (claimFeeExternalFrame evm m amount receiver) "id"
    (some [wordBytes32Value m.id])

def claimFeeAliasFrame (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) : Frame :=
  let frame := claimFeeAfterTouchFrame evm m amount receiver
  { frame with
    locals := frame.locals.insert "_marketState" (.storageRef (marketStateRef m.id) marketStateType) }

def claimFeeCreditFrame (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) : Frame :=
  wordLocal (claimFeeAliasFrame evm m amount receiver) "__c1" amount

def claimFeeUnitsFrame (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) : Frame :=
  wordLocal (claimFeeCreditFrame evm m amount receiver) "__c2" amount

def claimFeeFinalFrame (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) : Frame :=
  wordLocal (claimFeeUnitsFrame evm m amount receiver) "__c3" amount

theorem evalClaimFeeTouchArgs (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) :
    evalExprs? config (claimFeeExternalFrame evm m amount receiver) evm [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp [evalExprs?, evalExpr?, claimFeeExternalFrame, calldataFrame, marketAmountAccountArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem claimFeeAfterTouchSource {evm evm' : EVM.State} {m : MarketData} {amount receiver : UInt256}
    {frame : Frame} {result}
    (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      (.returned frame evm' (some [wordBytes32Value m.id])))
    (htail : ExecBlock config (claimFeeAfterTouchFrame evm m amount receiver) evm'
      (claimContinuousFeeTransition.body.drop 4) result) :
    ExecBlock config (claimFeeExternalFrame evm m amount receiver) evm
      (claimContinuousFeeTransition.body.drop 3) result :=
  ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (evalClaimFeeTouchArgs evm m amount receiver) rfl rfl htouch) htail

theorem claimFeeBindAlias (evm evm' : EVM.State) (m : MarketData) (amount receiver : UInt256) :
    ABlock config evm' (claimFeeAfterTouchFrame evm m amount receiver)
      (claimContinuousFeeTransition.body.drop 4) (claimFeeAliasFrame evm m amount receiver)
      (claimContinuousFeeTransition.body.drop 5) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  apply resolveBytes32Mapping
  · simp [claimFeeAfterTouchFrame, resumeAfterInternalCall, claimFeeExternalFrame,
      calldataFrame, marketAmountAccountArguments, collapseReturns]
  · exact store_get_self _ _ _
  · rfl

theorem claimFeeAuthEval (evm evm' : EVM.State) (m : MarketData) (amount receiver : UInt256) :
    evalExpr? config (claimFeeAliasFrame evm m amount receiver) evm' (roleGuard "feeClaimer") =
      .ok (.bool (decide (roleAllowed evm' ⟨11⟩))) := by
  exact evalRoleGuard evm' "feeClaimer" ⟨11⟩ rfl
    (by simp [claimFeeAliasFrame, claimFeeAfterTouchFrame, resumeAfterInternalCall,
      claimFeeExternalFrame, calldataFrame, marketAmountAccountArguments, collapseReturns]) rfl rfl

theorem claimFeeAlias_get (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) :
    let frame := claimFeeAliasFrame evm m amount receiver
    frame.contract = contract ∧ frame.locals.get? "amount" = some (.int amount.toNat) ∧
      frame.locals.get? "_marketState" = some (.storageRef (marketStateRef m.id) marketStateType) := by
  simp [claimFeeAliasFrame, claimFeeAfterTouchFrame, resumeAfterInternalCall,
    claimFeeExternalFrame, calldataFrame, marketAmountAccountArguments, collapseReturns,
    Std.HashMap.getElem_insert]

end Benchmarks.Midnight
