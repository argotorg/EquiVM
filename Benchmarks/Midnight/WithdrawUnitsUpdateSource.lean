import Benchmarks.Midnight.WithdrawUnitsSourceEntry

/-! Withdrawal's market alias and internal position update, followed by its local bindings. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawUnitsAliasFrame (origin : EVM.State) (m : MarketData) (user units : UInt256)
    (receiver : AccountAddress) : Frame :=
  let frame := withdrawUnitsAfterTouchFrame origin m user units receiver
  { frame with
    locals := frame.locals.insert "_marketState"
      (.storageRef (marketStateRef m.id) marketStateType) }

def withdrawUnitsAfterPositionFrame (origin : EVM.State) (m : MarketData)
    (user units : UInt256) (receiver : AccountAddress) (credit pending fee : UInt256) : Frame :=
  resumeAfterInternalCall (withdrawUnitsAliasFrame origin m user units receiver) "__c1"
    (some [.int credit.toNat, .int pending.toNat, .int fee.toNat])

def withdrawUnitsReadyFrame (origin : EVM.State) (m : MarketData)
    (user units : UInt256) (receiver : AccountAddress) (credit pending fee : UInt256) : Frame :=
  let frame := withdrawUnitsAfterPositionFrame origin m user units receiver credit pending fee
  wordLocal { frame with
    locals := frame.locals.insert "_position"
      (.storageRef (positionRef m.id user) positionType) } "pendingFeeDecrease" ⟨0⟩

theorem withdrawUnitsReady_get (origin : EVM.State) (m : MarketData)
    (user units : UInt256) (receiver : AccountAddress) (credit pending fee : UInt256) :
    WithdrawUnitsSourceFrame (withdrawUnitsReadyFrame origin m user units receiver credit pending fee)
      m m.id user units receiver := by
  constructor <;> simp [withdrawUnitsReadyFrame, withdrawUnitsAfterPositionFrame,
    withdrawUnitsAliasFrame, withdrawUnitsAfterTouchFrame, withdrawUnitsExternalFrame,
    wordLocal, resumeAfterInternalCall, collapseReturns, calldataFrame,
    marketUnitsReceiverArguments, Std.HashMap.getElem_insert]

theorem withdrawUnitsAliasPrefix (origin evm : EVM.State) (m : MarketData)
    (user units : UInt256) (receiver : AccountAddress) :
    ABlock config evm (withdrawUnitsAfterTouchFrame origin m user units receiver)
      (withdrawTransition.body.drop 5) (withdrawUnitsAliasFrame origin m user units receiver)
      (withdrawTransition.body.drop 6) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  apply resolveBytes32Mapping
  · simp [withdrawUnitsAfterTouchFrame, resumeAfterInternalCall, withdrawUnitsExternalFrame,
      calldataFrame, marketUnitsReceiverArguments, collapseReturns]
  · exact store_get_self ..
  · rfl

theorem withdrawUnitsPositionArgs (origin evm : EVM.State) (m : MarketData)
    (user units : UInt256) (receiver : AccountAddress) :
    evalExprs? config (withdrawUnitsAliasFrame origin m user units receiver) evm
      [.var "market", .var "id", .var "onBehalf"] =
      .ok [Model.marketValue m.value, wordBytes32Value m.id,
        .address (AccountAddress.ofNat user.toNat)] := by
  simp [evalExprs?, evalExpr?, withdrawUnitsAliasFrame, withdrawUnitsAfterTouchFrame,
    withdrawUnitsExternalFrame, resumeAfterInternalCall, collapseReturns, calldataFrame,
    marketUnitsReceiverArguments, EvalResult.ofOption, EvalResult.bind, bind, pure,
    Std.HashMap.getElem_insert]

theorem withdrawUnitsReadyPrefix (origin evm : EVM.State) (m : MarketData)
    (user units : UInt256) (receiver : AccountAddress) (credit pending fee : UInt256) :
    ABlock config evm
      (withdrawUnitsAfterPositionFrame origin m user units receiver credit pending fee)
      (withdrawTransition.body.drop 7)
      (withdrawUnitsReadyFrame origin m user units receiver credit pending fee)
      (withdrawTransition.body.drop 9) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_)
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, pure])) h)⟩
  apply resolvePositionAccount "onBehalf" rfl <;>
    simp [withdrawUnitsAfterPositionFrame, withdrawUnitsAliasFrame, withdrawUnitsAfterTouchFrame,
      withdrawUnitsExternalFrame, resumeAfterInternalCall, collapseReturns, calldataFrame,
      marketUnitsReceiverArguments, Std.HashMap.getElem_insert]

theorem withdrawUnitsUpdateReturns {origin evm evm' : EVM.State} {m : MarketData}
    {user units credit pending fee : UInt256} {receiver : AccountAddress} {callee : Frame}
    {result : ExecResult}
    (hbody : ExecFuncBody config (positionViewCallFrame ∅ m m.id user) evm
      positionUpdateFunction.body (.returned callee evm'
        (some [.int credit.toNat, .int pending.toNat, .int fee.toNat])))
    (htail : ExecBlock config (withdrawUnitsReadyFrame origin m user units receiver credit pending fee)
      evm' (withdrawTransition.body.drop 9) result) :
    ExecBlock config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
      (withdrawTransition.body.drop 5) result := by
  apply (withdrawUnitsAliasPrefix origin evm m user units receiver).run
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := positionUpdateFunction)
    (locals := positionViewArguments m m.id user)
    (withdrawUnitsPositionArgs origin evm m user units receiver) rfl rfl hbody)
  exact (withdrawUnitsReadyPrefix origin evm' m user units receiver credit pending fee).run htail

theorem withdrawUnitsUpdateReverts {origin evm : EVM.State} {m : MarketData}
    {user units : UInt256} {receiver : AccountAddress}
    (hbody : ExecFuncBody config (positionViewCallFrame ∅ m m.id user) evm
      positionUpdateFunction.body .reverted) :
    ExecBlock config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
      (withdrawTransition.body.drop 5) .reverted := by
  apply (withdrawUnitsAliasPrefix origin evm m user units receiver).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := positionUpdateFunction)
    (locals := positionViewArguments m m.id user)
    (withdrawUnitsPositionArgs origin evm m user units receiver) rfl rfl hbody)

theorem withdrawUnitsUpdateStatic {origin evm : EVM.State} {m : MarketData}
    {user units : UInt256} {receiver : AccountAddress}
    (hbody : ExecFuncBody config (positionViewCallFrame ∅ m m.id user) evm
      positionUpdateFunction.body .staticViolation) :
    ExecBlock config (withdrawUnitsAfterTouchFrame origin m user units receiver) evm
      (withdrawTransition.body.drop 5) .staticViolation := by
  apply (withdrawUnitsAliasPrefix origin evm m user units receiver).run
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (withdrawUnitsPositionArgs origin evm m user units receiver) rfl rfl hbody)

end Benchmarks.Midnight
