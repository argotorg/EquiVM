import Benchmarks.Midnight.LiquidateSourceFrame
import Benchmarks.Midnight.TouchMarketSource

/-! Liquidation's source entry and its market and position storage aliases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateExternalFrame (origin : State) (m : MarketData)
    (index seized repaid borrower mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) : Frame :=
  calldataFrame contract (liquidateArguments m index seized repaid
    (AccountAddress.ofNat borrower.toNat) mode receiver callback data) ∅ origin

def liquidateAfterTouchFrame (origin : State) (m : MarketData)
    (index seized repaid borrower mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) : Frame :=
  resumeAfterInternalCall
    (liquidateExternalFrame origin m index seized repaid borrower mode receiver callback data)
    "id" (some [wordBytes32Value m.id])

def liquidateReadyFrame (origin : State) (m : MarketData)
    (index seized repaid borrower mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) : Frame :=
  let frame := liquidateAfterTouchFrame origin m index seized repaid borrower mode
    receiver callback data
  { frame with locals := (
      (frame.locals.insert "_marketState" (.storageRef (marketStateRef m.id) marketStateType)).insert
        "_position" (.storageRef (positionRef m.id borrower) positionType)) }

theorem liquidateReadyFrame_spec (origin : State) (m : MarketData)
    (index seized repaid borrower mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) :
    LiquidateSourceFrame
      (liquidateReadyFrame origin m index seized repaid borrower mode receiver callback data)
      m m.id index seized repaid borrower mode receiver callback data := by
  constructor <;>
    simp [liquidateReadyFrame, liquidateAfterTouchFrame, resumeAfterInternalCall, collapseReturns,
      liquidateExternalFrame, calldataFrame, liquidateArguments, liquidateRawArguments,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem liquidateTouchArgs (origin : State) (m : MarketData)
    (index seized repaid borrower mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) :
    evalExprs? config
      (liquidateExternalFrame origin m index seized repaid borrower mode receiver callback data)
      origin [.var "market"] = .ok [Model.marketValue m.value] := by
  simp [evalExprs?, evalExpr?, liquidateExternalFrame, calldataFrame, liquidateArguments,
    liquidateRawArguments, EvalResult.ofOption, EvalResult.bind, bind, pure,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

set_option maxHeartbeats 800000 in
theorem liquidateReadyPrefix (origin evm : State) (m : MarketData)
    (index seized repaid borrower mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) :
    ABlock config evm
      (liquidateAfterTouchFrame origin m index seized repaid borrower mode receiver callback data)
      (liquidateTransition.body.drop 4)
      (liquidateReadyFrame origin m index seized repaid borrower mode receiver callback data)
      (liquidateTransition.body.drop 6) := by
  let frame := liquidateAfterTouchFrame origin m index seized repaid borrower mode
    receiver callback data
  let first := { frame with locals := (
    frame.locals.insert "_marketState" (.storageRef (marketStateRef m.id) marketStateType)) }
  refine ⟨fun h ↦ ExecBlock.consNormal (stele' := first) (ExecStmt.letStorage ?_)
    (ExecBlock.consNormal (ExecStmt.letStorage ?_) h)⟩
  · apply resolveBytes32Mapping
    · simp [liquidateAfterTouchFrame, resumeAfterInternalCall, collapseReturns,
        liquidateExternalFrame, calldataFrame, liquidateArguments, liquidateRawArguments]
    · exact store_get_self ..
    · rfl
  · apply resolvePositionBorrower rfl <;>
      simp [first, frame, liquidateAfterTouchFrame, resumeAfterInternalCall, collapseReturns,
        liquidateExternalFrame, calldataFrame, liquidateArguments, liquidateRawArguments,
        Std.HashMap.getElem_insert]

theorem liquidateAfterTouchSource {origin evm : State} {m : MarketData}
    {index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray} {callee : Frame} {result : ExecResult}
    (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
      (.returned callee evm (some [wordBytes32Value m.id])))
    (htail : ExecBlock config
      (liquidateReadyFrame origin m index seized repaid borrower mode receiver callback data) evm
      (liquidateTransition.body.drop 6) result) :
    ExecBlock config
      (liquidateExternalFrame origin m index seized repaid borrower mode receiver callback data)
      origin (liquidateTransition.body.drop 3) result := by
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m)
    (liquidateTouchArgs origin m index seized repaid borrower mode receiver callback data)
    rfl rfl htouch)
  exact (liquidateReadyPrefix origin evm m index seized repaid borrower mode receiver callback data).run
    htail

end Benchmarks.Midnight
