import Benchmarks.Midnight.RepayDecode
import Benchmarks.Midnight.TouchMarketSource
import Benchmarks.Midnight.Authorization

variable {fork : Ethereum.Fork}

/-! Repayment locals, source authorization, and market initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

structure RepaySourceFrame (frame : Frame) (m : MarketData) (id user units : UInt256)
    (callback : AccountAddress) (data : ByteArray) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  idValue : frame.locals.get? "id" = some (wordBytes32Value id)
  userValue : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat))
  units : frame.locals.get? "units" = some (.int units.toNat)
  callback : frame.locals.get? "callback" = some (.address callback)
  data : frame.locals.get? "data" = some (.bytes data)
  position : frame.locals.get? "position" = none
  marketState : frame.locals.get? "marketState" = none

theorem RepaySourceFrame.insert {frame : Frame} {m : MarketData} {id user units : UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (h : RepaySourceFrame frame m id user units callback data) (name : Ident) (value : Value)
    (hn : name ∉ ["market", "id", "onBehalf", "units", "callback", "data", "position", "marketState"]) :
    RepaySourceFrame { frame with locals := frame.locals.insert name value }
      m id user units callback data := by
  rcases h with ⟨hc, hm, hi, hu, hnits, hcb, hd, hp, hs⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

def repayExternalFrame (origin : State) (m : MarketData) (user units : UInt256)
    (callback : AccountAddress) (data : ByteArray) : Frame :=
  calldataFrame contract (repayArguments m units (AccountAddress.ofNat user.toNat) callback data)
    ∅ origin

def repayAfterTouchFrame (origin : State) (m : MarketData) (user units : UInt256)
    (callback : AccountAddress) (data : ByteArray) : Frame :=
  resumeAfterInternalCall (repayExternalFrame origin m user units callback data) "id"
    (some [wordBytes32Value m.id])

theorem repayAfterTouchFrame_spec (origin : State) (m : MarketData) (user units : UInt256)
    (callback : AccountAddress) (data : ByteArray) :
    RepaySourceFrame (repayAfterTouchFrame origin m user units callback data)
      m m.id user units callback data := by
  constructor <;>
    simp [repayAfterTouchFrame, resumeAfterInternalCall, collapseReturns, repayExternalFrame,
      calldataFrame, repayArguments, repayRawArguments, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]

theorem repayAuthEval (origin : State) (m : MarketData) (user units : UInt256)
    (callback : AccountAddress) (data : ByteArray) (hcanon : user.toNat < EVM.addressModulus) :
    evalExpr? config (repayExternalFrame origin m user units callback data) origin onBehalfGuard =
      .ok (.bool (decide (onBehalfAllowed origin user))) := by
  apply evalOnBehalfGuard origin user hcanon rfl
  · simp [repayExternalFrame, calldataFrame, repayArguments, repayRawArguments]
  · simp [repayExternalFrame, calldataFrame, repayArguments, repayRawArguments,
      Std.HashMap.getElem_insert]

theorem repayTouchArgs (origin : State) (m : MarketData) (user units : UInt256)
    (callback : AccountAddress) (data : ByteArray) :
    evalExprs? config (repayExternalFrame origin m user units callback data) origin [.var "market"] =
      .ok [Model.marketValue m.value] := by
  simp [evalExprs?, evalExpr?, repayExternalFrame, calldataFrame, repayArguments, repayRawArguments,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert]

theorem repayAfterAuthSource {origin : State} {m : MarketData} {user units : UInt256}
    {callback : AccountAddress} {data : ByteArray} {result : ExecResult}
    (hcanon : user.toNat < EVM.addressModulus) (hwv : origin.executionEnv.weiValue = ⟨0⟩)
    (hlimit : origin.executionEnv.calldata.size < calldataLimit) (hauth : onBehalfAllowed origin user)
    (htail : ExecBlock fork config (repayExternalFrame origin m user units callback data) origin
      (repayTransition.body.drop 4) result) :
    ExecBlock fork config
      { contract := contract
        locals := repayArguments m units (AccountAddress.ofNat user.toNat) callback data
        immutables := ∅ } origin repayTransition.body result := by
  apply guardedBodyBlock hwv hlimit
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  exact (repayAuthEval origin m user units callback data hcanon).trans
    (by rw [decide_eq_true hauth])

theorem repayAfterTouchSource {origin evm : State} {m : MarketData} {user units : UInt256}
    {callback : AccountAddress} {data : ByteArray} {callee : Frame} {result : ExecResult}
    (htouch : ExecFuncBody fork config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
      (.returned callee evm (some [wordBytes32Value m.id])))
    (htail : ExecBlock fork config (repayAfterTouchFrame origin m user units callback data) evm
      (repayTransition.body.drop 5) result) :
    ExecBlock fork config (repayExternalFrame origin m user units callback data) origin
      (repayTransition.body.drop 4) result :=
  ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments m) (repayTouchArgs origin m user units callback data)
    rfl rfl htouch) htail

end Benchmarks.Midnight
