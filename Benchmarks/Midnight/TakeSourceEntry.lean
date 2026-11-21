import Benchmarks.Midnight.TakeSourceFrame
import Benchmarks.Midnight.CallerAuthorization

/-! Take's source authorization and nested market initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeExternalFrame (origin : State) (offer : OfferData) (ratifierData : ByteArray)
    (units taker : UInt256) (receiver callback : AccountAddress) (data : ByteArray) : Frame :=
  calldataFrame contract
    (takeArguments offer ratifierData units (AccountAddress.ofNat taker.toNat) receiver callback data)
    ∅ origin

def takeAfterTouchFrame (origin : State) (offer : OfferData) (ratifierData : ByteArray)
    (units taker : UInt256) (receiver callback : AccountAddress) (data : ByteArray) : Frame :=
  resumeAfterInternalCall
    (takeExternalFrame origin offer ratifierData units taker receiver callback data) "id"
    (some [wordBytes32Value offer.market.id])

theorem takeAfterTouchFrame_spec (origin : State) (offer : OfferData) (ratifierData : ByteArray)
    (units taker : UInt256) (receiver callback : AccountAddress) (data : ByteArray) :
    TakeSourceFrame (takeAfterTouchFrame origin offer ratifierData units taker receiver callback data)
      offer offer.market.id units taker receiver callback ratifierData data := by
  constructor <;>
    simp [takeAfterTouchFrame, resumeAfterInternalCall, collapseReturns, takeExternalFrame,
      calldataFrame, takeArguments, takeRawArguments, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]

theorem takeAuthEval (origin : State) (offer : OfferData) (ratifierData : ByteArray)
    (units taker : UInt256) (receiver callback : AccountAddress) (data : ByteArray)
    (hcanon : taker.toNat < EVM.addressModulus) :
    evalExpr? config (takeExternalFrame origin offer ratifierData units taker receiver callback data)
      origin (callerOrDelegateGuard (.var "taker")) =
      .ok (.bool (decide (onBehalfAllowed origin taker))) := by
  apply evalCallerOrDelegate origin taker (.var "taker") hcanon rfl
  · simp [takeExternalFrame, calldataFrame, takeArguments, takeRawArguments]
  · simp [evalExpr?, takeExternalFrame, calldataFrame, takeArguments, takeRawArguments,
      Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem takeTouchArgs (origin : State) (offer : OfferData) (ratifierData : ByteArray)
    (units taker : UInt256) (receiver callback : AccountAddress) (data : ByteArray) :
    evalExprs? config (takeExternalFrame origin offer ratifierData units taker receiver callback data)
      origin [.field (.var "offer") "market"] = .ok [Model.marketValue offer.market.value] := by
  have ho : (takeExternalFrame origin offer ratifierData units taker receiver callback data).locals.get?
      "offer" = some (Model.offerValue offer.value) := by
    simp [takeExternalFrame, calldataFrame, takeArguments, takeRawArguments,
      Std.HashMap.getElem_insert]
  simp only [evalExprs?, evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem takeAfterAuthSource {origin : State} {offer : OfferData} {ratifierData : ByteArray}
    {units taker : UInt256} {receiver callback : AccountAddress} {data : ByteArray}
    {result : ExecResult} (hcanon : taker.toNat < EVM.addressModulus)
    (hwv : origin.executionEnv.weiValue = ⟨0⟩)
    (hlimit : origin.executionEnv.calldata.size < calldataLimit) (hauth : onBehalfAllowed origin taker)
    (htail : ExecBlock config
      (takeExternalFrame origin offer ratifierData units taker receiver callback data) origin
      (takeTransition.body.drop 4) result) :
    ExecBlock config { contract := contract, locals := (takeArguments offer ratifierData units
      (AccountAddress.ofNat taker.toNat) receiver callback data), immutables := ∅ }
      origin takeTransition.body result := by
  apply guardedBodyBlock hwv hlimit
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  exact (takeAuthEval origin offer ratifierData units taker receiver callback data hcanon).trans
    (by rw [decide_eq_true hauth])

theorem takeAfterTouchSource {origin evm : State} {offer : OfferData} {ratifierData : ByteArray}
    {units taker : UInt256} {receiver callback : AccountAddress} {data : ByteArray}
    {callee : Frame} {result : ExecResult}
    (htouch : ExecFuncBody config (touchMarketCallFrame ∅ offer.market) origin touchMarketFunction.body
      (.returned callee evm (some [wordBytes32Value offer.market.id])))
    (htail : ExecBlock config
      (takeAfterTouchFrame origin offer ratifierData units taker receiver callback data) evm
      (takeTransition.body.drop 5) result) :
    ExecBlock config (takeExternalFrame origin offer ratifierData units taker receiver callback data)
      origin (takeTransition.body.drop 4) result :=
  ExecBlock.consNormal (internalCallFunctionReturn (callee := touchMarketFunction)
    (locals := touchMarketArguments offer.market)
    (takeTouchArgs origin offer ratifierData units taker receiver callback data) rfl rfl htouch) htail

end Benchmarks.Midnight
