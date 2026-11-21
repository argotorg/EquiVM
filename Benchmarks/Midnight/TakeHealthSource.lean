import Benchmarks.Midnight.TakeReturn
import Benchmarks.Midnight.HealthSource
import Benchmarks.Midnight.OfferSourceValues

/-! The optional final health check and its returned Boolean in the take frame. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeHealthArgs : List Expr :=
  [.field (.var "offer") "market", .var "id", .var "seller"]

def takeHealthCondition : Expr := .unary .not (.var "locked")

def takeHealthStmt : Stmt := .internalCall "isHealthy_body" takeHealthArgs "healthy"

def takeHealthFrame (frame : Frame) (value : Bool) : Frame :=
  resumeAfterInternalCall frame "healthy" (some [.bool value])

theorem takeHealth_shape : takeTransition.body.drop 73 =
    .ite takeHealthCondition [takeHealthStmt, .require (.var "healthy")] [] ::
      [takeTransition.body[74]!] := by decide +kernel

theorem takeHealthCondition_eval {frame : Frame} {evm : State} {locked : UInt256}
    (hw : frame.locals.get? "locked" = some (wordToElem .bool locked)) :
    evalExpr? config frame evm takeHealthCondition = .ok (.bool (decide (locked = ⟨0⟩))) := by
  simp only [takeHealthCondition, evalExpr?, hw, EvalResult.ofOption, EvalResult.bind,
    bind, wordToElemBool, evalUnaryOp?, Bool.not_not]

theorem takeHealthArgs_eval {frame : Frame} {evm : State} {offer : OfferData} {id seller : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hs : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat))) :
    evalExprs? config frame evm takeHealthArgs =
      .ok [Model.marketValue offer.market.value, wordBytes32Value id,
        .address (AccountAddress.ofNat seller.toNat)] := by
  simp only [takeHealthArgs, evalExprs?, evalOfferMarket ho, evalExpr?, hi, hs,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem takeHealthGuard (frame : Frame) (evm : State) (value : Bool) :
    evalExpr? config (takeHealthFrame frame value) evm (.var "healthy") = .ok (.bool value) := by
  simp only [evalExpr?, takeHealthFrame, resumeAfterInternalCall, collapseReturns,
    store_get_self, EvalResult.ofOption]

end Benchmarks.Midnight
