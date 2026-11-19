import Benchmarks.Midnight.TakeBuyerUpdateGuard
import Benchmarks.Midnight.TakePositionReadSource
import Benchmarks.Midnight.PositionUpdateCall

/-! Source evaluation of take's short-circuited buyer-update condition. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyerUpdateCondition : Expr :=
  .binary .or (.var "__c9")
    (.binary .gt (.var "units") (.storage { base := "buyerPos", steps := [.field "debt"] }))

def takeBuyerUpdateStmt : Stmt :=
  .ite takeBuyerUpdateCondition
    [.internalCall "_updatePosition" [.field (.var "offer") "market", .var "id", .var "buyer"]
      "__c10"] []

theorem takeBuyerUpdate_shape : takeTransition.body.drop 32 =
    takeBuyerUpdateStmt :: takeTransition.body.drop 33 := rfl

theorem evalTakePositionUpdateArgs {frame : Frame} {evm : State} {offer : OfferData}
    {id user : UInt256} {name : Ident}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hu : frame.locals.get? name = some (.address (AccountAddress.ofNat user.toNat))) :
    evalExprs? config frame evm [.field (.var "offer") "market", .var "id", .var name] =
      .ok [Model.marketValue offer.market.value, wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)] := by
  simp only [evalExprs?, evalOfferMarket ho, evalExpr?, hi, hu, EvalResult.ofOption,
    bind, pure, EvalResult.bind]

theorem evalTakeBuyerUpdateCondition {frame : Frame} {evm : State} {id buyer units : UInt256}
    (hcanon : buyer.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hc : frame.locals.get? "__c9" = some (.bool (hasCreditValue evm id buyer))) :
    evalExpr? config frame evm takeBuyerUpdateCondition =
      .ok (.bool (decide (TakeBuyerNeedsUpdate (positionFieldWord evm id buyer 0)
        (low128 (healthPositionWord evm id buyer)) units))) := by
  have hd : evalExpr? config frame evm (.binary .gt (.var "units")
      (.storage { base := "buyerPos", steps := [.field "debt"] })) =
      .ok (.bool (decide ((low128 (healthPositionWord evm id buyer)).toNat < units.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalWordLocal hu,
      evalNamedPositionDebt hcanon hp]
    simp only [bind, EvalResult.bind, evalBinaryOp?, gt_iff_lt, Int.ofNat_lt]
  have hl : evalExpr? config frame evm (.var "__c9") =
      .ok (.bool (hasCreditValue evm id buyer)) := by
    simp only [evalExpr?, hc, EvalResult.ofOption]
  have hpos : 0 < (positionFieldWord evm id buyer 0).toNat ↔
      positionFieldWord evm id buyer 0 ≠ ⟨0⟩ := by
    constructor
    · intro h he; rw [he] at h; contradiction
    · intro h
      exact Nat.pos_of_ne_zero (fun he ↦ h (uint256_toNat_eq_zero he))
  rw [takeBuyerUpdateCondition, evalExpr?, hl]
  simp only [hasCreditValue, hpos, decide_not]
  by_cases hz : positionFieldWord evm id buyer 0 = ⟨0⟩
  · simp only [TakeBuyerNeedsUpdate, decide_not, hz, decide_true, Bool.not_true, bind,
      EvalResult.bind, hd, ne_eq, not_true_eq_false, false_or, pure]
  · simp only [TakeBuyerNeedsUpdate, decide_not, hz, decide_false, Bool.not_false, bind,
      EvalResult.bind, ne_eq, not_false_eq_true, true_or, decide_true, pure]

end Benchmarks.Midnight
