import Benchmarks.Midnight.TakeOfferGuardsSource

variable {fork : Ethereum.Fork}

/-! Maturity and reduce-only restrictions on the computed trade deltas. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def TakeMaturityAllowed (I : ExecutionEnv) (offer : OfferData) (debt : UInt256) : Prop :=
  (UInt256.ofNat I.header.timestamp).toNat ≤ offer.market.maturity.toNat ∨ debt = ⟨0⟩

instance (I : ExecutionEnv) (offer : OfferData) (debt : UInt256) :
    Decidable (TakeMaturityAllowed I offer debt) := inferInstanceAs (Decidable (_ ∨ _))

def takeReduceDelta (offer : OfferData) (increase debt : UInt256) : UInt256 :=
  if offer.buy = ⟨0⟩ then debt else increase

def TakeReduceAllowed (offer : OfferData) (increase debt : UInt256) : Prop :=
  offer.reduceOnly = ⟨0⟩ ∨ takeReduceDelta offer increase debt = ⟨0⟩

instance (offer : OfferData) (increase debt : UInt256) :
    Decidable (TakeReduceAllowed offer increase debt) := inferInstanceAs (Decidable (_ ∨ _))

def takeMaturityGuard : Expr :=
  .binary .or (.binary .le (.env .timestamp) (.field (.field (.var "offer") "market") "maturity"))
    (.binary .eq (.var "sellerDebtIncrease") (.intLit 0))

def takeReduceGuard : Expr :=
  .binary .or (.unary .not (.field (.var "offer") "reduceOnly"))
    (.ite (.field (.var "offer") "buy")
      (.binary .eq (.var "buyerCreditIncrease") (.intLit 0))
      (.binary .eq (.var "sellerDebtIncrease") (.intLit 0)))

theorem takeTradeGuards_shape : takeTransition.body.drop 42 =
    .require takeMaturityGuard :: .require takeReduceGuard :: takeTransition.body.drop 44 := rfl

-- LIBRARY CANDIDATE: compare a word-valued local with zero in the source semantics.
theorem evalLocalWordEqZero {cfg : Config} {frame : Frame} {evm : State}
    {name : Ident} {word : UInt256}
    (hw : frame.locals.get? name = some (.int word.toNat)) :
    evalExpr? cfg frame evm (.binary .eq (.var name) (.intLit 0)) =
      .ok (.bool (decide (word = ⟨0⟩))) := by
  have he : word.toNat = 0 ↔ word = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, fun h ↦ congrArg UInt256.toNat h⟩
  simp only [evalExpr?, hw, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?]
  simp only [Reasoning.VyperDispatch.value_int_beq, Int.natCast_eq_zero, he]

theorem evalTakeMaturityGuard {frame : Frame} {evm : State} {offer : OfferData} {debt : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat)) :
    evalExpr? config frame evm takeMaturityGuard =
      .ok (.bool (decide (TakeMaturityAllowed evm.executionEnv offer debt))) := by
  have hm : evalExpr? config frame evm (.field (.field (.var "offer") "market") "maturity") =
      .ok (.int offer.market.maturity.toNat) := by
    simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  have ht : evalExpr? config frame evm
      (.binary .le (.env .timestamp) (.field (.field (.var "offer") "market") "maturity")) =
      .ok (.bool (decide ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        offer.market.maturity.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hm]
    simp only [evalExpr?, envValue, bind, pure, EvalResult.bind, evalBinaryOp?,
      Int.ofNat_eq_natCast, Int.ofNat_le]
  rw [takeMaturityGuard, evalExpr?, ht]
  by_cases hb : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤ offer.market.maturity.toNat
  · simp only [TakeMaturityAllowed, hb, decide_true, true_or, bind, pure, EvalResult.bind]
  · simp only [TakeMaturityAllowed, hb, decide_false, false_or, bind, pure, EvalResult.bind,
      evalLocalWordEqZero hd]

theorem evalTakeReduceDelta {frame : Frame} {evm : State} {offer : OfferData}
    {increase debt : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat)) :
    evalExpr? config frame evm
      (.ite (.field (.var "offer") "buy")
        (.binary .eq (.var "buyerCreditIncrease") (.intLit 0))
        (.binary .eq (.var "sellerDebtIncrease") (.intLit 0))) =
      .ok (.bool (decide (takeReduceDelta offer increase debt = ⟨0⟩))) := by
  rw [evalExpr?, evalOfferBuy ho]
  by_cases hz : offer.buy = ⟨0⟩
  · simp only [wordToElemBool, hz, decide_true, Bool.not_true, bind, EvalResult.bind,
      takeReduceDelta, if_true, evalLocalWordEqZero hd]
  · simp only [wordToElemBool, hz, decide_false, Bool.not_false, bind, EvalResult.bind,
      takeReduceDelta, if_false, evalLocalWordEqZero hi]

theorem evalTakeReduceGuard {frame : Frame} {evm : State} {offer : OfferData}
    {increase debt : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat)) :
    evalExpr? config frame evm takeReduceGuard =
      .ok (.bool (decide (TakeReduceAllowed offer increase debt))) := by
  have hn : evalExpr? config frame evm (.unary .not (.field (.var "offer") "reduceOnly")) =
      .ok (.bool (decide (offer.reduceOnly = ⟨0⟩))) := by
    rw [evalExpr?, evalOfferReduceOnly ho]
    simp only [wordToElemBool, bind, EvalResult.bind, evalUnaryOp?, Bool.not_not,
      EvalResult.ofOption]
  rw [takeReduceGuard, evalExpr?, hn]
  by_cases hz : offer.reduceOnly = ⟨0⟩
  · simp only [TakeReduceAllowed, hz, decide_true, true_or, bind, pure, EvalResult.bind]
  · simp only [TakeReduceAllowed, hz, decide_false, false_or, bind, pure, EvalResult.bind,
      evalTakeReduceDelta ho hi hd]

theorem takeTradeGuardsSource {frame : Frame} {evm : State} {offer : OfferData}
    {increase debt : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat))
    (hm : TakeMaturityAllowed evm.executionEnv offer debt)
    (hr : TakeReduceAllowed offer increase debt) :
    ABlock fork config evm frame (takeTransition.body.drop 42) frame (takeTransition.body.drop 44) := by
  rw [takeTradeGuards_shape]
  exact ⟨fun h ↦ ExecBlock.consNormal
    (ExecStmt.requireTrue ((evalTakeMaturityGuard ho hd).trans (by rw [decide_eq_true hm])))
    (ExecBlock.consNormal
      (ExecStmt.requireTrue ((evalTakeReduceGuard ho hi hd).trans (by rw [decide_eq_true hr]))) h)⟩

theorem takeTradeGuardsSourceRevert {frame : Frame} {evm : State} {offer : OfferData}
    {increase debt : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat))
    (hbad : ¬ (TakeMaturityAllowed evm.executionEnv offer debt ∧
      TakeReduceAllowed offer increase debt)) :
    ExecBlock fork config frame evm (takeTransition.body.drop 42) .reverted := by
  rw [takeTradeGuards_shape]
  by_cases hm : TakeMaturityAllowed evm.executionEnv offer debt
  · exact ExecBlock.consNormal
      (ExecStmt.requireTrue ((evalTakeMaturityGuard ho hd).trans (by rw [decide_eq_true hm])))
      (ExecBlock.consRevert (ExecStmt.requireFalse ((evalTakeReduceGuard ho hi hd).trans
        (by rw [decide_eq_false (fun h ↦ hbad ⟨hm, h⟩)]))))
  · exact ExecBlock.consRevert
      (ExecStmt.requireFalse ((evalTakeMaturityGuard ho hd).trans (by rw [decide_eq_false hm])))

end Benchmarks.Midnight
