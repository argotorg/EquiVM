import Benchmarks.Midnight.TakeGateABI
import Benchmarks.Midnight.TakeTradeGuardsSource

/-! Source control flow for the two optional entry-gate calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def TakeGateKind.userName : TakeGateKind → Ident
  | .credit => "buyer"
  | .debt => "seller"

def TakeGateKind.deltaName : TakeGateKind → Ident
  | .credit => "buyerCreditIncrease"
  | .debt => "sellerDebtIncrease"

def takeGateReceiver : Expr := .field (.field (.var "offer") "market") "enterGate"

def TakeGateNeeded (offer : OfferData) (delta : UInt256) : Prop :=
  offer.market.enterGate ≠ 0 ∧ delta ≠ ⟨0⟩

instance (offer : OfferData) (delta : UInt256) : Decidable (TakeGateNeeded offer delta) :=
  inferInstanceAs (Decidable (_ ∧ _))

def takeGateCondition (kind : TakeGateKind) : Expr :=
  .binary .and (.binary .ne takeGateReceiver (.cast (.intLit 0) (.elem .address)))
    (.binary .ne (.var kind.deltaName) (.intLit 0))

def takeGateCall (kind : TakeGateKind) : Stmt :=
  .externalCall takeGateReceiver kind.name (.intLit 0) [.var kind.userName] "allowed" false

def takeGateStmt (kind : TakeGateKind) : Stmt :=
  .ite (takeGateCondition kind) [takeGateCall kind, .require (.var "allowed")] []

def takeGateAllowedFrame (frame : Frame) (word : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "allowed" (wordToElem .bool word) }

theorem takeGates_shape : takeTransition.body.drop 44 =
    takeGateStmt .credit :: takeGateStmt .debt :: takeTransition.body.drop 46 := rfl

theorem evalTakeGateReceiver {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm takeGateReceiver = .ok (.address offer.market.enterGate) := by
  simp only [takeGateReceiver, evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalTakeGateCondition {frame : Frame} {evm : State} {offer : OfferData} {delta : UInt256}
    (kind : TakeGateKind)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? kind.deltaName = some (.int delta.toNat)) :
    evalExpr? config frame evm (takeGateCondition kind) =
      .ok (.bool (decide (TakeGateNeeded offer delta))) := by
  have hg : evalExpr? config frame evm
      (.binary .ne takeGateReceiver (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (offer.market.enterGate ≠ 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalTakeGateReceiver ho]
    simp only [evalExpr?, castValue?, EvalResult.ofOption, bind, pure, EvalResult.bind]
    change EvalResult.ok (Value.bool (!(Value.address offer.market.enterGate == .address 0))) = _
    simp only [Reasoning.VyperDispatch.value_address_beq, decide_not]
  have he : delta.toNat = 0 ↔ delta = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, fun h ↦ congrArg UInt256.toNat h⟩
  have hd' : evalExpr? config frame evm (.binary .ne (.var kind.deltaName) (.intLit 0)) =
      .ok (.bool (decide (delta ≠ ⟨0⟩))) := by
    simp only [evalExpr?, hd, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
      Reasoning.VyperDispatch.value_int_beq, Int.natCast_eq_zero, he, decide_not]
  rw [takeGateCondition, evalExpr?, hg]
  by_cases hn : offer.market.enterGate ≠ 0
  · have hp : TakeGateNeeded offer delta ↔ delta ≠ ⟨0⟩ :=
      ⟨And.right, fun h ↦ ⟨hn, h⟩⟩
    simp only [decide_eq_true hn, propext hp, bind, pure, EvalResult.bind, hd']
  · have hp : ¬ TakeGateNeeded offer delta := fun h ↦ hn h.1
    simp only [decide_eq_false hn, decide_eq_false hp, bind, pure, EvalResult.bind]

theorem takeGateSkipped {frame : Frame} {evm : State} {offer : OfferData} {delta : UInt256}
    (kind : TakeGateKind)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? kind.deltaName = some (.int delta.toNat))
    (hn : ¬ TakeGateNeeded offer delta) :
    ExecStmt config frame evm (takeGateStmt kind) (.ok frame evm) :=
  ExecStmt.iteFalse ((evalTakeGateCondition kind ho hd).trans (by rw [decide_eq_false hn]))
    ExecBlock.nil

theorem takeGateFailed {frame : Frame} {evm : State} {offer : OfferData} {delta : UInt256}
    (kind : TakeGateKind)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? kind.deltaName = some (.int delta.toNat))
    (hn : TakeGateNeeded offer delta)
    (hcall : ExecStmt config frame evm (takeGateCall kind) .reverted) :
    ExecStmt config frame evm (takeGateStmt kind) .reverted :=
  ExecStmt.iteTrue ((evalTakeGateCondition kind ho hd).trans (by rw [decide_eq_true hn]))
    (ExecBlock.consRevert hcall)

theorem takeGateDenied {frame : Frame} {evm evm' : State} {offer : OfferData} {delta : UInt256}
    (kind : TakeGateKind)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? kind.deltaName = some (.int delta.toNat))
    (hn : TakeGateNeeded offer delta)
    (hcall : ExecStmt config frame evm (takeGateCall kind)
      (.ok (takeGateAllowedFrame frame ⟨0⟩) evm')) :
    ExecStmt config frame evm (takeGateStmt kind) .reverted := by
  apply ExecStmt.iteTrue ((evalTakeGateCondition kind ho hd).trans (by rw [decide_eq_true hn]))
  refine ExecBlock.consNormal hcall (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
  simp only [evalExpr?, takeGateAllowedFrame, store_get_self, EvalResult.ofOption]
  rfl

theorem takeGateAllowed {frame : Frame} {evm evm' : State} {offer : OfferData} {delta : UInt256}
    (kind : TakeGateKind)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? kind.deltaName = some (.int delta.toNat))
    (hn : TakeGateNeeded offer delta)
    (hcall : ExecStmt config frame evm (takeGateCall kind)
      (.ok (takeGateAllowedFrame frame ⟨1⟩) evm')) :
    ExecStmt config frame evm (takeGateStmt kind) (.ok (takeGateAllowedFrame frame ⟨1⟩) evm') := by
  apply ExecStmt.iteTrue ((evalTakeGateCondition kind ho hd).trans (by rw [decide_eq_true hn]))
  refine ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil)
  simp only [evalExpr?, takeGateAllowedFrame, store_get_self, EvalResult.ofOption]
  rfl

theorem TakeSourceFrame.enterGate {frame : Frame} {offer : OfferData} {word : UInt256}
    {id units taker : UInt256} {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeGateAllowedFrame frame word) offer id units taker receiver callback
      ratifierData data := hf.insert "allowed" _ (by decide)

end Benchmarks.Midnight
