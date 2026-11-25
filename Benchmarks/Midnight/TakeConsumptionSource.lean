import Benchmarks.Midnight.TakeConsumptionStep

variable {fork : Ethereum.Fork}

/-! Source execution through the consumed counter's checked increment and cap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeConsumedIncrementExpr (offer : OfferData) : Expr :=
  if offer.maxAssets = ⟨0⟩ then .var "units" else takeConsumedAssetExpr

def takeConsumedCapExpr (offer : OfferData) : Expr :=
  .field (.var "offer") (if offer.maxAssets = ⟨0⟩ then "maxUnits" else "maxAssets")

def takeConsumptionInit (frame : Frame) : Frame := wordLocal frame "newConsumed" ⟨0⟩

def takeConsumptionFrame (frame : Frame) (old : UInt256) (offer : OfferData)
    (units bought sold : UInt256) : Frame :=
  wordLocal (takeConsumptionInit frame) "newConsumed"
    (old + takeConsumedDelta offer units bought sold)

def takeConsumptionStmt : Stmt :=
  .ite (.binary .gt (.field (.var "offer") "maxAssets") (.intLit 0))
    (takeConsumptionStep takeConsumedAssetExpr (.field (.var "offer") "maxAssets"))
    (takeConsumptionStep (.var "units") (.field (.var "offer") "maxUnits"))

theorem takeConsumption_shape : takeTransition.body.drop 25 =
    .letDecl "newConsumed" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0) ::
    takeConsumptionStmt :: takeTransition.body.drop 27 := rfl

theorem evalTakeConsumedIncrement {frame : Frame} {evm : State} {offer : OfferData}
    {units bought sold : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat)) :
    evalExpr? config frame evm (takeConsumedIncrementExpr offer) =
      .ok (.int (takeConsumedDelta offer units bought sold).toNat) := by
  by_cases hz : offer.maxAssets = ⟨0⟩
  · simpa only [takeConsumedIncrementExpr, takeConsumedDelta, if_pos hz] using evalWordLocal hu
  · simpa only [takeConsumedIncrementExpr, takeConsumedDelta, if_neg hz] using
      evalTakeConsumedAsset ho hb hs

theorem evalTakeConsumedLimit {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm (takeConsumedCapExpr offer) =
      .ok (.int (takeConsumedCap offer).toNat) := by
  by_cases hz : offer.maxAssets = ⟨0⟩
  · simpa only [takeConsumedCapExpr, takeConsumedCap, if_pos hz] using evalOfferMaxUnits ho
  · simpa only [takeConsumedCapExpr, takeConsumedCap, if_neg hz] using evalOfferMaxAssets ho

theorem takeConsumptionStmtSource {frame : Frame} {evm : State} {offer : OfferData}
    {result : ExecResult}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hx : ExecBlock fork config frame evm
      (takeConsumptionStep (takeConsumedIncrementExpr offer) (takeConsumedCapExpr offer)) result) :
    ExecStmt fork config frame evm takeConsumptionStmt result := by
  have he := evalTakeConsumedMode (cfg := config) (evm := evm) ho
  by_cases hz : offer.maxAssets = ⟨0⟩
  · apply ExecStmt.iteFalse (by simpa only [hz, decide_true, Bool.not_true] using he)
    simpa only [takeConsumedIncrementExpr, takeConsumedCapExpr, if_pos hz] using hx
  · apply ExecStmt.iteTrue (by simpa only [hz, decide_false, Bool.not_false] using he)
    simpa only [takeConsumedIncrementExpr, takeConsumedCapExpr, if_neg hz] using hx

theorem takeConsumptionSource {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker bought sold : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hsafe : TakeConsumptionSafe (takeConsumedStored evm offer) offer units bought sold) :
    ABlock fork config evm frame (takeTransition.body.drop 25)
      (takeConsumptionFrame frame (takeConsumedStored evm offer) offer units bought sold)
      (takeTransition.body.drop 27) := by
  have hf0 : TakeSourceFrame (takeConsumptionInit frame) offer id units taker receiver callback
      ratifierData data := hf.insert "newConsumed" (.int 0) (by decide)
  have hb0 : (takeConsumptionInit frame).locals.get? "buyerAssets" =
      some (.int bought.toNat) := (store_get_ne _ _ (by decide)).trans hb
  have hs0 : (takeConsumptionInit frame).locals.get? "sellerAssets" =
      some (.int sold.toNat) := (store_get_ne _ _ (by decide)).trans hs
  have hstep := takeConsumptionStepSource (fork := fork) (evm := evm) (wordLocal_get ..)
    (evalTakeConsumed hf0.contract hf0.consumed hf0.offerValue)
    (evalTakeConsumedIncrement hf0.offerValue hf0.units hb0 hs0)
    (evalTakeConsumedLimit ((store_get_ne _ _ (by decide)).trans hf0.offerValue)) hsafe
  rw [takeConsumption_shape]
  exact ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl))
    (ExecBlock.consNormal (takeConsumptionStmtSource hf0.offerValue hstep) h)⟩

theorem takeConsumptionSourceRevert {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker bought sold : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hbad : ¬ TakeConsumptionSafe (takeConsumedStored evm offer) offer units bought sold) :
    ExecBlock fork config frame evm (takeTransition.body.drop 25) .reverted := by
  have hf0 : TakeSourceFrame (takeConsumptionInit frame) offer id units taker receiver callback
      ratifierData data := hf.insert "newConsumed" (.int 0) (by decide)
  have hb0 : (takeConsumptionInit frame).locals.get? "buyerAssets" =
      some (.int bought.toNat) := (store_get_ne _ _ (by decide)).trans hb
  have hs0 : (takeConsumptionInit frame).locals.get? "sellerAssets" =
      some (.int sold.toNat) := (store_get_ne _ _ (by decide)).trans hs
  have hstep := takeConsumptionStepRevert (fork := fork) (evm := evm) (wordLocal_get ..)
    (evalTakeConsumed hf0.contract hf0.consumed hf0.offerValue)
    (evalTakeConsumedIncrement hf0.offerValue hf0.units hb0 hs0)
    (evalTakeConsumedLimit ((store_get_ne _ _ (by decide)).trans hf0.offerValue)) hbad
  rw [takeConsumption_shape]
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl))
    (ExecBlock.consRevert (takeConsumptionStmtSource hf0.offerValue hstep))

theorem TakeSourceFrame.consumption {frame : Frame} {offer : OfferData}
    {old id units taker bought sold : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeConsumptionFrame frame old offer units bought sold) offer id units taker
      receiver callback ratifierData data :=
  (hf.insert "newConsumed" (.int 0) (by decide)).insert "newConsumed"
    (.int (old + takeConsumedDelta offer units bought sold).toNat) (by decide)

end Benchmarks.Midnight
