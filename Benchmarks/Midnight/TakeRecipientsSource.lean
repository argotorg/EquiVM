import Benchmarks.Midnight.OfferSourceValues

/-! Callback, payer, and receiver selection after the trade's accounting writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyerCallback (offer : OfferData) (callback : AccountAddress) : AccountAddress :=
  if offer.buy = ⟨0⟩ then callback else offer.callback

def takeSellerCallback (offer : OfferData) (callback : AccountAddress) : AccountAddress :=
  if offer.buy = ⟨0⟩ then offer.callback else callback

def takePayer (offer : OfferData) (callback buyer sender : AccountAddress) : AccountAddress :=
  if takeBuyerCallback offer callback = 0 then
    if offer.buy = ⟨0⟩ then sender else buyer
  else takeBuyerCallback offer callback

def takeReceiver (offer : OfferData) (receiver : AccountAddress) : AccountAddress :=
  if offer.buy = ⟨0⟩ then offer.receiverIfMakerIsSeller else receiver

def takeBuyerCallbackExpr : Expr :=
  .ite (.field (.var "offer") "buy") (.field (.var "offer") "callback") (.var "takerCallback")

def takeSellerCallbackExpr : Expr :=
  .ite (.field (.var "offer") "buy") (.var "takerCallback") (.field (.var "offer") "callback")

def takePayerExpr : Expr :=
  .ite (.binary .ne (.var "buyerCallback") (.cast (.intLit 0) (.elem .address)))
    (.var "buyerCallback") (.ite (.field (.var "offer") "buy") (.var "buyer") (.env .caller))

def takeReceiverExpr : Expr :=
  .ite (.field (.var "offer") "buy") (.var "receiverIfTakerIsSeller")
    (.field (.var "offer") "receiverIfMakerIsSeller")

def takeCallbacksFrame (frame : Frame) (offer : OfferData) (callback : AccountAddress) : Frame :=
  { frame with
    locals := (frame.locals.insert "buyerCallback"
      (.address (takeBuyerCallback offer callback))).insert "sellerCallback"
      (.address (takeSellerCallback offer callback)) }

def takePayerFrame (frame : Frame) (offer : OfferData) (callback buyer sender : AccountAddress) : Frame :=
  { takeCallbacksFrame frame offer callback with
    locals :=
      (takeCallbacksFrame frame offer callback).locals.insert "payer"
      (.address (takePayer offer callback buyer sender)) }

def takeRecipientsFrame (frame : Frame) (offer : OfferData)
    (callback buyer sender receiver : AccountAddress) : Frame :=
  { takePayerFrame frame offer callback buyer sender with
    locals :=
      (takePayerFrame frame offer callback buyer sender).locals.insert "receiver"
      (.address (takeReceiver offer receiver)) }

theorem evalTakeBuyerCallback {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {callback : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "takerCallback" = some (.address callback)) :
    evalExpr? cfg frame evm takeBuyerCallbackExpr =
      .ok (.address (takeBuyerCallback offer callback)) := by
  rw [takeBuyerCallbackExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hz : offer.buy = ⟨0⟩
  · simp only [hz, decide_true, Bool.not_true, takeBuyerCallback, if_true,
      evalExpr?, ht, EvalResult.ofOption]
  · simp only [hz, decide_false, Bool.not_false, takeBuyerCallback, if_false, evalOfferCallback ho]

theorem evalTakeSellerCallback {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {callback : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "takerCallback" = some (.address callback)) :
    evalExpr? cfg frame evm takeSellerCallbackExpr =
      .ok (.address (takeSellerCallback offer callback)) := by
  rw [takeSellerCallbackExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hz : offer.buy = ⟨0⟩
  · simp only [hz, decide_true, Bool.not_true, takeSellerCallback, if_true, evalOfferCallback ho]
  · simp only [hz, decide_false, Bool.not_false, takeSellerCallback, if_false,
      evalExpr?, ht, EvalResult.ofOption]

theorem evalTakePayer {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {callback buyer : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hcb : frame.locals.get? "buyerCallback" = some (.address (takeBuyerCallback offer callback)))
    (hb : frame.locals.get? "buyer" = some (.address buyer)) :
    evalExpr? cfg frame evm takePayerExpr =
      .ok (.address (takePayer offer callback buyer evm.executionEnv.source)) := by
  have hecb : evalExpr? cfg frame evm (.var "buyerCallback") =
      .ok (.address (takeBuyerCallback offer callback)) := by
    simp only [evalExpr?, hcb, EvalResult.ofOption]
  have hzero : evalExpr? cfg frame evm (.cast (.intLit 0) (.elem .address)) =
      .ok (.address 0) := by
    simp only [evalExpr?, castValue?, EvalResult.ofOption, bind, pure, EvalResult.bind]
    rfl
  have hcond : evalExpr? cfg frame evm
      (.binary .ne (.var "buyerCallback") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (takeBuyerCallback offer callback ≠ 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hecb, hzero]
    simp only [bind, EvalResult.bind, evalBinaryOpNeAddress,
      Reasoning.VyperDispatch.value_address_beq, decide_not]
  rw [takePayerExpr, evalExpr?, hcond]
  simp only [bind, EvalResult.bind]
  by_cases hcb0 : takeBuyerCallback offer callback = 0
  · rw [takePayer, if_pos hcb0]
    simp only [hcb0, ne_eq, not_true_eq_false, decide_false]
    rw [evalExpr?, evalOfferBuy ho]
    simp only [wordToElemBool, bind, EvalResult.bind]
    by_cases hb0 : offer.buy = ⟨0⟩
    · simp only [hb0, decide_true, Bool.not_true, if_true, evalExpr?]
      rfl
    · simp only [hb0, decide_false, Bool.not_false, if_false, evalExpr?, hb, EvalResult.ofOption]
  · rw [takePayer, if_neg hcb0]
    simp only [hcb0, ne_eq, not_false_eq_true, decide_true, hecb]

theorem evalTakeReceiver {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {receiver : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hr : frame.locals.get? "receiverIfTakerIsSeller" = some (.address receiver)) :
    evalExpr? cfg frame evm takeReceiverExpr = .ok (.address (takeReceiver offer receiver)) := by
  rw [takeReceiverExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hz : offer.buy = ⟨0⟩
  · simp only [hz, decide_true, Bool.not_true, takeReceiver, if_true,
      evalOfferReceiverIfMakerIsSeller ho]
  · simp only [hz, decide_false, Bool.not_false, takeReceiver, if_false,
      evalExpr?, hr, EvalResult.ofOption]

theorem takeRecipients_shape : takeTransition.body.drop 60 =
    .letDecl "buyerCallback" (some (.elem .address)) takeBuyerCallbackExpr ::
    .letDecl "sellerCallback" (some (.elem .address)) takeSellerCallbackExpr ::
    .letDecl "payer" (some (.elem .address)) takePayerExpr ::
    .letDecl "receiver" (some (.elem .address)) takeReceiverExpr :: takeTransition.body.drop 64 := rfl

theorem takeRecipientsSource {frame : Frame} {evm : State} {offer : OfferData}
    {callback buyer receiver : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "takerCallback" = some (.address callback))
    (hb : frame.locals.get? "buyer" = some (.address buyer))
    (hr : frame.locals.get? "receiverIfTakerIsSeller" = some (.address receiver)) :
    ABlock config evm frame (takeTransition.body.drop 60)
      (takeRecipientsFrame frame offer callback buyer evm.executionEnv.source receiver)
      (takeTransition.body.drop 64) := by
  have ho1 := (store_get_ne frame.locals (.address (takeBuyerCallback offer callback))
    (by decide : ("buyerCallback" == "offer") = false)).trans ho
  have ho2 : (takeCallbacksFrame frame offer callback).locals.get? "offer" =
      some (Model.offerValue offer.value) := (store_get_ne _ _ (by decide)).trans ho1
  rw [takeRecipients_shape]
  refine ⟨fun hx ↦ ExecBlock.consNormal (ExecStmt.letDecl (evalTakeBuyerCallback ho ht))
    (ExecBlock.consNormal (ExecStmt.letDecl (evalTakeSellerCallback ho1
      ((store_get_ne _ _ (by decide)).trans ht)))
    (ExecBlock.consNormal (ExecStmt.letDecl (evalTakePayer ho2 ?_ ?_))
    (ExecBlock.consNormal (ExecStmt.letDecl (evalTakeReceiver ?_ ?_)) hx)))⟩
  · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
  · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hb)
  · exact (store_get_ne _ _ (by decide)).trans ho2
  · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans hr))

end Benchmarks.Midnight
