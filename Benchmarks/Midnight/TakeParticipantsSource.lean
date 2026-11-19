import Benchmarks.Midnight.TakeConsumption

/-! Buyer and seller addresses selected by the offer's direction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyer (offer : OfferData) (taker : UInt256) : UInt256 :=
  if offer.buy = ⟨0⟩ then taker else UInt256.ofNat offer.maker.val

def takeSeller (offer : OfferData) (taker : UInt256) : UInt256 :=
  if offer.buy = ⟨0⟩ then UInt256.ofNat offer.maker.val else taker

def takeBuyerExpr : Expr :=
  .ite (.field (.var "offer") "buy") (.field (.var "offer") "maker") (.var "taker")

def takeSellerExpr : Expr :=
  .ite (.field (.var "offer") "buy") (.var "taker") (.field (.var "offer") "maker")

def takeBuyerFrame (frame : Frame) (offer : OfferData) (taker : UInt256) : Frame :=
  { frame with
    locals := frame.locals.insert "buyer"
      (.address (AccountAddress.ofNat (takeBuyer offer taker).toNat)) }

def takeParticipantsFrame (frame : Frame) (offer : OfferData) (taker : UInt256) : Frame :=
  { takeBuyerFrame frame offer taker with
    locals := (takeBuyerFrame frame offer taker).locals.insert "seller"
      (.address (AccountAddress.ofNat (takeSeller offer taker).toNat)) }

theorem takeBuyer_canonical {offer : OfferData} {taker : UInt256}
    (ht : taker.toNat < EVM.addressModulus) : (takeBuyer offer taker).toNat < EVM.addressModulus := by
  unfold takeBuyer
  split
  · exact ht
  · exact addressWord_canonical offer.maker

theorem takeSeller_canonical {offer : OfferData} {taker : UInt256}
    (ht : taker.toNat < EVM.addressModulus) : (takeSeller offer taker).toNat < EVM.addressModulus := by
  unfold takeSeller
  split
  · exact addressWord_canonical offer.maker
  · exact ht

theorem evalTakeBuyer {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {taker : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "taker" = some (.address (AccountAddress.ofNat taker.toNat))) :
    evalExpr? cfg frame evm takeBuyerExpr =
      .ok (.address (AccountAddress.ofNat (takeBuyer offer taker).toNat)) := by
  rw [takeBuyerExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hz : offer.buy = ⟨0⟩
  · simp only [hz, decide_true, Bool.not_true, takeBuyer, if_true,
      evalExpr?, ht, EvalResult.ofOption]
  · simp only [hz, decide_false, Bool.not_false, takeBuyer, if_false, evalOfferMaker ho]
    exact congrArg (fun a ↦ EvalResult.ok (Value.address a))
      (accountAddress_of_addressWord_toNat offer.maker).symm

theorem evalTakeSeller {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {taker : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "taker" = some (.address (AccountAddress.ofNat taker.toNat))) :
    evalExpr? cfg frame evm takeSellerExpr =
      .ok (.address (AccountAddress.ofNat (takeSeller offer taker).toNat)) := by
  rw [takeSellerExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hz : offer.buy = ⟨0⟩
  · simp only [hz, decide_true, Bool.not_true, takeSeller, if_true, evalOfferMaker ho]
    exact congrArg (fun a ↦ EvalResult.ok (Value.address a))
      (accountAddress_of_addressWord_toNat offer.maker).symm
  · simp only [hz, decide_false, Bool.not_false, takeSeller, if_false,
      evalExpr?, ht, EvalResult.ofOption]

theorem takeParticipants_shape : takeTransition.body.drop 27 =
    .letDecl "buyer" (some (.elem .address)) takeBuyerExpr ::
    .letDecl "seller" (some (.elem .address)) takeSellerExpr :: takeTransition.body.drop 29 := rfl

theorem takeParticipantsSource {frame : Frame} {evm : State} {offer : OfferData} {taker : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "taker" = some (.address (AccountAddress.ofNat taker.toNat))) :
    ABlock config evm frame (takeTransition.body.drop 27) (takeParticipantsFrame frame offer taker)
      (takeTransition.body.drop 29) := by
  rw [takeParticipants_shape]
  exact ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letDecl (evalTakeBuyer ho ht))
    (ExecBlock.consNormal (ExecStmt.letDecl (evalTakeSeller
      ((store_get_ne _ _ (by decide)).trans ho) ((store_get_ne _ _ (by decide)).trans ht))) h)⟩

theorem TakeSourceFrame.participants {frame : Frame} {offer : OfferData} {id units taker : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeParticipantsFrame frame offer taker) offer id units taker receiver callback
      ratifierData data :=
  (hf.insert "buyer" (.address (AccountAddress.ofNat (takeBuyer offer taker).toNat)) (by decide)).insert
    "seller" (.address (AccountAddress.ofNat (takeSeller offer taker).toNat)) (by decide)

end Benchmarks.Midnight
