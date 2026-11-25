import Benchmarks.Midnight.TakeCreditSource
import Benchmarks.Midnight.TakeBuyerUpdateSource

variable {fork : Ethereum.Fork}

/-! Source frames and calls for the seller's conditional position update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSellerCreditStmt : Stmt :=
  .internalCall "hasCredit" [.var "id", .var "seller"] "__c11"

def takeSellerUpdateStmt : Stmt :=
  .ite (.var "__c11")
    [.internalCall "_updatePosition" [.field (.var "offer") "market", .var "id", .var "seller"]
      "__c12"] []

def takeSellerUpdateBody : List Stmt := [takeSellerCreditStmt, takeSellerUpdateStmt]

theorem takeSellerUpdate_shape : takeTransition.body.drop 33 =
    takeSellerUpdateBody ++ takeTransition.body.drop 35 := rfl

def takeSellerCreditFrame (frame : Frame) (evm : State) (id seller : UInt256) : Frame :=
  resumeAfterInternalCall frame "__c11" (some [.bool (hasCreditValue evm id seller)])

def takeSellerUpdateFrame (frame : Frame) (evm : State) (offer : OfferData)
    (id seller : UInt256) : Frame :=
  if positionFieldWord evm id seller 0 = ⟨0⟩ then takeSellerCreditFrame frame evm id seller else
    positionUpdateCallerFrame (takeSellerCreditFrame frame evm id seller) evm offer.market
      id seller "__c12"

def takeSellerUpdateState (evm : State) (offer : OfferData) (id seller : UInt256) : State :=
  if positionFieldWord evm id seller 0 = ⟨0⟩ then evm else
    positionUpdateFinalState evm offer.market id seller

def takeSellerUpdateMemory (mem : ByteArray) (root : UInt256) (evm : State) (offer : OfferData)
    (id seller : UInt256) : ByteArray :=
  if positionFieldWord evm id seller 0 = ⟨0⟩ then positionReadMemory mem id seller else
    positionUpdateLogMemory (positionReadMemory mem id seller) root evm offer.market id seller

theorem takeSellerCreditFrame_get (frame : Frame) (evm : State) (id seller : UInt256)
    (name : Ident) (hn : name ≠ "__c11") :
    (takeSellerCreditFrame frame evm id seller).locals.get? name = frame.locals.get? name :=
  store_get_ne _ _ (by simpa using hn.symm)

theorem takeSellerUpdateFrame_get (frame : Frame) (evm : State) (offer : OfferData)
    (id seller : UInt256) (name : Ident) (h1 : name ≠ "__c11") (h2 : name ≠ "__c12") :
    (takeSellerUpdateFrame frame evm offer id seller).locals.get? name =
      frame.locals.get? name := by
  unfold takeSellerUpdateFrame
  split
  · exact takeSellerCreditFrame_get frame evm id seller name h1
  · exact (store_get_ne _ _ (by simpa using h2.symm)).trans
      (takeSellerCreditFrame_get frame evm id seller name h1)

theorem takeSellerCreditSource {frame : Frame} {evm : State} {id seller : UInt256}
    (hc : frame.contract = contract)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hs : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hcanon : seller.toNat < EVM.addressModulus) :
    ExecStmt fork config frame evm takeSellerCreditStmt
      (.ok (takeSellerCreditFrame frame evm id seller) evm) := by
  apply callHasCredit hc _ hcanon
  simp only [evalExprs?, evalExpr?, hi, hs, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem evalTakeSellerUpdateCondition (frame : Frame) (evm : State) (id seller : UInt256) :
    evalExpr? config (takeSellerCreditFrame frame evm id seller) evm (.var "__c11") =
      .ok (.bool (!decide (positionFieldWord evm id seller 0 = ⟨0⟩))) := by
  simp only [evalExpr?, takeSellerCreditFrame, resumeAfterInternalCall, collapseReturns,
    store_get_self, EvalResult.ofOption, hasCreditValue_eq]

theorem TakeSourceFrame.sellerCredit {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker seller : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeSellerCreditFrame frame evm id seller) offer id units taker receiver
      callback ratifierData data :=
  hf.insert "__c11" (.bool (hasCreditValue evm id seller)) (by decide)

theorem TakeSourceFrame.sellerUpdate {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker seller : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeSellerUpdateFrame frame evm offer id seller) offer id units taker receiver
      callback ratifierData data := by
  unfold takeSellerUpdateFrame
  split
  · exact hf.sellerCredit
  · exact hf.sellerCredit.insert "__c12" _ (by decide)

end Benchmarks.Midnight
