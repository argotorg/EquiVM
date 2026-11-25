import Benchmarks.Midnight.TakePositionReadSource

variable {fork : Ethereum.Fork}

/-! Source preparation of the participant addresses and their position aliases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takePositionPrepareFrame (frame : Frame) (evm : State) (offer : OfferData)
    (id taker : UInt256) : Frame :=
  takePositionReadFrame (takeParticipantsFrame frame offer taker) evm id
    (takeBuyer offer taker) (takeSeller offer taker)

theorem takeParticipantsFrame_buyer (frame : Frame) (offer : OfferData) (taker : UInt256) :
    (takeParticipantsFrame frame offer taker).locals.get? "buyer" =
      some (.address (AccountAddress.ofNat (takeBuyer offer taker).toNat)) :=
  (store_get_ne _ _ (by decide)).trans (store_get_self ..)

theorem takeParticipantsFrame_seller (frame : Frame) (offer : OfferData) (taker : UInt256) :
    (takeParticipantsFrame frame offer taker).locals.get? "seller" =
      some (.address (AccountAddress.ofNat (takeSeller offer taker).toNat)) := store_get_self ..

theorem takePositionReadFrame_get (frame : Frame) (evm : State) (id buyer seller : UInt256)
    (name : Ident) (h1 : name ≠ "__c9") (h2 : name ≠ "buyerPos") (h3 : name ≠ "sellerPos") :
    (takePositionReadFrame frame evm id buyer seller).locals.get? name =
      frame.locals.get? name :=
  (store_get_ne _ _ (by simpa using h1.symm)).trans
    (takePositionAliasesFrame_get frame id buyer seller name h2 h3)

theorem takePositionPrepareFrame_buyer (frame : Frame) (evm : State) (offer : OfferData)
    (id taker : UInt256) :
    (takePositionPrepareFrame frame evm offer id taker).locals.get? "buyer" =
      some (.address (AccountAddress.ofNat (takeBuyer offer taker).toNat)) :=
  (takePositionReadFrame_get _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
    (takeParticipantsFrame_buyer frame offer taker)

theorem takePositionPrepareFrame_seller (frame : Frame) (evm : State) (offer : OfferData)
    (id taker : UInt256) :
    (takePositionPrepareFrame frame evm offer id taker).locals.get? "seller" =
      some (.address (AccountAddress.ofNat (takeSeller offer taker).toNat)) :=
  (takePositionReadFrame_get _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
    (takeParticipantsFrame_seller frame offer taker)

theorem takePositionPrepareFrame_buyerPos (frame : Frame) (evm : State) (offer : OfferData)
    (id taker : UInt256) :
    (takePositionPrepareFrame frame evm offer id taker).locals.get? "buyerPos" =
      some (.storageRef (positionRef id (takeBuyer offer taker)) positionType) :=
  (store_get_ne _ _ (by decide)).trans (takePositionAliasesFrame_buyer ..)

theorem takePositionPrepareFrame_sellerPos (frame : Frame) (evm : State) (offer : OfferData)
    (id taker : UInt256) :
    (takePositionPrepareFrame frame evm offer id taker).locals.get? "sellerPos" =
      some (.storageRef (positionRef id (takeSeller offer taker)) positionType) :=
  (store_get_ne _ _ (by decide)).trans (takePositionAliasesFrame_seller ..)

theorem takePositionPrepareFrame_credit (frame : Frame) (evm : State) (offer : OfferData)
    (id taker : UInt256) :
    (takePositionPrepareFrame frame evm offer id taker).locals.get? "__c9" =
      some (.bool (hasCreditValue evm id (takeBuyer offer taker))) := store_get_self ..

theorem takePositionPrepareSource {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker : UInt256} {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (ht : taker.toNat < EVM.addressModulus) :
    ABlock fork config evm frame (takeTransition.body.drop 27)
      (takePositionPrepareFrame frame evm offer id taker) (takeTransition.body.drop 32) := by
  have hf1 := hf.participants
  have h1 := takeParticipantsSource (fork := fork) (evm := evm) hf.offerValue hf.taker
  have h2 := takePositionReadSource (fork := fork) (evm := evm) hf1.contract hf1.position hf1.idValue
    (takeParticipantsFrame_buyer frame offer taker) (takeParticipantsFrame_seller frame offer taker)
    (takeBuyer_canonical ht)
  exact ⟨fun h ↦ h1.run (h2.run h)⟩

theorem TakeSourceFrame.positionPrepare {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker : UInt256} {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takePositionPrepareFrame frame evm offer id taker) offer id units taker
      receiver callback ratifierData data := hf.participants.positionRead

end Benchmarks.Midnight
