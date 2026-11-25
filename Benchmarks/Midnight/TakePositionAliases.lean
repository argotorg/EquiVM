import Benchmarks.Midnight.TakeParticipantsSource
import Benchmarks.Midnight.NamedPositionSource

variable {fork : Ethereum.Fork}

/-! Named storage aliases for the two positions used by take. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyerPositionFrame (frame : Frame) (id buyer : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "buyerPos" (.storageRef (positionRef id buyer)
      positionType) }

def takePositionAliasesFrame (frame : Frame) (id buyer seller : UInt256) : Frame :=
  { takeBuyerPositionFrame frame id buyer with
    locals := (takeBuyerPositionFrame frame id buyer).locals.insert "sellerPos"
      (.storageRef (positionRef id seller) positionType) }

theorem takePositionAliasesSource {frame : Frame} {evm : State} {id buyer seller : UInt256}
    (hc : frame.contract = contract) (hp : frame.locals.get? "position" = none)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hb : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat buyer.toNat)))
    (hs : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat))) :
    ABlock fork config evm frame (takeTransition.body.drop 29)
      (takePositionAliasesFrame frame id buyer seller) (takeTransition.body.drop 31) := by
  refine ⟨fun h ↦ ExecBlock.consNormal
    (ExecStmt.letStorage (resolveNamedPositionRef hc hp hi hb))
    (ExecBlock.consNormal (ExecStmt.letStorage ?_) h)⟩
  exact resolveNamedPositionRef (frame := takeBuyerPositionFrame frame id buyer) hc
    ((store_get_ne _ _ (by decide)).trans hp) ((store_get_ne _ _ (by decide)).trans hi)
    ((store_get_ne _ _ (by decide)).trans hs)

theorem takePositionAliasesFrame_buyer (frame : Frame) (id buyer seller : UInt256) :
    (takePositionAliasesFrame frame id buyer seller).locals.get? "buyerPos" =
      some (.storageRef (positionRef id buyer) positionType) :=
  (store_get_ne _ _ (by decide)).trans (store_get_self ..)

theorem takePositionAliasesFrame_seller (frame : Frame) (id buyer seller : UInt256) :
    (takePositionAliasesFrame frame id buyer seller).locals.get? "sellerPos" =
      some (.storageRef (positionRef id seller) positionType) := store_get_self ..

theorem takePositionAliasesFrame_get (frame : Frame) (id buyer seller : UInt256) (name : Ident)
    (hb : name ≠ "buyerPos") (hs : name ≠ "sellerPos") :
    (takePositionAliasesFrame frame id buyer seller).locals.get? name = frame.locals.get? name :=
  (store_get_ne _ _ (by simpa using hs.symm)).trans (store_get_ne _ _ (by simpa using hb.symm))

theorem TakeSourceFrame.positionAliases {frame : Frame} {offer : OfferData}
    {id units taker buyer seller : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takePositionAliasesFrame frame id buyer seller) offer id units taker receiver
      callback ratifierData data :=
  (hf.insert "buyerPos" (.storageRef (positionRef id buyer) positionType) (by decide)).insert
    "sellerPos" (.storageRef (positionRef id seller) positionType) (by decide)

end Benchmarks.Midnight
