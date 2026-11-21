import Benchmarks.Midnight.TakePositionPrepareSource
import Benchmarks.Midnight.TakePositionPrepareMemory
import Benchmarks.Midnight.TakeBuyerUpdateValues
import Benchmarks.Midnight.TakeSellerUpdateSource

/-! The successive buyer and seller updates, with the seller reading the buyer's output state. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takePositionUpdatesState (evm : State) (offer : OfferData) (id units taker : UInt256) : State :=
  takeSellerUpdateState (takeBuyerUpdateState evm offer id (takeBuyer offer taker) units)
    offer id (takeSeller offer taker)

def takePositionUpdatesFrame (frame : Frame) (evm : State) (offer : OfferData)
    (id units taker : UInt256) : Frame :=
  takeSellerUpdateFrame
    (takeBuyerUpdateFrame (takePositionPrepareFrame frame evm offer id taker) evm offer id
      (takeBuyer offer taker) units)
    (takeBuyerUpdateState evm offer id (takeBuyer offer taker) units) offer id
    (takeSeller offer taker)

def takePositionUpdatesMemory (mem : ByteArray) (root : UInt256) (evm : State) (offer : OfferData)
    (id units taker : UInt256) : ByteArray :=
  takeSellerUpdateMemory
    (takeBuyerUpdateMemory (takePositionPrepareMemory mem offer id taker) root evm offer id
      (takeBuyer offer taker) units) root
    (takeBuyerUpdateState evm offer id (takeBuyer offer taker) units) offer id
    (takeSeller offer taker)

theorem takePositionUpdatesFrame_get (frame : Frame) (evm : State) (offer : OfferData)
    (id units taker : UInt256) (name : Ident)
    (h1 : name ≠ "__c10") (h2 : name ≠ "__c11") (h3 : name ≠ "__c12") :
    (takePositionUpdatesFrame frame evm offer id units taker).locals.get? name =
      (takePositionPrepareFrame frame evm offer id taker).locals.get? name :=
  (takeSellerUpdateFrame_get _ _ _ _ _ name h2 h3).trans
    (takeBuyerUpdateFrame_get _ _ _ _ _ _ name h1)

theorem takePositionUpdatesFrame_buyerPos (frame : Frame) (evm : State) (offer : OfferData)
    (id units taker : UInt256) :
    (takePositionUpdatesFrame frame evm offer id units taker).locals.get? "buyerPos" =
      some (.storageRef (positionRef id (takeBuyer offer taker)) positionType) :=
  (takePositionUpdatesFrame_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
    (takePositionPrepareFrame_buyerPos ..)

theorem takePositionUpdatesFrame_sellerPos (frame : Frame) (evm : State) (offer : OfferData)
    (id units taker : UInt256) :
    (takePositionUpdatesFrame frame evm offer id units taker).locals.get? "sellerPos" =
      some (.storageRef (positionRef id (takeSeller offer taker)) positionType) :=
  (takePositionUpdatesFrame_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
    (takePositionPrepareFrame_sellerPos ..)

end Benchmarks.Midnight
