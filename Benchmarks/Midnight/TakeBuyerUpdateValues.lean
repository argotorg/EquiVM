import Benchmarks.Midnight.TakeBuyerUpdateSource
import Benchmarks.Midnight.PositionUpdateCallFunding

/-! Conditional source state, local frame, and runtime memory after the buyer update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

abbrev TakeBuyerUpdateNeeded (evm : State) (id buyer units : UInt256) : Prop :=
  TakeBuyerNeedsUpdate (positionFieldWord evm id buyer 0)
    (low128 (healthPositionWord evm id buyer)) units

def takeBuyerUpdateState (evm : State) (offer : OfferData) (id buyer units : UInt256) : State :=
  if TakeBuyerUpdateNeeded evm id buyer units then
    positionUpdateFinalState evm offer.market id buyer else evm

def takeBuyerUpdateFrame (frame : Frame) (evm : State) (offer : OfferData)
    (id buyer units : UInt256) : Frame :=
  if TakeBuyerUpdateNeeded evm id buyer units then
    positionUpdateCallerFrame frame evm offer.market id buyer "__c10" else frame

def takeBuyerUpdateMemory (mem : ByteArray) (root : UInt256) (evm : State) (offer : OfferData)
    (id buyer units : UInt256) : ByteArray :=
  if TakeBuyerUpdateNeeded evm id buyer units then
    positionUpdateLogMemory mem root evm offer.market id buyer else mem

theorem takeBuyerUpdateFrame_get (frame : Frame) (evm : State) (offer : OfferData)
    (id buyer units : UInt256) (name : Ident) (hn : name ≠ "__c10") :
    (takeBuyerUpdateFrame frame evm offer id buyer units).locals.get? name =
      frame.locals.get? name := by
  unfold takeBuyerUpdateFrame
  split
  · exact store_get_ne _ _ (by simpa using hn.symm)
  · rfl

theorem TakeSourceFrame.buyerUpdate {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker buyer : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeBuyerUpdateFrame frame evm offer id buyer units) offer id units taker
      receiver callback ratifierData data := by
  unfold takeBuyerUpdateFrame
  split
  · exact hf.insert "__c10" _ (by decide)
  · exact hf

end Benchmarks.Midnight
