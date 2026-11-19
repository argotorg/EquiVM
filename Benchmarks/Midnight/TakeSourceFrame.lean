import Benchmarks.Midnight.TakeDecode
import Benchmarks.Midnight.TouchMarketSource

/-! Source locals retained through take's internal calls and storage updates. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure TakeSourceFrame (frame : Frame) (offer : OfferData) (id units taker : UInt256)
    (receiver callback : AccountAddress) (ratifierData data : ByteArray) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  offerValue : frame.locals.get? "offer" = some (Model.offerValue offer.value)
  idValue : frame.locals.get? "id" = some (wordBytes32Value id)
  units : frame.locals.get? "units" = some (.int units.toNat)
  taker : frame.locals.get? "taker" = some (.address (AccountAddress.ofNat taker.toNat))
  receiver : frame.locals.get? "receiverIfTakerIsSeller" = some (.address receiver)
  callback : frame.locals.get? "takerCallback" = some (.address callback)
  ratifierData : frame.locals.get? "ratifierData" = some (.bytes ratifierData)
  data : frame.locals.get? "takerCallbackData" = some (.bytes data)
  authorization : frame.locals.get? "isAuthorized" = none
  marketState : frame.locals.get? "marketState" = none
  position : frame.locals.get? "position" = none
  consumed : frame.locals.get? "consumed" = none
  claimableFee : frame.locals.get? "claimableSettlementFee" = none

theorem TakeSourceFrame.insert {frame : Frame} {offer : OfferData} {id units taker : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (h : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (name : Ident) (value : Value)
    (hn : name ∉ ["offer", "id", "units", "taker", "receiverIfTakerIsSeller", "takerCallback",
      "ratifierData", "takerCallbackData", "isAuthorized", "marketState", "position", "consumed",
      "claimableSettlementFee"]) :
    TakeSourceFrame { frame with locals := frame.locals.insert name value }
      offer id units taker receiver callback ratifierData data := by
  rcases h with ⟨hc, ho, hi, hu, ht, hr, hcb, hrd, hd, ha, hm, hp, hcon, hf⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

end Benchmarks.Midnight
