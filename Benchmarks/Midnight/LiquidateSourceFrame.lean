import Benchmarks.Midnight.LiquidateDecode
import Benchmarks.Midnight.HealthStorage
import Benchmarks.Midnight.SettlementSource

/-! The liquidation arguments and storage aliases retained throughout the body. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure LiquidateSourceFrame (frame : Frame) (m : MarketData)
    (id index seized repaid borrower mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  idValue : frame.locals.get? "id" = some (wordBytes32Value id)
  index : frame.locals.get? "collateralIndex" = some (.int index.toNat)
  seized : frame.locals.get? "seizedAssets" = some (.int seized.toNat)
  repaid : frame.locals.get? "repaidUnits" = some (.int repaid.toNat)
  borrowerValue : frame.locals.get? "borrower" =
    some (.address (AccountAddress.ofNat borrower.toNat))
  mode : frame.locals.get? "postMaturityMode" = some (wordToElem .bool mode)
  receiver : frame.locals.get? "receiver" = some (.address receiver)
  callback : frame.locals.get? "callback" = some (.address callback)
  data : frame.locals.get? "data" = some (.bytes data)
  position : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType)
  marketState : frame.locals.get? "_marketState" =
    some (.storageRef (marketStateRef id) marketStateType)

theorem LiquidateSourceFrame.insert {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (name : Ident) (value : Value)
    (hn : name ∉ ["market", "id", "collateralIndex", "seizedAssets", "repaidUnits", "borrower",
      "postMaturityMode", "receiver", "callback", "data", "_position", "_marketState"]) :
    LiquidateSourceFrame { frame with locals := frame.locals.insert name value }
      m id index seized repaid borrower mode receiver callback data := by
  rcases h with ⟨hc, hm, hid, hi, hs, hr, hb, hmode, hrecv, hcb, hd, hp, hms⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

end Benchmarks.Midnight
