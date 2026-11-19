import Benchmarks.Midnight.MarketBalanceFields
import Benchmarks.Midnight.NamedCollateralSource

/-! Source locals retained through the checked withdrawal balance updates. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure WithdrawUnitsSourceFrame (frame : Frame) (m : MarketData)
    (id user units : UInt256) (receiver : AccountAddress) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  idValue : frame.locals.get? "id" = some (wordBytes32Value id)
  userValue : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat))
  units : frame.locals.get? "units" = some (.int units.toNat)
  receiver : frame.locals.get? "receiver" = some (.address receiver)
  position : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)
  marketState : frame.locals.get? "_marketState" =
    some (.storageRef (marketStateRef id) marketStateType)

theorem WithdrawUnitsSourceFrame.insert {frame : Frame} {m : MarketData}
    {id user units : UInt256} {receiver : AccountAddress}
    (h : WithdrawUnitsSourceFrame frame m id user units receiver) (name : Ident) (value : Value)
    (hn : name ∉ ["market", "id", "onBehalf", "units", "receiver", "_position", "_marketState"]) :
    WithdrawUnitsSourceFrame { frame with locals := frame.locals.insert name value }
      m id user units receiver := by
  rcases h with ⟨hc, hm, hi, hu, hnits, hr, hp, hs⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

end Benchmarks.Midnight
