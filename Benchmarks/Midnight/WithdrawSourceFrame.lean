import Benchmarks.Midnight.NamedCollateralSource
import Benchmarks.Midnight.SupplyBitmapSource

/-! Source locals retained by collateral withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

structure WithdrawSourceFrame (frame : Frame) (m : MarketData)
    (id user index assets : UInt256) (token receiver : AccountAddress) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  idValue : frame.locals.get? "id" = some (wordBytes32Value id)
  userValue : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat))
  index : frame.locals.get? "collateralIndex" = some (.int index.toNat)
  assets : frame.locals.get? "assets" = some (.int assets.toNat)
  receiver : frame.locals.get? "receiver" = some (.address receiver)
  token : frame.locals.get? "collateralToken" = some (.address token)
  position : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)

theorem WithdrawSourceFrame.insert {frame : Frame} {m : MarketData}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (h : WithdrawSourceFrame frame m id user index assets token receiver) (name : Ident) (value : Value)
    (hn : name ∉ ["market", "id", "onBehalf", "collateralIndex", "assets", "receiver",
      "collateralToken", "_position"]) :
    WithdrawSourceFrame { frame with locals := frame.locals.insert name value }
      m id user index assets token receiver := by
  rcases h with ⟨hc, hm, hid, hu, hi, ha, ho, ht, hp⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

def withdrawClearGuard : Expr := .binary .and
  (.binary .eq (.var "newCollateral") (.intLit 0))
  (.binary .gt (.var "assets") (.intLit 0))

theorem evalWithdrawClearGuard {frame : Frame} {m : MarketData}
    {id user index assets newValue : UInt256} {token receiver : AccountAddress} (evm : EVM.State)
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hnew : frame.locals.get? "newCollateral" = some (.int newValue.toNat)) :
    evalExpr? config frame evm withdrawClearGuard =
      .ok (.bool (decide (newValue = ⟨0⟩ ∧ assets ≠ ⟨0⟩))) := by
  have ho : newValue.toNat = 0 ↔ newValue = ⟨0⟩ := by
    constructor
    · intro h; apply u256_inj; exact h
    · rintro rfl; rfl
  have ha : 0 < assets.toNat ↔ assets ≠ ⟨0⟩ := by
    constructor
    · intro h hz; subst assets; exact (by decide : ¬ 0 < (⟨0⟩ : UInt256).toNat) h
    · intro h; by_contra hn; apply h; apply u256_inj; change assets.toNat = 0; omega
  simp only [withdrawClearGuard, evalExpr?, hnew, hf.assets, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq,
    Int.natCast_eq_zero, ho, Int.natCast_pos, ha]
  split <;> simp_all

end Benchmarks.Midnight
