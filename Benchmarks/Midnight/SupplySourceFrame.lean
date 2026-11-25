import Benchmarks.Midnight.NamedCollateralSource
import Benchmarks.Midnight.SupplyBitmapSource

/-! Source locals retained after the initial collateral read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

structure SupplySourceFrame (frame : Frame) (m : MarketData)
    (id user index assets old : UInt256) (token : AccountAddress) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  idValue : frame.locals.get? "id" = some (wordBytes32Value id)
  userValue : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat))
  index : frame.locals.get? "collateralIndex" = some (.int index.toNat)
  assets : frame.locals.get? "assets" = some (.int assets.toNat)
  old : frame.locals.get? "oldCollateral" = some (.int old.toNat)
  token : frame.locals.get? "collateralToken" = some (.address token)
  position : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)

theorem SupplySourceFrame.insert {frame : Frame} {m : MarketData}
    {id user index assets old : UInt256} {token : AccountAddress}
    (h : SupplySourceFrame frame m id user index assets old token) (name : Ident) (value : Value)
    (hn : name ∉ ["market", "id", "onBehalf", "collateralIndex", "assets", "oldCollateral",
      "collateralToken", "_position"]) :
    SupplySourceFrame { frame with locals := frame.locals.insert name value }
      m id user index assets old token := by
  rcases h with ⟨hc, hm, hid, hu, hi, ha, ho, ht, hp⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem SupplySourceFrame.countFrame {frame : Frame} {m : MarketData}
    {id user index assets old : UInt256} {token : AccountAddress}
    (h : SupplySourceFrame frame m id user index assets old token) (bitmap : UInt256) :
    SupplySourceFrame (supplyCountFrame frame bitmap) m id user index assets old token :=
  (h.insert "newCollateralBitmap" (.int bitmap.toNat) (by decide)).insert
    "__c3" (.int (bitmapCount bitmap).toNat) (by decide)

def supplyNewCollateralGuard : Expr := .binary .and
  (.binary .eq (.var "oldCollateral") (.intLit 0))
  (.binary .gt (.var "assets") (.intLit 0))

theorem evalSupplyNewCollateralGuard {frame : Frame} {m : MarketData}
    {id user index assets old : UInt256} {token : AccountAddress} (evm : EVM.State)
    (hf : SupplySourceFrame frame m id user index assets old token) :
    evalExpr? config frame evm supplyNewCollateralGuard =
      .ok (.bool (decide (old = ⟨0⟩ ∧ assets ≠ ⟨0⟩))) := by
  have ho : old.toNat = 0 ↔ old = ⟨0⟩ := by
    constructor
    · intro h; apply u256_inj; exact h
    · rintro rfl; rfl
  have ha : 0 < assets.toNat ↔ assets ≠ ⟨0⟩ := by
    constructor
    · intro h hz; subst assets; exact (by decide : ¬ 0 < (⟨0⟩ : UInt256).toNat) h
    · intro h; by_contra hn; apply h; apply u256_inj; change assets.toNat = 0; omega
  simp only [supplyNewCollateralGuard, evalExpr?, hf.old, hf.assets, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq,
    Int.natCast_eq_zero, ho, Int.natCast_pos, ha]
  split <;> simp_all

end Benchmarks.Midnight
