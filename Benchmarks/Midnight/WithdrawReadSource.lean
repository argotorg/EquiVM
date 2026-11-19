import Benchmarks.Midnight.WithdrawCollateralSource
import Benchmarks.Midnight.SupplyReadSource

/-! Token lookup and position binding before collateral withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawReadFrame_get {frame : Frame} {m : MarketData} {user index assets : UInt256}
    {receiver : AccountAddress} (hf : SupplyTouchSourceFrame frame m user index assets)
    (hr : frame.locals.get? "receiver" = some (.address receiver)) (token : AccountAddress) :
    WithdrawSourceFrame (supplyPositionFrame frame m.id user token)
      m m.id user index assets token receiver := by
  rcases hf with ⟨hc, hm, hid, hu, hi, ha, hp⟩
  constructor <;> simp_all [supplyPositionFrame, supplyTokenFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem withdrawReadSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {user index assets : UInt256} {result : ExecResult}
    (hf : SupplyTouchSourceFrame frame m user index assets)
    (hi : index.toNat < m.collaterals.length)
    (htail : ExecBlock config
      (supplyPositionFrame frame m.id user m.collaterals[index.toNat].token) evm
      (withdrawCollateralTransition.body.drop 7) result) :
    ExecBlock config frame evm (withdrawCollateralTransition.body.drop 5) result :=
  ExecBlock.consNormal (ExecStmt.letDecl (supplyTokenValue hf evm hi))
    (ExecBlock.consNormal (supplyPositionBind hf evm _) htail)

theorem withdrawReadRevert {frame : Frame} {m : MarketData} {evm : EVM.State}
    {user index assets : UInt256} (hf : SupplyTouchSourceFrame frame m user index assets)
    (hbad : ¬ index.toNat < m.collaterals.length ∨ ¬ index.toNat < 128) :
    ExecBlock config frame evm (withdrawCollateralTransition.body.drop 5) .reverted := by
  by_cases hi : index.toNat < m.collaterals.length
  · have h128 : ¬ index.toNat < 128 := hbad.resolve_left (not_not.mpr hi)
    apply withdrawReadSource hf hi
    apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
    have he := evalPositionCollateralRevert
      (frame := supplyPositionFrame frame m.id user m.collaterals[index.toNat].token)
      (evm := evm) "collateralIndex" (by exact hf.contract) (store_get_self ..)
      (by simpa [supplyPositionFrame, supplyTokenFrame, Std.HashMap.getElem?_insert]
          using hf.index) h128
    change evalExpr? config _ evm withdrawSubExpr = .revert
    rw [withdrawSubExpr, evalExpr?, evalExpr_binary_nonshort (by decide) (by decide), he]
    rfl
  · apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
    change evalExpr? config frame evm
      (.field (marketCollateralExpr "collateralIndex") "token") = .revert
    rw [evalExpr?, evalMarketCollateralAtRevert "collateralIndex" hf.market hf.index hi]
    rfl

end Benchmarks.Midnight
