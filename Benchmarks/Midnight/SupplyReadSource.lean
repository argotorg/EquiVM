import Benchmarks.Midnight.SupplySourceFrame

/-! Source token lookup, position alias, and initial collateral read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

structure SupplyTouchSourceFrame (frame : Frame) (m : MarketData)
    (user index assets : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  idValue : frame.locals.get? "id" = some (wordBytes32Value m.id)
  userValue : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat))
  index : frame.locals.get? "collateralIndex" = some (.int index.toNat)
  assets : frame.locals.get? "assets" = some (.int assets.toNat)
  positionNone : frame.locals.get? "position" = none

def supplyTokenFrame (frame : Frame) (token : AccountAddress) : Frame :=
  { frame with locals := frame.locals.insert "collateralToken" (.address token) }

def supplyPositionFrame (frame : Frame) (id user : UInt256) (token : AccountAddress) : Frame :=
  let f := supplyTokenFrame frame token
  { f with locals := f.locals.insert "_position" (.storageRef (positionRef id user) positionType) }

def supplyReadFrame (frame : Frame) (id user old : UInt256) (token : AccountAddress) : Frame :=
  wordLocal (supplyPositionFrame frame id user token) "oldCollateral" old

theorem supplyReadFrame_get {frame : Frame} {m : MarketData} {user index assets : UInt256}
    (hf : SupplyTouchSourceFrame frame m user index assets) (old : UInt256) (token : AccountAddress) :
    SupplySourceFrame (supplyReadFrame frame m.id user old token)
      m m.id user index assets old token := by
  rcases hf with ⟨hc, hm, hid, hu, hi, ha, hp⟩
  constructor <;> simp_all [supplyReadFrame, supplyPositionFrame, supplyTokenFrame, wordLocal,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem supplyTokenValue {frame : Frame} {m : MarketData} {user index assets : UInt256}
    (hf : SupplyTouchSourceFrame frame m user index assets) (evm : EVM.State)
    (hi : index.toNat < m.collaterals.length) :
    evalExpr? config frame evm (.field (marketCollateralExpr "collateralIndex") "token") =
      .ok (.address m.collaterals[index.toNat].token) := by
  rw [evalExpr?, evalMarketCollateralAt "collateralIndex" hf.market hf.index hi]
  rfl

theorem supplyPositionBind {frame : Frame} {m : MarketData} {user index assets : UInt256}
    (hf : SupplyTouchSourceFrame frame m user index assets) (evm : EVM.State)
    (token : AccountAddress) :
    ExecStmt config (supplyTokenFrame frame token) evm (supplyCollateralTransition.body[6]!)
      (.ok (supplyPositionFrame frame m.id user token) evm) := by
  apply ExecStmt.letStorage
  apply resolvePositionAccount (frame := supplyTokenFrame frame token) "onBehalf"
    (by exact hf.contract)
  · simpa [supplyTokenFrame, Std.HashMap.getElem?_insert] using hf.positionNone
  · simpa [supplyTokenFrame, Std.HashMap.getElem?_insert] using hf.idValue
  · simpa [supplyTokenFrame, Std.HashMap.getElem?_insert] using hf.userValue

theorem supplyReadSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {user index assets : UInt256} {result : ExecResult}
    (hf : SupplyTouchSourceFrame frame m user index assets)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < m.collaterals.length)
    (hi128 : index.toNat < 128)
    (htail : ExecBlock config (supplyReadFrame frame m.id user
      (collateralWord (EVM.storageLoad evm evm.executionEnv.codeOwner) m.id user index)
      m.collaterals[index.toNat].token) evm (supplyCollateralTransition.body.drop 8) result) :
    ExecBlock config frame evm (supplyCollateralTransition.body.drop 5) result := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (supplyTokenValue hf evm hi))
  apply ExecBlock.consNormal (supplyPositionBind hf evm _)
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
  apply evalPositionCollateral
    (frame := supplyPositionFrame frame m.id user m.collaterals[index.toNat].token)
    "collateralIndex" (by exact hf.contract) hcanon
    (store_get_self ..) ?_ hi128
  simpa [supplyPositionFrame, supplyTokenFrame, Std.HashMap.getElem?_insert] using hf.index

theorem supplyReadRevert {frame : Frame} {m : MarketData} {evm : EVM.State}
    {user index assets : UInt256} (hf : SupplyTouchSourceFrame frame m user index assets)
    (hbad : ¬ index.toNat < m.collaterals.length ∨ ¬ index.toNat < 128) :
    ExecBlock config frame evm (supplyCollateralTransition.body.drop 5) .reverted := by
  by_cases hi : index.toNat < m.collaterals.length
  · have h128 : ¬ index.toNat < 128 := hbad.resolve_left (not_not.mpr hi)
    apply ExecBlock.consNormal (ExecStmt.letDecl (supplyTokenValue hf evm hi))
    apply ExecBlock.consNormal (supplyPositionBind hf evm _)
    apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
    apply evalPositionCollateralRevert
      (frame := supplyPositionFrame frame m.id user m.collaterals[index.toNat].token)
      "collateralIndex" (by exact hf.contract) (store_get_self ..) ?_ h128
    simpa [supplyPositionFrame, supplyTokenFrame, Std.HashMap.getElem?_insert] using hf.index
  · apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
    change evalExpr? config frame evm
      (.field (marketCollateralExpr "collateralIndex") "token") = .revert
    rw [evalExpr?, evalMarketCollateralAtRevert "collateralIndex" hf.market hf.index hi]
    rfl

end Benchmarks.Midnight
