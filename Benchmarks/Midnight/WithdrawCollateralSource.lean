import Benchmarks.Midnight.WithdrawSourceFrame
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.CollateralPackedStore

/-! Source subtraction, collateral assignment, event, and outgoing-transfer arguments. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawSubExpr : Expr := .inRange (.uint ⟨256, by decide⟩)
  (.binary .sub (positionCollateralExpr "collateralIndex") (.var "assets"))

def withdrawSubFrame (frame : Frame) (value : UInt256) : Frame :=
  wordLocal (wordLocal frame "newCollateral" value) "__c1" value

theorem WithdrawSourceFrame.subFrame {frame : Frame} {m : MarketData}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver) (value : UInt256) :
    WithdrawSourceFrame (withdrawSubFrame frame value) m id user index assets token receiver :=
  (hf.insert "newCollateral" (.int value.toNat) (by decide)).insert
    "__c1" (.int value.toNat) (by decide)

theorem withdrawSubEval {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hread : evalExpr? config frame evm (positionCollateralExpr "collateralIndex") =
      .ok (.int old.toNat)) (hle : assets.toNat ≤ old.toNat) :
    evalExpr? config frame evm withdrawSubExpr = .ok (.int (UInt256.sub old assets).toNat) :=
  evalExpr_uint256_sub hread (evalWordLocal hf.assets) hle

theorem withdrawSubRevert {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hread : evalExpr? config frame evm (positionCollateralExpr "collateralIndex") =
      .ok (.int old.toNat)) (hlt : old.toNat < assets.toNat) :
    ExecBlock config frame evm (withdrawCollateralTransition.body.drop 7) .reverted := by
  apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  exact Reasoning.VyperDispatch.evalExpr_uint256_sub_underflow
    hread (evalWordLocal hf.assets) hlt

theorem withdrawCollateralAssign {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128) (value : UInt256) :
    assignStorageRef? config (withdrawSubFrame frame value) evm .storage
      { base := "_position", steps := [.field "collateral", .aindex (.var "collateralIndex")] }
      (.int value.toNat) = .ok (withdrawSubFrame frame value,
        collateralWriteState evm id user index value) := by
  have hf' := hf.subFrame value
  exact assignPositionCollateral "collateralIndex" hf'.contract hcanon hf'.position hf'.index hi
    (storageLocStore_collateral evm id user index value)

theorem withdrawSubPrefix {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hread : evalExpr? config frame evm (positionCollateralExpr "collateralIndex") =
      .ok (.int old.toNat)) (hle : assets.toNat ≤ old.toNat) (hold : old.toNat < 2^128) :
    ABlock config evm frame (withdrawCollateralTransition.body.drop 7)
      (withdrawSubFrame frame (UInt256.sub old assets))
      (withdrawCollateralTransition.body.drop 9) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letDecl (withdrawSubEval hf hread hle))
    (ExecBlock.consNormal (callToUint128 (frame := wordLocal frame "newCollateral"
      (UInt256.sub old assets)) (by exact hf.contract) ?_ ?_) h)⟩
  · simp only [evalExprs?, evalExpr?, wordLocal_get, EvalResult.ofOption,
      EvalResult.bind, bind, pure]
  · rw [usub_toNat hle]; omega

theorem withdrawSubSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token receiver : AccountAddress} {result : ExecResult}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hread : evalExpr? config frame evm (positionCollateralExpr "collateralIndex") =
      .ok (.int old.toNat)) (hle : assets.toNat ≤ old.toNat) (hold : old.toNat < 2^128)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hp : evm.executionEnv.perm = true)
    (htail : ExecBlock config (withdrawSubFrame frame (UInt256.sub old assets))
      (collateralWriteState evm id user index (UInt256.sub old assets))
      (withdrawCollateralTransition.body.drop 10) result) :
    ExecBlock config frame evm (withdrawCollateralTransition.body.drop 7) result := by
  apply (withdrawSubPrefix hf hread hle hold).run
  exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hp)
    (evalWordLocal (wordLocal_get ..)) (withdrawCollateralAssign hf hcanon hi _)) htail

theorem withdrawSubStatic {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hread : evalExpr? config frame evm (positionCollateralExpr "collateralIndex") =
      .ok (.int old.toNat)) (hle : assets.toNat ≤ old.toNat) (hold : old.toNat < 2^128)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hp : evm.executionEnv.perm = false) :
    ExecBlock config frame evm (withdrawCollateralTransition.body.drop 7) .staticViolation := by
  apply (withdrawSubPrefix hf hread hle hold).run
  exact ExecBlock.consStatic (ExecStmt.assignStatic (evalWordLocal (wordLocal_get ..))
    (withdrawCollateralAssign hf hcanon hi _) hp)

theorem withdrawCollateralEmit {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hp : evm.executionEnv.perm = true) :
    ABlock config evm frame (withdrawCollateralTransition.body.drop 13)
      frame (withdrawCollateralTransition.body.drop 14) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address evm.executionEnv.source, wordBytes32Value id, .address token, .int assets.toNat,
      .address (AccountAddress.ofNat user.toNat), .address receiver]) hp ?_) h⟩
  simp only [evalExprs?, evalExpr?, hf.idValue, hf.token, hf.assets, hf.userValue, hf.receiver,
    envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem withdrawCollateralTransferArgs {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver) :
    evalExprs? config frame evm [.var "collateralToken", .var "receiver", .var "assets"] =
      .ok [.address token, .address receiver, .int assets.toNat] := by
  simp only [evalExprs?, evalExpr?, hf.token, hf.receiver, hf.assets, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

theorem withdrawCollateralHealthArgs {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets : UInt256} {token receiver : AccountAddress}
    (hf : WithdrawSourceFrame frame m id user index assets token receiver) :
    evalExprs? config frame evm [.var "market", .var "id", .var "onBehalf"] =
      .ok [Model.marketValue m.value, wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)] := by
  simp only [evalExprs?, evalExpr?, hf.market, hf.idValue, hf.userValue, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

end Benchmarks.Midnight
