import Benchmarks.Midnight.SupplySourceFrame
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.CollateralPackedStore

variable {fork : Ethereum.Fork}

/-! The checked balance update and source event for collateral supply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def supplyAddExpr : Expr := .inRange (.uint ⟨256, by decide⟩)
  (.binary .add (.var "oldCollateral") (.var "assets"))

theorem supplyAddArgs {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token : AccountAddress}
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hfit : old.toNat + assets.toNat < UInt256.size) :
    evalExprs? config frame evm [supplyAddExpr] = .ok [.int (old + assets).toNat] := by
  have he := Reasoning.VyperDispatch.evalExpr_uint256_add (cfg := config)
    (evalWordLocal (evm := evm) hf.old) (evalWordLocal (evm := evm) hf.assets) hfit
  simp only [evalExprs?, supplyAddExpr, he, EvalResult.bind, bind, pure]
  rfl

theorem supplyAddRevert {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token : AccountAddress}
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hfit : ¬ old.toNat + assets.toNat < 2^128) :
    ExecBlock fork config frame evm (supplyCollateralTransition.body.drop 9) .reverted := by
  apply ExecBlock.consRevert
  by_cases h256 : old.toNat + assets.toNat < UInt256.size
  · apply callToUint128Revert hf.contract (supplyAddArgs hf h256)
    have hn : (old + assets).toNat = old.toNat + assets.toNat := addWord_toNat _ _ h256
    rw [hn]
    omega
  · apply ExecStmt.internalCallArgsRevert
    have he := Reasoning.VyperDispatch.evalExpr_uint256_add_overflow (cfg := config)
      (evalWordLocal (evm := evm) hf.old) (evalWordLocal (evm := evm) hf.assets) (by omega :
        UInt256.size ≤ old.toNat + assets.toNat)
    simp only [evalExprs?, he, EvalResult.bind, bind]

theorem supplyCollateralAssign {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token : AccountAddress}
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128) :
    assignStorageRef? config (wordLocal frame "__c4" (old + assets)) evm .storage
      { base := "_position", steps := [.field "collateral", .aindex (.var "collateralIndex")] }
      (.int (old + assets).toNat) = .ok (wordLocal frame "__c4" (old + assets),
        collateralWriteState evm id user index (old + assets)) := by
  have hf' := hf.insert "__c4" (.int (old + assets).toNat) (by decide)
  exact assignPositionCollateral "collateralIndex" hf'.contract hcanon hf'.position hf'.index hi
    (storageLocStore_collateral evm id user index (old + assets))

theorem supplyAddSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token : AccountAddress} {result : ExecResult}
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hfit : old.toNat + assets.toNat < 2^128) (hp : evm.executionEnv.perm = true)
    (htail : ExecBlock fork config (wordLocal frame "__c4" (old + assets))
      (collateralWriteState evm id user index (old + assets))
      (supplyCollateralTransition.body.drop 11) result) :
    ExecBlock fork config frame evm (supplyCollateralTransition.body.drop 9) result := by
  have h256 : old.toNat + assets.toNat < UInt256.size := by change _ < 2^256; omega
  have hn : (old + assets).toNat = old.toNat + assets.toNat := addWord_toNat _ _ h256
  apply ExecBlock.consNormal (callToUint128 hf.contract (supplyAddArgs hf h256)
    (by rw [hn]; exact hfit))
  exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hp)
    (evalWordLocal (wordLocal_get ..)) (supplyCollateralAssign hf hcanon hi)) htail

theorem supplyAddStatic {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token : AccountAddress}
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hfit : old.toNat + assets.toNat < 2^128) (hp : evm.executionEnv.perm = false) :
    ExecBlock fork config frame evm (supplyCollateralTransition.body.drop 9) .staticViolation := by
  have h256 : old.toNat + assets.toNat < UInt256.size := by change _ < 2^256; omega
  have hn : (old + assets).toNat = old.toNat + assets.toNat := addWord_toNat _ _ h256
  apply ExecBlock.consNormal (callToUint128 hf.contract (supplyAddArgs hf h256)
    (by rw [hn]; exact hfit))
  exact ExecBlock.consStatic (ExecStmt.assignStatic (evalWordLocal (wordLocal_get ..))
    (supplyCollateralAssign hf hcanon hi) hp)

theorem supplyCollateralEmit {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token : AccountAddress}
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hp : evm.executionEnv.perm = true) :
    ABlock fork config evm frame (supplyCollateralTransition.body.drop 11)
      frame (supplyCollateralTransition.body.drop 12) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address evm.executionEnv.source, wordBytes32Value id, .address token, .int assets.toNat,
      .address (AccountAddress.ofNat user.toNat)]) hp ?_) h⟩
  simp only [evalExprs?, evalExpr?, hf.idValue, hf.token, hf.assets, hf.userValue,
    envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem supplyCollateralTransferArgs {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user index assets old : UInt256} {token : AccountAddress}
    (hf : SupplySourceFrame frame m id user index assets old token) :
    evalExprs? config frame evm
      [.var "collateralToken", .env .caller, .env .this, .var "assets"] =
      .ok [.address token, .address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
        .int assets.toNat] := by
  simp only [evalExprs?, evalExpr?, hf.token, hf.assets, envValue, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

end Benchmarks.Midnight
