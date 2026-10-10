import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawSource

/-! Checked supply adjustment, balance lookup, and conversion in the withdrawal limit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxWithdrawSupplyFrame (frame : Frame) (supply : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "newTotalSupply" (uint256Value supply) }

def maxWithdrawBalanceFrame (frame : Frame) (supply balance : UInt256) : Frame :=
  { maxWithdrawSupplyFrame frame supply with
    locals := (maxWithdrawSupplyFrame frame supply).locals.insert "__c2" (uint256Value balance) }

def maxWithdrawConvertedFrame (frame : Frame) (assets : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "__c3" (uint256Value assets)).insert
      "assets" (uint256Value assets) }

def maxWithdrawConvertArgs : List Expr :=
  [.var "__c2", .var "newTotalSupply", .var "newTotalAssets", .intLit 0]

theorem allocatedMaxWithdrawFunction_balance :
    allocatedMaxWithdrawFunction.body.drop 10 =
      [.assign .localVar ⟨"newTotalSupply", []⟩ (.inRange (.uint ⟨256, by decide⟩)
          (.binary .add (.var "__c1") (.var "feeShares"))),
        .internalCall "balanceOf_body" [.var "owner"] "__c2"] ++
      allocatedMaxWithdrawFunction.body.drop 12 := by decide +kernel

theorem allocatedMaxWithdrawFunction_convert :
    allocatedMaxWithdrawFunction.body.drop 12 =
      [.internalCall "_convertToAssetsWithTotals" maxWithdrawConvertArgs "__c3",
        .assign .localVar ⟨"assets", []⟩ (.var "__c3")] ++
      allocatedMaxWithdrawFunction.body.drop 14 := by decide +kernel

theorem maxWithdrawBalanceSource {locals imms : Store} {evm : State} {owner : AccountAddress}
    {supply shares : UInt256} {old : Value}
    (ho : locals.get? "owner" = some (.address owner))
    (hs : locals.get? "__c1" = some (uint256Value supply))
    (hf : locals.get? "feeShares" = some (uint256Value shares))
    (hn : locals.get? "newTotalSupply" = some old)
    (hfit : supply.toNat + shares.toNat < UInt256.size) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (allocatedMaxWithdrawFunction.body.drop 10)
      (maxWithdrawBalanceFrame { contract := contract, locals := locals, immutables := imms }
        (supply + shares) (balanceInternalWord evm owner))
      (allocatedMaxWithdrawFunction.body.drop 12) := by
  refine ⟨fun h ↦ ?_⟩
  rw [allocatedMaxWithdrawFunction_balance]
  have hsum := checkedAddSourceOk
    (show evalExpr? config ⟨contract, locals, imms⟩ evm (.var "__c1") =
      .ok (uint256Value supply) by simp only [evalExpr?, hs, EvalResult.ofOption])
    (show evalExpr? config ⟨contract, locals, imms⟩ evm (.var "feeShares") =
      .ok (uint256Value shares) by simp only [evalExpr?, hf, EvalResult.ofOption]) hfit
  apply ExecBlock.consNormal (ExecStmt.assign hsum ?_)
  · apply ExecBlock.consNormal (balanceInternalCall evm _ imms owner "__c2" (.var "owner") ?_) h
    simp only [evalExpr?, maxWithdrawSupplyFrame,
      store_get_ne _ _ (by decide : ("newTotalSupply" == "owner") = false),
      ho, EvalResult.ofOption]
  · simp only [assignStorageRef?, hn, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl

theorem maxWithdrawSupplyReverts {frame : Frame} {evm : State} {supply shares : UInt256}
    (hs : frame.locals.get? "__c1" = some (uint256Value supply))
    (hf : frame.locals.get? "feeShares" = some (uint256Value shares))
    (hbad : UInt256.size ≤ supply.toNat + shares.toNat) :
    ExecBlock config frame evm (allocatedMaxWithdrawFunction.body.drop 10) .reverted := by
  rw [allocatedMaxWithdrawFunction_balance]
  apply ExecBlock.consRevert (ExecStmt.assignExprRevert (checkedAddSourceOverflow ?_ ?_ hbad))
  · simp only [evalExpr?, hs, EvalResult.ofOption]
  · simp only [evalExpr?, hf, EvalResult.ofOption]

theorem maxWithdrawConvertArgsSource {frame : Frame} {evm : State}
    {supply total balance : UInt256}
    (hs : frame.locals.get? "newTotalSupply" = some (uint256Value supply))
    (ht : frame.locals.get? "newTotalAssets" = some (uint256Value total))
    (hb : frame.locals.get? "__c2" = some (uint256Value balance)) :
    evalExprs? config frame evm maxWithdrawConvertArgs =
      .ok [uint256Value balance, uint256Value supply, uint256Value total, uint256Value ⟨0⟩] := by
  simp only [maxWithdrawConvertArgs, evalExprs?, evalExpr?, hs, ht, hb,
    EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem maxWithdrawConvertSource (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {supply total balance : UInt256} {old : Value}
    (hs : locals.get? "newTotalSupply" = some (uint256Value supply))
    (ht : locals.get? "newTotalAssets" = some (uint256Value total))
    (hb : locals.get? "__c2" = some (uint256Value balance))
    (ha : locals.get? "assets" = some old)
    (hfit : convertAssetsFits v.DECIMALS_OFFSET balance supply total) :
    ABlock config evm { contract := contract, locals := locals, immutables := immStore v }
      (allocatedMaxWithdrawFunction.body.drop 12)
      (maxWithdrawConvertedFrame
        { contract := contract, locals := locals, immutables := immStore v }
        (convertAssetsWord v.DECIMALS_OFFSET balance supply total))
      (allocatedMaxWithdrawFunction.body.drop 14) := by
  refine ⟨fun h ↦ ?_⟩
  rw [allocatedMaxWithdrawFunction_convert]
  apply ExecBlock.consNormal (convertAssetsCall v
    (maxWithdrawConvertArgsSource (frame := ⟨contract, locals, immStore v⟩) hs ht hb) hfit)
  apply ExecBlock.consNormal (ExecStmt.assign
    (value := uint256Value (convertAssetsWord v.DECIMALS_OFFSET balance supply total))
    (by simp only [evalExpr?, store_get_self, EvalResult.ofOption]) ?_) h
  simp only [assignStorageRef?,
    store_get_ne _ _ (by decide : ("__c3" == "assets") = false), ha,
    updateLocalPath?, bind, EvalResult.bind, pure]
  rfl

theorem maxWithdrawConvertReverts (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {supply total balance : UInt256}
    (hs : locals.get? "newTotalSupply" = some (uint256Value supply))
    (ht : locals.get? "newTotalAssets" = some (uint256Value total))
    (hb : locals.get? "__c2" = some (uint256Value balance))
    (hbad : ¬ convertAssetsFits v.DECIMALS_OFFSET balance supply total) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedMaxWithdrawFunction.body.drop 12) .reverted := by
  rw [allocatedMaxWithdrawFunction_convert]
  exact ExecBlock.consRevert (convertAssetsCallReverts v
    (maxWithdrawConvertArgsSource (frame := ⟨contract, locals, immStore v⟩) hs ht hb) hbad)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
