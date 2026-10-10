import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedConvertSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsRoutines

/-! Cursor-aware internal asset conversion: accrued totals, supply adjustment, and return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def allocatedAssetsFrame (imms : Store) (assets ptr : UInt256)
    (rounding : UInt256 := ⟨0⟩) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert cursorName (uint256Value ptr)).insert "rounding"
      (uint256Value rounding)).insert "shares" (uint256Value assets)
    immutables := imms }

theorem allocatedConvertToAssetsFunction_prefix :
    allocatedConvertToAssetsFunction.body =
      cursorCall allocatedAccruedFeeAssetsFunction.name [] "__c0" ++
        allocatedConvertToAssetsFunction.body.drop 3 := by decide +kernel

theorem allocatedConvertToAssetsFunction_totals :
    allocatedConvertToAssetsFunction.body.drop 3 =
      [.letDecl "feeShares" (some abiUInt256) (.tupleGet (.var "__c0") 0),
        .letDecl "newTotalAssets" (some abiUInt256) (.tupleGet (.var "__c0") 1),
        .internalCall "totalSupply_body" [] "__c1"] ++
      allocatedConvertToAssetsFunction.body.drop 6 := by decide +kernel

theorem allocatedAssetsFrame_cursorArgs (imms : Store) (assets ptr : UInt256) (evm : State)
    (rounding : UInt256 := ⟨0⟩) :
    evalExprs? config (allocatedAssetsFrame imms assets ptr rounding) evm [.var cursorName] =
      .ok [uint256Value ptr] := by
  simp only [evalExprs?, evalExpr?, allocatedAssetsFrame,
    store_get_ne _ _ (by decide : ("shares" == cursorName) = false),
    store_get_ne _ _ (by decide : ("rounding" == cursorName) = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedAssetsPrefixSource (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {final : Frame} {assets ptr lost total shares ptr' supply rounding : UInt256}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body
      (.returned final evm' [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
        uint256Value ptr']))
    (hs : Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ = supply)
    {outcome : ExecResult}
    (htail : ExecBlock config
      (allocatedConvertTotalsFrame (allocatedAssetsFrame (immStore v) assets ptr rounding)
        lost total shares ptr' supply) evm'
      (allocatedConvertToAssetsFunction.body.drop 6) outcome) :
    ExecBlock config (allocatedAssetsFrame (immStore v) assets ptr rounding) evm
      allocatedConvertToAssetsFunction.body outcome := by
  rw [allocatedConvertToAssetsFunction_prefix, allocatedConvertToAssetsFunction_totals]
  exact allocatedAccrualTotalsPrefixSource v
    (allocatedAssetsFrame_cursorArgs (immStore v) assets ptr evm rounding) hbody hs htail

theorem allocatedAssetsAccrualReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} {assets ptr rounding : UInt256}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body .reverted) :
    ExecFuncBody config (allocatedAssetsFrame (immStore v) assets ptr rounding) evm
      allocatedConvertToAssetsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedConvertToAssetsFunction_prefix]
  exact ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedAccruedFeeAssetsFunction)
      (allocatedAssetsFrame_cursorArgs (immStore v) assets ptr evm rounding) rfl rfl hbody)

def allocatedAssetsArgs : List Expr :=
  [.var "shares", .inRange (.uint ⟨256, by decide⟩)
      (.binary .add (.var "__c1") (.var "feeShares")), .var "newTotalAssets", .var "rounding"]

theorem allocatedConvertToAssetsFunction_tail :
    allocatedConvertToAssetsFunction.body.drop 6 =
      [.internalCall "_convertToAssetsWithTotals" allocatedAssetsArgs "__c2",
        .return [.var "__c2", .var cursorName]] := by decide +kernel

structure AllocatedAssetsLocals (frame : Frame) (assets total shares supply ptr : UInt256)
    (mode : UInt256 := ⟨0⟩) :
    Prop where
  assets : frame.locals.get? "shares" = some (uint256Value assets)
  total : frame.locals.get? "newTotalAssets" = some (uint256Value total)
  shares : frame.locals.get? "feeShares" = some (uint256Value shares)
  supply : frame.locals.get? "__c1" = some (uint256Value supply)
  rounding : frame.locals.get? "rounding" = some (uint256Value mode)
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)

theorem allocatedAssetsTotalsLocals (imms : Store)
    (assets ptr lost total shares ptr' supply : UInt256) (mode : UInt256 := ⟨0⟩) :
    AllocatedAssetsLocals (allocatedConvertTotalsFrame (allocatedAssetsFrame imms assets ptr mode)
      lost total shares ptr' supply) assets total shares supply ptr' mode := by
  constructor <;> simp [allocatedConvertTotalsFrame, allocatedConvertResumeFrame,
    cursorResultFrame, allocatedAssetsFrame, cursorName, slotsAndCursorName,
    Std.HashMap.getElem_insert]

theorem allocatedAssetsArgsSource {frame : Frame} {evm : State}
    {assets total shares supply ptr mode : UInt256}
    (hl : AllocatedAssetsLocals frame assets total shares supply ptr mode)
    (hfit : supply.toNat + shares.toNat < UInt256.size) :
    evalExprs? config frame evm allocatedAssetsArgs =
      .ok [uint256Value assets, uint256Value (supply + shares),
        uint256Value total, uint256Value mode] := by
  have hsum := checkedAddSourceOk
    (show evalExpr? config frame evm (.var "__c1") = .ok (uint256Value supply) by
      simp only [evalExpr?, hl.supply, EvalResult.ofOption])
    (show evalExpr? config frame evm (.var "feeShares") = .ok (uint256Value shares) by
      simp only [evalExpr?, hl.shares, EvalResult.ofOption]) hfit
  simp only [allocatedAssetsArgs, evalExprs?, hsum, evalExpr?, hl.assets, hl.total,
    hl.rounding, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedAssetsArgsRevert {frame : Frame} {evm : State}
    {assets total shares supply ptr mode : UInt256}
    (hl : AllocatedAssetsLocals frame assets total shares supply ptr mode)
    (hbad : UInt256.size ≤ supply.toNat + shares.toNat) :
    evalExprs? config frame evm allocatedAssetsArgs = .revert := by
  have hsum := checkedAddSourceOverflow
    (show evalExpr? config frame evm (.var "__c1") = .ok (uint256Value supply) by
      simp only [evalExpr?, hl.supply, EvalResult.ofOption])
    (show evalExpr? config frame evm (.var "feeShares") = .ok (uint256Value shares) by
      simp only [evalExpr?, hl.shares, EvalResult.ofOption]) hbad
  simp only [allocatedAssetsArgs, evalExprs?, hsum, evalExpr?, hl.assets,
    EvalResult.ofOption, bind, EvalResult.bind]

theorem allocatedAssetsTailSource (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedAssetsLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr)
    (hs : supply.toNat + shares.toNat < UInt256.size)
    (hc : convertAssetsFits v.DECIMALS_OFFSET assets (supply + shares) total) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToAssetsFunction.body.drop 6)
      (.returned
        { contract := contract
          locals := locals.insert "__c2"
            (uint256Value (convertAssetsWord v.DECIMALS_OFFSET assets (supply + shares) total))
          immutables := immStore v } evm
        [uint256Value (convertAssetsWord v.DECIMALS_OFFSET assets (supply + shares) total),
          uint256Value ptr]) := by
  rw [allocatedConvertToAssetsFunction_tail]
  apply ExecBlock.consNormal (convertAssetsCall v (allocatedAssetsArgsSource hl hs) hc)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self,
    store_get_ne _ _ (by decide : ("__c2" == cursorName) = false), hl.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedAssetsTailReverts (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedAssetsLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr)
    (hbad : ¬ (supply.toNat + shares.toNat < UInt256.size ∧
      convertAssetsFits v.DECIMALS_OFFSET assets (supply + shares) total)) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToAssetsFunction.body.drop 6) .reverted := by
  rw [allocatedConvertToAssetsFunction_tail]
  by_cases hs : supply.toNat + shares.toNat < UInt256.size
  · exact ExecBlock.consRevert (convertAssetsCallReverts v
      (allocatedAssetsArgsSource hl hs) (fun hc ↦ hbad ⟨hs, hc⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (allocatedAssetsArgsRevert hl (Nat.le_of_not_gt hs)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
