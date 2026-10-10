import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsSimulation

/-! Cursor-aware internal share conversion: accrued totals, supply adjustment, and return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def allocatedConvertFrame (imms : Store) (assets ptr : UInt256)
    (rounding : UInt256 := ⟨0⟩) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert cursorName (uint256Value ptr)).insert "rounding"
      (uint256Value rounding)).insert "assets" (uint256Value assets)
    immutables := imms }

def allocatedConvertResumeFrame (frame : Frame) (lost total shares ptr : UInt256) : Frame :=
  cursorResultFrame frame "__c0"
    (.tuple [uint256Value shares, uint256Value total, uint256Value lost]) ptr

def allocatedConvertTotalsFrame (frame : Frame) (lost total shares ptr supply : UInt256) :
    Frame :=
  { allocatedConvertResumeFrame frame lost total shares ptr with
    locals := (((allocatedConvertResumeFrame frame lost total shares ptr).locals.insert
      "feeShares" (uint256Value shares)).insert "newTotalAssets" (uint256Value total)).insert
      "__c1" (uint256Value supply) }

theorem allocatedConvertToSharesFunction_prefix :
    allocatedConvertToSharesFunction.body =
      cursorCall allocatedAccruedFeeAssetsFunction.name [] "__c0" ++
        allocatedConvertToSharesFunction.body.drop 3 := by decide +kernel

theorem allocatedConvertToSharesFunction_totals :
    allocatedConvertToSharesFunction.body.drop 3 =
      [.letDecl "feeShares" (some abiUInt256) (.tupleGet (.var "__c0") 0),
        .letDecl "newTotalAssets" (some abiUInt256) (.tupleGet (.var "__c0") 1),
        .internalCall "totalSupply_body" [] "__c1"] ++
      allocatedConvertToSharesFunction.body.drop 6 := by decide +kernel

theorem allocatedConvertFrame_cursorArgs (imms : Store) (assets ptr : UInt256) (evm : State)
    (rounding : UInt256 := ⟨0⟩) :
    evalExprs? config (allocatedConvertFrame imms assets ptr rounding) evm [.var cursorName] =
      .ok [uint256Value ptr] := by
  simp only [evalExprs?, evalExpr?, allocatedConvertFrame,
    store_get_ne _ _ (by decide : ("assets" == cursorName) = false),
    store_get_ne _ _ (by decide : ("rounding" == cursorName) = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedAccrualTotalsPrefixSource (v : MetaMorphoV1_1Immutables)
    {locals : Store} {evm evm' : State} {final : Frame}
    {ptr lost total shares ptr' supply : UInt256} {tail : List Stmt} {outcome : ExecResult}
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm [.var cursorName] =
      .ok [uint256Value ptr])
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body
      (.returned final evm' [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
        uint256Value ptr']))
    (hs : Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ = supply)
    (htail : ExecBlock config
      (allocatedConvertTotalsFrame
        { contract := contract, locals := locals, immutables := immStore v }
        lost total shares ptr' supply) evm' tail outcome) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (cursorCall allocatedAccruedFeeAssetsFunction.name [] "__c0" ++
        [.letDecl "feeShares" (some abiUInt256) (.tupleGet (.var "__c0") 0),
          .letDecl "newTotalAssets" (some abiUInt256) (.tupleGet (.var "__c0") 1),
          .internalCall "totalSupply_body" [] "__c1"] ++ tail) outcome := by
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  apply cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedAccruedFeeAssetsFunction)
      hargs rfl rfl hbody)
  have hv := cursorResultFrame_value frame
    "__c0" (.tuple [uint256Value shares, uint256Value total, uint256Value lost]) ptr' (by decide)
  have hget0 : evalExpr? config
      (allocatedConvertResumeFrame frame
        lost total shares ptr') evm' (.tupleGet (.var "__c0") 0) =
      .ok (uint256Value shares) := by
    simp only [evalExpr?, allocatedConvertResumeFrame, hv,
      EvalResult.ofOption, bind, EvalResult.bind]; rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl hget0)
  have hget1 : evalExpr? config
      { allocatedConvertResumeFrame frame
          lost total shares ptr' with
        locals := (allocatedConvertResumeFrame frame
          lost total shares ptr').locals.insert "feeShares" (uint256Value shares) }
      evm' (.tupleGet (.var "__c0") 1) = .ok (uint256Value total) := by
    simp only [evalExpr?, allocatedConvertResumeFrame,
      store_get_ne _ _ (by decide : ("feeShares" == "__c0") = false), hv,
      EvalResult.ofOption, bind, EvalResult.bind]; rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl hget1)
  have hcall := totalSupplyInternalCall
    (((allocatedConvertResumeFrame frame
      lost total shares ptr').locals.insert "feeShares" (uint256Value shares)).insert
      "newTotalAssets" (uint256Value total)) (immStore v) evm' "__c1"
  rw [hs] at hcall
  exact ExecBlock.consNormal hcall htail


theorem allocatedConvertPrefixSource (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {final : Frame} {assets ptr lost total shares ptr' supply rounding : UInt256}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body
      (.returned final evm' [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
        uint256Value ptr']))
    (hs : Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ = supply)
    {outcome : ExecResult}
    (htail : ExecBlock config
      (allocatedConvertTotalsFrame (allocatedConvertFrame (immStore v) assets ptr rounding)
        lost total shares ptr' supply) evm'
      (allocatedConvertToSharesFunction.body.drop 6) outcome) :
    ExecBlock config (allocatedConvertFrame (immStore v) assets ptr rounding) evm
      allocatedConvertToSharesFunction.body outcome := by
  rw [allocatedConvertToSharesFunction_prefix, allocatedConvertToSharesFunction_totals]
  exact allocatedAccrualTotalsPrefixSource v
    (allocatedConvertFrame_cursorArgs (immStore v) assets ptr evm rounding) hbody hs htail

theorem allocatedConvertAccrualReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} {assets ptr rounding : UInt256}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body .reverted) :
    ExecFuncBody config (allocatedConvertFrame (immStore v) assets ptr rounding) evm
      allocatedConvertToSharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedConvertToSharesFunction_prefix]
  exact ExecBlock.consRevert
    (internalCallFunctionRevert (callee := allocatedAccruedFeeAssetsFunction)
      (allocatedConvertFrame_cursorArgs (immStore v) assets ptr evm rounding) rfl rfl hbody)

def allocatedConvertArgs : List Expr :=
  [.var "assets", .inRange (.uint ⟨256, by decide⟩)
      (.binary .add (.var "__c1") (.var "feeShares")), .var "newTotalAssets", .var "rounding"]

theorem allocatedConvertToSharesFunction_tail :
    allocatedConvertToSharesFunction.body.drop 6 =
      [.internalCall "_convertToSharesWithTotals" allocatedConvertArgs "__c2",
        .return [.var "__c2", .var cursorName]] := by decide +kernel

structure AllocatedConvertLocals (frame : Frame) (assets total shares supply ptr : UInt256)
    (mode : UInt256 := ⟨0⟩) :
    Prop where
  assets : frame.locals.get? "assets" = some (uint256Value assets)
  total : frame.locals.get? "newTotalAssets" = some (uint256Value total)
  shares : frame.locals.get? "feeShares" = some (uint256Value shares)
  supply : frame.locals.get? "__c1" = some (uint256Value supply)
  rounding : frame.locals.get? "rounding" = some (uint256Value mode)
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)

theorem allocatedConvertTotalsLocals (imms : Store)
    (assets ptr lost total shares ptr' supply : UInt256) (mode : UInt256 := ⟨0⟩) :
    AllocatedConvertLocals (allocatedConvertTotalsFrame (allocatedConvertFrame imms assets ptr mode)
      lost total shares ptr' supply) assets total shares supply ptr' mode := by
  constructor <;> simp [allocatedConvertTotalsFrame, allocatedConvertResumeFrame,
    cursorResultFrame, allocatedConvertFrame, cursorName, slotsAndCursorName,
    Std.HashMap.getElem_insert]

theorem allocatedConvertArgsSource {frame : Frame} {evm : State}
    {assets total shares supply ptr mode : UInt256}
    (hl : AllocatedConvertLocals frame assets total shares supply ptr mode)
    (hfit : supply.toNat + shares.toNat < UInt256.size) :
    evalExprs? config frame evm allocatedConvertArgs =
      .ok [uint256Value assets, uint256Value (supply + shares),
        uint256Value total, uint256Value mode] := by
  have hsum := checkedAddSourceOk
    (show evalExpr? config frame evm (.var "__c1") = .ok (uint256Value supply) by
      simp only [evalExpr?, hl.supply, EvalResult.ofOption])
    (show evalExpr? config frame evm (.var "feeShares") = .ok (uint256Value shares) by
      simp only [evalExpr?, hl.shares, EvalResult.ofOption]) hfit
  simp only [allocatedConvertArgs, evalExprs?, hsum, evalExpr?, hl.assets, hl.total,
    hl.rounding, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedConvertArgsRevert {frame : Frame} {evm : State}
    {assets total shares supply ptr mode : UInt256}
    (hl : AllocatedConvertLocals frame assets total shares supply ptr mode)
    (hbad : UInt256.size ≤ supply.toNat + shares.toNat) :
    evalExprs? config frame evm allocatedConvertArgs = .revert := by
  have hsum := checkedAddSourceOverflow
    (show evalExpr? config frame evm (.var "__c1") = .ok (uint256Value supply) by
      simp only [evalExpr?, hl.supply, EvalResult.ofOption])
    (show evalExpr? config frame evm (.var "feeShares") = .ok (uint256Value shares) by
      simp only [evalExpr?, hl.shares, EvalResult.ofOption]) hbad
  simp only [allocatedConvertArgs, evalExprs?, hsum, evalExpr?, hl.assets,
    EvalResult.ofOption, bind, EvalResult.bind]

theorem allocatedConvertTailSource (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedConvertLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr)
    (hs : supply.toNat + shares.toNat < UInt256.size)
    (hc : convertSharesFits v.DECIMALS_OFFSET assets (supply + shares) total) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToSharesFunction.body.drop 6)
      (.returned
        { contract := contract
          locals := locals.insert "__c2"
            (uint256Value (convertSharesWord v.DECIMALS_OFFSET assets (supply + shares) total))
          immutables := immStore v } evm
        [uint256Value (convertSharesWord v.DECIMALS_OFFSET assets (supply + shares) total),
          uint256Value ptr]) := by
  rw [allocatedConvertToSharesFunction_tail]
  apply ExecBlock.consNormal (convertSharesCall v (allocatedConvertArgsSource hl hs) hc)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self,
    store_get_ne _ _ (by decide : ("__c2" == cursorName) = false), hl.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedConvertTailReverts (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedConvertLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr)
    (hbad : ¬ (supply.toNat + shares.toNat < UInt256.size ∧
      convertSharesFits v.DECIMALS_OFFSET assets (supply + shares) total)) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToSharesFunction.body.drop 6) .reverted := by
  rw [allocatedConvertToSharesFunction_tail]
  by_cases hs : supply.toNat + shares.toNat < UInt256.size
  · exact ExecBlock.consRevert (convertSharesCallReverts v
      (allocatedConvertArgsSource hl hs) (fun hc ↦ hbad ⟨hs, hc⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (allocatedConvertArgsRevert hl (Nat.le_of_not_gt hs)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
