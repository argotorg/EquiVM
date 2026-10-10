import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource

/-! Interest accrual resumes the allocated fee calculation, then records the returned assets. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

abbrev accrueInterestFrame := allocatedAccruedAssetsFrame

def accrueInterestResumeFrame (imms : Store) (ptr lost total shares ptr' : UInt256) : Frame :=
  cursorResultFrame (accrueInterestFrame imms ptr) "__c0"
    (.tuple [uint256Value shares, uint256Value total, uint256Value lost]) ptr'

def accrueInterestValuesFrame (imms : Store) (ptr lost total shares ptr' : UInt256) : Frame :=
  { accrueInterestResumeFrame imms ptr lost total shares ptr' with
    locals := (((accrueInterestResumeFrame imms ptr lost total shares ptr').locals.insert
      "feeShares" (uint256Value shares)).insert "newTotalAssets" (uint256Value total)).insert
      "newLostAssets" (uint256Value lost) }

def accrueInterestStoredFrame (imms : Store) (ptr lost total shares ptr' : UInt256) : Frame :=
  { accrueInterestValuesFrame imms ptr lost total shares ptr' with
    locals :=
      (accrueInterestValuesFrame imms ptr lost total shares ptr').locals.insert "__c1" .unit }

def accrueInterestStoredState (evm : State) (lost total : UInt256) : State :=
  let changed := updateLastAssetsState evm total
  Solm.EVM.storageStore changed changed.executionEnv.codeOwner ⟨23⟩ lost

theorem allocatedAccrueInterestFunction_prefix :
    allocatedAccrueInterestFunction.body =
      cursorCall allocatedAccruedFeeAssetsFunction.name [] "__c0" ++
        [.letDecl "feeShares" (some abiUInt256) (.tupleGet (.var "__c0") 0),
          .letDecl "newTotalAssets" (some abiUInt256) (.tupleGet (.var "__c0") 1),
          .letDecl "newLostAssets" (some abiUInt256) (.tupleGet (.var "__c0") 2)] ++
        allocatedAccrueInterestFunction.body.drop 6 := by decide +kernel

theorem allocatedAccrueInterestFunction_stores :
    allocatedAccrueInterestFunction.body.drop 6 =
      [.internalCall "_updateLastTotalAssets" [.var "newTotalAssets"] "__c1",
        .assign .storage ⟨"lostAssets", []⟩ (.var "newLostAssets"),
        .emit "UpdateLostAssets" [.var "newLostAssets"]] ++
      allocatedAccrueInterestFunction.body.drop 9 := by decide +kernel

theorem accrueInterestCursorArgs (imms : Store) (ptr : UInt256) (evm : State) :
    evalExprs? config (accrueInterestFrame imms ptr) evm [.var cursorName] =
      .ok [uint256Value ptr] := by
  simp only [evalExprs?, evalExpr?, allocatedAccruedAssetsFrame, store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem accrueInterestValuesPrefix (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {final : Frame} {ptr lost total shares ptr' : UInt256}
    {outcome : ExecResult}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body
      (.returned final evm' [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
        uint256Value ptr']))
    (htail : ExecBlock config (accrueInterestValuesFrame (immStore v) ptr lost total shares ptr')
      evm' (allocatedAccrueInterestFunction.body.drop 6) outcome) :
    ExecBlock config (accrueInterestFrame (immStore v) ptr) evm
      allocatedAccrueInterestFunction.body outcome := by
  rw [allocatedAccrueInterestFunction_prefix]
  apply cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedAccruedFeeAssetsFunction)
      (accrueInterestCursorArgs (immStore v) ptr evm) rfl rfl hbody)
  have hv := cursorResultFrame_value (accrueInterestFrame (immStore v) ptr) "__c0"
    (.tuple [uint256Value shares, uint256Value total, uint256Value lost]) ptr' (by decide)
  let start := accrueInterestResumeFrame (immStore v) ptr lost total shares ptr'
  let first : Frame :=
    { start with locals := start.locals.insert "feeShares" (uint256Value shares) }
  let second : Frame :=
    { first with locals := first.locals.insert "newTotalAssets" (uint256Value total) }
  have h0 : evalExpr? config start evm' (.tupleGet (.var "__c0") 0) =
      .ok (uint256Value shares) := by
    simp only [evalExpr?, start, accrueInterestResumeFrame, hv,
      EvalResult.ofOption, bind, EvalResult.bind]; rfl
  have h1 : evalExpr? config first evm' (.tupleGet (.var "__c0") 1) =
      .ok (uint256Value total) := by
    simp only [evalExpr?, first, start, accrueInterestResumeFrame,
      store_get_ne _ _ (by decide : ("feeShares" == "__c0") = false), hv,
      EvalResult.ofOption, bind, EvalResult.bind]; rfl
  have h2 : evalExpr? config second evm' (.tupleGet (.var "__c0") 2) =
      .ok (uint256Value lost) := by
    simp only [evalExpr?, second, first, start, accrueInterestResumeFrame,
      store_get_ne _ _ (by decide : ("newTotalAssets" == "__c0") = false),
      store_get_ne _ _ (by decide : ("feeShares" == "__c0") = false), hv,
      EvalResult.ofOption, bind, EvalResult.bind]; rfl
  exact ExecBlock.consNormal (ExecStmt.letDecl h0)
    (ExecBlock.consNormal (ExecStmt.letDecl h1)
      (ExecBlock.consNormal (ExecStmt.letDecl h2) htail))

theorem accrueInterestCalculationReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} {ptr : UInt256}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body .reverted) :
    ExecFuncBody config (accrueInterestFrame (immStore v) ptr) evm
      allocatedAccrueInterestFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedAccrueInterestFunction_prefix]
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedAccruedFeeAssetsFunction)
    (accrueInterestCursorArgs (immStore v) ptr evm) rfl rfl hbody)

theorem accrueInterestTotalValue (imms : Store) (ptr lost total shares ptr' : UInt256)
    (evm : State) :
    evalExpr? config (accrueInterestValuesFrame imms ptr lost total shares ptr') evm
      (.var "newTotalAssets") = .ok (uint256Value total) := by
  simp only [evalExpr?, accrueInterestValuesFrame,
    store_get_ne _ _ (by decide : ("newLostAssets" == "newTotalAssets") = false),
    store_get_self, EvalResult.ofOption]

theorem accrueInterestLostAssign (imms : Store) (ptr lost total shares ptr' : UInt256)
    (evm : State) :
    ExecStmt config (accrueInterestStoredFrame imms ptr lost total shares ptr')
      (updateLastAssetsState evm total)
      (.assign .storage ⟨"lostAssets", []⟩ (.var "newLostAssets"))
      (.ok (accrueInterestStoredFrame imms ptr lost total shares ptr')
        (accrueInterestStoredState evm lost total)) := by
  apply ExecStmt.assign (value := uint256Value lost)
  · simp only [evalExpr?, accrueInterestStoredFrame, accrueInterestValuesFrame,
      store_get_ne _ _ (by decide : ("__c1" == "newLostAssets") = false),
      store_get_self, EvalResult.ofOption]
  · exact assignStorageRef_storage_scalar_value (er := ⟨"lostAssets", []⟩)
      (ty := .elem (.int (.uint ⟨256, by decide⟩)))
      (by simp [accrueInterestStoredFrame, accrueInterestValuesFrame, accrueInterestResumeFrame,
        cursorResultFrame, allocatedAccruedAssetsFrame, cursorName, slotsAndCursorName])
      (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
      rfl rfl rfl (.inl ⟨_, rfl⟩)
      (storageLocStore_uint256 (updateLastAssetsState evm total) ⟨23⟩ lost)

theorem accrueInterestStoresPrefix (imms : Store) (ptr lost total shares ptr' : UInt256)
    (evm : State) {outcome : ExecResult}
    (htail : ExecBlock config (accrueInterestStoredFrame imms ptr lost total shares ptr')
      (accrueInterestStoredState evm lost total) (allocatedAccrueInterestFunction.body.drop 9)
      outcome) :
    ExecBlock config (accrueInterestValuesFrame imms ptr lost total shares ptr') evm
      (allocatedAccrueInterestFunction.body.drop 6) outcome := by
  rw [allocatedAccrueInterestFunction_stores]
  apply ExecBlock.consNormal
    (updateLastAssetsCall evm _ imms total (.var "newTotalAssets") "__c1"
      (accrueInterestTotalValue imms ptr lost total shares ptr' evm))
  apply ExecBlock.consNormal (accrueInterestLostAssign imms ptr lost total shares ptr' evm)
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [uint256Value lost]) ?_) htail
  simp only [evalExprs?, evalExpr?, accrueInterestStoredFrame, accrueInterestValuesFrame,
    store_get_ne _ _ (by decide : ("__c1" == "newLostAssets") = false),
    store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem accrueInterestStoresStatic (imms : Store) (ptr lost total shares ptr' : UInt256)
    (evm : State) (hperm : evm.executionEnv.perm = false) :
    ExecBlock config (accrueInterestValuesFrame imms ptr lost total shares ptr') evm
      (allocatedAccrueInterestFunction.body.drop 6) .staticViolation := by
  rw [allocatedAccrueInterestFunction_stores]
  exact ExecBlock.consStatic
    (updateLastAssetsCallStatic evm _ imms total (.var "newTotalAssets") "__c1"
      (accrueInterestTotalValue imms ptr lost total shares ptr' evm) hperm)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
