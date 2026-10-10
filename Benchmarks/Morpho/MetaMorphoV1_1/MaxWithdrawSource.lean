import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedConvertSource
import Benchmarks.Morpho.MetaMorphoV1_1.BalanceInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsSource

/-! Initialization and accrued totals for the internal withdrawal limit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxWithdrawFrame (imms : Store) (owner : AccountAddress) (ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert cursorName (uint256Value ptr)).insert "owner" (.address owner)
    immutables := imms }

def maxWithdrawZerosFrame (imms : Store) (owner : AccountAddress) (ptr : UInt256) : Frame :=
  { maxWithdrawFrame imms owner ptr with
    locals := ((((maxWithdrawFrame imms owner ptr).locals.insert "assets"
      (uint256Value ⟨0⟩)).insert "newTotalSupply" (uint256Value ⟨0⟩)).insert "newTotalAssets"
      (uint256Value ⟨0⟩)).insert "feeShares" (uint256Value ⟨0⟩) }

theorem allocatedMaxWithdrawFunction_prefix :
    allocatedMaxWithdrawFunction.body =
      [.letDecl "assets" (some abiUInt256) (.intLit 0),
        .letDecl "newTotalSupply" (some abiUInt256) (.intLit 0),
        .letDecl "newTotalAssets" (some abiUInt256) (.intLit 0),
        .letDecl "feeShares" (some abiUInt256) (.intLit 0)] ++
      allocatedMaxWithdrawFunction.body.drop 4 := by decide +kernel

theorem allocatedMaxWithdrawFunction_accrual :
    allocatedMaxWithdrawFunction.body.drop 4 =
      cursorCall allocatedAccruedFeeAssetsFunction.name [] "__c0" ++
        [.assign .localVar ⟨"feeShares", []⟩ (.tupleGet (.var "__c0") 0),
          .assign .localVar ⟨"newTotalAssets", []⟩ (.tupleGet (.var "__c0") 1),
          .internalCall "totalSupply_body" [] "__c1"] ++
        allocatedMaxWithdrawFunction.body.drop 10 := by decide +kernel

theorem maxWithdrawZerosSource (imms : Store) (owner : AccountAddress) (ptr : UInt256)
    (evm : State) :
    ABlock config evm (maxWithdrawFrame imms owner ptr) allocatedMaxWithdrawFunction.body
      (maxWithdrawZerosFrame imms owner ptr) (allocatedMaxWithdrawFunction.body.drop 4) := by
  refine ⟨fun h ↦ ?_⟩
  rw [allocatedMaxWithdrawFunction_prefix]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact h

theorem maxWithdrawCursorArgs (imms : Store) (owner : AccountAddress) (ptr : UInt256)
    (evm : State) :
    evalExprs? config (maxWithdrawZerosFrame imms owner ptr) evm [.var cursorName] =
      .ok [uint256Value ptr] := by
  simp [evalExprs?, evalExpr?, maxWithdrawZerosFrame, maxWithdrawFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem maxWithdrawAccrualReverts (v : MetaMorphoV1_1Immutables)
    {evm : State} {owner : AccountAddress} {ptr : UInt256}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body .reverted) :
    ExecFuncBody config (maxWithdrawFrame (immStore v) owner ptr) evm
      allocatedMaxWithdrawFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (maxWithdrawZerosSource (immStore v) owner ptr evm).run
  rw [allocatedMaxWithdrawFunction_accrual]
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedAccruedFeeAssetsFunction)
    (maxWithdrawCursorArgs (immStore v) owner ptr evm) rfl rfl hbody)

theorem maxWithdrawAccrualPrefix (v : MetaMorphoV1_1Immutables)
    {evm evm' : State} {final : Frame} {owner : AccountAddress}
    {ptr lost total shares ptr' supply : UInt256} {outcome : ExecResult}
    (hbody : ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body
      (.returned final evm' [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
        uint256Value ptr']))
    (hs : Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨2⟩ = supply)
    (htail : ExecBlock config
      (allocatedConvertTotalsFrame (maxWithdrawZerosFrame (immStore v) owner ptr)
        lost total shares ptr' supply) evm'
      (allocatedMaxWithdrawFunction.body.drop 10) outcome) :
    ExecBlock config (maxWithdrawFrame (immStore v) owner ptr) evm
      allocatedMaxWithdrawFunction.body outcome := by
  apply (maxWithdrawZerosSource (immStore v) owner ptr evm).run
  rw [allocatedMaxWithdrawFunction_accrual]
  let frame := maxWithdrawZerosFrame (immStore v) owner ptr
  apply cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedAccruedFeeAssetsFunction)
      (maxWithdrawCursorArgs (immStore v) owner ptr evm) rfl rfl hbody)
  have hv := cursorResultFrame_value frame "__c0"
    (.tuple [uint256Value shares, uint256Value total, uint256Value lost]) ptr' (by decide)
  have hget0 : evalExpr? config (allocatedConvertResumeFrame frame lost total shares ptr')
      evm' (.tupleGet (.var "__c0") 0) = .ok (uint256Value shares) := by
    simp only [evalExpr?, allocatedConvertResumeFrame, hv,
      EvalResult.ofOption, bind, EvalResult.bind]; rfl
  apply ExecBlock.consNormal (ExecStmt.assign hget0 ?_)
  · have hget1 : evalExpr? config
        { allocatedConvertResumeFrame frame lost total shares ptr' with
          locals := (allocatedConvertResumeFrame frame lost total shares ptr').locals.insert
            "feeShares" (uint256Value shares) }
        evm' (.tupleGet (.var "__c0") 1) = .ok (uint256Value total) := by
      simp only [evalExpr?, allocatedConvertResumeFrame,
        store_get_ne _ _ (by decide : ("feeShares" == "__c0") = false), hv,
        EvalResult.ofOption, bind, EvalResult.bind]; rfl
    apply ExecBlock.consNormal (ExecStmt.assign hget1 ?_)
    · have hcall := totalSupplyInternalCall
        (((allocatedConvertResumeFrame frame lost total shares ptr').locals.insert "feeShares"
          (uint256Value shares)).insert "newTotalAssets" (uint256Value total))
        (immStore v) evm' "__c1"
      rw [hs] at hcall
      exact ExecBlock.consNormal hcall htail
    · simp [assignStorageRef?, updateLocalPath?, allocatedConvertResumeFrame,
        cursorResultFrame, frame, maxWithdrawZerosFrame, maxWithdrawFrame, cursorName,
        slotsAndCursorName, Std.HashMap.getElem_insert,
        bind, EvalResult.bind, pure]
  · simp [assignStorageRef?, updateLocalPath?, allocatedConvertResumeFrame,
      cursorResultFrame, frame, maxWithdrawZerosFrame, maxWithdrawFrame, cursorName,
      slotsAndCursorName, Std.HashMap.getElem_insert,
      bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
