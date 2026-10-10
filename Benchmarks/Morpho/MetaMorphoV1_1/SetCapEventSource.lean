import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEnableSource
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayRead
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsSource

/-! Checked total-assets update and withdrawal-queue event in the cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def setCapQueueValues (evm : State) : List Value :=
  wordArrayValues (fun i ↦ Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (solidityBytesDataBaseSlot ⟨21⟩ + UInt256.ofNat i)) 0 (setCapQueueLength evm).toNat

theorem setCapQueueRead {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none) :
    evalExpr? config frame evm (.storage ⟨"withdrawQueue", []⟩) =
      .ok (.array (setCapQueueValues evm)) := by
  have hr : resolveStorageRef? config frame evm ⟨"withdrawQueue", []⟩ =
      .ok (⟨"withdrawQueue", []⟩, .dynamicArray (.elem (.bytes abiBytes32Width))) := by
    apply resolveStorageRef?_ok hqueue
    · simp only [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure]
    · rw [hcontract]; rfl
  have hl := storageDynamicArrayLength (cfg := config) (evm := evm)
    (elem := .elem (.bytes abiBytes32Width)) (er := ⟨"withdrawQueue", []⟩) rfl rfl
  change solidityDynamicLength? stringStorageLayout evm ⟨"withdrawQueue", []⟩ =
    .ok (setCapQueueLength evm).toNat at hl
  simp only [evalExpr?, hr, bind, EvalResult.bind]
  change solidityReadStorage? stringStorageLayout evm _ _ = _
  rw [solidityReadStorage?, hl]
  simp only [bind, EvalResult.bind]
  rw [solidityReadWordArray withdrawQueueElementLayout]
  rfl

theorem setCapEmitQueue {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none) :
    ExecBlock config frame evm
      [.emit "SetWithdrawQueue" [.env .caller, .storage ⟨"withdrawQueue", []⟩]]
      (.ok frame evm) := by
  apply (ABlock.start.emitStep
    (vals := [.address evm.executionEnv.source, .array (setCapQueueValues evm)]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, setCapQueueRead hcontract hqueue, evalExpr?, envValue,
      bind, EvalResult.bind, pure]

def setCapUpdatedFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "__c1" .unit }

theorem setCapUpdateSource {frame : Frame} {evm : State} {previous assets : UInt256}
    (hcontract : frame.contract = contract)
    (hp : frame.locals.get? "previousTotalAssets" = some (uint256Value previous))
    (ha : frame.locals.get? "__c0" = some (uint256Value assets))
    (hfit : previous.toNat + assets.toNat < UInt256.size) :
    ExecStmt config frame evm setCapEnableBody[8]!
      (.ok (setCapUpdatedFrame frame) (updateLastAssetsState evm (previous + assets))) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hp ha
  subst c
  apply updateLastAssetsCall
  apply checkedAddSourceOk _ _ hfit
  · simp only [evalExpr?, hp, EvalResult.ofOption]
  · simp only [evalExpr?, ha, EvalResult.ofOption]

theorem setCapUpdateOverflow {frame : Frame} {evm : State} {previous assets : UInt256}
    (hp : frame.locals.get? "previousTotalAssets" = some (uint256Value previous))
    (ha : frame.locals.get? "__c0" = some (uint256Value assets))
    (hbad : UInt256.size ≤ previous.toNat + assets.toNat) :
    ExecBlock config frame evm (setCapEnableBody.drop 8) .reverted := by
  apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
  have he : evalExpr? config frame evm
      (.inRange (.uint ⟨256, by decide⟩)
        (.binary .add (.var "previousTotalAssets") (.var "__c0"))) = .revert :=
    checkedAddSourceOverflow
      (by simp only [evalExpr?, hp, EvalResult.ofOption])
      (by simp only [evalExpr?, ha, EvalResult.ofOption]) hbad
  simp only [evalExprs?, he, bind, EvalResult.bind]

theorem setCapUpdateAndEmit {frame : Frame} {evm : State} {previous assets : UInt256}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none)
    (hp : frame.locals.get? "previousTotalAssets" = some (uint256Value previous))
    (ha : frame.locals.get? "__c0" = some (uint256Value assets))
    (hfit : previous.toNat + assets.toNat < UInt256.size) :
    ExecBlock config frame evm (setCapEnableBody.drop 8)
      (.ok (setCapUpdatedFrame frame) (updateLastAssetsState evm (previous + assets))) := by
  refine ExecBlock.consNormal (setCapUpdateSource hcontract hp ha hfit) ?_
  apply setCapEmitQueue (frame := setCapUpdatedFrame frame) hcontract
  rw [setCapUpdatedFrame, store_get_ne _ _ (by decide)]
  exact hqueue

end Benchmarks.Morpho.MetaMorphoV1_1
