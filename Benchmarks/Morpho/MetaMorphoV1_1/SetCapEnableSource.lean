import Benchmarks.Morpho.MetaMorphoV1_1.SetCapQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.BoolByteStorage
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyAssetsSource

/-! Enabling a market and reading the previous total after the queue writes. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def setCapEnableState (evm : State) (id : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id)
    (setBoolByteTrueWord (marketRemovalConfigWord evm id) 23)

@[simp] theorem setCapEnableState_executionEnv (evm : State) (id : UInt256) :
    (setCapEnableState evm id).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem setCapEnableAssign {frame : Frame} {evm : State} {id : UInt256}
    (halias : frame.locals.get? "marketConfig" =
      some (.storageRef (marketConfigRef id) marketConfigType)) :
    ExecStmt config frame evm
      (.assign .storage ⟨"marketConfig", [.field "enabled"]⟩ (.boolLit true))
      (.ok frame (setCapEnableState evm id)) := by
  apply ExecStmt.assign (value := .bool true)
  · simp only [evalExpr?, pure]
  apply assignStorageResolved
    (loc := packedBoolLocAt (solcMappingSlot ⟨13⟩ id) 23)
    (marketConfigFieldResolve halias "enabled" .bool rfl) rfl
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 23, size := 1, hbound := by decide, type := .bool }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
    rfl
  · exact storageLocStore_bool_true_at evm _ 23

def setCapPreviousFrame (frame : Frame) (previous : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "previousTotalAssets" (uint256Value previous) }

theorem setCapEnableAssignedPrefix {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap ptr : UInt256} {result : ExecResult}
    (hready : SetCapReady frame p id cap ptr)
    (htail : ExecBlock config
      (setCapPreviousFrame frame
        (Solm.EVM.storageLoad (setCapEnableState evm id) evm.executionEnv.codeOwner ⟨22⟩))
      (setCapEnableState evm id) (setCapEnableBody.drop 5) result) :
    ExecBlock config frame evm (setCapEnableBody.drop 3) result := by
  refine ExecBlock.consNormal (setCapEnableAssign hready.reference) ?_
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
  rcases frame with ⟨c, locals, imms⟩
  have hc := hready.contract
  dsimp only at hc
  subst c
  simpa only [setCapEnableState_executionEnv] using
    evalStorage_lastTotalAssets (setCapEnableState evm id) locals imms hready.lastAssets

end Benchmarks.Morpho.MetaMorphoV1_1
