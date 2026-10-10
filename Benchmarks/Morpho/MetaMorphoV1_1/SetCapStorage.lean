import Benchmarks.Morpho.MetaMorphoV1_1.SetCapSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.LowBytesStorage
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationMutation

/-! Packed writes and final pending-cap deletion in the cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def setCapValueState (evm : State) (id cap : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id)
    (setLowBytesWord (marketRemovalConfigWord evm id) cap 23)

def setCapClearTimeState (evm : State) (id : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id)
    (UInt256.land (UInt256.ofNat (2 ^ 192 - 1)) (marketRemovalConfigWord evm id))

def setCapFinalState (evm : State) (id cap : UInt256) : State :=
  Solm.EVM.storageStore (setCapValueState evm id cap) evm.executionEnv.codeOwner
    (solcMappingSlot ⟨16⟩ id) ⟨0⟩

@[simp] theorem setCapValueState_executionEnv (evm : State) (id cap : UInt256) :
    (setCapValueState evm id cap).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

@[simp] theorem setCapClearTimeState_executionEnv (evm : State) (id : UInt256) :
    (setCapClearTimeState evm id).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem setCapValueAssign {frame : Frame} {evm : State} {id cap : UInt256}
    (halias : frame.locals.get? "marketConfig" =
      some (.storageRef (marketConfigRef id) marketConfigType))
    (hcap : frame.locals.get? "supplyCap" = some (uint256Value cap)) :
    ExecStmt config frame evm
      (.assign .storage ⟨"marketConfig", [.field "cap"]⟩ (.var "supplyCap"))
      (.ok frame (setCapValueState evm id cap)) := by
  apply ExecStmt.assign (value := uint256Value cap)
  · simp only [evalExpr?, hcap, EvalResult.ofOption]
  apply assignStorageResolved
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ id, offset := 0, size := 23, hbound := by decide,
        type := .int (.uint ⟨184, by decide⟩) })
    (marketConfigFieldResolve halias "cap" (.int (.uint ⟨184, by decide⟩)) rfl) rfl
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 0, size := 23, hbound := by decide,
        type := .int (.uint ⟨184, by decide⟩) }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
  · exact storageLocStore_uint_lowBytes evm _ cap 23 ⟨184, by decide⟩

theorem setCapClearTimeAssign {frame : Frame} {evm : State} {id : UInt256}
    (halias : frame.locals.get? "marketConfig" =
      some (.storageRef (marketConfigRef id) marketConfigType)) :
    ExecStmt config frame evm
      (.assign .storage ⟨"marketConfig", [.field "removableAt"]⟩ (.intLit 0))
      (.ok frame (setCapClearTimeState evm id)) := by
  apply ExecStmt.assign (value := .int 0)
  · simp only [evalExpr?, pure]
  apply assignStorageResolved
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ id, offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) })
    (marketConfigFieldResolve halias "removableAt" (.int (.uint ⟨64, by decide⟩)) rfl) rfl
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
  · rw [storageLocStore_zero_field _ _ rfl]
    change some (clearFieldState evm (solcMappingSlot ⟨13⟩ id) 24 8) = _
    rw [clearFieldState, clearFieldWord_high192]
    rfl

theorem setCapTailReturns {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap ptr : UInt256} (hready : SetCapReady frame p id cap ptr) :
    ∃ final, ExecBlock config frame evm setCapTail
      (.returned final (setCapFinalState evm id cap) (some [uint256Value ptr])) := by
  rcases frame with ⟨c, locals, imms⟩
  have hc : c = contract := hready.contract
  subst c
  refine ⟨⟨contract, locals.insert "__c2" (.address evm.executionEnv.source), imms⟩, ?_⟩
  refine ExecBlock.consNormal (setCapValueAssign hready.reference hready.cap) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address evm.executionEnv.source) (by rfl)
      (by simp only [evalExpr?, envValue, setCapValueState_executionEnv, pure])) ?_
  apply (ABlock.start.emitStep
    (vals := [.address evm.executionEnv.source, wordBytes32Value id, uint256Value cap]) ?_).run
  · refine ExecBlock.consNormal
      (ExecStmt.delete (evm' := setCapFinalState evm id cap) ?_) ?_
    · simpa only [setCapValueState_executionEnv] using
        deleteStorage_pendingCap (setCapValueState evm id cap)
          (locals.insert "__c2" (.address evm.executionEnv.source)) imms
          (EVM.Word.toBytesBE id) id (word_toBytesBE_length_32 id)
          (by rw [store_get_ne _ _ (by decide)]; exact hready.pending)
          (by rw [store_get_ne _ _ (by decide)]; exact hready.id)
          (keyValueToWord_fixedBytes32 id)
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp only [evalExprs?, evalExpr?,
        store_get_ne _ _ (by decide : ("__c2" == cursorName) = false), hready.cursor,
        EvalResult.ofOption, bind, EvalResult.bind, pure]
  · simp only [evalExprs?, evalExpr?, store_get_self,
      store_get_ne _ _ (by decide : ("__c2" == "id") = false), hready.id,
      store_get_ne _ _ (by decide : ("__c2" == "supplyCap") = false), hready.cap,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem setCapTailStatic {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap ptr : UInt256} (hready : SetCapReady frame p id cap ptr)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm setCapTail .staticViolation :=
  ExecBlock.consStatic (execStmt_assign_static
    (setCapValueAssign hready.reference hready.cap) hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
