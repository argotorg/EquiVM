import Benchmarks.CompoundIII.Comet.UserBasicData
import Benchmarks.CompoundIII.Comet.AggregateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem readUserBasicPrincipal (evm : EVM.State) (addr : AccountAddress) :
    config.storageBackend.read
      ⟨"userBasic", [.mindex (.address addr), .field "principal"]⟩
      (.elem (.int (.sint ⟨104, by decide⟩))) evm =
    .ok (.int (signed104
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)))) := by
  rw [readStorage?_elem (hbackend := rfl)
    (loc := { slot := userBasicSlot addr, offset := 0, size := 13, hbound := by decide,
              type := .int (.sint ⟨104, by decide⟩) })
    (by simp only [userBasicSlot, solcMappingSlot, keyValueToWord_address]; rfl)]
  rw [packedSint_load]
  rfl

theorem readUserBasicField (evm : EVM.State) (addr : AccountAddress) (i : Fin 4) :
    config.storageBackend.read
      ⟨"userBasic", [.mindex (.address addr), .field (userBasicFieldName i)]⟩
      (.elem (.int (.uint (userBasicFieldWidth i)))) evm =
    .ok (.int (userBasicFieldWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)) i).toNat) := by
  have hbound : (userBasicFieldOffset i).val + (userBasicFieldSize i).val - 1 < 32 := by
    fin_cases i <;> decide
  rw [readStorage?_elem (hbackend := rfl)
    (loc := { slot := userBasicSlot addr, offset := userBasicFieldOffset i,
              size := userBasicFieldSize i, hbound := hbound,
              type := .int (.uint (userBasicFieldWidth i)) })
    (by fin_cases i <;>
      simp only [userBasicSlot, userBasicFieldName, userBasicFieldOffset, userBasicFieldSize,
        userBasicFieldWidth, solcMappingSlot, keyValueToWord_address] <;> rfl)]
  rw [packedUint_load evm _ _ _ _ rfl]
  rfl

theorem readUserBasic (evm : EVM.State) (addr : AccountAddress) :
    config.storageBackend.read ⟨"userBasic", [.mindex (.address addr)]⟩ userBasicType evm =
      .ok (userBasicValue (userBasicData
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)))) := by
  change solidityReadStorage? config.storageBackend.locate? evm _ _ = _
  have hf := solidityReadFields_from_fields config.storageBackend.locate? evm
    ⟨"userBasic", [.mindex (.address addr)]⟩ userBasicTypes
    (userBasicValues (userBasicData
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))))
    (.cons ⟨rfl, readUserBasicPrincipal evm addr⟩
      (.cons ⟨rfl, readUserBasicField evm addr 0⟩
        (.cons ⟨rfl, readUserBasicField evm addr 1⟩
          (.cons ⟨rfl, readUserBasicField evm addr 2⟩
            (.cons ⟨rfl, readUserBasicField evm addr 3⟩ .nil)))))
  simp only [userBasicType, solidityReadStorage?, hf, bind, EvalResult.bind, pure]
  rfl

theorem evalUserBasic (frame : Frame) (evm : EVM.State) (addr : AccountAddress) (arg : Expr)
    (hc : frame.contract = contract) (hlocal : frame.locals.get? "userBasic" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address addr)) :
    evalExpr? config frame evm (.storage ⟨"userBasic", [.mindex arg]⟩) =
      .ok (userBasicValue (userBasicData
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)))) := by
  apply evalExpr_storage_typed hlocal
    (er := ⟨"userBasic", [.mindex (.address addr)]⟩) (ty := userBasicType)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact readUserBasic evm addr

theorem evalUserBasicFieldOf (frame : Frame) (evm : EVM.State) (addr : AccountAddress)
    (arg : Expr) (i : Fin 4) (hc : frame.contract = contract)
    (hlocal : frame.locals.get? "userBasic" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address addr)) :
    evalExpr? config frame evm
      (.storage ⟨"userBasic", [.mindex arg, .field (userBasicFieldName i)]⟩) =
      .ok (.int (userBasicFieldWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)) i).toNat) := by
  apply evalExpr_storage_typed hlocal
    (er := ⟨"userBasic", [.mindex (.address addr), .field (userBasicFieldName i)]⟩)
    (ty := .elem (.int (.uint (userBasicFieldWidth i))))
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; fin_cases i <;> rfl
  · exact readUserBasicField evm addr i

end Benchmarks.CompoundIII.Comet
