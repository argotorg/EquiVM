import Benchmarks.CompoundIII.Comet.UserBasicRead
import Benchmarks.CompoundIII.Comet.PackedStateWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def storeUserBasic (evm : EVM.State) (addr : AccountAddress) (basic : UserBasicData) : EVM.State :=
  let slot := userBasicSlot addr
  let evm := storePackedWord evm slot (UInt256.signextend ⟨12⟩ basic.principal) 0 13
  let evm := storePackedWord evm slot basic.index 13 8
  let evm := storePackedWord evm slot basic.accrued 21 8
  let evm := storePackedWord evm slot basic.assets 29 2
  storePackedWord evm slot basic.reserved 31 1

theorem writeUserBasicPrincipal (evm : EVM.State) (addr : AccountAddress) (principal : UInt256) :
    config.storageBackend.write
      ⟨"userBasic", [.mindex (.address addr), .field "principal"]⟩
      (.elem (.int (.sint ⟨104, by decide⟩))) (.int (signed104 principal)) evm =
    .ok (storePackedWord evm (userBasicSlot addr) (UInt256.signextend ⟨12⟩ principal) 0 13) := by
  apply solidityStorageBackend_write_elem _ _ _ _ _ _
    { slot := userBasicSlot addr, offset := 0, size := 13, hbound := by decide,
      type := .int (.sint ⟨104, by decide⟩) }
  · simp only [userBasicSlot, solcMappingSlot, keyValueToWord_address]; rfl
  · exact storageLocStore_packed_value evm _ _ 0 13 _ _
      (by simp only [valueToWord, signed104_word]; rfl)

theorem writeUserBasicField (evm : EVM.State) (addr : AccountAddress) (i : Fin 4)
    (word : UInt256) :
    config.storageBackend.write
      ⟨"userBasic", [.mindex (.address addr), .field (userBasicFieldName i)]⟩
      (.elem (.int (.uint (userBasicFieldWidth i)))) (.int word.toNat) evm =
    .ok (storePackedWord evm (userBasicSlot addr) word
      (userBasicFieldOffset i).val (userBasicFieldSize i).val) := by
  apply solidityStorageBackend_write_elem _ _ _ _ _ _
    { slot := userBasicSlot addr, offset := userBasicFieldOffset i,
      size := userBasicFieldSize i, hbound := by fin_cases i <;> decide,
      type := .int (.uint (userBasicFieldWidth i)) }
  · fin_cases i <;>
      simp only [userBasicSlot, userBasicFieldName, userBasicFieldOffset, userBasicFieldSize,
        userBasicFieldWidth, solcMappingSlot, keyValueToWord_address] <;> rfl
  · exact storageLocStore_packed_int evm _ word _ _ _

theorem assignUserBasicField (frame : Frame) (evm : EVM.State) (addr : AccountAddress)
    (arg : Expr) (i : Fin 4) (word : UInt256) (hc : frame.contract = contract)
    (hlocal : frame.locals.get? "userBasic" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address addr)) :
    assignStorageRef? config frame evm .storage
      ⟨"userBasic", [.mindex arg, .field (userBasicFieldName i)]⟩ (.int word.toNat) =
      .ok (frame, storePackedWord evm (userBasicSlot addr) word
        (userBasicFieldOffset i).val (userBasicFieldSize i).val) := by
  apply assignStorageRef_storage_typed hlocal
    (er := ⟨"userBasic", [.mindex (.address addr), .field (userBasicFieldName i)]⟩)
    (ty := .elem (.int (.uint (userBasicFieldWidth i))))
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; fin_cases i <;> rfl
  · exact writeUserBasicField evm addr i word

theorem writeUserBasic (evm : EVM.State) (addr : AccountAddress) (basic : UserBasicData) :
    config.storageBackend.write ⟨"userBasic", [.mindex (.address addr)]⟩
      userBasicType (userBasicValue basic) evm = .ok (storeUserBasic evm addr basic) := by
  change solidityWriteStorage? config.storageBackend.locate? evm _ _ _ = _
  rw [userBasicType, userBasicValue, solidityWriteStorage?, if_pos rfl]
  apply solidityWriteFields_cons
  · exact writeUserBasicPrincipal evm addr basic.principal
  apply solidityWriteFields_cons
  · exact writeUserBasicField _ addr 0 basic.index
  apply solidityWriteFields_cons
  · exact writeUserBasicField _ addr 1 basic.accrued
  apply solidityWriteFields_cons
  · exact writeUserBasicField _ addr 2 basic.assets
  apply solidityWriteFields_cons
  · exact writeUserBasicField _ addr 3 basic.reserved
  simp only [solidityWriteFields?]
  rfl

theorem assignUserBasic (frame : Frame) (evm : EVM.State) (addr : AccountAddress)
    (arg : Expr) (basic : UserBasicData) (hc : frame.contract = contract)
    (hlocal : frame.locals.get? "userBasic" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address addr)) :
    assignStorageRef? config frame evm .storage ⟨"userBasic", [.mindex arg]⟩
      (userBasicValue basic) = .ok (frame, storeUserBasic evm addr basic) := by
  apply assignStorageRef_storage_typed hlocal
    (er := ⟨"userBasic", [.mindex (.address addr)]⟩) (ty := userBasicType)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact writeUserBasic evm addr basic

end Benchmarks.CompoundIII.Comet
